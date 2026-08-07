/**
 * A position in the token stream, and the diagnostics raised against it.
 *
 * Every error is fatal: `fail` reports and throws, and `expect` is `fail` on a
 * mismatch. So a rule either returns a node it fully read or does not return,
 * which is what lets the tree hold no recovery nodes at all.
 *
 * Layout is gone by the time anything here runs -- `layout` turned it into `{`,
 * `}` and `;` -- so this is an ordinary cursor over an array. No column is read,
 * and what `peek` shows is simply what is there.
 *
 * The stream is balanced, which is what the skips rest on: a block's end is a
 * token, so skipping to it cannot run past it into the enclosing one.
 */

import {
  type Diagnostic,
  type Position,
  reportError,
} from "../diagnostics/diagnostic.ts";
import type { Token, TokenKind } from "./lexer.ts";

/**
 * Name a token in a message.
 *
 * An inserted token is named for what it stands for, never quoted: the source
 * holds no such character, so a reader following the caret would find something
 * else there and doubt the rest of the message.
 *
 * And named as *above*, since a boundary layout inserted takes the position of
 * the line that follows it. The caret lands on that line's first token, which
 * is the one thing the boundary is not -- so the message has to say which way
 * to look, or it reads as a denial of the token under it.
 */
function show(token: Token): string {
  if (token.kind === "eof") return "end of input";
  if (token.inserted !== true) return `\`${token.text}\``;
  return token.kind === "semi"
    ? "the end of the item above"
    : "the end of the block above";
}

/**
 * Thrown by `fail`, caught only where a run of items resumes. It carries
 * nothing: the message is in `diagnostics` before it flies, so a handler has
 * only to decide where to pick the parse back up.
 */
export class ParseFailure extends Error {}

/** Re-raise anything that is not a parse failure, so real bugs still surface. */
export function rethrowUnexpected(failure: unknown): void {
  if (!(failure instanceof ParseFailure)) throw failure;
}

export class Cursor {
  private index = 0;
  /** Where the last error landed, so a cascade onto it can be dropped. */
  private lastError: Position | undefined;
  readonly diagnostics: Diagnostic[] = [];

  constructor(private readonly tokens: readonly Token[]) {
    // `peek` clamps to the last token and hands it back for ever, so if that
    // token were not `eof` every loop guarded by it would spin.
    if (tokens[tokens.length - 1]?.kind !== "eof") {
      throw new Error("token stream must end with eof");
    }
  }

  /** The next token. Never runs off: the stream ends in eof. */
  peek(): Token {
    return this.tokens[Math.min(this.index, this.tokens.length - 1)] as Token;
  }

  at(kind: TokenKind): boolean {
    return this.peek().kind === kind;
  }

  advance(): void {
    if (this.index < this.tokens.length - 1) this.index += 1;
  }

  accept(kind: TokenKind): Token | undefined {
    const token = this.peek();
    if (token.kind !== kind) return undefined;
    this.advance();
    return token;
  }

  /** The token, or no return at all. */
  expect(kind: TokenKind, what: string): Token {
    return this.accept(kind) ?? this.fail(what);
  }

  /**
   * Report what was wanted here, in the caller's own words, and give up on the
   * construct being read. Recovery is the business of whoever catches this.
   */
  fail(expected: string): never {
    this.complain(`expected ${expected}, found ${show(this.peek())}`);
    this.abandon();
  }

  /**
   * As `fail`, about something already read rather than about what is next.
   *
   * For what only a finished node can be asked -- whether a type parameter came
   * with a bound the position it sits in has no use for. The caret goes back to
   * it, since the token the parse now stands on had nothing to do with it, and
   * the message states the rule rather than naming a token that would have done.
   */
  failAt(at: Position, message: string): never {
    this.reportOnce(message, at, 1);
    this.abandon();
  }

  /**
   * Give up silently, for a construct left unreadable by a failure already
   * reported inside it -- a block whose only item was dropped has no result,
   * which is the first error's doing and not a second one.
   */
  abandon(): never {
    throw new ParseFailure();
  }

  /**
   * Report at the next token, at most one error per position.
   *
   * Recovery resumes at a token it did not consume, so the rule resuming there
   * can fail on it again -- from further out, hence with a vaguer message. The
   * first is the specific one.
   *
   * An inserted token is complained about like any other: it marks a real
   * boundary, and an error landing on one is as real as any. Only its *wording*
   * differs, which `show` handles.
   */
  private complain(message: string): void {
    const token = this.peek();
    this.reportOnce(message, token.at, Math.max(1, token.text.length));
  }

  /** The one-error-per-position rule itself, wherever the position came from. */
  private reportOnce(message: string, at: Position, length: number): void {
    if (
      this.lastError !== undefined &&
      this.lastError.line === at.line &&
      this.lastError.column === at.column
    ) {
      return;
    }
    this.lastError = at;
    this.diagnostics.push(reportError(message, at, length));
  }

  /** Recovery in a block: drop what is left, stopping at the `;` after it. */
  skipToSemi(): void {
    this.skipTo((kind) => kind === "semi");
  }

  /**
   * Recovery inside an arm list, whose separator is `|`. A `;` cannot delimit
   * an arm, so one here is wreckage to skip rather than a place to resume.
   */
  skipToBar(): void {
    this.skipTo((kind) => kind === "bar");
  }

  /**
   * Skip to the next separator of the run being recovered, or to the `}` ending
   * it. Nested blocks are skipped whole, so a separator inside one is not
   * mistaken for this run's. Always terminates: eof stops it regardless.
   *
   * Braces alone are counted, `(` and `[` being wreckage like anything else: a
   * run of items is delimited by braces, so stopping at a `]` would leave the
   * parse inside a construct nobody is left to finish -- `T[a b]` would resume
   * at the `]`, which the item loop cannot use.
   */
  private skipTo(isSeparator: (kind: TokenKind) => boolean): void {
    let depth = 0;
    for (;;) {
      const token = this.peek();
      if (token.kind === "eof") return;
      if (token.kind === "lbrace") depth += 1;
      else if (token.kind === "rbrace") {
        if (depth === 0) return; // the end of the run itself
        depth -= 1;
      } else if (depth === 0 && isSeparator(token.kind)) return;
      this.advance();
    }
  }

  /** Position for a node that has no token of its own to point at. */
  get here(): Position {
    return this.peek().at;
  }

  /** For loop guards: whether anything was consumed since `mark`. */
  mark(): number {
    return this.index;
  }
}
