/**
 * A position in the token stream, and the diagnostics raised against it.
 *
 * Layout is gone by the time anything here runs -- `prescan` turned it into
 * `{`, `}` and `;` -- so this is an ordinary cursor over an array. No column is
 * read, and there is no filtered/unfiltered distinction: what `peek` shows is
 * simply what is there.
 *
 * The stream is balanced, which is what `skipStray` rests on: a construct's end
 * is a token, so skipping to it cannot run past it into the enclosing one.
 */

import {
  type Diagnostic,
  type Position,
  reportError,
  reportWarning,
} from "../diagnostics/diagnostic.ts";
import { isCloser, isOpener, type Token, type TokenKind } from "./lexer.ts";

function show(token: Token): string {
  return token.kind === "eof" ? "end of input" : `\`${token.text}\``;
}

export class Cursor {
  private index = 0;
  /** Where the last error landed, so a cascade onto it can be dropped. */
  private lastError: Position | undefined;
  readonly diagnostics: Diagnostic[] = [];

  constructor(private readonly tokens: readonly Token[]) {
    if (tokens[0] === undefined) {
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

  get isEof(): boolean {
    return this.at("eof");
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

  expect(kind: TokenKind, what: string): Token | undefined {
    const token = this.accept(kind);
    if (token === undefined) this.report(what);
    return token;
  }

  /** Report what was wanted here, in the caller's own words. */
  report(expected: string): void {
    this.complain(`expected ${expected}, found ${show(this.peek())}`);
  }

  /**
   * Report at the next token.
   *
   * At most one error per position. A rule that fails without consuming leaves
   * the token for its caller, which fails on it in turn, so the second error
   * describes the same token from further out. The first is nearly always the
   * specific one -- where it is not, the fix is for the outer rule to say what
   * it wanted up front.
   *
   * A token inserted as a *repair* is silent: the prescan reported the omission
   * it stands for, at the place the author actually left something out, and
   * complaining again here would name a position with nothing written at it.
   * The `{`, `}` and `;` layout itself produces carry no such flag -- they are
   * what indentation means, and an error landing on one is as real as any.
   */
  complain(message: string): void {
    const token = this.peek();
    if (token.inserted === true) return;
    if (
      this.lastError !== undefined &&
      this.lastError.line === token.at.line &&
      this.lastError.column === token.at.column
    ) {
      return;
    }
    this.lastError = token.at;
    this.diagnostics.push(
      reportError(message, token.at, Math.max(1, token.text.length)),
    );
  }

  /** As `complain`, for what parses but reads wrong. */
  warn(message: string): void {
    const token = this.peek();
    this.diagnostics.push(
      reportWarning(message, token.at, Math.max(1, token.text.length)),
    );
  }

  /**
   * Recovery: drop what is left of the current construct, stopping at its next
   * item or its end. Bracketed runs are skipped whole, so a `;` inside one is
   * not mistaken for this construct's separator.
   *
   * `pastSemi` is for a construct a `;` cannot occur in -- an arm list, a type
   * -- where one is itself part of the wreckage rather than a place to resume.
   * Always terminates: every opener has its closer, and eof stops it regardless.
   */
  skipStray(pastSemi = false): void {
    let depth = 0;
    for (;;) {
      const token = this.peek();
      if (token.kind === "eof") return;
      if (depth === 0) {
        if (isCloser(token.kind)) return;
        if (token.kind === "semi" && !pastSemi) return;
      }
      if (isOpener(token.kind)) depth += 1;
      else if (isCloser(token.kind)) depth -= 1;
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
