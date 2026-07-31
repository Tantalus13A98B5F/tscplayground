/**
 * The layout-aware cursor: the offside rule lives here and nowhere else.
 *
 * `peek` *filters* -- a token outside the current block is reported absent, so
 * blocks end through the parser's ordinary "nothing usable here" path rather
 * than through a token the lexer had to invent. A block is a column plus a
 * flag: a line's first token sits at exactly that column, anything after it
 * strictly right of it. Closers are exempt, so `)` may sit left of what it ends.
 */

import {
  type Diagnostic,
  type Position,
  reportError,
  reportWarning,
} from "../diagnostics/diagnostic.ts";
import { isCloser, type Token, type TokenKind } from "./lexer.ts";

function show(token: Token): string {
  return token.kind === "eof" ? "end of input" : `\`${token.text}\``;
}

function widthOf(token: Token): number {
  return Math.max(1, token.text.length);
}

export class Cursor {
  private index = 0;
  private indent: number;
  private lineStart = true;
  private blockAt: Position;
  readonly diagnostics: Diagnostic[] = [];

  constructor(private readonly tokens: readonly Token[]) {
    const first = tokens[0];
    if (first === undefined) throw new Error("token stream must end with eof");
    // Top-level items sit in column 1; anything else would be file-relative,
    // and concatenated includes would then depend silently on order.
    this.indent = 1;
    this.blockAt = first.at;
  }

  /** The next token regardless of layout. Never runs off: the stream ends in eof. */
  get raw(): Token {
    return this.tokens[Math.min(this.index, this.tokens.length - 1)] as Token;
  }

  get isEof(): boolean {
    return this.raw.kind === "eof";
  }

  private belongs(token: Token): boolean {
    if (isCloser(token.kind)) return token.at.column >= this.indent;
    return this.lineStart
      ? token.at.column === this.indent
      : token.at.column > this.indent;
  }

  /** The next token, or `undefined` when layout says the block has ended. */
  peek(): Token | undefined {
    const token = this.raw;
    return this.belongs(token) ? token : undefined;
  }

  at(kind: TokenKind): boolean {
    return this.peek()?.kind === kind;
  }

  advance(): void {
    if (this.index < this.tokens.length - 1) this.index += 1;
    this.lineStart = false;
  }

  accept(kind: TokenKind): Token | undefined {
    const token = this.peek();
    if (token === undefined || token.kind !== kind) return undefined;
    this.advance();
    return token;
  }

  expect(kind: TokenKind, what: string): Token | undefined {
    const token = this.accept(kind);
    if (token === undefined) this.report(what);
    return token;
  }

  /**
   * Report what was wanted here, naming a layout-filtered token as such --
   * otherwise every offside error reads as a missing token, which is the one
   * weakness of resolving layout by filtering.
   */
  report(expected: string): void {
    const token = this.raw;
    this.complain(
      this.belongs(token)
        ? `expected ${expected}, found ${show(token)}`
        : `expected ${expected}; ${
          show(token)
        } is not part of the block that ` +
          `began at line ${this.blockAt.line}, column ${this.blockAt.column}`,
    );
  }

  /** Report at the next token, in the caller's own words. */
  complain(message: string): void {
    const token = this.raw;
    this.diagnostics.push(reportError(message, token.at, widthOf(token)));
  }

  /** As `complain`, for what parses but reads wrong. */
  warn(message: string): void {
    const token = this.raw;
    this.diagnostics.push(reportWarning(message, token.at, widthOf(token)));
  }

  /**
   * Begin a new line at this block's column. Callers ignoring the result rely
   * on the other half of the rule: what stays on the *same* line sits right of
   * the column, so `peek` admits it unaided.
   */
  tryNewline(): boolean {
    const token = this.raw;
    if (!isCloser(token.kind) && token.at.column === this.indent) {
      this.lineStart = true;
      return true;
    }
    return false;
  }

  /**
   * The next item of this block: a `;` anywhere within it, or a new line at its
   * column. Nothing marks where an expression begins, so its absence is worth
   * reporting. Paired with `tryBarNewline`, which asks the same for arms and
   * differs only in leaving the `|` for the arm that follows.
   */
  trySemiNewline(): boolean {
    const token = this.raw;
    if (token.kind === "semi" && token.at.column >= this.indent) {
      // Unambiguous, so not an error, but it reads as opening the line it
      // starts rather than ending the one above.
      if (token.first) {
        this.warn(
          "`;` here ends the previous item; put it at the end of that line, " +
            "or drop it and rely on the new line",
        );
      }
      this.advance();
      this.lineStart = this.raw.at.column === this.indent;
      return true;
    }
    return this.tryNewline();
  }

  /** As `trySemiNewline`, for arms. The `|` is left for the arm parser. */
  tryBarNewline(): boolean {
    if (this.raw.kind !== "bar") return false;
    this.tryNewline(); // licenses a `|` sitting exactly at the column
    return this.at("bar");
  }

  /**
   * Run `parse` in a block starting at the next token's column.
   *
   * `strict` separates a body from a run of arms: a `let` body must be indented
   * past the `let` or it could not be told from what follows, while arms may sit
   * at the enclosing column because `|` marks them.
   */
  block<T>(strict: boolean, parse: () => T): T | undefined {
    const token = this.raw;
    const column = token.at.column;
    if (
      token.kind === "eof" ||
      (strict ? column <= this.indent : column < this.indent)
    ) {
      this.report(strict ? "an indented block" : "a block");
      return undefined;
    }
    const outerIndent = this.indent;
    const outerLineStart = this.lineStart;
    const outerAt = this.blockAt;
    this.indent = column;
    this.lineStart = true;
    this.blockAt = token.at;
    try {
      const result = parse();
      // A block holds exactly what `parse` consumed, so anything left *strictly
      // inside* it is stray. At the column itself a token is the enclosing
      // construct's next item; `;` is excluded because callers say better.
      const rest = this.raw;
      if (
        rest.kind !== "eof" && rest.kind !== "semi" && !isCloser(rest.kind) &&
        rest.at.column > this.indent
      ) {
        this.complain(
          `${show(rest)} is left over inside the block that began at line ` +
            `${this.blockAt.line}, column ${this.blockAt.column}`,
        );
      }
      return result;
    } finally {
      this.indent = outerIndent;
      this.lineStart = outerLineStart;
      this.blockAt = outerAt;
    }
  }

  /**
   * Recovery: drop tokens until one could begin the next item of this block.
   * Always terminates -- `eof` belongs to no block, so it stops every scan.
   */
  skipToBlockStart(): void {
    while (
      !this.isEof &&
      !(this.raw.at.column === this.indent && !isCloser(this.raw.kind))
    ) {
      this.advance();
    }
    this.lineStart = true;
  }

  /** Position for a node that has no token of its own to point at. */
  get here(): Position {
    return this.raw.at;
  }

  /** For loop guards: whether anything was consumed since `mark`. */
  mark(): number {
    return this.index;
  }
}
