/**
 * The layout-aware cursor: the offside rule lives here and nowhere else.
 *
 * `peek` *filters*. A token that does not belong to the current block is
 * reported as absent, so a block ends through the parser's ordinary "nothing
 * here I can use" path rather than through a token the lexer had to invent. A
 * block is a column plus a flag: the first token of a line must sit at exactly
 * that column, anything after it must sit strictly right of it. Closers are
 * exempt, which is what lets `)` sit at or left of the block it ends.
 */

import {
  type Diagnostic,
  type Position,
  reportError,
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
   * Report what was wanted here. A token filtered by layout is named as such:
   * otherwise every offside error reads as a missing token, which is the one
   * weakness of resolving layout by filtering.
   */
  report(expected: string): void {
    const token = this.raw;
    const message = this.belongs(token)
      ? `expected ${expected}, found ${show(token)}`
      : `expected ${expected}; ${show(token)} is not part of the block that ` +
        `began at line ${this.blockAt.line}, column ${this.blockAt.column}`;
    this.diagnostics.push(reportError(message, token.at, widthOf(token)));
  }

  /**
   * Move to the next item of the current block: an explicit `;` trailing on this
   * line, or a token already sitting at the block's column.
   */
  tryStartNextLine(): boolean {
    const token = this.raw;
    if (token.kind === "semi" && token.at.column > this.indent) {
      this.advance();
      this.lineStart = this.raw.at.column === this.indent;
      return true;
    }
    if (!isCloser(token.kind) && token.at.column === this.indent) {
      this.lineStart = true;
      return true;
    }
    return false;
  }

  /**
   * Run `parse` in a block starting at the next token's column.
   *
   * `strict` is the difference between a body and a run of arms. A `let` body
   * must be indented past the `let`, or the binding could not be told from what
   * follows it. Arms may sit at the enclosing column, because `|` marks them --
   * that marker is exactly what makes the looser rule safe.
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
      return parse();
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
