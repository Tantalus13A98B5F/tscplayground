/**
 * Layout, resolved in one pass between the lexer and the parser.
 *
 * The offside rule lives here and nowhere else. Indentation becomes `{`, `}`
 * and `;` -- the tokens the source may also write by hand -- so the parser has
 * one block form rather than a column rule shadowing a bracket rule. Nothing
 * here consults the parser, which is what lets the two recover independently.
 *
 * The contract the parser may rely on: **the stream is balanced**, every closer
 * inserted here if the author omitted one. That is what makes its own recovery
 * safe -- skipping to the end of a construct cannot run past it.
 *
 * ## Contexts
 *
 * The stack holds one kind of thing, a context, carrying two columns:
 *
 *   - **alignment** -- where its items begin. Past it a line continues the item
 *     above; from the floor up to it a new item begins, and takes a `;`.
 *   - **floor** -- at or left of it the context is over. It sits where the
 *     *enclosing* context's items begin, since a line there belongs to that one.
 *
 * So a line between the two is ragged, not outside:
 *
 *     let stuff =
 *         thing
 *       other        // ragged, and still an item of the block
 *     the_end        // at the enclosing alignment, so the block is over
 *
 * A bracket is a context with alignment 0, which no line can fall short of, so
 * its contents are always continuations -- that is all "layout is suspended
 * inside brackets" means. Its floor still bounds it, so a `(` the author never
 * closed dies at the end of the block it began in rather than swallowing the
 * file.
 *
 * ## The rules, entire
 *
 *   1. `with` and `where` open a block wherever they appear, being delimiters
 *      nothing but arms may follow; `=` and `->` only at end of line, since
 *      mid-line an arm's `->` would swallow every arm after it. A written `{`
 *      brings its own. Nothing else opens one.
 *   2. A block's alignment is the column of the token after its opener, and it
 *      opens only if that column clears the floor it would inherit.
 *   3. A line-initial token is measured against the two columns above.
 *   4. Except a closer, which belongs to whatever the author opened before the
 *      line.
 *   5. A closer ends every context opened inside its own, then matches.
 */

import {
  type Diagnostic,
  type Position,
  produced,
  reportError,
  type Result,
} from "../diagnostics/diagnostic.ts";
import { isCloser, type Token, type TokenKind } from "./lexer.ts";

/**
 * A run of items: a block, or the inside of a bracket pair.
 *
 * Three invariants, which the rules below are written to keep:
 *
 *   1. A bracket's alignment is 0, so no line falls short of it.
 *   2. A block's alignment is past its floor, so it can hold an item at all.
 *      A block that fails this is closed by its own first line; rather than
 *      push one, we decline to open it.
 *   3. Floors are non-decreasing up the stack. So popping at a line never
 *      lands on a context that line continues -- it pops on, or the line
 *      begins an item there.
 */
type Context = {
  readonly alignment: number;
  readonly floor: number;
  /** Where it opened, to report it left unclosed. */
  readonly at: Position;
  readonly closerKind: TokenKind;
  readonly closer: string;
  /**
   * The delimiter the author wrote, `undefined` for a context layout opened.
   * Written means promised: only such a context can be left unclosed, and only
   * it may be what a written closer matches.
   */
  readonly opener?: string;
};

/** The bracket pairs whose contents are laid out freely. `{` is a block. */
const BRACKETS: Partial<
  Record<TokenKind, Pick<Context, "closerKind" | "closer" | "opener">>
> = {
  lparen: { closerKind: "rparen", closer: ")", opener: "(" },
  lbracket: { closerKind: "rbracket", closer: "]", opener: "[" },
};

/** Every block ends with `}`, whether layout opened it or the author did. */
const BLOCK_CLOSER: Pick<Context, "closerKind" | "closer"> = {
  closerKind: "rbrace",
  closer: "}",
};

/** Opens a block, and whether it may do so mid-line. See rule 1. */
const OPENERS: Partial<Record<TokenKind, "anywhere" | "lineend">> = {
  with: "anywhere",
  where: "anywhere",
  equals: "lineend",
  arrow: "lineend",
};

export function prescan(tokens: readonly Token[]): Result<readonly Token[]> {
  // Checked, not assumed: two casts below rest on it. The loop breaks at `eof`,
  // so every token it handles has a successor; and the flush needs the last
  // token to be the `eof` it passes on, or the parser's cursor runs off.
  const eof = tokens[tokens.length - 1];
  if (eof === undefined || eof.kind !== "eof") {
    throw new Error("token stream must end with eof");
  }
  const out: Token[] = [];
  const diagnostics: Diagnostic[] = [];
  /**
   * Bottom is the file, at column 1: top-level items sit there and nowhere
   * else, or concatenated includes would depend silently on order. Its floor is
   * below every real column, so it is never popped and the stack never empty.
   */
  const stack: Context[] = [{
    alignment: 1,
    floor: 0,
    // Non-empty, having an `eof`; and its position is only ever a fallback.
    at: tokens[0]!.at,
    ...BLOCK_CLOSER,
  }];

  const top = (): Context => stack[stack.length - 1] as Context;

  /**
   * The floor a context opened now inherits: the enclosing alignment, a line
   * there being an item of that context rather than of this one. Falling back
   * to its floor covers a bracket, whose alignment names no column -- and
   * taking the greater is what keeps invariant 3.
   */
  const newFloor = (): number => Math.max(top().floor, top().alignment);

  const emit = (token: Token): void => void out.push(token);

  /**
   * Add a token the source does not contain. Diagnostics are the only audience
   * for `inserted`: no such character is there, so a message must not quote one
   * the author could go and look for.
   */
  const emitNew = (kind: TokenKind, text: string, at: Position): void =>
    void out.push({ kind, text, at, first: false, inserted: true });

  /** Close the innermost context, reporting a written opener left open. */
  const closeTop = (at: Position): void => {
    const context = stack.pop() as Context;
    emitNew(context.closerKind, context.closer, at);
    if (context.opener !== undefined) {
      diagnostics.push(
        reportError(`\`${context.opener}\` is never closed`, context.at),
      );
    }
  };

  /**
   * Open the block an opener promises, `peek` being the token that would begin
   * it and name its alignment. Invariant 2: short of the floor the block is one
   * its own first line would close, so none is pushed -- and a written `{` is
   * dropped with it, keeping the stream balanced and leaving its `}` unmatched.
   */
  const openBlock = (token: Token, peek: Token): void => {
    const floor = newFloor();
    const alignment = peek.at.column;
    if (alignment > floor) {
      const written = token.kind === "lbrace";
      if (written) emit(token);
      else emitNew("lbrace", "{", token.at);
      stack.push({
        alignment,
        floor,
        at: token.at,
        ...BLOCK_CLOSER,
        ...(written ? { opener: "{" } : {}),
      });
    } else {
      diagnostics.push(
        reportError(
          // The floor, not the enclosing alignment: that context may be a
          // bracket, whose alignment names no column at all.
          `the block opened by \`${token.text}\` must be indented past ` +
            `column ${floor}`,
          peek.at,
        ),
      );
    }
  };

  /**
   * Search the stack for the context this closer matches, answering its depth
   * or -1. Only a written opener is ever the answer: a closer may end what the
   * author opened, never a context layout put there.
   */
  const findOpener = (kind: TokenKind): number => {
    for (let depth = stack.length - 1; depth > 0; depth -= 1) {
      const context = stack[depth] as Context;
      if (context.opener !== undefined && context.closerKind === kind) {
        return depth;
      }
    }
    return -1;
  };

  for (const [index, token] of tokens.entries()) {
    if (token.kind === "eof") break;
    // There, the loop having broken at the `eof` the stream ends with: no
    // token it handles is the last.
    const peek = tokens[index + 1] as Token;

    if (isCloser(token.kind)) {
      const depth = findOpener(token.kind);
      if (depth > 0) {
        // Rule 5. What is above was opened inside it, so it ends with it.
        while (stack.length > depth + 1) closeTop(token.at);
        stack.pop();
        emit(token);
      } else {
        // Nothing to close, so it is dropped: passed on it would end whatever
        // item run the parser was in, losing the rest to one stray character.
        // This is also the other half of the balance contract -- every closer
        // the parser sees is one its own opener awaits.
        diagnostics.push(
          reportError(
            `unmatched \`${token.text}\``,
            token.at,
            token.text.length,
          ),
        );
      }
    } else {
      if (token.first) {
        // Rule 3: settle what this line's first token belongs to.
        const column = token.at.column;
        // Past here, `column > top().floor`: what the line falls out of is gone.
        while (column <= top().floor) closeTop(token.at);
        if (column <= top().alignment) {
          // A new item, but a separator only where the boundary is not already
          // marked: nothing above to separate from, a `{` or `;` above, or a
          // token that marks itself -- `;`, and the `|` of an arm list, which
          // routinely sits at the alignment.
          const above = out[out.length - 1];
          if (
            above !== undefined &&
            above.kind !== "lbrace" && above.kind !== "semi" &&
            token.kind !== "semi" && token.kind !== "bar"
          ) emitNew("semi", ";", token.at);
        }
      }

      if (token.kind === "lbrace") {
        openBlock(token, peek);
      } else {
        emit(token);
      }

      const bracket = BRACKETS[token.kind];
      if (bracket !== undefined) {
        stack.push({
          alignment: 0,
          floor: newFloor(),
          at: token.at,
          ...bracket,
        });
      }

      const opens = OPENERS[token.kind];
      if (
        // A written `{` next brings its own block, so opening here would nest a
        // second one over the same contents and extent.
        peek.kind !== "lbrace" &&
        // `eof` opens a line of its own, so it ends one too.
        (opens === "anywhere" || (opens === "lineend" && peek.first))
      ) openBlock(token, peek);
    }
  }

  while (stack.length > 1) closeTop(eof.at);
  emit(eof);
  return produced(out, diagnostics);
}

/** Render a stream compactly, for tests and for debugging the rules. */
export function showTokens(tokens: readonly Token[]): string {
  return tokens
    .filter((token) => token.kind !== "eof")
    .map((token) => token.text)
    .join(" ");
}
