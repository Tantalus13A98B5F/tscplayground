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
 * its contents are always continuations -- that, and nothing else, is what
 * "layout is suspended inside brackets" means. Its floor still bounds it, so a
 * `(` the author never closed dies at the end of the block it began in rather
 * than swallowing the file. Contents that fail to clear that floor close it at
 * once: a line there is an item of the enclosing block, so whatever opened on
 * the line above it was never closed.
 *
 * ## The rules, entire
 *
 *   1. `with` and `where` open a block wherever they appear, being delimiters
 *      nothing but arms may follow; `=` and `->` only at end of line, since
 *      mid-line an arm's `->` would swallow every arm after it. A written `{`
 *      brings its own. Nothing else opens one.
 *   2. A block's alignment is the column of the token after its opener, and it
 *      opens only if that column is past the enclosing alignment.
 *   3. A line-initial token is measured against the two columns above.
 *   4. Except a closer, which belongs to a bracket opened before the line.
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
  /** Where it opened, to report a bracket that is never closed. */
  readonly at: Position;
  readonly closerKind: TokenKind;
  readonly closer: string;
  /**
   * The bracket that opened it, `undefined` for a block -- the one thing the
   * two kinds do not share, and only diagnostics read it. A bracket is a
   * promise the author made and may have broken; a block ends by indentation,
   * so it can never be left unclosed.
   */
  readonly opener?: string;
};

/** The token a context is waiting on before it can know its alignment. */
type Pending = {
  readonly at: Position;
  /** Names the opener when the contents fail to indent. */
  readonly what: string;
  /**
   * A written `{`, held back until we know it opens a block. One whose
   * contents fail to indent opens nothing, and a `{` emitted with no context
   * behind it would leave the stream unbalanced. Absent where the block brings
   * a brace of its own.
   */
  readonly opener?: Token;
};

/** The bracket pairs whose contents are laid out freely. `{` is a block. */
const BRACKETS: Partial<
  Record<TokenKind, Pick<Context, "closerKind" | "closer" | "opener">>
> = {
  lparen: { closerKind: "rparen", closer: ")", opener: "(" },
  lbracket: { closerKind: "rbracket", closer: "]", opener: "[" },
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
   * else, since a file-relative column would make concatenated includes depend
   * silently on order. Its floor is below every real column, so it is never
   * popped and the stack is never empty.
   */
  const stack: Context[] = [{
    alignment: 1,
    floor: 0,
    // Non-empty, having an `eof`; and its position is only ever a fallback.
    at: tokens[0]!.at,
    closerKind: "rbrace",
    closer: "}",
  }];
  let pending: Pending | undefined;

  const top = (): Context => stack[stack.length - 1] as Context;

  /**
   * Where the enclosing context ends, and so the floor a new one inherits.
   * Called before the push, so `top()` is still that context: a line at its
   * items' column belongs to it, not to what we are about to open. The greater
   * of its floor covers a bracket, which has no items of its own to sit at.
   */
  const newFloor = (): number => Math.max(top().floor, top().alignment);

  const emit = (token: Token): void => void out.push(token);

  /**
   * Add a token the source does not contain. Diagnostics are the only audience
   * for `inserted`: no such character is at that position, so a message must
   * not quote one the author could go and look for.
   */
  const emitNew = (kind: TokenKind, text: string, at: Position): void =>
    void out.push({ kind, text, at, first: false, inserted: true });

  /** Close the innermost context, reporting a bracket left open. */
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
   * Give up the block an opener promised, naming the column it owed.
   *
   * A written `{` is given up with it: held back until now, it simply never
   * reaches the stream, which stays balanced -- its `}` then turns up unmatched
   * and is dropped in its turn.
   */
  const declineBlock = (what: string, at: Position): void => {
    pending = undefined;
    diagnostics.push(
      reportError(
        // `newFloor`, not the alignment: the enclosing context may be a bracket
        // the line fell out of, whose alignment is 0 and names no real column.
        `the block opened by \`${what}\` must be indented past column ` +
          `${newFloor()}`,
        at,
      ),
    );
  };

  /**
   * Rule 3: settle what this line's first token belongs to.
   *
   * Never called for a closer; rule 4 is the caller's.
   */
  const beginLine = (token: Token): void => {
    const column = token.at.column;
    for (;;) {
      // Past here, `column > top().floor`: what the line falls out of is gone.
      if (column <= top().floor) {
        // The line has left the context the opener sat in, so the body it
        // promised never began. Given up before the pop, so the column the
        // message names is the one the opener was written against.
        if (pending !== undefined) declineBlock(pending.what, token.at);
        closeTop(token.at);
        continue;
      }
      if (column > top().alignment) return; // continues the item above

      // A new item, but a separator only where the boundary is not already
      // marked: nothing above to separate from, a `{` or `;` immediately above,
      // a block still waiting to open (which makes this token its body), or a
      // token that separates itself -- `;` being the separator, and `|`
      // delimiting the arm of a list that routinely sits at the alignment.
      const above = out[out.length - 1];
      if (
        above === undefined || above.kind === "lbrace" ||
        above.kind === "semi" || pending !== undefined ||
        token.kind === "semi" || token.kind === "bar"
      ) {
        return;
      }
      emitNew("semi", ";", token.at);
      return;
    }
  };

  /**
   * Search the stack for the bracket this closer matches, answering its depth
   * or -1. A block is never the answer: it has no `opener`, and a `}` claiming
   * one would end a context nobody asked it to.
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
    // Always there: the loop breaks on the `eof` the stream ends with, so a
    // token that gets this far is never the last.
    const peek = tokens[index + 1] as Token;

    if (token.first && !isCloser(token.kind)) beginLine(token);

    if (pending !== undefined) {
      const { at, what, opener } = pending;
      const floor = newFloor();
      const column = token.at.column;
      // The alignment invariant, checked where a block learns its alignment.
      // Inside a bracket the enclosing alignment is 0 and this cannot fail,
      // which frees a bracketed body from the indentation a block would want.
      if (column > top().alignment) {
        pending = undefined;
        if (opener === undefined) emitNew("lbrace", "{", token.at);
        else emit(opener);
        stack.push({
          alignment: column,
          floor,
          at,
          closerKind: "rbrace",
          closer: "}",
          ...(opener === undefined ? {} : { opener: "{" }),
        });
      } else {
        declineBlock(what, token.at);
      }
    }

    if (isCloser(token.kind)) {
      const depth = findOpener(token.kind);
      // Nothing to close, so it is dropped: passed on it would end whatever
      // item run the parser was in, losing the rest to one stray character,
      // and popping to some boundary would end a context nobody opened. It is
      // also what the contract rests on -- every closer the parser sees is one
      // its own opener awaits.
      if (depth === -1) {
        diagnostics.push(
          reportError(
            `unmatched \`${token.text}\``,
            token.at,
            token.text.length,
          ),
        );
        continue;
      }
      // Rule 5. What is above was opened inside it, so it ends with it.
      while (stack.length > depth + 1) closeTop(token.at);
      stack.pop();
      emit(token);
      continue;
    }

    if (token.kind === "lbrace") {
      pending = { at: token.at, what: "{", opener: token };
      continue; // held back; see `Pending.opener`
    }

    emit(token);

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
      // A written `{` next brings its own block, so arming here would nest a
      // second with the same contents and extent. Declining is how that is
      // avoided: there is no doubled block to notice later.
      peek.kind !== "lbrace" &&
      // `eof` opens a line of its own, so it ends one too.
      (opens === "anywhere" || (opens === "lineend" && peek.first))
    ) {
      pending = { at: token.at, what: token.text };
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
