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
 * safe -- skipping to the end of a block cannot run past it.
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
 *   3. A line-initial token is measured against the two columns above -- a `|`
 *      one column to its right, since it delimits an item beginning after it.
 *      That one column is the whole of the arm rule: arms written flush with
 *      their `match` clear its floor by it, so they are inside it, while an
 *      inner `match` written *on* an arm line inherits the floor they set and
 *      gets none of its own -- which is why its arms must be indented to be
 *      told from the outer ones.
 *   4. Except a closer, which belongs to whatever the author opened before the
 *      line.
 *   5. A closer ends what layout opened above it, and matches the innermost
 *      delimiter the author wrote -- only that one, since a closer must not
 *      end a construct the author can see.
 *   6. So does a `,`, when the innermost delimiter is a bracket: it separates
 *      that bracket's items, so an indented argument ends where the next one
 *      begins. It does not consume the bracket, and inside a written `{` it is
 *      an ordinary token, a block's items being separated by `;`.
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

type TokenTable<T> = Partial<Record<TokenKind, T>>;

/** The bracket pairs whose contents are laid out freely. `{` is a block. */
const BRACKETS: TokenTable<
  Pick<Context, "closerKind" | "closer" | "opener">
> = {
  lparen: { closerKind: "rparen", closer: ")", opener: "(" },
  lbracket: { closerKind: "rbracket", closer: "]", opener: "[" },
};

/** Opens a block, and whether it may do so mid-line. See rule 1. */
const OPENERS: TokenTable<"anywhere" | "lineend"> = {
  with: "anywhere",
  where: "anywhere",
  equals: "lineend",
  arrow: "lineend",
};

/**
 * The column an item beginning with this token is measured at: `|` is a
 * delimiter, so the item it introduces begins after it. An arm list therefore
 * aligns one right of its `|`, and an arm's body must clear *that*. See rule 3.
 */
const firstColumn = (token: Token): number =>
  token.at.column + (token.kind === "bar" ? 1 : 0);

export function layout(tokens: readonly Token[]): Result<readonly Token[]> {
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
    closerKind: "rbrace",
    closer: "}",
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
   *
   * Declining is silent. The parser reaches the same line and says what it
   * wanted there, with a caret on it; a column named from here would only
   * repeat what that caret already shows.
   */
  const openBlock = (token: Token, peek: Token): void => {
    const floor = newFloor();
    const alignment = firstColumn(peek);
    if (alignment > floor) {
      const written = token.kind === "lbrace";
      if (written) emit(token);
      else emitNew("lbrace", "{", token.at);
      stack.push({
        alignment,
        floor,
        at: token.at,
        closerKind: "rbrace",
        closer: "}",
        ...(written ? { opener: "{" } : {}),
      });
    }
  };

  /**
   * The innermost context the author opened, which is the only one a closer
   * may match. The search stops there rather than passing it: what layout put
   * above it may be popped to reach it, but a written opener may not, or one
   * stray closer would end a nesting the author can see is not its own.
   */
  const findWrittenOpener = (): Context | undefined => {
    for (let depth = stack.length - 1; depth > 0; depth -= 1) {
      const context = stack[depth] as Context;
      if (context.opener !== undefined) return context;
    }
    return undefined;
  };

  for (const [index, token] of tokens.entries()) {
    if (token.kind === "eof") break;
    // There, the loop having broken at the `eof` the stream ends with: no
    // token it handles is the last.
    const peek = tokens[index + 1] as Token;

    if (isCloser(token.kind)) {
      const opened = findWrittenOpener();
      if (opened !== undefined && opened.closerKind === token.kind) {
        // Rule 5. What stands above it layout opened inside it, so it ends
        // with it.
        while (top() !== opened) closeTop(token.at);
        stack.pop();
        emit(token);
      } else {
        // Closing nothing, so it is dropped: passed on it would end whatever
        // item run the parser was in, losing the rest to one stray character.
        // This is also the other half of the balance contract -- every closer
        // the parser sees is one its own opener awaits.
        diagnostics.push(
          reportError(
            // Named where there is one to name: an author looking at their own
            // `(` would not believe a closer called unmatched next to it.
            opened?.opener === undefined
              ? `unmatched \`${token.text}\``
              : `\`${token.text}\` cannot close \`${opened.opener}\``,
            token.at,
            token.text.length,
          ),
        );
      }
    } else {
      // Rule 6, before the line rules: settled first, the comma is measured
      // against the bracket it belongs to rather than against the block it
      // ends, so a leading `,` picks up no separator of its own.
      if (token.kind === "comma") {
        const opened = findWrittenOpener();
        // Everything above it layout opened, so nothing written is reported
        // unclosed here.
        if (opened !== undefined && opened.closerKind !== "rbrace") {
          while (top() !== opened) closeTop(token.at);
        }
      }

      if (token.first) {
        // Rule 3: settle what this line's first token belongs to.
        const column = firstColumn(token);
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
