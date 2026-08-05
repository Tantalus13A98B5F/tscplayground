/**
 * Layout, resolved in one pass between the lexer and the parser.
 *
 * The offside rule lives here and nowhere else. Indentation becomes `{`, `}` and
 * `;` -- the same tokens the source can write by hand -- so the parser has one
 * block form rather than a column rule shadowing a bracket rule. Information
 * flows one way: nothing here consults the parser, which is what lets the two
 * recover independently. A bad bracket corrupts this stack, not a feedback loop.
 *
 * The contract the parser may rely on: **the stream is balanced**. Every `{` has
 * its `}` and every opener its closer, inserted here if the author omitted one.
 * That is what makes the parser's own recovery safe -- skipping to the end of a
 * construct cannot run past it, because the end is a token, and every closer it
 * meets is one of its own openers'.
 *
 * The rules, entire:
 *
 *   1. `with` and `where` open a block wherever they appear, being delimiters
 *      nothing but arms may follow; `=` and `->` open one only at end of line,
 *      since mid-line an arm's `->` would swallow every arm after it. A written
 *      `{` brings its own. Nothing else opens one.
 *   2. A block's *alignment* is the column of the token after the opener, and it
 *      opens only if that column is past the enclosing alignment. Declining is
 *      ordinary: it is how arms come to sit at their `match`'s own column.
 *   3. A line-initial token at the alignment takes a `;`; below it, blocks close
 *      until it fits. Neither applies to the first token of a block.
 *   4. A line-initial closer is a continuation, exempt from rule 3.
 *   5. A closer closes every block opened inside its group, then matches.
 *
 * Two suppressions keep the output free of separators that separate nothing: no
 * `;` opening a block, and none before a `|`, which marks its own arm.
 */

import {
  type Diagnostic,
  type Position,
  produced,
  reportError,
  reportWarning,
  type Result,
} from "../diagnostics/diagnostic.ts";
import { isCloser, type Token, type TokenKind } from "./lexer.ts";

/**
 * How far left a line may start before an explicitly delimited context cannot
 * still be open. It bounds the damage of a bracket the author never closed:
 * without it one `(` runs to end of file and every item after it is parsed as
 * its contents.
 *
 * `min(enclosing alignment, first content column - 1)`. The second term is what
 * keeps a merely unindented body from destroying itself -- content flush with
 * its surroundings yields a floor of 0, no line can fall below it, and the
 * context survives to meet the closer the author did write. Where we cannot
 * tell a runaway from deliberate flush layout, we do not guess.
 */
function floorOf(enclosing: number, content: number): number {
  return Math.min(enclosing, content - 1);
}

/**
 * A run of items. `braced` is the whole difference between the two kinds. A
 * written `{` is closed by its `}` alone, since the author already said where
 * it ends and indentation is then advisory: popping it on a dedent would leave
 * the real `}` with nothing to match, so one ragged line would cost two errors
 * and a tree that reparents what the braces visibly enclose. For a layout
 * block there is no such witness -- the indentation *is* the delimiter.
 */
type Block = {
  readonly kind: "block";
  readonly alignment: number;
  readonly at: Position;
  readonly braced: boolean;
  /** Only consulted for a braced block; a layout block ends by dedent. */
  readonly floor: number;
};

/** A bracket pair. Layout is suspended inside one until a block opens. */
type Group = {
  readonly kind: "group";
  readonly closer: TokenKind;
  readonly opened: string;
  readonly closed: string;
  readonly at: Position;
  readonly floor: number;
};

type Context = Block | Group;

/** The token a block is waiting on before it can know its alignment. */
type Pending = {
  readonly braced: boolean;
  readonly at: Position;
  /** What opened it, for the message when its contents fail to indent. */
  readonly opener: string;
};

/** The bracket pairs that suspend layout. `{` is a block, so it is not one. */
const GROUPS: Partial<
  Record<TokenKind, Omit<Group, "kind" | "at" | "floor">>
> = {
  lparen: { closer: "rparen", opened: "(", closed: ")" },
  lbracket: { closer: "rbracket", opened: "[", closed: "]" },
};

export function prescan(tokens: readonly Token[]): Result<readonly Token[]> {
  const start = tokens[0];
  if (start === undefined) throw new Error("token stream must end with eof");

  const out: Token[] = [];
  const diagnostics: Diagnostic[] = [];
  /**
   * Bottom is the file itself, at column 1. Top-level items sit there and
   * nowhere else: a file-relative column would make concatenated includes
   * depend silently on order. It is never popped, so every real context has one
   * below it and the alignment lookup below always finds something.
   */
  const stack: Context[] = [
    { kind: "block", alignment: 1, at: start.at, braced: false, floor: 0 },
  ];
  let pending: Pending | undefined;

  const emit = (token: Token): void => void out.push(token);

  /**
   * `repair` marks a token standing in for one the author omitted, which is
   * always reported here. The `{`, `}` and `;` that layout itself produces are
   * not repairs -- they are what indentation *means*, and a parser error
   * landing on one is as real as any other.
   */
  const insert = (
    kind: TokenKind,
    text: string,
    at: Position,
    repair = false,
  ): void =>
    void out.push({
      kind,
      text,
      at,
      first: false,
      ...(repair ? { inserted: true } : {}),
    });

  /** The innermost block, or `undefined` when a bracket suspends layout. */
  const innermostBlock = (): Block | undefined => {
    const top = stack[stack.length - 1];
    return top?.kind === "block" ? top : undefined;
  };

  /**
   * A separator only where something needs separating: not against the `{` that
   * just opened the block, not against a `;` already there, and not before a
   * `|`, which delimits its own arm and would otherwise take one every time an
   * arm list sits at its block's alignment -- which is the usual case.
   */
  const insertSeparator = (before: Token): boolean => {
    const last = out[out.length - 1];
    if (last === undefined || last.kind === "lbrace" || last.kind === "semi") {
      return false;
    }
    if (before.kind === "bar" || before.kind === "semi") return false;
    insert("semi", ";", before.at);
    return true;
  };

  /**
   * Rule 3: settle what this line's first token belongs to, closing blocks it
   * has fallen out of and separating it from the item above when it has not.
   * Rule 4 is the caller's, which never calls this for a closer. Reports
   * whether a `;` went in, which the caller needs to avoid saying twice that
   * a body failed to indent.
   */
  const beginLine = (token: Token): boolean => {
    const column = token.at.column;
    for (;;) {
      const depth = stack.length - 1;
      const top = stack[depth] as Context;

      if (top.kind === "block" && !top.braced) {
        if (column > top.alignment) return false; // a continuation line
        if (column === top.alignment) return insertSeparator(token);
        stack.pop();
        insert("rbrace", "}", token.at);
        continue;
      }

      // Explicitly delimited, so only its closer ends it -- until the line
      // falls past the floor, where it can no longer be open at all.
      if (column <= top.floor) {
        closeThrough(depth, token.at);
        continue;
      }
      if (top.kind === "group") return false; // brackets suspend layout
      if (column > top.alignment) return false;
      if (column < top.alignment) {
        // Reading (a): the braces say where the block ends, so a ragged line
        // inside them is a misaligned item, not the end of it.
        diagnostics.push(
          reportError(
            `this line is left of column ${top.alignment}, where the items of ` +
              `the block opened at line ${top.at.line} begin`,
            token.at,
          ),
        );
      }
      return insertSeparator(token);
    }
  };

  /**
   * Unwind to `depth`, closing what the author left open. Everything above a
   * closer's own context was opened inside it and so ends with it, whether the
   * author said so or not.
   */
  const closeThrough = (depth: number, at: Position): void => {
    while (stack.length > depth) {
      const context = stack.pop() as Context;
      if (context.kind === "group") {
        insert(context.closer, context.closed, at, true);
        diagnostics.push(
          reportError(`\`${context.opened}\` is never closed`, context.at),
        );
      } else if (context.braced) {
        insert("rbrace", "}", at, true);
        diagnostics.push(reportError("`{` is never closed", context.at));
      } else {
        // Rule 5, not a repair: an unbraced block ends where its group does.
        insert("rbrace", "}", at);
      }
    }
  };

  /** Where a closer's opener sits, or -1 if the author never wrote one. */
  const openerDepth = (kind: TokenKind): number => {
    for (let depth = stack.length - 1; depth > 0; depth -= 1) {
      const context = stack[depth] as Context;
      if (kind === "rbrace") {
        if (context.kind === "block" && context.braced) return depth;
      } else if (context.kind === "group" && context.closer === kind) {
        return depth;
      }
    }
    return -1;
  };

  for (const [index, token] of tokens.entries()) {
    if (token.kind === "eof") break;

    const separated = token.first && !isCloser(token.kind)
      ? beginLine(token)
      : false;

    if (pending !== undefined) {
      const { braced, at, opener } = pending;
      pending = undefined;
      // A written `{` brings its own block, so an opener directly before one
      // would nest a second with the same contents and the same extent.
      const doubled = !braced && token.kind === "lbrace";
      // Inside brackets there is no enclosing alignment to be past, which is
      // what lets a bracketed body be laid out freely.
      const enclosing = innermostBlock()?.alignment ?? 0;
      const column = token.at.column;

      if (!doubled && enclosing > 0 && column <= enclosing) {
        diagnostics.push(
          reportError(
            `the block opened by \`${opener}\` must be indented past column ` +
              `${enclosing}`,
            token.at,
          ),
        );
        // The `;` just inserted stands where the body should have been, so the
        // parser must not report the same absence a second time against it.
        const last = out[out.length - 1];
        if (separated && last !== undefined) {
          out[out.length - 1] = { ...last, inserted: true };
        }
      }

      if (braced || (!doubled && column > enclosing)) {
        if (!braced) insert("lbrace", "{", token.at);
        stack.push({
          kind: "block",
          alignment: column,
          at,
          braced,
          floor: floorOf(enclosing, column),
        });
      }
    }

    if (isCloser(token.kind)) {
      const depth = openerDepth(token.kind);
      // No opener anywhere, so it closes nothing and is dropped. Passing it on
      // would end whatever item run the parser was in -- every item after it
      // lost to one stray character -- and popping to some boundary instead
      // would end a block the author never opened. Dropping it is also what
      // makes the contract worth stating: every closer the parser sees is one
      // its own opener is waiting for.
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
      closeThrough(depth + 1, token.at);
      stack.pop();
      emit(token);
      continue;
    }

    if (token.kind === "semi" && token.first) {
      diagnostics.push(
        reportWarning(
          "`;` here ends the previous item; put it at the end of that line, " +
            "or drop it and rely on the new line",
          token.at,
        ),
      );
    }

    emit(token);

    const next = tokens[index + 1];
    const group = GROUPS[token.kind];
    if (group !== undefined) {
      stack.push({
        kind: "group",
        ...group,
        at: token.at,
        floor: floorOf(
          innermostBlock()?.alignment ?? 0,
          next?.at.column ?? token.at.column,
        ),
      });
    }

    const endsLine = next === undefined || next.first || next.kind === "eof";
    if (token.kind === "lbrace") {
      pending = { braced: true, at: token.at, opener: "{" };
    } else if (token.kind === "with" || token.kind === "where") {
      // Pure delimiters: nothing but arms may follow, so a block is unambiguous
      // wherever they sit. That is what makes a one-line `match` read.
      pending = { braced: false, at: token.at, opener: token.text };
    } else if (
      (token.kind === "equals" || token.kind === "arrow") && endsLine
    ) {
      // Mid-line these must not open one: `| A -> 1 | B -> 2` would give the
      // first arm a body that swallows every arm after it.
      pending = { braced: false, at: token.at, opener: token.text };
    }
  }

  const end = tokens[tokens.length - 1] as Token;
  closeThrough(1, end.at);
  emit(end);
  return produced(out, diagnostics);
}

/** Render a stream compactly, for tests and for debugging the rules. */
export function showTokens(tokens: readonly Token[]): string {
  return tokens
    .filter((token) => token.kind !== "eof")
    .map((token) => token.text)
    .join(" ");
}
