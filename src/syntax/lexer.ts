/**
 * Tokenizer. Eager: the whole file becomes an array, so the parser can look past
 * a matching bracket -- cheap, and files are small.
 *
 * Layout is *not* resolved here. Each token carries its column and whether it
 * opens a line; `layout` turns those into `{`, `}` and `;`, and the parser sees
 * only the result. Nothing downstream of layout reads a column.
 */

import {
  type Diagnostic,
  mkPosition,
  type Position,
  produced,
  reportError,
  type Result,
  type Source,
} from "../diagnostics/diagnostic.ts";

export type TokenKind =
  | "identifier" // includes `_`, which is a name like any other
  | "let"
  | "datatype"
  | "typedef"
  | "match"
  | "fn"
  | "with" // delimits a match's scrutinee from its arms
  | "where" // the same, for a datatype's constructors
  | "unknown"
  | "never"
  | "arrow" // `->`, in a function type, after a pattern, and before a body
  | "subtype" // `<:`
  | "equals" // binds: `let` and `typedef`, nothing else
  | "colon"
  | "semi"
  | "comma"
  | "bar" // arms and constructors; never a binary operator
  | "lparen"
  | "rparen"
  | "lbracket"
  | "rbracket"
  | "lbrace"
  | "rbrace"
  | "eof";

export type Token = {
  readonly kind: TokenKind;
  readonly text: string;
  readonly at: Position;
  /** First token on its line. Read by `layout`, by nothing after it. */
  readonly first: boolean;
  /**
   * Synthesized by `layout`, so the source holds no such token. Only
   * diagnostics may consult it: an inserted token stands in for one the author
   * omitted, and the omission has already been reported where it happened.
   */
  readonly inserted?: boolean;
};

/** A line starting with one of these is a continuation, never a new item. */
export function isCloser(kind: TokenKind): boolean {
  return kind === "rparen" || kind === "rbracket" || kind === "rbrace";
}

export function isOpener(kind: TokenKind): boolean {
  return kind === "lparen" || kind === "lbracket" || kind === "lbrace";
}

/** Render a stream compactly, for tests and for debugging the layout rules. */
export function showTokens(tokens: readonly Token[]): string {
  return tokens
    .filter((token) => token.kind !== "eof")
    .map((token) => token.text)
    .join(" ");
}

/** Starts a comment, which runs to end of line. There are no block comments. */
export const LINE_COMMENT = "//";

/**
 * Drop any comment from `line`.
 *
 * A slice suffices: with no block comments and no string literals there is
 * nothing a `//` could nest inside, so the first occurrence always starts one.
 * The same invariant lets source be held as lines at all.
 *
 * Comments are whitespace -- stripped before layout is seen, so a comment-only
 * line behaves like a blank one and cannot close an indented block by sitting in
 * column 1. To grow doc comments later, record what this discards as trivia on
 * the following token.
 */
export function stripComment(line: string): string {
  const cut = line.indexOf(LINE_COMMENT);
  return cut === -1 ? line : line.slice(0, cut);
}

const KEYWORDS = new Map<string, TokenKind>([
  ["let", "let"],
  ["datatype", "datatype"],
  ["typedef", "typedef"],
  ["match", "match"],
  ["fn", "fn"],
  ["with", "with"],
  ["where", "where"],
  ["unknown", "unknown"],
  ["never", "never"],
]);

/** Longest first, so `->` never reads as a stray `-` and `<:` never as `<`. */
const PUNCTUATION: readonly (readonly [string, TokenKind])[] = [
  ["->", "arrow"],
  ["<:", "subtype"],
  ["=", "equals"],
  [":", "colon"],
  [";", "semi"],
  [",", "comma"],
  ["|", "bar"],
  ["(", "lparen"],
  [")", "rparen"],
  ["[", "lbracket"],
  ["]", "rbracket"],
  ["{", "lbrace"],
  ["}", "rbrace"],
];

const IDENTIFIER = /[A-Za-z_][A-Za-z0-9_]*/y;

/**
 * Tokenize every line. Blank lines contribute nothing, so they cannot affect
 * layout.
 *
 * The trailing `eof` sits at column 0, satisfying neither `column = indent` nor
 * `column > indent` for any real block, so it closes every open block at once
 * rather than needing a case in the parser.
 */
export function tokenize(source: Source): Result<readonly Token[]> {
  const tokens: Token[] = [];
  const diagnostics: Diagnostic[] = [];

  for (const [index, raw] of source.lines.entries()) {
    const line = stripComment(raw);
    const lineNumber = index + 1;
    let at = 0;
    let first = true;

    while (at < line.length) {
      const here = line[at];
      if (here === " ") {
        at += 1;
        continue;
      }
      const position = mkPosition(source.id, lineNumber, at + 1);

      const punctuation = PUNCTUATION.find(([text]) =>
        line.startsWith(text, at)
      );
      if (punctuation !== undefined) {
        const [text, kind] = punctuation;
        tokens.push({ kind, text, at: position, first });
        at += text.length;
        first = false;
        continue;
      }

      IDENTIFIER.lastIndex = at;
      const matched = IDENTIFIER.exec(line);
      if (matched !== null) {
        const text = matched[0];
        const kind: TokenKind = KEYWORDS.get(text) ?? "identifier";
        tokens.push({ kind, text, at: position, first });
        at += text.length;
        first = false;
        continue;
      }

      // Recovery: report and step over, so one stray byte is one diagnostic.
      diagnostics.push(reportError(`unexpected character ${here}`, position));
      at += 1;
      first = false;
    }
  }

  tokens.push({
    kind: "eof",
    text: "",
    at: mkPosition(source.id, source.lines.length, 0),
    first: true,
  });
  return produced(tokens, diagnostics);
}
