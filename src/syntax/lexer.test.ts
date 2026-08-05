import { expect } from "@std/expect";
import { isCloser, stripComment, type Token, tokenize } from "./lexer.ts";
import { mkSource } from "../diagnostics/diagnostic.ts";

function lex(text: string): readonly Token[] {
  const result = tokenize(mkSource(text, "demo.tg"));
  expect(result.diagnostics).toEqual([]);
  return result.value ?? [];
}

function kinds(text: string): readonly string[] {
  return lex(text).map((token) => token.kind);
}

Deno.test("tokenize ends every stream with eof", () => {
  expect(kinds("")).toEqual(["eof"]);
  expect(kinds("x")).toEqual(["identifier", "eof"]);
});

Deno.test("eof sits at column 0, so it closes every open block", () => {
  // Neither `column = indent` nor `column > indent` holds for any real block.
  const eof = lex("  x\n").at(-1);
  expect(eof?.at.column).toBe(0);
});

Deno.test("keywords are distinguished from identifiers", () => {
  expect(kinds("let datatype match unknown never")).toEqual([
    "let",
    "datatype",
    "match",
    "unknown",
    "never",
    "eof",
  ]);
  expect(kinds("lets datum matches")).toEqual([
    "identifier",
    "identifier",
    "identifier",
    "eof",
  ]);
});

Deno.test("`_` is an identifier, so the parser decides what it means", () => {
  expect(kinds("_ _x")).toEqual(["identifier", "identifier", "eof"]);
});

Deno.test("two-character punctuation wins over one", () => {
  expect(kinds("-> <: : =")).toEqual([
    "arrow",
    "subtype",
    "colon",
    "equals",
    "eof",
  ]);
});

Deno.test("tokenize covers the whole surface syntax", () => {
  expect(kinds("fn [T <: A](x: T) -> e")).toEqual([
    "fn",
    "lbracket",
    "identifier",
    "subtype",
    "identifier",
    "rbracket",
    "lparen",
    "identifier",
    "colon",
    "identifier",
    "rparen",
    "arrow",
    "identifier",
    "eof",
  ]);
  expect(kinds("datatype Pair[A, B] where | MkPair(a: A)")).toEqual([
    "datatype",
    "identifier",
    "lbracket",
    "identifier",
    "comma",
    "identifier",
    "rbracket",
    "where",
    "bar",
    "identifier",
    "lparen",
    "identifier",
    "colon",
    "identifier",
    "rparen",
    "eof",
  ]);
  expect(kinds("let x = e; {}")).toEqual([
    "let",
    "identifier",
    "equals",
    "identifier",
    "semi",
    "lbrace",
    "rbrace",
    "eof",
  ]);
});

Deno.test("columns are 1-based and count leading spaces", () => {
  const [first, second] = lex("  ab  cd");
  expect(first?.at.column).toBe(3);
  expect(second?.at.column).toBe(7);
});

Deno.test("`first` marks the leading token of each line", () => {
  const tokens = lex("a b\n  c\n");
  expect(tokens.map((token) => token.first)).toEqual([
    true,
    false,
    true,
    true, // eof
  ]);
});

Deno.test("a comment does not affect the following token's `first`", () => {
  // Comments are whitespace, so a leading one must not consume the flag.
  const tokens = lex("// note\n  c\n");
  expect(tokens[0]?.text).toBe("c");
  expect(tokens[0]?.first).toBe(true);
  expect(tokens[0]?.at.line).toBe(2);
});

Deno.test("blank lines contribute nothing, so layout cannot see them", () => {
  const tokens = lex("a\n\n   \n  b\n");
  expect(tokens.map((token) => token.text)).toEqual(["a", "b", ""]);
  expect(tokens[1]?.at.line).toBe(4);
});

Deno.test("an unexpected character is reported, then stepped over", () => {
  // Recovery: one stray byte must not swallow the rest of the line.
  const result = tokenize(mkSource("a ? b", "demo.tg"));
  expect(result.diagnostics.length).toBe(1);
  expect(result.diagnostics[0]?.message).toContain("?");
  expect(result.diagnostics[0]?.at.column).toBe(3);
  expect(result.value?.map((token) => token.text)).toEqual(["a", "b", ""]);
});

Deno.test("only closers are exempt from the layout filter", () => {
  expect(isCloser("rparen")).toBe(true);
  expect(isCloser("rbracket")).toBe(true);
  expect(isCloser("rbrace")).toBe(true);
  expect(isCloser("lparen")).toBe(false);
  expect(isCloser("identifier")).toBe(false);
});

Deno.test("stripComment drops from // to end of line", () => {
  expect(stripComment("let x = 1 // a note")).toBe("let x = 1 ");
  expect(stripComment("// whole line")).toBe("");
  expect(stripComment("let x = 1")).toBe("let x = 1");
});

Deno.test("stripComment needs no state, having nothing to nest inside", () => {
  // No block comments and no string literals, so the first // always wins.
  expect(stripComment("a // b // c")).toBe("a ");
});
