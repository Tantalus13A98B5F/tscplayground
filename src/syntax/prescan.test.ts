import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { tokenize } from "./lexer.ts";
import { prescan, showTokens } from "./prescan.ts";

/** The whole contract is the emitted stream, so every case asserts one. */
function scan(text: string): { stream: string; errors: readonly string[] } {
  const tokens = tokenize(mkSource(text, "demo.tg")).value ?? [];
  const result = prescan(tokens);
  return {
    stream: showTokens(result.value ?? []),
    errors: result.diagnostics.map((d) => d.message),
  };
}

function stream(text: string): string {
  const { stream, errors } = scan(text);
  expect(errors).toEqual([]);
  return stream;
}

Deno.test("a new line at the alignment separates items", () => {
  expect(stream("let x = a\nlet y = b\nx\n"))
    .toBe("let x = a ; let y = b ; x");
});

Deno.test("an indented line is a continuation, and takes no separator", () => {
  expect(stream("let g = f\n  (x)\ng\n")).toBe("let g = f ( x ) ; g");
  // The case that rules out a naive INDENT/DEDENT: at the alignment, `(x)`
  // must not become a call, and only the `;` says so.
  expect(stream("let g = f\n(x)\ng\n")).toBe("let g = f ; ( x ) ; g");
});

Deno.test("`=` at end of line opens a block, a dedent closes it", () => {
  expect(stream("let g =\n  let y = a\n  y\ng\n"))
    .toBe("let g = { let y = a ; y } ; g");
});

Deno.test("`=` mid-line opens nothing", () => {
  expect(stream("let x = a; let y = b\nx\n"))
    .toBe("let x = a ; let y = b ; x");
});

Deno.test("`with` opens a block wherever it sits, so one-liners read", () => {
  expect(stream("match x with | A -> p | B -> q\n"))
    .toBe("match x with { | A -> p | B -> q }");
});

Deno.test("arms must be indented past the enclosing alignment", () => {
  expect(stream("match x with\n  | A -> p\n  | B -> q\n"))
    .toBe("match x with { | A -> p | B -> q }");

  // Flush with the enclosing block they would read as items of it, so they are
  // reported -- and then admitted flat, since `|` still delimits them and the
  // rest of the file should not pay for one misindented arm list.
  const flush = scan("match x with\n| A -> p\n| B -> q\n");
  expect(flush.stream).toBe("match x with | A -> p | B -> q");
  expect(flush.errors).toEqual([
    "the block opened by `with` must be indented past column 1",
  ]);
});

Deno.test("indented arms do get a block, which a dedent then ends", () => {
  expect(stream("let x = match y with\n  | A -> p\n  | B -> q\nlet z = w\nx\n"))
    .toBe(
      "let x = match y with { | A -> p | B -> q } ; let z = w ; x",
    );
});

Deno.test("no `;` is ever emitted before a `|`", () => {
  // Arms routinely sit at their block's alignment, so this is the common case
  // rather than a corner of it.
  expect(stream("match x with | A -> p\n             | B -> q\n"))
    .toBe("match x with { | A -> p | B -> q }");
});

Deno.test("`->` at end of line opens the arm's body", () => {
  expect(stream("match x with\n  | A ->\n      f\n      g\n  | B -> q\n"))
    .toBe("match x with { | A -> { f ; g } | B -> q }");
});

Deno.test("`->` mid-line opens nothing, or one arm would eat the rest", () => {
  expect(stream("match x with | A -> p | B -> q\nx\n"))
    .toBe("match x with { | A -> p | B -> q } ; x");
});

Deno.test("a nested one-line match binds innermost", () => {
  // A dangling-else rule, but a deterministic one: nothing on the line can
  // close the inner block.
  expect(stream("match x with | A -> match y with | C -> p | D -> q\n"))
    .toBe("match x with { | A -> match y with { | C -> p | D -> q } }");
});

Deno.test("a closer closes every block opened inside its group", () => {
  // Which is how the other reading of the case above gets to be said.
  expect(stream("match x with | A -> (match y with | C -> p) | D -> q\n"))
    .toBe(
      "match x with { | A -> ( match y with { | C -> p } ) | D -> q }",
    );
  expect(stream("map (fn (x: A) ->\n  body) xs\n"))
    .toBe("map ( fn ( x : A ) -> { body } ) xs");
});

Deno.test("layout is suspended inside brackets until a block opens", () => {
  // A bracket's alignment is 0, which no column falls short of, so every line
  // inside it is a continuation however it is indented.
  expect(stream("f(\n  a,\n  b)\n")).toBe("f ( a , b )");
});

Deno.test("contents that fail to clear the floor close the bracket at once", () => {
  // A line at the enclosing block's alignment is an item of *that* block, so
  // whatever opened on the line above it was never closed. The bracket gets no
  // say: the alternative is letting it reach the end of the file.
  const { stream, errors } = scan("f(\na,\nb)\n");
  expect(stream).toBe("f ( ) ; a , ; b");
  expect(errors).toEqual(["`(` is never closed", "unmatched `)`"]);

  // Which is how an unclosed bracket costs one declaration and no more.
  const bounded = scan("let x =\n    f(\n  a\nlet y = b\ny\n");
  expect(bounded.stream).toBe("let x = { f ( ) ; a } ; let y = b ; y");
  expect(bounded.errors).toEqual(["`(` is never closed"]);
});

Deno.test("`where` delimits constructors as `with` does arms", () => {
  expect(stream("datatype Foo where\n  | A\n  | B\nx\n"))
    .toBe("datatype Foo where { | A | B } ; x");
  expect(stream("datatype Foo where | A | B\nx\n"))
    .toBe("datatype Foo where { | A | B } ; x");
});

Deno.test("a block may hold a type, closed by the same dedent rule", () => {
  expect(stream("typedef Foo[A] = (A) ->\n  (B) -> C\nx\n"))
    .toBe("typedef Foo [ A ] = ( A ) -> { ( B ) -> C } ; x");
});

Deno.test("a written `{` brings its own block, and is not doubled", () => {
  expect(stream("let x = {\n  a\n  b\n}\nx\n")).toBe("let x = { a ; b } ; x");
  expect(stream("let x =\n  { a }\nx\n")).toBe("let x = { a } ; x");
});

Deno.test("a ragged line begins an item, it does not end the block", () => {
  // Between the floor and the alignment: indented past what encloses the block,
  // so still inside it, but not lined up with its items. Ending the block there
  // would be an outside reading of a line that is visibly within it.
  expect(stream("let stuff =\n    thing\n  other\nthe_end\n"))
    .toBe("let stuff = { thing ; other } ; the_end");
  // A written `{` needs no rule of its own to keep this working.
  expect(stream("let x = { a\n  b }\nx\n")).toBe("let x = { a ; b } ; x");
});

Deno.test("a brace body flush with its surroundings cannot hold together", () => {
  // Nowhere for a floor to sit: at the enclosing alignment the body's own lines
  // are items of the enclosing block. The braces open nothing, so the `{` is
  // dropped with them and the `}` turns up unmatched. Braces buy no exemption
  // from layout, and this is the shape where that is felt.
  const { stream, errors } = scan("let x = {\na\nb\n}\nx\n");
  expect(stream).toBe("let x = a ; b ; x");
  expect(errors).toEqual([
    "the block opened by `{` must be indented past column 1",
    "unmatched `}`",
  ]);
});

Deno.test("a line that dedents past its opener gives the block up", () => {
  // The opener's own context is over, so the body it promised never began. The
  // block is given up at the dedent rather than after it, which is what lets
  // `z` be seen as the new item it is -- and what names the column the opener
  // was written against, not the one the line fell back to.
  const { stream, errors } = scan("let x =\n  let y =\nz\nw\n");
  expect(stream).toBe("let x = { let y = } ; z ; w");
  expect(errors).toEqual([
    "the block opened by `=` must be indented past column 3",
  ]);
});

Deno.test("an unclosed bracket dies at the enclosing block, not at eof", () => {
  // Without the floor one `(` runs to end of file and every item after it is
  // parsed as its contents.
  const { stream, errors } = scan("let x = f(a\nlet y = b\ny\n");
  expect(stream).toBe("let x = f ( a ) ; let y = b ; y");
  expect(errors).toEqual(["`(` is never closed"]);
});

Deno.test("what the author left open is closed, and reported once", () => {
  const paren = scan("let x = f(a\n");
  expect(paren.stream).toBe("let x = f ( a )");
  expect(paren.errors).toEqual(["`(` is never closed"]);

  const brace = scan("let x = {\n  a\n");
  expect(brace.stream).toBe("let x = { a }");
  expect(brace.errors).toEqual(["`{` is never closed"]);
});

Deno.test("an unmatched closer is dropped, and the items after it survive", () => {
  // Passed on it would end the item run the parser was in; popping to some
  // boundary would end a block the author never opened.
  const { stream, errors } = scan("let x = )\nlet y = b\ny\n");
  expect(stream).toBe("let x = ; let y = b ; y");
  expect(errors).toEqual(["unmatched `)`"]);
});

Deno.test("a `;` opening a line is measured, and brings its own separator", () => {
  // It begins an item like anything else, so it must still end the blocks the
  // line has fallen out of -- treating it as a continuation would let the item
  // after it be swallowed by a block that had visibly ended.
  expect(stream("let x = a\n; let y = b\ny\n")).toBe(
    "let x = a ; let y = b ; y",
  );
  expect(stream("let g =\n  a\n; let y = b\ny\n")).toBe(
    "let g = { a } ; let y = b ; y",
  );
});
