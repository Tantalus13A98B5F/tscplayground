import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { showTokens, tokenize } from "./lexer.ts";
import { layout } from "./layout.ts";

/** The whole contract is the emitted stream, so every case asserts one. */
function scan(text: string): { stream: string; errors: readonly string[] } {
  const tokens = tokenize(mkSource(text, "demo.tg")).value ?? [];
  const result = layout(tokens);
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

Deno.test("a `|` is measured one column right, which is the whole arm rule", () => {
  expect(stream("match x with\n  | A -> p\n  | B -> q\n"))
    .toBe("match x with { | A -> p | B -> q }");

  // Flush with their `match` the arms still clear its floor, by the one column
  // the `|` is worth -- so they are inside the block, where any other line at
  // that column would be an item of the block around it.
  expect(stream("match x with\n| A -> p\n| B -> q\n"))
    .toBe("match x with { | A -> p | B -> q }");
  expect(stream("let x =\n  match y with\n  | A -> p\n  | B -> q\nz\n"))
    .toBe("let x = { match y with { | A -> p | B -> q } } ; z");

  // Left of their `match` that one column no longer reaches the floor, so no
  // block opens -- though the arms stay in the block the `match` is in, being
  // still to the right of *its* floor.
  expect(stream("let x =\n  match y with\n| A -> p\nz\n"))
    .toBe("let x = { match y with | A -> p } ; z");

  // The column an arm's body must clear is that one, not the `|` itself.
  expect(stream("match x with\n| A ->\n  foo\n| B -> q\n"))
    .toBe("match x with { | A -> { foo } | B -> q }");
});

Deno.test("which line a nested match begins on says whose arms are whose", () => {
  // The reading flush arms could not spell while they were an error: `| D` sits
  // left of the inner list, so it closes that and goes on with the outer one.
  expect(stream("match x with\n| A ->\n  match y with\n  | C -> p\n| D -> q\n"))
    .toBe("match x with { | A -> { match y with { | C -> p } } | D -> q }");

  // Aligned with them, it is one of them.
  expect(
    stream("match x with\n| A ->\n  match y with\n  | C -> p\n  | D -> q\n"),
  )
    .toBe("match x with { | A -> { match y with { | C -> p | D -> q } } }");

  // Which the inner `match` can only say by beginning a line of its own. From
  // inside an arm list it lines up with that list, so a flush block there would
  // give both the same column and a `|` on every line, and neither reading
  // could be written. None opens, and the parser reports what it was left with.
  expect(stream("match x with\n| A -> match y with\n| C -> p\n| D -> q\n"))
    .toBe("match x with { | A -> match y with | C -> p | D -> q }");
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

Deno.test("a closer closes every block opened inside its bracket", () => {
  // Which is how the other reading of the case above gets to be said.
  expect(stream("match x with | A -> (match y with | C -> p) | D -> q\n"))
    .toBe(
      "match x with { | A -> ( match y with { | C -> p } ) | D -> q }",
    );
  expect(stream("map (fn (x: A) ->\n  body) xs\n"))
    .toBe("map ( fn ( x : A ) -> { body } ) xs");
});

Deno.test("a closer reaches past what layout opened, and no further", () => {
  // Reaching past a written `(` would end, on the word of one character, a
  // nesting the author can see is not this closer's. So the `]` is dropped and
  // named for what it ran into, and the dedent closes what was left open.
  const crossed = scan("let x = f[g(a]\nx\n");
  expect(crossed.stream).toBe("let x = f [ g ( a ) ] ; x");
  expect(crossed.errors).toEqual([
    "`]` cannot close `(`",
    "`(` is never closed",
    "`[` is never closed",
  ]);

  // Depth changes nothing, the search stopping at the first written opener:
  // `)` pops none of these braces rather than all three.
  const deep = scan("let x = f({ a { b { c )\nx\n");
  expect(deep.stream).toBe("let x = f ( { a { b { c } } } ) ; x");
  expect(deep.errors).toEqual([
    "`)` cannot close `{`",
    "`{` is never closed",
    "`{` is never closed",
    "`{` is never closed",
    "`(` is never closed",
  ]);

  // A written `{` counts as written, so it stops one too.
  const brace = scan("let x = { f(a }\nx\n");
  expect(brace.stream).toBe("let x = { f ( a ) } ; x");
  expect(brace.errors).toEqual([
    "`}` cannot close `(`",
    "`(` is never closed",
    "`{` is never closed",
  ]);
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
  expect(stream).toBe("let x = ; a ; b ; x");
  expect(errors).toEqual(["unmatched `}`"]);
});

Deno.test("a line that dedents past its opener gives the block up", () => {
  // The opener's own context is over, so the body it promised never began. The
  // block is given up at the dedent rather than after it, which is what lets
  // `z` be seen as the new item it is. Silently: the inner `=` is left facing
  // the `}`, and the parser says what it wanted there.
  expect(stream("let x =\n  let y =\nz\nw\n"))
    .toBe("let x = { let y = } ; z ; w");
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
