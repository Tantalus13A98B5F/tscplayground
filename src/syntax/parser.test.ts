import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { tokenize } from "./lexer.ts";
import { prescan } from "./prescan.ts";
import { parseProgram, parseType } from "./parser.ts";
import type { DatatypeDecl, Program, TermNode, TypeNode } from "./ast.ts";

/** The pipeline as the driver runs it: layout is resolved before parsing. */
function scan(text: string) {
  const tokens = tokenize(mkSource(text, "demo.tg")).value ?? [];
  return prescan(tokens);
}

function parse(text: string): { program: Program; errors: readonly string[] } {
  const laid = scan(text);
  const result = parseProgram(laid.value ?? []);
  return {
    program: result.value as Program,
    errors: [...laid.diagnostics, ...result.diagnostics].map((d) => d.message),
  };
}

function clean(text: string): Program {
  const { program, errors } = parse(text);
  expect(errors).toEqual([]);
  return program;
}

function type(text: string): TypeNode {
  const laid = scan(text);
  const result = parseType(laid.value ?? []);
  expect([...laid.diagnostics, ...result.diagnostics]).toEqual([]);
  return result.value as TypeNode;
}

/** The datatype declarations, narrowed out of the mixed declaration list. */
function datatypes(program: Program): DatatypeDecl[] {
  return program.decls.filter((decl): decl is DatatypeDecl =>
    decl.kind === "DatatypeDecl"
  );
}

/** The chain of names bound by the top-level `let`s, outermost first. */
function bindings(term: TermNode): string[] {
  const names: string[] = [];
  for (let node = term; node.kind === "Let"; node = node.body) {
    names.push(node.name.text);
  }
  return names;
}

Deno.test("a program is a chain of bindings ending in one expression", () => {
  const program = clean("let x = a\nlet y = b\nx\n");
  expect(bindings(program.term)).toEqual(["x", "y"]);
});

Deno.test("`;` and a new line are the same separator", () => {
  expect(bindings(clean("let x = a; let y = b; x").term)).toEqual(["x", "y"]);
});

Deno.test("a new line at the block column ends the bound expression", () => {
  // `(x)` here must not become a call; the prescan's `;` is what says so.
  const program = clean("let g = f\n(x)\n");
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind).toBe("Var");
  expect(program.term.kind === "Let" && program.term.body.kind).toBe("Var");
});

Deno.test("an indented continuation line does attach", () => {
  const program = clean("let g = f\n  (x)\ng\n");
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind).toBe("App");
});

Deno.test("an indented block after `=` holds its own bindings", () => {
  const program = clean("let g =\n  let y = a\n  y\ng\n");
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind).toBe("Let");
  expect(bound !== undefined && bindings(bound)).toEqual(["y"]);
});

Deno.test("a bare expression before the last one binds nothing", () => {
  // Sequencing, which earns its place once effects exist.
  expect(bindings(clean("f(a)\ng\n").term)).toEqual(["_"]);
});

Deno.test("declarations are collected, never nested in the chain", () => {
  const program = clean(
    "let a = x\ndatatype Pair[A, B] where\n  | MkPair(a: A, b: B)\nlet b = y\na\n",
  );
  expect(datatypes(program).map((d) => d.name.text)).toEqual(["Pair"]);
  expect(datatypes(program)[0]?.typeParams.map((p) => p.text)).toEqual([
    "A",
    "B",
  ]);
  expect(
    datatypes(program)[0]?.ctors[0]?.params.map((f) => f.name.text),
  ).toEqual(["a", "b"]);
  // Interleaving is erased: a `datatype` between two `let`s never entered the chain.
  expect(bindings(program.term)).toEqual(["a", "b"]);
});

Deno.test("typedef declares a transparent alias, with parameters", () => {
  const program = clean("typedef Endo[A] = (A) -> A\nx\n");
  const alias = program.decls[0];
  expect(alias?.kind).toBe("AliasDecl");
  if (alias?.kind !== "AliasDecl") return;
  expect(alias.typeParams.map((p) => p.text)).toEqual(["A"]);
  expect(alias.body.kind).toBe("FunType");
});

Deno.test("a type may span lines, wrapped in the block `->` opened", () => {
  // The prescan does not know a type from a term, and needs not: a block
  // holding one type is that type.
  const program = clean("typedef Foo[A] = (A) ->\n  (A) -> A\nx\n");
  const alias = program.decls[0];
  expect(alias?.kind === "AliasDecl" && alias.body.kind).toBe("FunType");
  const spread = clean("typedef Bar =\n  (A) -> A\nx\n");
  expect(spread.decls[0]?.kind === "AliasDecl" && spread.decls[0].body.kind)
    .toBe("FunType");
});

Deno.test("aliases and datatypes share one ordered list", () => {
  // Not two, or the source order a declaration may name backwards in
  const program = clean(
    "typedef Id = Bool\ndatatype Foo where | A\ntypedef Alt = Foo\nx\n",
  );
  expect(program.decls.map((d) => [d.kind, d.name.text])).toEqual([
    ["AliasDecl", "Id"],
    ["DatatypeDecl", "Foo"],
    ["AliasDecl", "Alt"],
  ]);
});

Deno.test("the Church encodings parse, quantifier fused into the arrow", () => {
  const program = clean(
    "typedef CBool = [A](A, A) -> A\n" +
      "typedef CNat = [A]((A) -> A, A) -> A\n" +
      "let czero = fn [A](s: (A) -> A, z: A) -> z\n" +
      "czero\n",
  );
  const [cbool, cnat] = program.decls;
  expect(
    cbool?.kind === "AliasDecl" && cbool.body.kind === "FunType" &&
      cbool.body.typeParams.length,
  ).toBe(1);
  expect(
    cnat?.kind === "AliasDecl" && cnat.body.kind === "FunType" &&
      cnat.body.params.length,
  ).toBe(2);
});

Deno.test("arms read the same on one line as on several", () => {
  // `where` opens their block wherever it sits, and rule 2 declines it when
  // they sit at the enclosing column -- so both spellings reach the same tree.
  const inline = clean("datatype Foo where | A | B\nx\n");
  const spread = clean("datatype Foo where\n  | A\n  | B\nx\n");
  const names = (p: Program) => datatypes(p)[0]?.ctors.map((c) => c.name.text);
  expect(names(inline)).toEqual(["A", "B"]);
  expect(names(spread)).toEqual(["A", "B"]);
});

Deno.test("`;` and `|` accept the same placements", () => {
  clean("let x = a;\nlet y = b\ny\n"); // trailing
  clean("match x with | A -> p | B -> q\n");
  clean("match x with\n   | A -> p\n   | B -> q\n");
  clean("match x with\n  | A -> p\n  | B -> q\n");
  // Opening a line it reads as starting an item rather than ending the one
  // above, but the two are the same separator and neither reading is wrong.
  for (
    const text of [
      "let x = a\n   ; let y = b\ny\n",
      "let x = a\n; let y = b\ny\n",
    ]
  ) {
    expect(bindings(clean(text).term)).toEqual(["x", "y"]);
  }
});

Deno.test("a prefix form may begin a sequence", () => {
  // `match` and `fn` head an item like any other, rather than stranding the rest.
  expect(
    bindings(
      clean("let f = fn (x) ->\n  match x with\n    | A -> p\n  q\nf\n").term,
    ),
  ).toEqual(["f"]);
  clean("let f = fn (x) ->\n  fn (y) -> y\n  q\nf\n");
});

Deno.test("arm placement past the opening column is free", () => {
  // An indented line is a continuation, and a continuation carries an arm just
  // as the original line could -- so these are all one rule, not three.
  clean("datatype Foo where | A | B | C\nx\n");
  clean("datatype Foo where | A\n                   | B | C\nx\n");
  clean("match x with\n  | A -> p\n   | B -> q\n");
  clean("match x with\n  | A -> p\n     | B -> q\n");
});

Deno.test("a block must be fully consumed", () => {
  // `| B` sits inside the block opened for `A`'s body, so it is stray there --
  // it reads as belonging to that body but would start an arm outside it.
  const nested = parse("match x with\n  | A ->\n   foo | B -> g\n");
  expect(nested.errors).toEqual([
    "expected `;` or a new line, then the body, found `|`",
  ]);

  // The same message catches juxtaposition, which is not application here.
  expect(parse("let x =\n  f g\nx\n").errors[0]).toContain("`;` or a new line");
  // Including at the top level, where no enclosing block would notice it.
  expect(parse("f g\n").errors[0]).toContain("`;` or a new line");
});

Deno.test("a position carries at most one error, the most specific one", () => {
  // A rule that fails without consuming leaves the token for its caller, which
  // fails on it too -- from further out, so with a vaguer message.
  expect(parse("datatype = | A\nlet y = b\ny\n").errors).toEqual([
    "expected a type name, found `=`",
  ]);
});

Deno.test("errors at distinct positions are all kept", () => {
  // The counterpart risk: deduplication must not silence a second real error.
  expect(parse("let = a\nlet = b\nlet = c\ny\n").errors.length).toBe(3);
  expect(parse("let = a; let = b\ny\n").errors.length).toBe(2); // one line
  expect(parse("let x : = a\nlet y = b\ny\n").errors.length).toBe(1);
});

Deno.test("a block never recovers into its enclosing block", () => {
  // A `let` with no body ends the inner block; `x` is the *program's* result and
  // must survive, or one missing body costs every item after it.
  const { program, errors } = parse("let x =\n  let w = a\nx\n");
  expect(errors.length).toBe(1);
  expect(program.term.kind === "Let" && program.term.body.kind).toBe("Var");
});

Deno.test("an unmatched closer costs its own item and nothing more", () => {
  // The prescan drops it, so the item run it appeared in is not ended by it and
  // `let y = b` survives -- which is the whole point of balancing the stream.
  const { program, errors } = parse("let x = )\nlet y = b\ny\n");
  expect(bindings(program.term)).toEqual(["x", "y"]);
  expect(errors[0]).toBe("unmatched `)`");
});

Deno.test("a nested block recovers like the item loop does", () => {
  // Juxtaposition is not application, so `a b c` is one mistake wherever it
  // sits -- and must cost one diagnostic there too, not a trail of leftovers.
  const outer = parse("let x = a b c\nlet y = q\ny\n");
  const inner = parse("let x =\n  let w = a b c\n  w\nx\n");
  expect(outer.errors.length).toBe(1);
  expect(inner.errors.length).toBe(1);
  // And a second mistake still reports itself rather than the wreckage.
  expect(parse("let x =\n  let w = a b c\n  let v = d e f\n  w\nx\n").errors)
    .toEqual([
      "expected `;` or a new line, then the body, found `b`",
      "expected `;` or a new line, then the body, found `e`",
    ]);
});

Deno.test("leftovers are reported once, and the items after them survive", () => {
  const { program, errors } = parse(
    "let x =\n  f g\nlet y = b\nlet z = c\ny\n",
  );
  expect(errors.length).toBe(1);
  expect(bindings(program.term)).toEqual(["x", "y", "z"]);
});

Deno.test("`;` separates items, never arms", () => {
  // Inside the block `with` or `where` opened, `|` is the only separator, so a
  // `;` there is wreckage rather than a place to resume.
  expect(parse("match x with | A -> p; | B -> q\n").errors.length)
    .toBeGreaterThan(0);
  expect(parse("datatype Foo where | A; | B\nx\n").errors.length)
    .toBeGreaterThan(0);
});

Deno.test("sequencing after a match is said with braces, or with a new line", () => {
  // On one line the arm block runs to the end of it, so `;` falls inside and is
  // rejected; braces end the block explicitly, and a new line ends it by dedent.
  expect(parse("let r = match x with | A -> f(y); g(z)\nr\n").errors.length)
    .toBeGreaterThan(0);
  clean("let r = { match x with | A -> f(y) }; g(z)\nr\n");
  clean("match x with\n  | A -> f(y)\ng(z)\n");
  // Indent the body instead, and the `;` sequences within the arm.
  clean("match x with\n  | A ->\n    f(y); g(z)\n");
});

Deno.test("arms must be indented, and a dedent ends the run", () => {
  // At the enclosing column they would read as items of the enclosing block,
  // which is the one thing `|` marking its own arm cannot make clear.
  const program = clean(
    "let x =\n  match y with\n    | A -> p\n    | B -> q\nlet z = w\nx\n",
  );
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind === "Match" && bound.arms.length).toBe(2);
  expect(bindings(program.term)).toEqual(["x", "z"]);

  // Flush, they are reported -- and then parsed anyway, since `|` does delimit
  // them and the rest of the file should not pay for one misindented list.
  const flush = parse("let x = match y with\n| A -> p\nx\n");
  expect(flush.errors).toEqual([
    "the block opened by `with` must be indented past column 1",
  ]);
  const inner = flush.program.term.kind === "Let"
    ? flush.program.term.bound
    : undefined;
  expect(inner?.kind === "Match" && inner.arms.length).toBe(1);
  expect(bindings(flush.program.term)).toEqual(["x"]);
});

Deno.test("a nested match binds its arms innermost", () => {
  // Deterministic, and the outer reading is expressible: indent the inner arms
  // so a dedent ends them, or parenthesise the inner match.
  const dangling = clean(
    "match x with | A -> match y with | C -> p | B -> q\n",
  );
  const armsOf = (term: TermNode) => term.kind === "Match" ? term.arms : [];
  expect(armsOf(dangling.term).length).toBe(1);
  expect(armsOf(armsOf(dangling.term)[0]?.body as TermNode).length).toBe(2);

  const fixed = clean(
    "match x with\n  | A -> match y with\n       | C -> p\n  | B -> q\n",
  );
  expect(armsOf(fixed.term).length).toBe(2);
  expect(armsOf(armsOf(fixed.term)[0]?.body as TermNode).length).toBe(1);

  const parenthesised = clean(
    "match x with | A -> (match y with | C -> p) | B -> q\n",
  );
  expect(armsOf(parenthesised.term).length).toBe(2);
});

Deno.test("patterns are one level deep and positional", () => {
  const program = clean("match y with\n  | MkPair(a, _) -> a\n  | _ -> b\n");
  const arms = program.term.kind === "Match" ? program.term.arms : [];
  expect(arms[0]?.pattern.kind).toBe("PCtor");
  expect(arms[0]?.pattern.kind === "PCtor" && arms[0].pattern.args.length)
    .toBe(2);
  expect(arms[1]?.pattern.kind).toBe("PWild");
});

Deno.test("a pattern that fails to parse is not a wildcard", () => {
  // `PWild` would cover every constructor, making the arm total.
  const { program, errors } = parse(
    "match y with\n  | -> a\n  | MkPair(p, q) -> p\n",
  );
  expect(errors.length).toBe(1);
  const arms = program.term.kind === "Match" ? program.term.arms : [];
  expect(arms.map((arm) => arm.pattern.kind)).toEqual(["PBad", "PCtor"]);
});

Deno.test("`_` is an ordinary name, so it binds and resolves like one", () => {
  // Only `matchPat` reads it specially; everywhere else it is just an
  // identifier, which is what leaves `let _ = e` and `fn (_) -> e` working.
  expect(bindings(clean("let _ = a\nb\n").term)).toEqual(["_"]);
  expect(clean("fn (_) -> x\n").term.kind).toBe("Abs");
  expect(clean("_\n").term.kind).toBe("Var");
});

Deno.test("a brace block may open on its own line or after the brace", () => {
  clean("let x = { a; b\n          c }\nx\n");
  clean("let x = {\n  a; b\n  c\n}\nx\n");
  clean("let x = { a\n          { b\n            c }\n        }\nx\n");
  clean("let x = {\n  a\n  {\n    b\n  }\n}\nx\n");
});

Deno.test("braces buy no exemption from layout", () => {
  // A body flush with the enclosing block is made of that block's items, so the
  // braces cannot hold it however the author meant them to. Indenting it is the
  // whole requirement -- past that, placement is free.
  expect(parse("let x = {\na\nb\n}\nx\n").errors[0]).toContain(
    "must be indented",
  );
  clean("let x = {\n  a\n  b\n}\nx\n");
  // A closing brace may still sit left of the block it ends.
  clean("let x = {\n    a\n    b\n  }\nx\n");
});

Deno.test("braces admit a binding, parentheses do not", () => {
  expect(parse("let x = { let y = a; y }\nx\n").errors).toEqual([]);
  expect(parse("let x = ( let y = a; y )\nx\n").errors.length)
    .toBeGreaterThan(0);
});

Deno.test("a lambda binds types and values in one node", () => {
  const program = clean("let id = fn [A <: unknown](x: A) -> x\nid\n");
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind).toBe("Abs");
  if (bound?.kind !== "Abs") return;
  expect(bound.typeParams.map((b) => b.name.text)).toEqual(["A"]);
  expect(bound.typeParams[0]?.bound?.kind).toBe("UnknownType");
  expect(bound.params.map((p) => p.name.text)).toEqual(["x"]);
});

Deno.test("a lambda's `->` is required, so its body is never guessed", () => {
  expect(parse("let f = fn (x) x\nf\n").errors[0]).toContain("`->`");
});

Deno.test("an omitted bound stays absent, not invented by the parser", () => {
  const program = clean("fn [A](x) -> x\n");
  const typeParams = program.term.kind === "Abs" ? program.term.typeParams : [];
  expect(typeParams[0]?.bound).toBeUndefined();
});

Deno.test("application and instantiation are both postfix", () => {
  const program = clean("f[A](x)(y)\n");
  const outer = program.term;
  expect(outer.kind).toBe("App");
  expect(outer.kind === "App" && outer.callee.kind).toBe("App");
});

Deno.test("parseType reads the fused quantifier", () => {
  const node = type("[A <: Bool](A, A) -> A");
  expect(node.kind).toBe("FunType");
  if (node.kind !== "FunType") return;
  expect(node.typeParams.map((b) => b.name.text)).toEqual(["A"]);
  expect(node.params.length).toBe(2);
});

Deno.test("a lone parenthesised type is a type, not a parameter list", () => {
  expect(type("(Bool)").kind).toBe("NameType");
  expect(type("(Bool) -> Bool").kind).toBe("FunType");
});

Deno.test("an unparenthesised parameter is the one-argument arrow", () => {
  const node = type("A -> B");
  expect(node.kind === "FunType" && node.params.length).toBe(1);
});

Deno.test("arrows are right-associative", () => {
  const node = type("A -> B -> C");
  expect(node.kind === "FunType" && node.result.kind).toBe("FunType");
});

Deno.test("a type name may be applied", () => {
  const node = type("Pair[A, Bool]");
  expect(node.kind === "NameType" && node.args.length).toBe(2);
});

Deno.test("a program with no result expression is reported", () => {
  const { errors } = parse("let x = a\n");
  expect(errors.join("\n")).toContain("result");
});

Deno.test("a match with no arms is reported", () => {
  const { errors } = parse("match y with\n");
  expect(errors.join("\n")).toContain("at least one arm");
});

Deno.test("a body that fails to indent", () => {
  const { program, errors } = parse("let x =\na\nb\n");
  expect(errors).toEqual([
    "the block opened by `=` must be indented past column 1",
    "expected an expression, found the end of this item",
  ]);
  expect(bindings(program.term)).toEqual(["x", "_"]);
});

Deno.test("recovery keeps going after a bad expression", () => {
  const { program, errors } = parse("let x = a b\nlet y = q\ny\n");
  expect(errors.length).toBe(1);
  expect(bindings(program.term)).toContain("y");
});
