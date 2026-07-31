import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { tokenize } from "./lexer.ts";
import { parseProgram, parseType } from "./parser.ts";
import type { DatatypeDecl, Program, TermNode, TypeNode } from "./ast.ts";

function parse(text: string): { program: Program; errors: readonly string[] } {
  const tokens = tokenize(mkSource(text, "demo.tg")).value ?? [];
  const result = parseProgram(tokens);
  return {
    program: result.value as Program,
    errors: result.diagnostics.map((d) => d.message),
  };
}

function clean(text: string): Program {
  const { program, errors } = parse(text);
  expect(errors).toEqual([]);
  return program;
}

function type(text: string): TypeNode {
  const tokens = tokenize(mkSource(text, "demo.tg")).value ?? [];
  const result = parseType(tokens);
  expect(result.diagnostics).toEqual([]);
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
  // The case that rules out INDENT/DEDENT: `(x)` here must not become a call,
  // and nothing in the token stream marks the boundary.
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
    "let a = x\ndatatype Pair[A, B] =\n| MkPair(a: A, b: B)\nlet b = y\na\n",
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

Deno.test("aliases and datatypes share one ordered list", () => {
  // Not two, or the source order a declaration may name backwards in
  const program = clean(
    "typedef Id = Bool\ndatatype Foo = | A\ntypedef Alt = Foo\nx\n",
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
      "let czero = \\[A](s: (A) -> A, z: A) z\n" +
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
  // The block opens at the first `|` either way, so `=` costs nothing.
  const inline = clean("datatype Foo = | A | B\nx\n");
  const spread = clean("datatype Foo =\n| A\n| B\nx\n");
  const names = (p: Program) => datatypes(p)[0]?.ctors.map((c) => c.name.text);
  expect(names(inline)).toEqual(["A", "B"]);
  expect(names(spread)).toEqual(["A", "B"]);
});

Deno.test("`;` and `|` accept the same placements", () => {
  // Each is a separator anywhere within its block, on this line or a new one.
  // They differ only in that `;` is consumed and `|` belongs to its arm.
  clean("let x = a;\nlet y = b\ny\n"); // trailing
  clean("match x | A -> p | B -> q\n");
  clean("match x\n   | A -> p\n   | B -> q\n");
  clean("match x\n| A -> p\n| B -> q\n");
  // A leading `;` parses, but is warned about rather than rejected.
  for (
    const text of [
      "let x = a\n   ; let y = b\ny\n",
      "let x = a\n; let y = b\ny\n",
    ]
  ) {
    const { program, errors } = parse(text);
    expect(bindings(program.term)).toEqual(["x", "y"]);
    expect(errors).toEqual([
      "`;` here ends the previous item; put it at the end of that line, or drop it and rely on the new line",
    ]);
  }
});

Deno.test("a prefix form may begin a sequence", () => {
  // `match` and `\` head an item like any other, rather than stranding the rest.
  expect(bindings(clean("let f = \\(x)\n  match x\n  | A -> p\n  q\nf\n").term))
    .toEqual(["f"]);
  clean("let f = \\(x)\n  \\(y) y\n  q\nf\n");
});

Deno.test("arm placement past the opening column is free", () => {
  // An indented line is a continuation, and a continuation carries an arm just
  // as the original line could -- so these are all one rule, not three.
  clean("datatype Foo = | A | B | C\nx\n");
  clean("datatype Foo = | A\n               | B | C\nx\n");
  clean("match x\n| A -> p\n   | B -> q\n");
  clean("match x\n| A -> p\n     | B -> q\n");
});

Deno.test("a block must be fully consumed", () => {
  // `| B` sits inside the block opened for `A`'s body, so it is stray there --
  // it reads as belonging to that body but would start an arm outside it.
  const nested = parse("match x\n| A ->\n   foo | B -> g\n");
  expect(nested.errors.length).toBe(1);
  expect(nested.errors[0]).toContain("left over");

  // The same check catches juxtaposition, which is not application here.
  expect(parse("let x =\n  f g\nx\n").errors[0]).toContain("left over");
});

Deno.test("`;` separates items, never arms", () => {
  // `|` already separates arms, so a `;` there must not be swallowed as one.
  expect(parse("match x | A -> p; | B -> q\n").errors.length)
    .toBeGreaterThan(0);
  expect(parse("datatype Foo = | A; | B\nx\n").errors.length)
    .toBeGreaterThan(0);
});

Deno.test("a `;` may not follow an arm at all", () => {
  // It would read as part of the arm but bind to the enclosing block, and the
  // same tokens legitimately end a one-line item -- so neither reading is safe.
  const { errors } = parse("match x\n| A -> f(y); g(z)\n");
  expect(errors.length).toBe(1);
  expect(errors[0]).toContain("cannot follow an arm");
  expect(parse("datatype Foo = | A; x\n").errors.length).toBe(1);
});

Deno.test("both ways of sequencing around a match stay open", () => {
  // Indent the body to sequence within the arm; brace the form to sequence
  // after it. The error above names exactly these two.
  clean("match x\n| A ->\n    f(y); g(z)\n");
  clean("let r = { match x | A -> f(y) }; g(z)\nr\n");
});

Deno.test("arms may share the keyword's column when it starts a line", () => {
  // A keyword that starts its own line owns that column, so `|` may sit there
  // -- and `let` at the same column still ends the run, since `|` marks arms.
  const program = clean(
    "let x =\n  match y\n  | A -> p\n  | B -> q\nlet z = w\nx\n",
  );
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind === "Match" && bound.arms.length).toBe(2);
  expect(bindings(program.term)).toEqual(["x", "z"]);
});

Deno.test("a mid-line keyword must have its arms indented", () => {
  // The column it would otherwise claim already belongs to the enclosing block.
  clean("let x = match y\n  | A -> p\nx\n");
  clean("let x = match y | A -> p\nx\n");
  expect(parse("let x = match y\n| A -> p\nx\n").errors.length)
    .toBeGreaterThan(0);
});

Deno.test("a nested match must indent its arms, so none dangles", () => {
  // Otherwise `| C` could belong to either match, resolved only by convention.
  expect(parse("match x\n| A -> match y\n| C -> p\n").errors.length)
    .toBeGreaterThan(0);

  const fixed = clean("match x\n| A -> match y\n       | C -> p\n| B -> q\n");
  const outer = fixed.term;
  expect(outer.kind === "Match" && outer.arms.length).toBe(2);
  const inner = outer.kind === "Match" ? outer.arms[0]?.body : undefined;
  expect(inner?.kind === "Match" && inner.arms.length).toBe(1);
});

Deno.test("patterns are one level deep and positional", () => {
  const program = clean("match y\n| MkPair(a, _) -> a\n| _ -> b\n");
  const arms = program.term.kind === "Match" ? program.term.arms : [];
  expect(arms[0]?.pattern.kind).toBe("PCtor");
  expect(arms[0]?.pattern.kind === "PCtor" && arms[0].pattern.args.length)
    .toBe(2);
  expect(arms[1]?.pattern.kind).toBe("PWild");
});

Deno.test("a pattern that fails to parse is not a wildcard", () => {
  // `PWild` would cover every constructor, making the arm total.
  const { program, errors } = parse("match y\n| -> a\n| MkPair(p, q) -> p\n");
  expect(errors.length).toBe(1);
  const arms = program.term.kind === "Match" ? program.term.arms : [];
  expect(arms.map((arm) => arm.pattern.kind)).toEqual(["PBad", "PCtor"]);
});

Deno.test("`_` is an ordinary name, so it binds and resolves like one", () => {
  // Only `matchPat` reads it specially; everywhere else it is just an
  // identifier, which is what leaves `let _ = e` and `\(_) e` working.
  expect(bindings(clean("let _ = a\nb\n").term)).toEqual(["_"]);
  expect(clean("\\(_) x\n").term.kind).toBe("Abs");
  expect(clean("_\n").term.kind).toBe("Var");
});

Deno.test("a brace block may open on its own line or after the brace", () => {
  // Either way the block's column is wherever the first expression lands, so
  // style (1) aligns under it and style (2) under the indentation.
  clean("let x = { a; b\n          c }\nx\n");
  clean("let x = {\n  a; b\n  c\n}\nx\n");
  clean("let x = { a\n          { b\n            c }\n        }\nx\n");
  clean("let x = {\n  a\n  {\n    b\n  }\n}\nx\n");
});

Deno.test("a brace block's body must be indented past the enclosing block", () => {
  expect(parse("let x = {\na\n}\nx\n").errors.length).toBeGreaterThan(0);
  // Style (1) fixes the column at the first expression, so later lines align
  // under it rather than under the brace.
  expect(parse("let x = { a\n  b }\nx\n").errors.length).toBeGreaterThan(0);
});

Deno.test("a closing brace may sit left of the block it ends", () => {
  // Closers are exempt from the layout filter; nothing else is.
  clean("let x = {\n    a\n    b\n  }\nx\n");
});

Deno.test("braces admit a binding, parentheses do not", () => {
  expect(parse("let x = { let y = a; y }\nx\n").errors).toEqual([]);
  expect(parse("let x = ( let y = a; y )\nx\n").errors.length)
    .toBeGreaterThan(0);
});

Deno.test("a lambda binds types and values in one node", () => {
  const program = clean("let id = \\[A <: unknown](x: A) x\nid\n");
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind).toBe("Abs");
  if (bound?.kind !== "Abs") return;
  expect(bound.typeParams.map((b) => b.name.text)).toEqual(["A"]);
  expect(bound.typeParams[0]?.bound?.kind).toBe("UnknownType");
  expect(bound.params.map((p) => p.name.text)).toEqual(["x"]);
});

Deno.test("an omitted bound stays absent, not invented by the parser", () => {
  const program = clean("\\[A](x) x\n");
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
  const { errors } = parse("match y\n");
  expect(errors.join("\n")).toContain("at least one arm");
});

Deno.test("an offside token is named as such, not as a missing one", () => {
  // The cost of resolving layout by filtering, paid back in the message.
  const { errors } = parse("let x =\na\n");
  expect(errors.join("\n")).toContain("indented block");
});

Deno.test("recovery keeps going after a bad expression", () => {
  const { program, errors } = parse("let x = )\nlet y = b\ny\n");
  expect(errors.length).toBeGreaterThan(0);
  expect(bindings(program.term)).toContain("y");
});
