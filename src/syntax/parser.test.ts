import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { tokenize } from "./lexer.ts";
import { parseProgram, parseType } from "./parser.ts";
import type { Program, Term, TypeNode } from "./ast.ts";

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

/** The chain of names bound by the top-level `let`s, outermost first. */
function bindings(term: Term): string[] {
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
    "let a = x\ndata Pair[A, B]\n| MkPair(a: A, b: B)\nlet b = y\na\n",
  );
  expect(program.decls.map((d) => d.name.text)).toEqual(["Pair"]);
  expect(program.decls[0]?.params.map((p) => p.text)).toEqual(["A", "B"]);
  expect(program.decls[0]?.constructors[0]?.fields.map((f) => f.name.text))
    .toEqual(["a", "b"]);
  // Interleaving is erased: a `data` between two `let`s was never in the chain.
  expect(bindings(program.term)).toEqual(["a", "b"]);
});

Deno.test("match arms may sit at the column of the enclosing block", () => {
  // Safe only because `|` marks them: `let` at that column ends the run.
  const program = clean("let x = match y\n| A => p\n| B => q\nlet z = w\nx\n");
  const bound = program.term.kind === "Let" ? program.term.bound : undefined;
  expect(bound?.kind).toBe("Match");
  expect(bound?.kind === "Match" && bound.arms.length).toBe(2);
  expect(bindings(program.term)).toEqual(["x", "z"]);
});

Deno.test("patterns are one level deep and positional", () => {
  const program = clean("match y\n| MkPair(a, _) => a\n| _ => b\n");
  const arms = program.term.kind === "Match" ? program.term.arms : [];
  expect(arms[0]?.pattern.kind).toBe("PCon");
  expect(arms[0]?.pattern.kind === "PCon" && arms[0].pattern.args.length)
    .toBe(2);
  expect(arms[1]?.pattern.kind).toBe("PWild");
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
  expect(bound.tyParams.map((b) => b.name.text)).toEqual(["A"]);
  expect(bound.tyParams[0]?.bound?.kind).toBe("UnknownType");
  expect(bound.params.map((p) => p.name.text)).toEqual(["x"]);
});

Deno.test("an omitted bound stays absent, not invented by the parser", () => {
  const program = clean("\\[A](x) x\n");
  const tyParams = program.term.kind === "Abs" ? program.term.tyParams : [];
  expect(tyParams[0]?.bound).toBeUndefined();
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
  expect(node.tyParams.map((b) => b.name.text)).toEqual(["A"]);
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
