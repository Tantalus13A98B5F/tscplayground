import { expect } from "@std/expect";
import {
  type Diagnostic,
  mkSource,
  type Source,
} from "../diagnostics/diagnostic.ts";
import { tokenize } from "../syntax/lexer.ts";
import { layout } from "../syntax/layout.ts";
import { parseProgram, parseType } from "../syntax/parser.ts";
import type { Program, TypeNode } from "../syntax/ast.ts";
import { Context } from "./context.ts";
import { Declarations } from "./declarations.ts";
import { constructorType, Elaborator } from "./elaborate.ts";
import {
  alphaEq,
  BVar,
  mkTypeParamInfo,
  TFun,
  TUnknown,
  type Type,
  typeToString,
} from "./types.ts";

function tokensOf(source: Source) {
  const tokens = tokenize(source);
  if (tokens.value === undefined) throw new Error("did not tokenize");
  const laid = layout(tokens.value);
  if (laid.value === undefined) throw new Error("did not lay out");
  return laid.value;
}

function programOf(text: string): Program {
  const parsed = parseProgram(tokensOf(mkSource(text, "test.tg")));
  if (parsed.value === undefined) {
    throw new Error(
      `did not parse: ${parsed.diagnostics.map((d) => d.message).join("; ")}`,
    );
  }
  return parsed.value;
}

function typeNodeOf(text: string): TypeNode {
  const parsed = parseType(tokensOf(mkSource(text, "type.tg")));
  if (parsed.value === undefined) {
    throw new Error(`did not parse type: ${text}`);
  }
  return parsed.value;
}

type Fixture = {
  readonly elaborator: Elaborator;
  readonly declarations: Declarations;
  readonly context: Context;
  readonly diagnostics: Diagnostic[];
  /** Elaborate a standalone type against the declarations. */
  readonly elaborate: (text: string) => Type;
  /** The same, rendered, for the cases a string pins down. */
  readonly show: (text: string) => string;
  readonly messages: () => string[];
};

/** Elaborate `source`'s declarations, then hand back the pieces to poke at. */
function elaborated(source: string): Fixture {
  const program = programOf(source);
  const declarations = new Declarations();
  const context = new Context();
  const diagnostics: Diagnostic[] = [];
  const elaborator = new Elaborator(declarations, context, diagnostics);
  elaborator.elaborateDeclarations(program.decls);
  return {
    elaborator,
    declarations,
    context,
    diagnostics,
    elaborate: (text) => elaborator.elaborateType(typeNodeOf(text)),
    show: (text) => typeToString(elaborator.elaborateType(typeNodeOf(text))),
    messages: () => diagnostics.map((d) => d.message),
  };
}

/** A program needs a trailing expression; the tests never look at it. */
const END = "\nx";

Deno.test("an alias is expanded away at the use site", () => {
  const fixture = elaborated("typedef Endo[A] = (A) -> A" + END);
  expect(fixture.messages()).toEqual([]);
  expect(fixture.show("Endo[unknown]")).toBe("unknown -> unknown");
});

Deno.test("an alias of an alias expands through both", () => {
  const fixture = elaborated(
    ["typedef Endo[A] = (A) -> A", "typedef Twice[A] = (Endo[A]) -> Endo[A]"]
      .join("\n") + END,
  );
  expect(fixture.messages()).toEqual([]);
  expect(fixture.show("Twice[never]")).toBe(
    "(never -> never) -> never -> never",
  );
});

Deno.test("an alias may not name one declared after it", () => {
  const fixture = elaborated(
    ["typedef First[A] = Second[A]", "typedef Second[A] = (A) -> A"].join(
      "\n",
    ) +
      END,
  );
  expect(fixture.messages()).toEqual(["unknown type Second"]);
});

Deno.test("a datatype elaborates to a saturated constructor", () => {
  const fixture = elaborated(
    "datatype Pair[A, B] where\n  | MkPair(A, B)" + END,
  );
  expect(fixture.messages()).toEqual([]);
  expect(fixture.show("Pair[unknown, never]")).toBe("Pair[unknown, never]");
});

Deno.test("a constructor's function type quantifies over the datatype", () => {
  const fixture = elaborated(
    "datatype Pair[A, B] where\n  | MkPair(A, B)" + END,
  );
  const pair = fixture.declarations.datatypeOf("Pair");
  const ctor = fixture.declarations.ctorOf("Pair", "MkPair");
  if (pair === undefined || ctor === undefined) throw new Error("no Pair");
  expect(typeToString(constructorType(pair, ctor)))
    .toBe("[A, B](A, B) -> Pair[A, B]");
});

Deno.test("a datatype may name itself, being nominal", () => {
  const fixture = elaborated(
    "datatype List[A] where\n  | Nil\n  | Cons(A, List[A])" + END,
  );
  expect(fixture.messages()).toEqual([]);
  const list = fixture.declarations.datatypeOf("List");
  const cons = fixture.declarations.ctorOf("List", "Cons");
  if (list === undefined || cons === undefined) throw new Error("no List");
  expect(typeToString(constructorType(list, cons)))
    .toBe("[A](A, List[A]) -> List[A]");
});

Deno.test("a constructor field may name a datatype declared later", () => {
  const fixture = elaborated(
    [
      "datatype Wrap[A] where",
      "  | MkWrap(Flag)",
      "datatype Flag where",
      "  | On",
    ].join("\n") + END,
  );
  expect(fixture.messages()).toEqual([]);
});

Deno.test("a nullary constructor of a monomorphic datatype is a value", () => {
  const fixture = elaborated("datatype Flag where\n  | On\n  | Off" + END);
  const flag = fixture.declarations.datatypeOf("Flag");
  const on = fixture.declarations.ctorOf("Flag", "On");
  if (flag === undefined || on === undefined) throw new Error("no Flag");
  // Nothing to apply and nothing to instantiate, so `On` rather than `On()`.
  expect(typeToString(constructorType(flag, on))).toBe("Flag");
});

Deno.test("a nullary constructor of a polymorphic datatype stays a function", () => {
  // `[A]List[A]` would be a quantifier over a non-function, which the value
  // restriction rules out -- so the argument list survives to carry it.
  const fixture = elaborated(
    "datatype List[A] where\n  | Nil\n  | Cons(A, List[A])" + END,
  );
  const list = fixture.declarations.datatypeOf("List");
  const nil = fixture.declarations.ctorOf("List", "Nil");
  if (list === undefined || nil === undefined) throw new Error("no List");
  expect(typeToString(constructorType(list, nil))).toBe("[A]() -> List[A]");
});

Deno.test("seedConstructors binds every constructor as a term", () => {
  const fixture = elaborated(
    "datatype Pair[A, B] where\n  | MkPair(A, B)" + END,
  );
  fixture.elaborator.seedConstructors();
  const bound = fixture.context.lookupTerm("MkPair");
  expect(bound).toBeDefined();
  expect(typeToString(bound?.entry.type ?? never())).toBe(
    "[A, B](A, B) -> Pair[A, B]",
  );
  expect(fixture.context.lookupTerm("MkTriple")).toBeUndefined();
});

function never(): never {
  throw new Error("expected a binding");
}

Deno.test("a quantifier closes its own group at index zero", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  expect(fixture.show("[A](A) -> A")).toBe("[A](A) -> A");
  expect(fixture.show("[A, B](A, B) -> B")).toBe("[A, B](A, B) -> B");
});

Deno.test("a nested quantifier shifts the outer group's indices", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  expect(fixture.show("[A]([B](B) -> A) -> A"))
    .toBe("[A]([B](B) -> A) -> A");
});

Deno.test("an inner binder shadows an outer one of the same name", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  // Printing cannot tell shadowing from capture -- both read `A` -- so this
  // compares indices. The inner `A` must be `BVar 0` of its *own* group; had
  // the outer binder captured it, it would be `BVar 1`.
  const type = fixture.elaborate("[A]([A](A) -> unknown) -> A");
  const inner = TFun([mkTypeParamInfo("A", TUnknown)], [BVar(0)], TUnknown);
  expect(
    alphaEq(type, TFun([mkTypeParamInfo("A", TUnknown)], [inner], BVar(0))),
  )
    .toBe(true);
});

Deno.test("a bound may name an enclosing binder", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  expect(fixture.show("[A]([B <: A](B) -> B) -> A")).toBe(
    "[A]([B <: A](B) -> B) -> A",
  );
  expect(fixture.messages()).toEqual([]);
});

Deno.test("a bound may not name a member of its own group", () => {
  // Bounds are parallel, not telescoping, so `A` is not yet in scope here.
  const fixture = elaborated("typedef Unit = unknown" + END);
  fixture.show("[A, B <: A](B) -> A");
  expect(fixture.messages()).toEqual(["unknown type A"]);
});

Deno.test("a datatype used at the wrong arity is reported", () => {
  const fixture = elaborated(
    "datatype Pair[A, B] where\n  | MkPair(A, B)" + END,
  );
  expect(fixture.show("Pair[unknown]")).toBe("<bad>");
  expect(fixture.messages()).toEqual([
    "datatype Pair takes 2 type arguments, given 1",
  ]);
});

Deno.test("an alias used at the wrong arity is reported", () => {
  const fixture = elaborated("typedef Endo[A] = (A) -> A" + END);
  expect(fixture.show("Endo")).toBe("<bad>");
  expect(fixture.messages()).toEqual([
    "type alias Endo takes 1 type argument, given 0",
  ]);
});

Deno.test("a type variable takes no arguments", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  expect(fixture.show("[A](A[unknown]) -> A")).toBe("[A](<bad>) -> A");
  expect(fixture.messages()).toEqual(["type variable A takes no arguments"]);
});

Deno.test("an unresolved name becomes TBad, so one error is one error", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  expect(fixture.show("(Nope) -> unknown")).toBe("<bad> -> unknown");
  expect(fixture.messages()).toEqual(["unknown type Nope"]);
});

Deno.test("an error inside an argument survives an unresolvable head", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  fixture.show("Nope[AlsoNope]");
  expect(fixture.messages()).toEqual([
    "unknown type AlsoNope",
    "unknown type Nope",
  ]);
});

Deno.test("a redeclared type name is reported once", () => {
  const fixture = elaborated(
    ["datatype Flag where", "  | On", "typedef Flag = unknown"].join("\n") +
      END,
  );
  expect(fixture.messages()).toEqual(["type Flag is already declared"]);
});

Deno.test("a redeclaration is blamed on the later declaration, either way", () => {
  // The two kinds are registered in one pass, in source order, so which one is
  // reported follows the source and not which kind sweeps first.
  const alias = elaborated(
    ["typedef Flag = unknown", "datatype Flag where", "  | On"].join("\n") +
      END,
  );
  expect(alias.messages()).toEqual(["type Flag is already declared"]);
  expect(alias.declarations.datatypeOf("Flag")).toBeUndefined();
  expect(alias.declarations.aliasOf("Flag")).toBeDefined();
});

Deno.test("a redeclared datatype does not take the first one's constructors", () => {
  const fixture = elaborated(
    [
      "datatype Flag where",
      "  | On",
      "datatype Flag where",
      "  | Off",
    ].join("\n") + END,
  );
  expect(fixture.messages()).toEqual(["type Flag is already declared"]);
  expect(fixture.declarations.ctorOf("Flag", "On")).toBeDefined();
  // The losing declaration is elaborated, so errors inside it are still
  // reported, but `initCtors` refuses to hand its constructors to the name.
  expect(fixture.declarations.ctorOf("Flag", "Off")).toBeUndefined();
});

Deno.test("two datatypes may share a constructor name", () => {
  // A pattern is resolved against the scrutinee's datatype, so each `On` is
  // reachable and neither shadows the other.
  const fixture = elaborated(
    [
      "datatype Flag where",
      "  | On",
      "datatype Switch where",
      "  | On",
    ].join("\n") + END,
  );
  expect(fixture.messages()).toEqual([]);
  expect(fixture.declarations.ctorOf("Flag", "On")).toBeDefined();
  expect(fixture.declarations.ctorOf("Switch", "On")).toBeDefined();
});

Deno.test("one datatype may not have two constructors of a name", () => {
  const fixture = elaborated(
    ["datatype Flag where", "  | On", "  | On"].join("\n") + END,
  );
  expect(fixture.messages()).toEqual([
    "datatype Flag already has a constructor On",
  ]);
  expect(fixture.declarations.datatypeOf("Flag")?.ctors.length).toBe(1);
});

Deno.test("a type parameter used twice in one group is reported", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  fixture.show("[A, A](A) -> A");
  expect(fixture.messages()).toEqual(["duplicate type parameter A"]);
});

Deno.test("the wildcard may fill a binder group twice over", () => {
  // `_` names nothing, so a second one collides with nothing. It still holds
  // its position: the result is `BVar 1`, the second of two binders.
  const fixture = elaborated("typedef Unit = unknown" + END);
  expect(fixture.show("[_, _](unknown) -> unknown")).toBe(
    "[_, _](unknown) -> unknown",
  );
  expect(fixture.messages()).toEqual([]);
});

Deno.test("elaborating a binder leaves the context as it found it", () => {
  const fixture = elaborated("typedef Unit = unknown" + END);
  const before = fixture.context.size;
  fixture.show("[A, B](A, B) -> B");
  expect(fixture.context.size).toBe(before);
});
