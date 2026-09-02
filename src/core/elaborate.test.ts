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
import { Declarations } from "./context.ts";
import { constructorType, Elaborator } from "./elaborate.ts";
import {
  alphaEq,
  BVar,
  mkTypeParamInfo,
  TFun,
  TUnknown,
  type Type,
  typeToString,
  type Variance,
} from "./types.ts";

function tokensOf(source: Source) {
  const tokens = tokenize(source);
  if (tokens.value === undefined) throw new Error("did not tokenize");
  const laid = layout(tokens.value);
  if (laid.value === undefined) throw new Error("did not lay out");
  return laid.value;
}

function programOf(text: string): Program {
  const parsed = parseProgram(tokensOf(mkSource(text, "test.ga")));
  if (parsed.value === undefined) {
    throw new Error(
      `did not parse: ${parsed.diagnostics.map((d) => d.message).join("; ")}`,
    );
  }
  return parsed.value;
}

function typeNodeOf(text: string): TypeNode {
  const parsed = parseType(tokensOf(mkSource(text, "type.ga")));
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
  // As `checkProgram` runs it: `Ref` is a seeded name like any other, so a
  // fixture that skipped this would not resolve one.
  elaborator.seedBuiltins();
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
    "datatype List[A] where\n  | Nil()\n  | Cons(A, List[A])" + END,
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
      "  | MkWrap(A, Flag)",
      "datatype Flag where",
      "  | On",
    ].join("\n") + END,
  );
  expect(fixture.messages()).toEqual([]);
});

/** The type a datatype's constructor is bound at, by name. */
function ctorTypeOf(
  fixture: ReturnType<typeof elaborated>,
  data: string,
  ctor: string,
): string {
  const datatype = fixture.declarations.datatypeOf(data);
  const found = fixture.declarations.ctorOf(data, ctor);
  if (datatype === undefined || found === undefined) {
    throw new Error(`no ${data}.${ctor}`);
  }
  return typeToString(constructorType(datatype, found));
}

Deno.test("a bare constructor is a value, and a written `()` a function", () => {
  // The whole of the distinction, and both legal on a monomorphic datatype:
  // the arity is the same either way, so only the declaration can say which
  // was meant.
  const fixture = elaborated("datatype Flag where\n  | On\n  | Off()" + END);
  expect(fixture.messages()).toEqual([]);
  expect(ctorTypeOf(fixture, "Flag", "On")).toBe("Flag");
  expect(ctorTypeOf(fixture, "Flag", "Off")).toBe("() -> Flag");
});

Deno.test("a nullary constructor of a polymorphic datatype stays a function", () => {
  // `[A]List[A]` would be a quantifier over a non-function, which the value
  // restriction rules out -- so the argument list survives to carry it.
  const fixture = elaborated(
    "datatype List[A] where\n  | Nil()\n  | Cons(A, List[A])" + END,
  );
  expect(fixture.messages()).toEqual([]);
  expect(ctorTypeOf(fixture, "List", "Nil")).toBe("[A]() -> List[A]");
});

Deno.test("a value constructor of a polymorphic datatype is refused", () => {
  // There is no type to give it: `[A]List[A]` is the quantifier over a
  // non-function the value restriction rules out, so the form has no reading
  // rather than an inconvenient one.
  const fixture = elaborated(
    "datatype List[A] where\n  | Nil\n  | Cons(A, List[A])" + END,
  );
  expect(fixture.messages()).toEqual([
    "Nil is declared as a value, but List takes type parameters, so it has " +
    "no one type -- write Nil() instead",
  ]);
  // Recovered as the function it would have been, so the report is the whole
  // of what goes wrong: nothing downstream sees a second thing about `Nil`.
  expect(ctorTypeOf(fixture, "List", "Nil")).toBe("[A]() -> List[A]");
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

// ---------------------------------------------------- inferring variance

/**
 * Every parameterised datatype's inferred variance, as `Foo[+A, -B, =C]` --
 * `+` covariant, `-` contravariant, `=` invariant, which is the one that has
 * to be the same type either way round.
 *
 * Read after elaboration rather than built by hand, since what a field *is* by
 * then is half of what the walk answers.
 */
function variancesOf(...lines: readonly string[]): string[] {
  return elaborated(lines.join("\n") + END).declarations.datatypes()
    .filter((datatype) => datatype.params.length > 0)
    .map((datatype) =>
      `${datatype.name}[${
        datatype.params
          .map((param) => `${SIGN[param.variance]}${param.hint}`)
          .join(", ")
      }]`
    );
}

const SIGN: Record<Variance, string> = { 1: "+", 0: "=", [-1]: "-" };

/** What was reported -- a phantom is the only thing this pass reports. */
function saidOf(...lines: readonly string[]): string[] {
  return elaborated(lines.join("\n") + END).diagnostics
    .map((d) => `${d.severity}: ${d.message}`);
}

const BOOL = ["datatype Bool where", "  | True", "  | False"];

Deno.test("a field puts its parameter where it stands", () => {
  expect(variancesOf(
    ...BOOL,
    "datatype Box[A] where",
    "  | MkBox(A)",
    "datatype Sink[A] where",
    "  | MkSink((A) -> Bool)",
    "datatype Cell[A] where",
    "  | MkCell((A) -> A)",
  )).toEqual(["Box[+A]", "Sink[-A]", "Cell[=A]"]);
});

Deno.test("a field is entered covariantly, so a result is not flipped", () => {
  // `match` projects a field and nothing assigns one, which is the whole
  // reason there is no contravariant entry to the walk.
  expect(variancesOf(
    ...BOOL,
    "datatype Source[A] where",
    "  | MkSource((Bool) -> A)",
  )).toEqual(["Source[+A]"]);
});

Deno.test("a bound is contravariant, like a parameter", () => {
  expect(variancesOf(
    ...BOOL,
    "datatype Lower[A] where",
    "  | MkLower([B <: A](B) -> Bool)",
  )).toEqual(["Lower[-A]"]);
});

Deno.test("a datatype argument composes rather than merging", () => {
  // Two flips are none, and an invariant argument absorbs whatever reaches
  // it -- neither of which a walk that merged positions could say.
  expect(variancesOf(
    ...BOOL,
    "datatype Sink[A] where",
    "  | MkSink((A) -> Bool)",
    "datatype Cell[A] where",
    "  | MkCell((A) -> A)",
    "datatype Twice[A] where",
    "  | MkTwice(Sink[Sink[A]])",
    "datatype Once[A] where",
    "  | MkOnce(Sink[Cell[A]])",
  )).toEqual(["Sink[-A]", "Cell[=A]", "Twice[+A]", "Once[=A]"]);
});

Deno.test("a cell says its own variance, so a field holding one is invariant", () => {
  // No table entry to read and no round to wait for: `TRef` carries the `0`
  // itself, which is what taking the cell out of `TData` bought.
  expect(variancesOf(
    ...BOOL,
    "datatype Holder[A] where",
    "  | H(Ref[A])",
    "datatype Deep[A] where",
    "  | D((Ref[A]) -> Bool)",
  )).toEqual(["Holder[=A]", "Deep[=A]"]);
});

Deno.test("the recursive occurrence is read from the table, not unfolded", () => {
  expect(variancesOf(
    ...BOOL,
    "datatype List[A] where",
    "  | Nil()",
    "  | Cons(A, List[A])",
  )).toEqual(["List[+A]"]);
});

Deno.test("two datatypes that name each other settle together", () => {
  // One table and one fixed point over all of it: `Even` learns nothing in
  // the round that `Odd` learns it in, which is what makes a per-datatype
  // pass wrong here.
  expect(variancesOf(
    ...BOOL,
    "datatype Even[A] where",
    "  | Stop",
    "  | E(Odd[A])",
    "datatype Odd[A] where",
    "  | O(A, Even[A])",
  )).toEqual(["Even[+A]", "Odd[+A]"]);
});

Deno.test("a rotation is invariant, which one pass over the fields is not", () => {
  // Round 1 is `Foo[-A, +B, +C]` -- complete, plausible, and unsound: taking
  // `+B` on faith licenses `Foo[A,B,C] <: Foo[A,B\',C]` for `B <: B\'`, and
  // projecting `Shift` from the supertype then wants `B\' <: B`. Any
  // implementation that walks the fields once and stops answers round 1.
  //
  // `Shift` is written *first* on purpose, this being the one test where the
  // constructor order is load-bearing. The rounds update one table in place, so
  // a recursive occurrence read *after* the fields that decide it settles in
  // the same pass -- move `Shift` last and one pass answers correctly here, by
  // luck rather than by being right, and this stops catching anything.
  expect(variancesOf(
    ...BOOL,
    "datatype Foo[A, B, C] where",
    "  | Shift(Foo[B, C, A])",
    "  | Arrow((A) -> B)",
    "  | Data(C)",
  )).toEqual(["Foo[=A, =B, =C]"]);
});

Deno.test("a rotation that never returns to its start settles all the same", () => {
  // `Foo[A,B,C] > Foo[B,C,A->B] > Foo[C,A->B,B->C]`: the unfolding does not
  // come back, so no argument about permutations reaches the answer and the
  // fixed point is the only way to it. `Shift` first, for the reason above.
  expect(variancesOf(
    ...BOOL,
    "datatype Foo[A, B, C] where",
    "  | Shift(Foo[B, C, (A) -> B])",
    "  | Arrow((A) -> B)",
    "  | Data(C)",
  )).toEqual(["Foo[=A, =B, =C]"]);
});

Deno.test("a parameter only the recursion holds is observed by nothing", () => {
  // Optimism is correct here rather than merely convenient: nothing in
  // `Opaque` ever produces an `A`, so no program can tell an `Opaque[X]` from
  // an `Opaque[Y]`, and the greatest permissive fixed point is what says so.
  expect(variancesOf(
    ...BOOL,
    "datatype Opaque[A] where",
    "  | Mk((Opaque[A]) -> Bool)",
  )).toEqual(["Opaque[+A]"]);
  expect(saidOf(
    ...BOOL,
    "datatype Opaque[A] where",
    "  | Mk((Opaque[A]) -> Bool)",
  )).toEqual([
    "warning: nothing observes the type parameter A of Opaque, so it makes " +
    "no difference to the type; write it `_` if that is meant",
  ]);
});

Deno.test("a phantom is reported once, at the parameter", () => {
  // It takes the fixed point and not a pass: a parameter that occurs in no
  // field at all is the easy case, and this is the other one.
  expect(saidOf(
    ...BOOL,
    "datatype Tag[A] where",
    "  | MkTag(Bool)",
  )).toEqual([
    "warning: nothing observes the type parameter A of Tag, so it makes no " +
    "difference to the type; write it `_` if that is meant",
  ]);
});

Deno.test("a wildcard parameter is deliberate, so it is not reported", () => {
  expect(saidOf(
    ...BOOL,
    "datatype Tag[_] where",
    "  | MkTag(Bool)",
  )).toEqual([]);
});

Deno.test("a datatype with a bad field is not also blamed for a phantom", () => {
  // The field is what went wrong; a parameter left with nowhere to occur is
  // that same mistake seen a second time.
  expect(saidOf(
    ...BOOL,
    "datatype Tag[A] where",
    "  | MkTag(Nosuchtype)",
  )).toEqual(["error: unknown type Nosuchtype"]);

  // However deep the bad type sits, and under whatever kind. Asking the
  // *report* rather than searching the field types is what makes this hold
  // for a kind nobody thought to look under.
  expect(saidOf(
    ...BOOL,
    "datatype Tag[A] where",
    "  | MkTag(Ref[Nosuchtype[A]])",
  )).toEqual(["error: unknown type Nosuchtype"]);
});

Deno.test("a dropped duplicate takes its fields, so no phantom either", () => {
  // The second `MkTag` is refused, and with it the only occurrence of `A`.
  // The parameter is not what went wrong there either.
  expect(saidOf(
    ...BOOL,
    "datatype Tag[A] where",
    "  | MkTag(Bool)",
    "  | MkTag(A)",
  )).toEqual(["error: datatype Tag already has a constructor MkTag"]);
});

Deno.test("a base is one more occurrence in the fixed point, covariant", () => {
  expect(variancesOf(
    ...BOOL,
    "datatype Box[A] where",
    "  | MkBox(A)",
    // No fields at all, so the base is the only place the parameter occurs and
    // the only thing that can answer for it.
    "datatype Small[A] <: Box[A] where",
    "  | MkSmall()",
    // A base is walked like a field, so a parameter under an arrow in one
    // flips.
    "datatype Flip[A] <: Box[(A) -> Bool] where",
    "  | MkFlip()",
    // Covariant from the base and contravariant from a field, which meet at
    // invariant -- and that is what makes the covariance requirement vacuous.
    "datatype Both[A] <: Box[A] where",
    "  | MkBoth((A) -> Bool)",
  )).toEqual(["Box[+A]", "Small[+A]", "Flip[-A]", "Both[=A]"]);
});

Deno.test("a base must be a datatype declared above", () => {
  expect(saidOf(
    ...BOOL,
    "datatype Cells <: Ref[Bool] where",
    "  | MkCells() -> MkCells()",
  )).toEqual([
    "error: Cells may present as a datatype, and Ref[Bool] is not one",
  ]);

  // Equal to a datatype is not the same as naming one: the base's name has to
  // be readable off the tree, and an alias is gone by the time anything looks.
  expect(saidOf(
    ...BOOL,
    "datatype Box where",
    "  | MkBox(Bool)",
    "typedef Alias = Box",
    "datatype Small <: Alias where",
    "  | MkSmall(Bool) -> MkBox(True)",
  )).toEqual(["error: Small must name Box directly to present as it"]);

  // Declared below, so the table has not got it yet -- the alias rule, and it
  // is what leaves a base chain no way to close on itself.
  expect(saidOf(
    ...BOOL,
    "datatype Early <: Late where",
    "  | MkEarly() -> MkLate",
    "datatype Late where",
    "  | MkLate",
  )).toEqual(["error: unknown type Late"]);

  expect(saidOf(
    ...BOOL,
    "datatype Loop <: Loop where",
    "  | MkLoop() -> MkLoop()",
  )).toEqual(["error: unknown type Loop"]);
});

Deno.test("a coercion is written exactly where there is a base", () => {
  expect(saidOf(
    ...BOOL,
    "datatype Box where",
    "  | MkBox(Bool) -> MkBox(True)",
  )).toEqual([
    "error: MkBox writes a coercion, but Box presents as nothing -- " +
    "give it a base with `<:`",
  ]);

  expect(saidOf(
    ...BOOL,
    "datatype Box where",
    "  | MkBox(Bool)",
    "datatype Small <: Box where",
    "  | MkSmall(Bool)",
  )).toEqual([
    "error: MkSmall needs a coercion: every Small presents as Box, " +
    "and this says which one",
  ]);
});
