import { expect } from "@std/expect";
import { type Diagnostic, mkSource } from "../diagnostics/diagnostic.ts";
import { tokenize } from "../syntax/lexer.ts";
import { layout } from "../syntax/layout.ts";
import { parseProgram } from "../syntax/parser.ts";
import { Context } from "./context.ts";
import { Declarations } from "./declarations.ts";
import { Elaborator } from "./elaborate.ts";
import type { Variance } from "./types.ts";

/**
 * Elaborate declarations alone -- which is where the variance pass runs, so a
 * trailing term would only be scenery. Read after elaboration rather than
 * built by hand, since what a field *is* by then is half of what the walk
 * answers.
 */
function elaborated(...lines: readonly string[]): {
  declarations: Declarations;
  diagnostics: Diagnostic[];
} {
  const source = mkSource([...lines, "x"].join("\n"), "variance.ga");
  const tokens = tokenize(source);
  if (tokens.value === undefined) throw new Error("did not tokenize");
  const laid = layout(tokens.value);
  if (laid.value === undefined) throw new Error("did not lay out");
  const program = parseProgram(laid.value);
  if (program.value === undefined) throw new Error("did not parse");

  const declarations = new Declarations();
  const diagnostics: Diagnostic[] = [];
  new Elaborator(declarations, new Context(declarations), diagnostics)
    .elaborateDeclarations(program.value.decls);
  return { declarations, diagnostics };
}

const SIGN: Record<Variance, string> = { 1: "+", 0: "=", [-1]: "-" };

/**
 * Every parameterised datatype's inferred variance, as `Foo[+A, -B, =C]` --
 * `+` covariant, `-` contravariant, `=` invariant, which is the one that has
 * to be the same type either way round.
 */
function variancesOf(...lines: readonly string[]): string[] {
  return elaborated(...lines).declarations.datatypes()
    .filter((datatype) => datatype.params.length > 0)
    .map((datatype) =>
      `${datatype.name}[${
        datatype.params
          .map((param) => `${SIGN[param.variance]}${param.hint}`)
          .join(", ")
      }]`
    );
}

/** What was reported -- a phantom is the only thing this pass reports. */
function saidOf(...lines: readonly string[]): string[] {
  return elaborated(...lines).diagnostics
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

Deno.test("the recursive occurrence is read from the table, not unfolded", () => {
  expect(variancesOf(
    ...BOOL,
    "datatype List[A] where",
    "  | Nil",
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
  // `+B` on faith licenses `Foo[A,B,C] <: Foo[A,B',C]` for `B <: B'`, and
  // projecting `Shift` from the supertype then wants `B' <: B`. Any
  // implementation that walks the fields once and stops answers round 1.
  expect(variancesOf(
    ...BOOL,
    "datatype Foo[A, B, C] where",
    "  | Arrow((A) -> B)",
    "  | Data(C)",
    "  | Shift(Foo[B, C, A])",
  )).toEqual(["Foo[=A, =B, =C]"]);
});

Deno.test("a rotation that never returns to its start settles all the same", () => {
  // `Foo[A,B,C] > Foo[B,C,A->B] > Foo[C,A->B,B->C]`: the unfolding does not
  // come back, so no argument about permutations reaches the answer and the
  // fixed point is the only way to it.
  expect(variancesOf(
    ...BOOL,
    "datatype Foo[A, B, C] where",
    "  | Arrow((A) -> B)",
    "  | Data(C)",
    "  | Shift(Foo[B, C, (A) -> B])",
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
});
