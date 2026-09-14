import { expect } from "@std/expect";
import { Context, type EVarEntry } from "./context.ts";
import {
  alphaEq,
  BVar,
  type DataHead,
  FVar,
  mkLevel,
  TData,
  TUnknown,
} from "./types.ts";

/** Nothing here reads a parameter back, so a nullary head is enough. */
const Bool: DataHead = { name: "Bool", family: "Bool", params: [] };

/** Levels are positions, so a context has to be built to have any. */
function withEVar(): { context: Context; a: EVarEntry } {
  const context = new Context();
  return { context, a: context.pushEVar("a") };
}

Deno.test("lookupTerm finds the innermost binding", () => {
  const context = new Context();
  context.pushTermVar(TUnknown, "x");
  const inner = context.pushTermVar(TData(Bool), "x");

  const found = context.lookupTerm("x");
  expect(alphaEq(found?.entry.type ?? TUnknown, TData(Bool))).toBe(true);
  // The level, not the name, is what tells two shadowing bindings apart.
  expect(found?.level).toBe(inner);
  expect(context.lookupTerm("y")).toBeUndefined();
});

Deno.test("a term variable shadows a type variable of the same name", () => {
  // One namespace: the innermost binding answers, and being the wrong kind
  // makes the name unusable rather than sending the lookup further out.
  const context = new Context();
  const type = context.pushTypeVar(TUnknown, "x");
  expect(context.lookupTypeVar("x")?.level).toBe(type);

  const term = context.pushTermVar(TData(Bool), "x");
  expect(context.lookupTerm("x")?.level).toBe(term);
  expect(context.lookupTypeVar("x")).toBeUndefined();
});

Deno.test("ending a scope reveals the binding it shadowed", () => {
  const context = new Context();
  const outer = context.pushTermVar(TUnknown, "x");

  const mark = context.size;
  context.pushTypeVar(TUnknown, "x");
  expect(context.lookupTerm("x")).toBeUndefined();

  context.truncate(mark);
  expect(context.lookupTerm("x")?.level).toBe(outer);
});

Deno.test("a nameless binding holds a position but answers to no name", () => {
  // What subtyping opens a quantifier under, and what `_` becomes.
  const context = new Context();
  const outer = context.pushTypeVar(TUnknown, "X");
  const nameless = context.pushTypeVar(TData(Bool));

  expect(nameless).toBe(mkLevel(1));
  expect(
    alphaEq(
      context.typeVarAt(FVar(nameless, "_"))?.bound ?? TUnknown,
      TData(Bool),
    ),
  )
    .toBe(true);
  // Still reachable by level, so its bound is not lost -- only its name is.
  expect(context.lookupTypeVar("X")?.level).toBe(outer);
});

Deno.test("push hands back the level it allocated", () => {
  const context = new Context();
  expect(context.pushTypeVar(TUnknown, "X")).toBe(mkLevel(0));
  expect(context.pushEVar("a").level).toBe(mkLevel(1));
  expect(context.size).toBe(2);
});

Deno.test("which kind a level holds is a question, but the level itself is not", () => {
  // An `FVar` says a level and no more, so asking whether it names an EVar is
  // ordinary. Asking about a level nothing was ever pushed at is a checker bug.
  const context = new Context();
  const X = FVar(context.pushTypeVar(TUnknown, "X"), "X");
  const a = context.pushEVar("a");

  expect(context.evarAt(X)).toBeUndefined();
  expect(context.typeVarAt(a.ref)).toBeUndefined();
  expect(context.evarAt(a.ref)?.hint).toBe("a");
  expect(() => context.entryAt(FVar(mkLevel(9), "stray")))
    .toThrow("names no entry");
});

Deno.test("an EVar records constraints, refusing one it could not be solved to", () => {
  const { a } = withEVar();

  a.addConstraint("lower", TData(Bool));
  expect(alphaEq(a.lower[0] ?? TUnknown, TData(Bool))).toBe(true);
  // `?a` begins its own batch, so a bound naming it is one its solution could
  // not mention either -- the caller was to have avoided it first.
  expect(() => a.addConstraint("upper", a.ref)).toThrow("past level");
});

Deno.test("truncate ends a scope, keeping what came before it", () => {
  const context = new Context();
  context.pushTermVar(TUnknown, "x");

  const mark = context.size;
  context.pushEVar("a");
  context.pushTermVar(TUnknown, "y");
  expect(context.size).toBe(mark + 2);

  context.truncate(mark);
  expect(context.size).toBe(1);
  expect(context.entries[0]?.kind).toBe("TermVar");
  expect(context.lookupTerm("y")).toBeUndefined();
});

Deno.test("truncate past the end leaves the context alone", () => {
  const context = new Context();
  context.pushTermVar(TUnknown, "x");
  context.truncate(mkLevel(99));
  expect(context.size).toBe(1);
});

Deno.test("truncate reuses the levels it dropped", () => {
  // Why `assertClosed` exists: without closing first, a stale FVar would now
  // name `Y` rather than fail to resolve.
  const context = new Context();
  const mark = context.size;
  const X = context.pushTypeVar(TUnknown, "X");
  context.truncate(mark);
  expect(context.pushTypeVar(TUnknown, "Y")).toBe(X);
});

Deno.test("assertClosed throws on a type that outlives its scope", () => {
  const context = new Context();
  const mark = context.size;
  const X = context.pushTypeVar(TUnknown, "X");
  context.truncate(mark);
  // The bar is the context as it now stands, so the truncation above is what
  // makes `X` an escapee -- no mark is passed, and none could disagree.
  expect(() => context.assertClosed("test", [FVar(X, "X")])).toThrow(
    "escaped a scope",
  );
  expect(() => context.assertClosed("test", [TData(Bool)])).not.toThrow();
});

Deno.test("assertClosed allows the binders a stored type was closed into", () => {
  // A constructor field over a 2-parameter datatype: no free levels, but two
  // legitimate `BVar`s. Checking it at depth zero would reject valid output.
  const context = new Context();
  const field = TData(
    { name: "Pair", family: "Pair", params: [] },
    [BVar(0), BVar(1)],
  );
  expect(() => context.assertClosed("field", [field], 2)).not.toThrow();
  expect(() => context.assertClosed("field", [field])).toThrow();
});

Deno.test("an EVar records where it stands, accumulating its occurrences", () => {
  const { a } = withEVar();
  // Nothing noted yet, where a variable the result never mentions also stays.
  expect([a.covariantly, a.contravariantly]).toEqual([false, false]);

  a.noteOccurrence(1);
  expect([a.covariantly, a.contravariantly]).toEqual([true, false]);
  // Twice at the same variance says nothing new.
  a.noteOccurrence(1);
  expect([a.covariantly, a.contravariantly]).toEqual([true, false]);
  // Standing both ways is what leaves no bound free to widen -- reached by two
  // occurrences here, and by one invariant occurrence on its own.
  a.noteOccurrence(-1);
  expect([a.covariantly, a.contravariantly]).toEqual([true, true]);

  const { a: b } = withEVar();
  b.noteOccurrence(0);
  expect([b.covariantly, b.contravariantly]).toEqual([true, true]);
});
