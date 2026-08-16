import { expect } from "@std/expect";
import { Context } from "./context.ts";
import {
  alphaEq,
  BVar,
  EVar,
  FVar,
  type Level,
  mkDataName,
  mkLevel,
  TData,
  TFun,
  TUnknown,
} from "./types.ts";

const Bool = mkDataName("Bool");

/** Levels are positions, so a context has to be built to have any. */
function withEVar(): { context: Context; a: Level } {
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
  expect(alphaEq(context.upperBoundAt(nameless), TData(Bool))).toBe(true);
  // Still reachable by level, so its bound is not lost -- only its name is.
  expect(context.lookupTypeVar("X")?.level).toBe(outer);
});

Deno.test("push hands back the level it allocated", () => {
  const context = new Context();
  expect(context.pushTypeVar(TUnknown, "X")).toBe(mkLevel(0));
  expect(context.pushEVar("a")).toBe(mkLevel(1));
  expect(context.size).toBe(2);
});

Deno.test("solve records a solution in place", () => {
  const { context, a } = withEVar();

  context.setSolution(a, TData(Bool));
  expect(alphaEq(context.evarAt(a).solution ?? TUnknown, TData(Bool))).toBe(
    true,
  );
});

Deno.test("solve rejects a solution mentioning the variable itself", () => {
  const { context, a } = withEVar();

  // `?a` is not to the left of itself, so this is the escape check doing it.
  expect(() => context.setSolution(a, TFun([], [EVar(a, "a")], TUnknown)))
    .toThrow("escapes");
  expect(context.evarAt(a).solution).toBeUndefined();
});

Deno.test("solve rejects a solution that escapes its scope", () => {
  // `?a` is bound to the left of `X`, so `?a := X` would let X escape.
  const { context, a } = withEVar();
  const X = context.pushTypeVar(TUnknown, "X");

  expect(() => context.setSolution(a, FVar(X, "X"))).toThrow("escapes");
});

Deno.test("solve accepts a solution mentioning something to its left", () => {
  const context = new Context();
  const X = context.pushTypeVar(TUnknown, "X");
  const a = context.pushEVar("a");

  context.setSolution(a, FVar(X, "X"));
  expect(alphaEq(context.evarAt(a).solution ?? TUnknown, FVar(X, "X"))).toBe(
    true,
  );
});

Deno.test("solve refuses to overwrite an existing solution", () => {
  const { context, a } = withEVar();
  context.setSolution(a, TData(Bool));

  expect(() => context.setSolution(a, TUnknown)).toThrow("already solved");
  expect(alphaEq(context.evarAt(a).solution ?? TUnknown, TData(Bool))).toBe(
    true,
  );
});

Deno.test("a read by level is total, so a wrong one is a bug and not a value", () => {
  // Every level comes from a `push` or off a node the checker built, so the
  // kind is known before the read. Answering `undefined` would leave a caller
  // inventing a type for a program that has nothing wrong with it.
  const context = new Context();
  const X = context.pushTypeVar(TUnknown, "X");
  const a = context.pushEVar("a");

  expect(() => context.setSolution(X, TUnknown)).toThrow("holds a TypeVar");
  expect(() => context.evarAt(X)).toThrow("holds a TypeVar");
  expect(() => context.upperBoundAt(a)).toThrow("holds a EVar");
  expect(() => context.evarAt(mkLevel(9))).toThrow("names no entry");
});

Deno.test("apply follows a chain of solutions", () => {
  // ?b to the left of ?a, so `?a := ?b` is well scoped.
  const context = new Context();
  const b = context.pushEVar("b");
  const a = context.pushEVar("a");
  context.setSolution(b, TData(Bool));
  context.setSolution(a, EVar(b, "b"));

  const applied = context.apply(TFun([], [EVar(a, "a")], TUnknown));
  expect(alphaEq(applied, TFun([], [TData(Bool)], TUnknown))).toBe(true);
});

Deno.test("apply leaves unsolved EVars alone", () => {
  const { context, a } = withEVar();
  expect(alphaEq(context.apply(EVar(a, "a")), EVar(a, "a"))).toBe(true);
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
  context.truncate(99);
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
  const field = TData(Bool, [BVar(0), BVar(1)]);
  expect(() => context.assertClosed("field", [field], 2)).not.toThrow();
  expect(() => context.assertClosed("field", [field])).toThrow();
});
