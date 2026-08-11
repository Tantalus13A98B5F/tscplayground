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
  context.pushTermVar("x", TUnknown);
  const inner = context.pushTermVar("x", TData(Bool));

  const found = context.lookupTerm("x");
  expect(alphaEq(found?.type ?? TUnknown, TData(Bool))).toBe(true);
  // The level, not the name, is what tells two shadowing bindings apart.
  expect(found?.level).toBe(inner);
  expect(context.lookupTerm("y")).toBeUndefined();
});

Deno.test("a type variable and a term variable may share a name", () => {
  const context = new Context();
  const type = context.pushTypeVar("x", TUnknown);
  const term = context.pushTermVar("x", TData(Bool));
  expect(context.lookupTypeVar("x")?.level).toBe(type);
  expect(context.lookupTerm("x")?.level).toBe(term);
});

Deno.test("push hands back the level it allocated", () => {
  const context = new Context();
  expect(context.pushTypeVar("X", TUnknown)).toBe(mkLevel(0));
  expect(context.pushEVar("a")).toBe(mkLevel(1));
  expect(context.size).toBe(2);
});

Deno.test("solve records a solution in place", () => {
  const { context, a } = withEVar();

  expect(context.setSolution(a, TData(Bool))).toBeUndefined();
  expect(alphaEq(context.evarAt(a)?.solution ?? TUnknown, TData(Bool))).toBe(
    true,
  );
});

Deno.test("solve rejects a solution mentioning the variable itself", () => {
  const { context, a } = withEVar();

  const failure = context.setSolution(a, TFun([], [EVar(a, "a")], TUnknown));
  expect(failure?.kind).toBe("occurs");
  expect(context.evarAt(a)?.solution).toBeUndefined();
});

Deno.test("solve rejects a solution that escapes its scope", () => {
  // `?a` is bound to the left of `X`, so `?a := X` would let X escape.
  const { context, a } = withEVar();
  const X = context.pushTypeVar("X", TUnknown);

  expect(context.setSolution(a, FVar(X, "X"))?.kind).toBe("escapes");
});

Deno.test("solve accepts a solution mentioning something to its left", () => {
  const context = new Context();
  const X = context.pushTypeVar("X", TUnknown);
  const a = context.pushEVar("a");

  expect(context.setSolution(a, FVar(X, "X"))).toBeUndefined();
  expect(alphaEq(context.evarAt(a)?.solution ?? TUnknown, FVar(X, "X"))).toBe(
    true,
  );
});

Deno.test("solve refuses to overwrite an existing solution", () => {
  const { context, a } = withEVar();
  context.setSolution(a, TData(Bool));

  expect(context.setSolution(a, TUnknown)?.kind).toBe("alreadySolved");
  expect(alphaEq(context.evarAt(a)?.solution ?? TUnknown, TData(Bool))).toBe(
    true,
  );
});

Deno.test("solve reports a level that is not an EVar", () => {
  const context = new Context();
  const X = context.pushTypeVar("X", TUnknown);
  expect(context.setSolution(X, TUnknown)?.kind).toBe("unbound");
  expect(context.setSolution(mkLevel(9), TUnknown)?.kind).toBe("unbound");
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
  context.pushTermVar("x", TUnknown);

  const mark = context.size;
  context.pushEVar("a");
  context.pushTermVar("y", TUnknown);
  expect(context.size).toBe(mark + 2);

  context.truncate(mark);
  expect(context.size).toBe(1);
  expect(context.entries[0]?.kind).toBe("TermVar");
  expect(context.lookupTerm("y")).toBeUndefined();
});

Deno.test("truncate past the end leaves the context alone", () => {
  const context = new Context();
  context.pushTermVar("x", TUnknown);
  context.truncate(99);
  expect(context.size).toBe(1);
});

Deno.test("truncate reuses the levels it dropped", () => {
  // Why `assertLeft` exists: without closing first, a stale FVar would now
  // name `Y` rather than fail to resolve.
  const context = new Context();
  const mark = context.size;
  const X = context.pushTypeVar("X", TUnknown);
  context.truncate(mark);
  expect(context.pushTypeVar("Y", TUnknown)).toBe(X);
});

Deno.test("assertClosed throws on a type that outlives its scope", () => {
  const context = new Context();
  const mark = context.size;
  const X = context.pushTypeVar("X", TUnknown);
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
