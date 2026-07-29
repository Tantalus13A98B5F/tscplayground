import { expect } from "@std/expect";
import {
  alphaEq,
  BVar,
  close,
  closeMany,
  EVar,
  FVar,
  mkBinder,
  mkDataName,
  mkEVarId,
  mkVarId,
  occurs,
  open,
  openMany,
  substFVar,
  substMany,
  TAll,
  TData,
  TFun,
  TNever,
  TUnknown,
  typeToString,
} from "./types.ts";

const X = mkVarId(0);
const Y = mkVarId(1);
const Pair = mkDataName("Pair");
const Bool = mkDataName("Bool");

Deno.test("open replaces the nearest bound variable", () => {
  const opened = open(TFun([BVar(0)], BVar(0)), TNever);
  expect(alphaEq(opened, TFun([TNever], TNever))).toBe(true);
});

Deno.test("TAll bounds are parallel, outside the scope of the quantifier", () => {
  // The body's index 0 belongs to the inner quantifier, not the opened one.
  const opened = open(TAll([mkBinder("B", BVar(0))], BVar(0)), TData(Bool));
  expect(alphaEq(opened, TAll([mkBinder("B", TData(Bool))], BVar(0)))).toBe(
    true,
  );
});

Deno.test("open moves inward by the full arity of a quantifier", () => {
  // Under `forall A, B` the outer variable is BVar 2, not BVar 1.
  const type = TAll(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    TFun([BVar(0)], BVar(2)),
  );
  const opened = open(type, TData(Bool));
  const expected = TAll(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    TFun([BVar(0)], TData(Bool)),
  );
  expect(alphaEq(opened, expected)).toBe(true);
});

Deno.test("open traverses TData arguments", () => {
  // The trap: skipping `args` leaves a stale BVar and nothing complains.
  const opened = open(TData(Pair, [BVar(0), TData(Bool)]), TNever);
  expect(alphaEq(opened, TData(Pair, [TNever, TData(Bool)]))).toBe(true);
});

Deno.test("openMany instantiates a binder's variables simultaneously", () => {
  const field = TFun([BVar(0)], TData(Pair, [BVar(1), BVar(0)]));
  const opened = openMany(field, [TData(Bool), TNever]);
  const expected = TFun([TData(Bool)], TData(Pair, [TNever, TData(Bool)]));
  expect(alphaEq(opened, expected)).toBe(true);
});

Deno.test("closeMany abstracts variables simultaneously", () => {
  const body = TFun([FVar(X, "X")], FVar(Y, "Y"));
  expect(alphaEq(closeMany(body, [X, Y]), TFun([BVar(0)], BVar(1)))).toBe(true);
});

Deno.test("iterating close collapses variables onto one index", () => {
  // Both calls run at depth 0 and the second leaves the first's BVar alone, so
  // X and Y collapse onto index 0. Why closeMany is not a loop over close.
  const body = TFun([FVar(X, "X")], FVar(Y, "Y"));
  const iterated = close(close(body, X), Y);
  expect(alphaEq(iterated, TFun([BVar(0)], BVar(0)))).toBe(true);
  expect(alphaEq(iterated, closeMany(body, [X, Y]))).toBe(false);
});

Deno.test("close then open is the identity on a free variable", () => {
  const original = TFun(
    [FVar(X, "X")],
    TData(Pair, [FVar(X, "X"), FVar(Y, "Y")]),
  );
  expect(alphaEq(open(close(original, X), FVar(X, "X")), original)).toBe(true);
});

Deno.test("close shifts by the arity of each enclosing quantifier", () => {
  const closed = close(
    TAll([mkBinder("A", TUnknown), mkBinder("B", TUnknown)], FVar(X, "X")),
    X,
  );
  const expected = TAll(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    BVar(2),
  );
  expect(alphaEq(closed, expected)).toBe(true);
});

Deno.test("substFVar is open after close", () => {
  // The classic identity, and a check that both implementations agree.
  const type = TFun([FVar(X, "X")], TData(Pair, [FVar(X, "X"), FVar(Y, "Y")]));
  const replacement = TData(Bool);
  expect(
    alphaEq(
      substFVar(type, X, replacement),
      open(close(type, X), replacement),
    ),
  ).toBe(true);
});

Deno.test("substMany is simultaneous, unlike iterated substFVar", () => {
  // At once this is a swap; in sequence the second rewrites the first's output.
  const type = TFun([FVar(X, "X")], FVar(Y, "Y"));
  const swapped = substMany(type, [X, Y], [FVar(Y, "Y"), FVar(X, "X")]);
  expect(alphaEq(swapped, TFun([FVar(Y, "Y")], FVar(X, "X")))).toBe(true);

  const sequential = substFVar(
    substFVar(type, X, FVar(Y, "Y")),
    Y,
    FVar(X, "X"),
  );
  expect(alphaEq(sequential, TFun([FVar(X, "X")], FVar(X, "X")))).toBe(true);
});

Deno.test("substFVar does not shift when landing under a binder", () => {
  // An FVar is an identity, not a position, so depth changes nothing.
  const type = TAll([mkBinder("A", TUnknown)], TFun([BVar(0)], FVar(X, "X")));
  const substituted = substFVar(type, X, TData(Bool));
  const expected = TAll(
    [mkBinder("A", TUnknown)],
    TFun([BVar(0)], TData(Bool)),
  );
  expect(alphaEq(substituted, expected)).toBe(true);
});

Deno.test("occurs finds an existential nested in TData arguments", () => {
  const a = mkEVarId(0);
  expect(occurs(a, TData(Pair, [TUnknown, EVar(a, "a")]))).toBe(true);
  expect(occurs(a, TData(Pair, [TUnknown, EVar(mkEVarId(1), "b")]))).toBe(
    false,
  );
});

Deno.test("alphaEq ignores printing hints but not arity", () => {
  expect(
    alphaEq(
      TAll([mkBinder("A", TUnknown)], BVar(0)),
      TAll([mkBinder("Z", TUnknown)], BVar(0)),
    ),
  ).toBe(true);
  expect(
    alphaEq(TFun([TData(Bool)], TData(Bool)), TFun([], TData(Bool))),
  ).toBe(false);
});

Deno.test("typeToString names bound variables from their binders", () => {
  const type = TAll(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    TFun([BVar(0)], TData(Pair, [BVar(1), TNever])),
  );
  expect(typeToString(type))
    .toBe("forall A <: unknown, B <: unknown. A -> Pair[B, never]");
});

Deno.test("typeToString parenthesises by arity, not habit", () => {
  expect(typeToString(TFun([TData(Bool), TData(Bool)], TData(Bool))))
    .toBe("(Bool, Bool) -> Bool");
  expect(
    typeToString(TFun([TFun([TData(Bool)], TData(Bool))], TData(Bool))),
  ).toBe("(Bool -> Bool) -> Bool");
});

Deno.test("TAll with no binders is its body", () => {
  // `forall . T = T`, so the constructor normalizes instead of building one.
  expect(alphaEq(TAll([], TData(Bool)), TData(Bool))).toBe(true);
  expect(TAll([], TData(Bool)).kind).toBe("TData");
});

Deno.test("normalizing an empty quantifier survives a traversal", () => {
  // closeAt rebuilds every TAll it passes; a real one must survive that.
  const type = TAll([mkBinder("A", TUnknown)], FVar(X, "X"));
  expect(close(type, X).kind).toBe("TAll");
});
