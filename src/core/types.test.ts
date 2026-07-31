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
  const opened = open(TFun([], [BVar(0)], BVar(0)), TNever);
  expect(alphaEq(opened, TFun([], [TNever], TNever))).toBe(true);
});

Deno.test("bounds are parallel, but parameters are inside the binder", () => {
  // The bound's index 0 is the enclosing binder; the parameter's is this one.
  const opened = open(
    TFun([mkBinder("B", BVar(0))], [BVar(0)], TUnknown),
    TData(Bool),
  );
  const expected = TFun([mkBinder("B", TData(Bool))], [BVar(0)], TUnknown);
  expect(alphaEq(opened, expected)).toBe(true);
});

Deno.test("open moves inward by the full arity of a quantifier", () => {
  // Under `forall A, B` the outer variable is BVar 2, not BVar 1.
  const type = TFun(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    [BVar(0)],
    BVar(2),
  );
  const opened = open(type, TData(Bool));
  const expected = TFun(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    [BVar(0)],
    TData(Bool),
  );
  expect(alphaEq(opened, expected)).toBe(true);
});

Deno.test("open traverses TData arguments", () => {
  // The trap: skipping `args` leaves a stale BVar and nothing complains.
  const opened = open(TData(Pair, [BVar(0), TData(Bool)]), TNever);
  expect(alphaEq(opened, TData(Pair, [TNever, TData(Bool)]))).toBe(true);
});

Deno.test("openMany instantiates a binder's variables simultaneously", () => {
  const field = TFun([], [BVar(0)], TData(Pair, [BVar(1), BVar(0)]));
  const opened = openMany(field, [TData(Bool), TNever]);
  const expected = TFun([], [TData(Bool)], TData(Pair, [TNever, TData(Bool)]));
  expect(alphaEq(opened, expected)).toBe(true);
});

Deno.test("closeMany abstracts variables simultaneously", () => {
  const body = TFun([], [FVar(X, "X")], FVar(Y, "Y"));
  expect(alphaEq(closeMany(body, [X, Y]), TFun([], [BVar(0)], BVar(1)))).toBe(
    true,
  );
});

Deno.test("iterating close collapses variables onto one index", () => {
  // Both calls run at depth 0 and the second leaves the first's BVar alone, so
  // X and Y collapse onto index 0. Why closeMany is not a loop over close.
  const body = TFun([], [FVar(X, "X")], FVar(Y, "Y"));
  const iterated = close(close(body, X), Y);
  expect(alphaEq(iterated, TFun([], [BVar(0)], BVar(0)))).toBe(true);
  expect(alphaEq(iterated, closeMany(body, [X, Y]))).toBe(false);
});

Deno.test("close then open is the identity on a free variable", () => {
  const original = TFun(
    [],
    [FVar(X, "X")],
    TData(Pair, [FVar(X, "X"), FVar(Y, "Y")]),
  );
  expect(alphaEq(open(close(original, X), FVar(X, "X")), original)).toBe(true);
});

Deno.test("close shifts by the arity of each enclosing quantifier", () => {
  const closed = close(
    TFun([mkBinder("A", TUnknown), mkBinder("B", TUnknown)], [], FVar(X, "X")),
    X,
  );
  const expected = TFun(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    [],
    BVar(2),
  );
  expect(alphaEq(closed, expected)).toBe(true);
});

Deno.test("substFVar is open after close", () => {
  // The classic identity, and a check that both implementations agree.
  const type = TFun(
    [],
    [FVar(X, "X")],
    TData(Pair, [FVar(X, "X"), FVar(Y, "Y")]),
  );
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
  const type = TFun([], [FVar(X, "X")], FVar(Y, "Y"));
  const swapped = substMany(type, [X, Y], [FVar(Y, "Y"), FVar(X, "X")]);
  expect(alphaEq(swapped, TFun([], [FVar(Y, "Y")], FVar(X, "X")))).toBe(true);

  const sequential = substFVar(
    substFVar(type, X, FVar(Y, "Y")),
    Y,
    FVar(X, "X"),
  );
  expect(alphaEq(sequential, TFun([], [FVar(X, "X")], FVar(X, "X")))).toBe(
    true,
  );
});

Deno.test("substFVar does not shift when landing under a binder", () => {
  // An FVar is an identity, not a position, so depth changes nothing.
  const type = TFun([mkBinder("A", TUnknown)], [BVar(0)], FVar(X, "X"));
  const substituted = substFVar(type, X, TData(Bool));
  const expected = TFun([mkBinder("A", TUnknown)], [BVar(0)], TData(Bool));
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
      TFun([mkBinder("A", TUnknown)], [], BVar(0)),
      TFun([mkBinder("Z", TUnknown)], [], BVar(0)),
    ),
  ).toBe(true);
  expect(
    alphaEq(TFun([], [TData(Bool)], TData(Bool)), TFun([], [], TData(Bool))),
  ).toBe(false);
});

Deno.test("typeToString names bound variables from their binders", () => {
  const type = TFun(
    [mkBinder("A", TUnknown), mkBinder("B", TUnknown)],
    [BVar(0)],
    TData(Pair, [BVar(1), TNever]),
  );
  expect(typeToString(type)).toBe("[A, B](A) -> Pair[B, never]");
});

Deno.test("typeToString elides only the trivial bound", () => {
  // `<: unknown` is the default, so printing it is noise on every signature.
  const type = TFun([mkBinder("A", TData(Bool))], [BVar(0)], BVar(0));
  expect(typeToString(type)).toBe("[A <: Bool](A) -> A");
});

Deno.test("typeToString parenthesises by arity, not habit", () => {
  expect(typeToString(TFun([], [TData(Bool), TData(Bool)], TData(Bool))))
    .toBe("(Bool, Bool) -> Bool");
  expect(
    typeToString(TFun([], [TFun([], [TData(Bool)], TData(Bool))], TData(Bool))),
  ).toBe("(Bool -> Bool) -> Bool");
});

Deno.test("TFun is TPoly binding nothing", () => {
  // One node, so a monomorphic arrow needs no case of its own anywhere.
  expect(alphaEq(TFun([], [TNever], TUnknown), TFun([], [TNever], TUnknown)))
    .toBe(true);
});

Deno.test("a quantifier survives a traversal that rebuilds it", () => {
  const type = TFun([mkBinder("A", TUnknown)], [], FVar(X, "X"));
  const closed = close(type, X);
  expect(closed.kind === "TFun" && closed.typeParams.length).toBe(1);
});
