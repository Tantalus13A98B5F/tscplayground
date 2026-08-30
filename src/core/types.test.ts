import { expect } from "@std/expect";
import {
  alphaEq,
  BVar,
  closeFrom,
  type DataHead,
  FVar,
  isClosed,
  mkLevel,
  mkTypeParamInfo,
  open,
  openMany,
  openWith,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
  typeToString,
  type Variance,
} from "./types.ts";

// Levels 0 and 1 stand for the two outermost context entries.
const X = mkLevel(0);
const Y = mkLevel(1);
/** Close the scope starting at X, taking both levels with it. */
const closeXY = (type: typeof TUnknown) => closeFrom(type, X);
/**
 * A `TData` carries its declaration's parameters, so a test that builds one
 * states the variances it means to be read back.
 */
const head = (name: string, ...variances: readonly Variance[]): DataHead => ({
  name: name,
  params: variances.map((variance, j) => ({
    hint: String.fromCharCode(65 + j),
    variance,
  })),
});
const Pair = head("Pair", 0, 0);
const Bool = head("Bool");
const List = head("List", 1);

Deno.test("open replaces the nearest bound variable", () => {
  const opened = open(TFun([], [BVar(0)], BVar(0)), TNever);
  expect(alphaEq(opened, TFun([], [TNever], TNever))).toBe(true);
});

Deno.test("bounds are parallel, but parameters are inside the binder", () => {
  // The bound's index 0 is the enclosing binder; the parameter's is this one.
  const opened = open(
    TFun([mkTypeParamInfo("B", BVar(0))], [BVar(0)], TUnknown),
    TData(Bool),
  );
  const expected = TFun(
    [mkTypeParamInfo("B", TData(Bool))],
    [BVar(0)],
    TUnknown,
  );
  expect(alphaEq(opened, expected)).toBe(true);
});

Deno.test("open moves inward by the full arity of a quantifier", () => {
  // Under `forall A, B` the outer variable is BVar 2, not BVar 1.
  const type = TFun(
    [mkTypeParamInfo("A", TUnknown), mkTypeParamInfo("B", TUnknown)],
    [BVar(0)],
    BVar(2),
  );
  const opened = open(type, TData(Bool));
  const expected = TFun(
    [mkTypeParamInfo("A", TUnknown), mkTypeParamInfo("B", TUnknown)],
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

Deno.test("closeFrom abstracts a whole scope simultaneously", () => {
  const body = TFun([], [FVar(X, "X")], FVar(Y, "Y"));
  expect(alphaEq(closeXY(body), TFun([], [BVar(0)], BVar(1)))).toBe(true);
});

Deno.test("closeFrom leaves levels outside its range alone", () => {
  // Only the scope being ended is abstracted; anything enclosing it stays free.
  const body = TFun([], [FVar(X, "X")], FVar(Y, "Y"));
  const closed = closeFrom(body, Y);
  expect(alphaEq(closed, TFun([], [FVar(X, "X")], BVar(0)))).toBe(true);
});

Deno.test("close then open is the identity on a free variable", () => {
  // Closing from Y takes the innermost scope only, so X stays free and one
  // replacement is exactly what reopening it needs.
  const original = TFun(
    [],
    [FVar(X, "X")],
    TData(Pair, [FVar(X, "X"), FVar(Y, "Y")]),
  );
  const roundTrip = open(closeFrom(original, Y), FVar(Y, "Y"));
  expect(alphaEq(roundTrip, original)).toBe(true);
});

Deno.test("close shifts by the arity of each enclosing quantifier", () => {
  const closed = closeFrom(
    TFun(
      [mkTypeParamInfo("A", TUnknown), mkTypeParamInfo("B", TUnknown)],
      [],
      FVar(X, "X"),
    ),
    X,
  );
  const expected = TFun(
    [mkTypeParamInfo("A", TUnknown), mkTypeParamInfo("B", TUnknown)],
    [],
    BVar(2),
  );
  expect(alphaEq(closed, expected)).toBe(true);
});

Deno.test("isClosed bounds free levels and bound indices at once", () => {
  const type = TFun([], [FVar(Y, "Y")], BVar(0));
  // `Y` is level 1, so it needs two levels in scope; `BVar 0` needs one binder.
  expect(isClosed(type, mkLevel(2), 1)).toBe(true);
  expect(isClosed(type, mkLevel(1), 1)).toBe(false);
  expect(isClosed(type, mkLevel(2), 0)).toBe(false);
});

Deno.test("isClosed counts a quantifier's own group as binders", () => {
  // What a stored constructor field looks like: no free levels, `BVar j` for
  // each of the datatype's parameters. A depth-zero check could not say this.
  const field = TData(Pair, [BVar(0), BVar(1)]);
  expect(isClosed(field, mkLevel(0), 2)).toBe(true);
  expect(isClosed(field, mkLevel(0), 1)).toBe(false);

  const inside = TFun([mkTypeParamInfo("A", TUnknown)], [BVar(0)], BVar(1));
  expect(isClosed(inside, mkLevel(0), 1)).toBe(true);
  expect(isClosed(inside, mkLevel(0), 0)).toBe(false);
});

Deno.test("isClosed reads a bound in the enclosing scope, being parallel", () => {
  // The bound sits outside its own binder, so `BVar 0` there is the *enclosing*
  // group -- it needs a depth the parameters do not.
  const type = TFun([mkTypeParamInfo("A", BVar(0))], [BVar(0)], TUnknown);
  expect(isClosed(type, mkLevel(0), 1)).toBe(true);
  expect(isClosed(type, mkLevel(0), 0)).toBe(false);
});

Deno.test("alphaEq ignores printing hints but not arity", () => {
  expect(
    alphaEq(
      TFun([mkTypeParamInfo("A", TUnknown)], [], BVar(0)),
      TFun([mkTypeParamInfo("Z", TUnknown)], [], BVar(0)),
    ),
  ).toBe(true);
  expect(
    alphaEq(TFun([], [TData(Bool)], TData(Bool)), TFun([], [], TData(Bool))),
  ).toBe(false);
});

Deno.test("typeToString names bound variables from their binders", () => {
  const type = TFun(
    [mkTypeParamInfo("A", TUnknown), mkTypeParamInfo("B", TUnknown)],
    [BVar(0)],
    TData(Pair, [BVar(1), TNever]),
  );
  expect(typeToString(type)).toBe("[A, B](A) -> Pair[B, never]");
});

Deno.test("typeToString elides only the trivial bound", () => {
  // `<: unknown` is the default, so printing it is noise on every signature.
  const type = TFun([mkTypeParamInfo("A", TData(Bool))], [BVar(0)], BVar(0));
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
  const type = TFun([mkTypeParamInfo("A", TUnknown)], [], FVar(X, "X"));
  const closed = closeFrom(type, X);
  expect(closed.kind === "TFun" && closed.typeParams.length).toBe(1);
});

/** Where `BVar 0` occurs, as the pair of flags an EVar entry would keep. */
function occurrencesIn(type: Type): [boolean, boolean] {
  const seen: [boolean, boolean] = [false, false];
  openWith(type, (index, variance) => {
    if (index === 0) {
      if (variance >= 0) seen[0] = true;
      if (variance <= 0) seen[1] = true;
    }
    return TNever;
  });
  return seen;
}

Deno.test("opening reads a variable's occurrences by variance", () => {
  const v = BVar(0);
  expect(occurrencesIn(TFun([], [TNever], v))).toEqual([true, false]);
  expect(occurrencesIn(TFun([], [v], TNever))).toEqual([false, true]);
  expect(occurrencesIn(TFun([], [v], v))).toEqual([true, true]);
  expect(occurrencesIn(TFun([], [TNever], TUnknown))).toEqual([false, false]);
});

Deno.test("a doubly contravariant position is covariant again", () => {
  // `((X) -> Bool) -> Bool`: X is a parameter of a parameter, so it flips twice.
  const inner = TFun([], [BVar(0)], TUnknown);
  expect(occurrencesIn(TFun([], [inner], TUnknown))).toEqual([true, false]);
});

Deno.test("a binder's bound is contravariant, like a parameter", () => {
  // Bounds are parallel, so `BVar 0` there is the *enclosing* binder's.
  expect(occurrencesIn(TFun([mkTypeParamInfo("A", BVar(0))], [], TUnknown)))
    .toEqual([false, true]);
});

Deno.test("an argument stands where the node says its parameter does", () => {
  // Read off the node and not a table: `Pair` is invariant in both, `List`
  // covariant, and the opening asks neither anything.
  expect(occurrencesIn(TData(Pair, [BVar(0), TUnknown]))).toEqual([true, true]);
  expect(occurrencesIn(TData(List, [BVar(0)]))).toEqual([true, false]);
});

Deno.test("an occurrence inside an invariant argument is invariant however deep", () => {
  // Nothing under one may be widened, even at a position that would otherwise
  // be contravariant twice over.
  const nested = TData(Pair, [TFun([], [BVar(0)], TUnknown), TUnknown]);
  expect(occurrencesIn(nested)).toEqual([true, true]);
  // Where the argument does have a direction, what is under it composes.
  expect(occurrencesIn(TData(List, [TFun([], [BVar(0)], TUnknown)])))
    .toEqual([false, true]);
});

Deno.test("a rule is offered every occurrence, and may answer each differently", () => {
  // What the opening is shaped for: a replacement that reads the position.
  const type = TFun([], [BVar(0)], BVar(0));
  const opened = openWith(
    type,
    (_, variance) => variance > 0 ? TNever : TUnknown,
  );
  expect(typeToString(opened)).toBe("unknown -> never");
});

Deno.test("an inner binder's variables are not the ones being opened", () => {
  // `BVar 0` under a nested quantifier belongs to it, so the rule never sees
  // it -- and what the rule does see is the outer variable at index 0.
  const inner = TFun([mkTypeParamInfo("B", TUnknown)], [BVar(0)], BVar(1));
  const indices: number[] = [];
  openWith(inner, (index) => {
    indices.push(index);
    return TNever;
  });
  expect(indices).toEqual([0]);
});
