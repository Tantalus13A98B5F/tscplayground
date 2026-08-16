import { expect } from "@std/expect";
import { Context } from "./context.ts";
import { Subtyper } from "./subtype.ts";
import {
  BVar,
  EVar,
  FVar,
  type Level,
  mkDataName,
  mkTypeParamInfo,
  TBad,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
  typeToString,
} from "./types.ts";

const Bool = TData(mkDataName("Bool"));
const Int = TData(mkDataName("Int"));
const List = (arg: Type) => TData(mkDataName("List"), [arg]);
const fn = (params: readonly Type[], result: Type) => TFun([], params, result);

function fixture(): { context: Context; sub: Subtyper } {
  const context = new Context();
  return { context, sub: new Subtyper(context) };
}

Deno.test("everything is below unknown and above never", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(Bool, TUnknown)).toBe("yes");
  expect(sub.isSubtype(TNever, Bool)).toBe("yes");
  expect(sub.isSubtype(TUnknown, Bool)).toBe("no");
});

Deno.test("a bad type relates to anything, in both directions", () => {
  // One unresolved name must not become an error at every use of it.
  const { sub } = fixture();
  expect(sub.isSubtype(TBad, Bool)).toBe("yes");
  expect(sub.isSubtype(Bool, TBad)).toBe("yes");
});

Deno.test("a bad type flows into an EVar rather than short-circuiting", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  expect(sub.isSubtype(TBad, EVar(a, "a"))).toBe("yes");
  // Recorded, so the EVar solves to `<bad>` instead of looking unconstrained.
  expect(context.evarAt(a)?.lower.map(typeToString)).toEqual(["<bad>"]);
  expect(typeToString(sub.solveLowerBoundOf(a))).toBe("<bad>");
});

Deno.test("a datatype is invariant in its arguments", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(List(Bool), List(Bool))).toBe("yes");
  expect(sub.isSubtype(List(TNever), List(TUnknown))).toBe("no");
  expect(sub.isSubtype(List(Bool), List(Int))).toBe("no");
});

Deno.test("functions are contravariant in parameters, covariant in results", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(fn([TUnknown], TNever), fn([Bool], TUnknown)))
    .toBe("yes");
  expect(sub.isSubtype(fn([TNever], Bool), fn([Bool], Bool))).toBe("no");
  expect(sub.isSubtype(fn([Bool], TUnknown), fn([Bool], Bool))).toBe("no");
});

Deno.test("arity is part of the type", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(fn([Bool], Bool), fn([Bool, Bool], Bool))).toBe("no");
  expect(
    sub.isSubtype(
      TFun([mkTypeParamInfo("A", TUnknown)], [], Bool),
      fn([], Bool),
    ),
  )
    .toBe("no");
});

Deno.test("a type variable is promoted to its bound, but only on the left", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(Bool, "X");
  expect(sub.isSubtype(FVar(X, "X"), Bool)).toBe("yes");
  expect(sub.isSubtype(Bool, FVar(X, "X"))).toBe("no");
});

Deno.test("promotion follows a chain of bounds", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(Bool, "X");
  const Y = context.pushTypeVar(FVar(X, "X"), "Y");
  expect(sub.isSubtype(FVar(Y, "Y"), Bool)).toBe("yes");
  expect(typeToString(sub.expose(FVar(Y, "Y")))).toBe("Bool");
});

Deno.test("bounds are contravariant, which is full Fsub not kernel", () => {
  const { sub } = fixture();
  // `[A <: unknown]() -> Bool  <:  [A <: Bool]() -> Bool`: the right assumes
  // less of A, so the left, which assumes nothing, is the more general.
  const loose = TFun([mkTypeParamInfo("A", TUnknown)], [], Bool);
  const tight = TFun([mkTypeParamInfo("A", Bool)], [], Bool);
  expect(sub.isSubtype(loose, tight)).toBe("yes");
  expect(sub.isSubtype(tight, loose)).toBe("no");
});

Deno.test("a quantifier's body is compared under fresh variables", () => {
  const { sub } = fixture();
  const identity = TFun([mkTypeParamInfo("A", TUnknown)], [BVar(0)], BVar(0));
  expect(sub.isSubtype(identity, identity)).toBe("yes");
  const toUnknown = TFun(
    [mkTypeParamInfo("A", TUnknown)],
    [BVar(0)],
    TUnknown,
  );
  expect(sub.isSubtype(identity, toUnknown)).toBe("yes");
  expect(sub.isSubtype(toUnknown, identity)).toBe("no");
});

Deno.test("comparing a quantifier leaves the context as it found it", () => {
  const { context, sub } = fixture();
  const before = context.size;
  const identity = TFun([mkTypeParamInfo("A", TUnknown)], [BVar(0)], BVar(0));
  sub.isSubtype(identity, identity);
  expect(context.size).toBe(before);
});

Deno.test("an EVar collects a bound instead of answering", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");

  expect(sub.isSubtype(Bool, EVar(a, "a"))).toBe("yes");
  expect(sub.isSubtype(EVar(a, "a"), TUnknown)).toBe("yes");
  expect(context.evarAt(a)?.lower.map(typeToString)).toEqual(["Bool"]);
  // `?a <: unknown` is discharged by the top rule before any bound is recorded.
  expect(context.evarAt(a)?.upper.length).toBe(0);
});

Deno.test("several lower bounds join into one solution", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, EVar(a, "a"));
  sub.isSubtype(Int, EVar(a, "a"));
  // Nothing relates Bool and Int, and there is no union, so the join is top.
  expect(typeToString(sub.solveLowerBoundOf(a))).toBe("unknown");
});

Deno.test("a lower bound is joined, not overwritten by the last constraint", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(TNever, EVar(a, "a"));
  sub.isSubtype(Bool, EVar(a, "a"));
  expect(typeToString(sub.solveLowerBoundOf(a))).toBe("Bool");
});

Deno.test("between two EVars the constraint lands on the righthand one", () => {
  // ?a is to the left of ?b, so only ?b may mention ?a.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const b = context.pushEVar("b");

  expect(sub.isSubtype(EVar(a, "a"), EVar(b, "b"))).toBe("yes");
  expect(context.evarAt(b)?.lower.map(typeToString)).toEqual(["?a"]);
  expect(context.evarAt(a)?.upper.length).toBe(0);
});

Deno.test("avoidance widens an out-of-scope variable to its bound", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  // X is introduced *after* ?a, so ?a's solution may not mention it.
  const X = context.pushTypeVar(Bool, "X");

  expect(sub.isSubtype(FVar(X, "X"), EVar(a, "a"))).toBe("yes");
  expect(context.evarAt(a)?.lower.map(typeToString)).toEqual(["Bool"]);
});

Deno.test("avoidance falls back to top when a variable has no useful bound", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(TUnknown, "X");
  expect(sub.isSubtype(FVar(X, "X"), EVar(a, "a"))).toBe("yes");
  expect(context.evarAt(a)?.lower.map(typeToString)).toEqual(["unknown"]);
});

Deno.test("avoidance swaps direction at a contravariant position", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(Bool, "X");

  // Widening `(X) -> X` means *narrowing* the parameter: `(never) -> Bool`
  // accepts more arguments, so it is the supertype.
  expect(sub.isSubtype(fn([FVar(X, "X")], FVar(X, "X")), EVar(a, "a")))
    .toBe("yes");
  expect(context.evarAt(a)?.lower.map(typeToString)).toEqual([
    "never -> Bool",
  ]);
});

Deno.test("avoidance cannot touch an invariant argument, so it collapses", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(Bool, "X");

  // `List[X]` has no in-scope supertype but top: widening the argument would
  // change the type, invariance being the whole point.
  expect(sub.isSubtype(List(FVar(X, "X")), EVar(a, "a"))).toBe("yes");
  expect(context.evarAt(a)?.lower.map(typeToString)).toEqual(["unknown"]);
});

Deno.test("an out-of-scope EVar is interdependent, and is rejected", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const b = context.pushEVar("b");

  // `List[?b] <: ?a` would need ?a's solution to mention ?b, which stands to
  // its right and has no solution yet. Nothing sound to record, so: reject.
  expect(sub.isSubtype(List(EVar(b, "b")), EVar(a, "a")))
    .toBe("interdependent");
  expect(context.evarAt(a)?.lower.length).toBe(0);
});

Deno.test("a solved EVar is substituted before anything else looks at it", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  context.setSolution(a, Bool);
  expect(sub.isSubtype(EVar(a, "a"), Bool)).toBe("yes");
  expect(sub.isSubtype(EVar(a, "a"), Int)).toBe("no");
  expect(context.evarAt(a)?.upper.length).toBe(0);
});

Deno.test("join and meet agree with the relation on ordered pairs", () => {
  const { sub } = fixture();
  expect(typeToString(sub.join(TNever, Bool))).toBe("Bool");
  expect(typeToString(sub.join(Bool, TUnknown))).toBe("unknown");
  expect(typeToString(sub.meet(TUnknown, Bool))).toBe("Bool");
  expect(typeToString(sub.meet(Bool, TNever))).toBe("never");
});

Deno.test("join of unrelated types is top, there being no union", () => {
  const { sub } = fixture();
  expect(typeToString(sub.join(Bool, Int))).toBe("unknown");
  expect(typeToString(sub.meet(Bool, Int))).toBe("never");
});

Deno.test("join of two arrows meets their parameters", () => {
  const { sub } = fixture();
  const joined = sub.join(fn([Bool], Bool), fn([Int], Int));
  // Parameters are contravariant, so they meet where the results join.
  expect(typeToString(joined)).toBe("never -> unknown");
});

Deno.test("two quantified arrows join under their binders", () => {
  const { sub, context } = fixture();
  const before = context.size;
  // `[A <: Bool](A) -> Bool` and `[A <: Int](A) -> Int`. The bounds are
  // contravariant, so the joined quantifier takes their meet.
  const left = TFun([mkTypeParamInfo("A", Bool)], [BVar(0)], Bool);
  const right = TFun([mkTypeParamInfo("A", Int)], [BVar(0)], Int);
  expect(typeToString(sub.join(left, right))).toBe(
    "[A <: never](A) -> unknown",
  );
  // The group opened to join under is gone again, and the result closed over it.
  expect(context.size).toBe(before);
});

Deno.test("arrows of different arity share no arrow", () => {
  const { sub } = fixture();
  expect(typeToString(sub.join(fn([Bool], Bool), fn([Bool, Bool], Bool))))
    .toBe("unknown");
  const quantified = TFun([mkTypeParamInfo("A", TUnknown)], [BVar(0)], Bool);
  expect(typeToString(sub.join(quantified, fn([Bool], Bool)))).toBe("unknown");
});

Deno.test("a bad type absorbs both lattice operations", () => {
  const { sub } = fixture();
  expect(typeToString(sub.join(TBad, Bool))).toBe("<bad>");
  expect(typeToString(sub.meet(Bool, TBad))).toBe("<bad>");
});

Deno.test("an EVar with no bounds spans the whole lattice", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  expect(typeToString(sub.solveLowerBoundOf(a))).toBe("never");
  expect(typeToString(sub.solveUpperBoundOf(a))).toBe("unknown");
});

/** Nested arrows, each level forcing one more bound comparison. */
function nest(depth: number, innermost: Type): Type {
  let type = innermost;
  for (let i = 0; i < depth; i++) {
    type = TFun([mkTypeParamInfo("A", type)], [], Bool);
  }
  return type;
}

Deno.test("a comparison past the budget is exhausted, not a mismatch", () => {
  const context = new Context();
  const sub = new Subtyper(context, 20);
  // The two differ only at the very bottom, so nothing short-circuits and the
  // budget runs out first. Reporting this as "no" would blame the program for
  // the checker's limit.
  expect(sub.isSubtype(nest(50, Bool), nest(50, Int))).toBe("exhausted");
});

Deno.test("the budget is per query, so one deep ask does not poison the next", () => {
  const context = new Context();
  const sub = new Subtyper(context, 20);
  expect(sub.isSubtype(nest(50, Bool), nest(50, Int))).toBe("exhausted");
  expect(sub.isSubtype(Bool, TUnknown)).toBe("yes");
  expect(typeToString(sub.join(TNever, Bool))).toBe("Bool");
});

Deno.test("a comparison within the budget still decides", () => {
  const context = new Context();
  const sub = new Subtyper(context, 2000);
  expect(sub.isSubtype(nest(50, Bool), nest(50, Bool))).toBe("yes");
  expect(sub.isSubtype(nest(50, Bool), nest(50, Int))).toBe("no");
});

Deno.test("expose promotes an unbounded variable to top", () => {
  // There is no "no bound": unbounded means `TUnknown`, so exposure has an
  // answer here rather than stopping at the variable.
  const { context, sub } = fixture();
  const X = context.pushTypeVar(TUnknown, "X");
  expect(typeToString(sub.expose(FVar(X, "X")))).toBe("unknown");
});

Deno.test("a variable naming no entry is a bug, not a type that exposes to itself", () => {
  const { sub } = fixture();
  expect(() => sub.expose(FVar(99 as Level, "Stray"))).toThrow(
    "names no entry",
  );
});

Deno.test("a contravariant occurrence takes the upper bound", () => {
  // `?a` is only ever a parameter of the result, so the widest type that still
  // satisfies the constraints is the informative answer.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(EVar(a, "a"), Bool);

  const solved = sub.solveEVar(a, "contravariant");
  expect(solved.kind === "solved" && typeToString(solved.type)).toBe("Bool");
});

Deno.test("a covariant occurrence takes the lower bound", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, EVar(a, "a"));

  const solved = sub.solveEVar(a, "covariant");
  expect(solved.kind === "solved" && typeToString(solved.type)).toBe("Bool");
});

Deno.test("a covariant EVar with only an upper bound takes bottom", () => {
  // Principal, and the point of asking polarity at all: nothing demanded a
  // larger type, so the smallest the constraints admit is the answer.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(EVar(a, "a"), Bool);

  const solved = sub.solveEVar(a, "covariant");
  expect(solved.kind === "solved" && typeToString(solved.type)).toBe("never");
});

Deno.test("an invariant occurrence demands the bounds meet", () => {
  // `Bool` would check. It is declined because nothing says it is *the*
  // answer, and settling silently hides that a choice was made.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, EVar(a, "a"));
  expect(sub.solveEVar(a, "invariant").kind).toBe("disagrees");

  // Bounded from both sides by the same type, there is nothing to choose.
  const b = context.pushEVar("b");
  sub.isSubtype(Bool, EVar(b, "b"));
  sub.isSubtype(EVar(b, "b"), Bool);
  const solved = sub.solveEVar(b, "invariant");
  expect(solved.kind === "solved" && typeToString(solved.type)).toBe("Bool");
});

Deno.test("occurring nowhere is not the invariant case", () => {
  // Nothing downstream can tell which bound it took, so nothing is hidden by
  // taking one -- the demand.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, EVar(a, "a"));

  const solved = sub.solveEVar(a, "none");
  expect(solved.kind === "solved" && typeToString(solved.type)).toBe("Bool");
});

Deno.test("bounds with nothing between them are a conflict, not a choice", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, EVar(a, "a"));
  sub.isSubtype(EVar(a, "a"), Int);

  const solved = sub.solveEVar(a, "covariant");
  expect(solved.kind).toBe("conflict");
});

Deno.test("an EVar with no bounds at all is unconstrained, not bottom", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  expect(sub.solveEVar(a, "covariant").kind).toBe("unconstrained");
});

Deno.test("one batch's EVars may not depend on each other", () => {
  // Polarity is read off the result type alone, so a sibling standing in a
  // pending bound would be a dependency the selection cannot see.
  const { context, sub } = fixture();
  const [a, b] = context.pushEVarBatch(["a", "b"]);
  if (a === undefined || b === undefined) throw new Error("no batch");

  expect(sub.isSubtype(EVar(a, "a"), EVar(b, "b"))).toBe("interdependent");
  expect(context.evarAt(b).lower.length).toBe(0);
  expect(context.evarAt(a).upper.length).toBe(0);
});

Deno.test("an EVar of an enclosing batch is an ordinary dependency", () => {
  // How a bare lambda's parameter gets its type: the outer variable is solved
  // by its own batch, later, and `apply` resolves the chain then.
  const { context, sub } = fixture();
  const outer = context.pushEVar("A");
  const [inner] = context.pushEVarBatch(["B"]);
  if (inner === undefined) throw new Error("no batch");

  expect(sub.isSubtype(EVar(outer, "A"), EVar(inner, "B"))).toBe("yes");
  expect(context.evarAt(inner).lower.map(typeToString)).toEqual(["?A"]);
});
