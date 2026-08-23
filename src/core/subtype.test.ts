import { expect } from "@std/expect";
import { Context } from "./context.ts";
import { type Cast, Subtyper } from "./subtype.ts";
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
  TMissing,
  TNever,
  TUnknown,
  type Type,
  type TypePattern,
  typeToString,
} from "./types.ts";

const ListP = (arg: TypePattern) => TData(mkDataName("List"), [arg]);
const fnP = (params: readonly TypePattern[], result: TypePattern) =>
  TFun([], params, result);

/**
 * A cast's answer, or `<none>` when it declined -- which reads better in a
 * table of results than the `<bad>` that stands in for it.
 */
function castToString(cast: Cast): string {
  return cast.verdict === "yes" ? typeToString(cast.type) : "<none>";
}

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

Deno.test("a solved EVar never reaches the relation", () => {
  // The checker substitutes at the one boundary where a solution escapes, so
  // arriving here unsubstituted is a bug in it -- and a quiet one if the
  // relation coped, since the variable would take fresh bounds after the fact.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  context.setSolution(a, Bool);

  expect(() => sub.isSubtype(EVar(a, "a"), Bool)).toThrow("is solved");
  expect(() => sub.expose(EVar(a, "a"))).toThrow("is solved");
  // Nested rather than at the head, so the whole-type traversal is what says so.
  const b = context.pushEVar("b");
  expect(() => sub.isSubtype(List(EVar(a, "a")), EVar(b, "b")))
    .toThrow("is solved");
  // Applying first is what a caller owes the relation, and then it answers.
  expect(sub.isSubtype(context.apply(EVar(a, "a")), Bool)).toBe("yes");
  expect(sub.isSubtype(context.apply(EVar(a, "a")), Int)).toBe("no");
  expect(context.evarAt(a).upper.length).toBe(0);
});

Deno.test("join and meet agree with the relation on ordered pairs", () => {
  const { sub } = fixture();
  expect(typeToString(sub.join(TNever, Bool))).toBe("Bool");
  expect(typeToString(sub.join(Bool, TUnknown))).toBe("unknown");
  expect(typeToString(sub.meet(TUnknown, Bool))).toBe("Bool");
  expect(typeToString(sub.meet(Bool, TNever))).toBe("never");
});

Deno.test("top and bottom meet an EVar without constraining it", () => {
  // Both are decided by shape, before the relation is consulted. Asking the
  // relation would answer with a *constraint* -- `unknown <: ?a` recorded as a
  // lower bound -- which is true, useless, and not something anyone asked for:
  // a lattice operation must not write on its operands.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const evar = EVar(a, "a");
  expect(typeToString(sub.join(TNever, evar))).toBe("?a");
  expect(typeToString(sub.join(evar, TUnknown))).toBe("unknown");
  expect(typeToString(sub.meet(TUnknown, evar))).toBe("?a");
  expect(typeToString(sub.meet(evar, TNever))).toBe("never");
  expect(context.evarAt(a).lower).toEqual([]);
  expect(context.evarAt(a).upper).toEqual([]);
});

Deno.test("a variable joins at its bound and meets as itself", () => {
  const { context, sub } = fixture();
  const X = FVar(context.pushTypeVar(Bool, "X"), "X");
  // Upward the bound stands in for the variable; downward it only answers
  // whether the variable fits, since nothing sits below `X` but `X`.
  expect(typeToString(sub.join(X, Bool))).toBe("Bool");
  expect(typeToString(sub.meet(X, Bool))).toBe("X");
  expect(typeToString(sub.join(X, Int))).toBe("unknown");
  expect(typeToString(sub.meet(X, Int))).toBe("never");
});

Deno.test("two unrelated variables join above both their bounds", () => {
  // Neither sits under the other, so an ordering test would give up at top.
  // Each stands aside for its bound instead, and the join goes on there.
  const { context, sub } = fixture();
  const X = FVar(context.pushTypeVar(Bool, "X"), "X");
  const Y = FVar(context.pushTypeVar(Bool, "Y"), "Y");
  expect(typeToString(sub.join(X, Y))).toBe("Bool");
  expect(typeToString(sub.join(Y, X))).toBe("Bool");
  // And the bound keeps its shape, so the join is still taken pointwise.
  const F = FVar(context.pushTypeVar(fn([Bool], Bool), "F"), "F");
  expect(typeToString(sub.join(F, fn([Int], Bool)))).toBe("never -> Bool");
});

Deno.test("an unbounded variable has no meet with anything but itself", () => {
  // Promoting `X` to `unknown` and meeting there would answer `Bool`, which
  // nothing says sits under `X`. Bottom is the honest answer.
  const { context, sub } = fixture();
  const X = FVar(context.pushTypeVar(TUnknown, "X"), "X");
  expect(typeToString(sub.meet(X, Bool))).toBe("never");
  expect(typeToString(sub.meet(X, X))).toBe("X");
  expect(typeToString(sub.join(X, Bool))).toBe("unknown");
});

Deno.test("two variables order by their bounds, however they are given", () => {
  const { context, sub } = fixture();
  const X = FVar(context.pushTypeVar(TUnknown, "X"), "X");
  const Y = FVar(context.pushTypeVar(X, "Y"), "Y");
  const pairs: readonly (readonly [Type, Type])[] = [[X, Y], [Y, X]];
  for (const [a, b] of pairs) {
    expect(typeToString(sub.join(a, b))).toBe("X");
    expect(typeToString(sub.meet(a, b))).toBe("Y");
  }
});

Deno.test("a lattice operation leaves an EVar alone", () => {
  // The relation records a bound instead of answering, so testing a pair with
  // it is a write. `join` is asked as a question -- the LUB of a match's arms
  // -- and must not answer by constraining whichever side it tried first.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const evar = EVar(a, "a");
  expect(typeToString(sub.join(evar, Bool))).toBe("unknown");
  expect(typeToString(sub.meet(evar, Bool))).toBe("never");
  expect(typeToString(sub.join(List(evar), List(Bool)))).toBe("unknown");
  expect(context.evarAt(a).lower).toEqual([]);
  expect(context.evarAt(a).upper).toEqual([]);
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

Deno.test("a nest of datatypes compares with itself in one walk", () => {
  // Invariance relates each argument in both directions, so without the
  // equality test in that loop this pair costs `2^depth` and exhausts a real
  // budget by depth 11. A budget of two says it is not recursing at all.
  const sub = new Subtyper(new Context(), 2);
  let deep: Type = Bool;
  for (let i = 0; i < 20; i++) deep = List(deep);
  expect(sub.isSubtype(deep, deep)).toBe("yes");
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

Deno.test("a missing part takes whatever the type has there", () => {
  const { sub } = fixture();
  expect(castToString(sub.upcast(Bool, TMissing))).toBe("Bool");
  expect(castToString(sub.downcast(Bool, TMissing))).toBe("Bool");
  expect(castToString(sub.exactcast(Bool, TMissing))).toBe("Bool");
});

Deno.test("a written pattern matches only itself, and the direction decides", () => {
  const { sub } = fixture();
  // `Bool <: unknown`, so `unknown` is reachable going up but not down.
  expect(castToString(sub.upcast(Bool, TUnknown))).toBe("unknown");
  expect(castToString(sub.downcast(Bool, TUnknown))).toBe("<none>");
  expect(castToString(sub.downcast(TUnknown, Bool))).toBe("Bool");
  expect(castToString(sub.upcast(Bool, Int))).toBe("<none>");
});

Deno.test("a cast fills a function pointwise, flipping at the parameters", () => {
  const { sub } = fixture();
  const idish = fn([Bool], Bool);
  expect(castToString(sub.upcast(idish, fnP([TMissing], TMissing))))
    .toBe("Bool -> Bool");
  // Nothing on the left, so the pattern alone decides: least going up means
  // the smallest result and -- parameters being contravariant -- the largest
  // parameter.
  expect(castToString(sub.upcast(TNever, fnP([TMissing], TMissing))))
    .toBe("unknown -> never");
  expect(castToString(sub.downcast(TUnknown, fnP([TMissing], TMissing))))
    .toBe("never -> unknown");
});

Deno.test("an invariant cast is not either of the other two", () => {
  // The case that makes the third direction necessary. A datatype argument is
  // invariant, so recursing into it may not move -- but it must still recurse,
  // since the argument pattern has a missing part to fill from the type.
  const { sub } = fixture();
  const listOfId = List(fn([Bool], Bool));
  expect(castToString(sub.downcast(listOfId, ListP(fnP([TMissing], Bool)))))
    .toBe("List[Bool -> Bool]");
  expect(castToString(sub.upcast(listOfId, ListP(fnP([Bool], TMissing)))))
    .toBe("List[Bool -> Bool]");
  // Written and disagreeing: invariance has nowhere to go.
  expect(castToString(sub.upcast(listOfId, ListP(fnP([TMissing], Int)))))
    .toBe("<none>");
});

Deno.test("an invariant missing part costs the verdict, not the answer", () => {
  // Nothing is greatest among the types a `List` can be of, so an extreme
  // lifted into one has to invent the argument. The shape is still built and
  // handed back -- so a `match` on it has a datatype to work with -- but it is
  // a stand-in, and must not read as a success.
  const { sub } = fixture();
  const lifted = sub.upcast(TNever, ListP(TMissing));
  expect(lifted.verdict).toBe("no");
  expect(typeToString(lifted.type)).toBe("List[<bad>]");

  // Nested, the walk fills the rest of the shape rather than stopping at the
  // first invented argument.
  const nested = sub.upcast(TNever, ListP(ListP(TMissing)));
  expect(nested.verdict).toBe("no");
  expect(typeToString(nested.type)).toBe("List[List[<bad>]]");

  // With every argument written there is nothing to invent, so the same lift
  // is an answer.
  expect(castToString(sub.downcast(TUnknown, ListP(Bool)))).toBe("List[Bool]");
  expect(castToString(sub.upcast(TNever, ListP(Bool)))).toBe("List[Bool]");
});

Deno.test("a variable stands aside for its bound going up, and not down", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(fn([Bool], Bool), "X");
  const x = FVar(X, "X");
  expect(castToString(sub.upcast(x, fnP([TMissing], TMissing))))
    .toBe("Bool -> Bool");
  // Nothing structural sits under a variable, so there is no answer below it
  // -- and inventing one from the pattern would build a type not under `X`.
  expect(castToString(sub.downcast(x, fnP([TMissing], TMissing))))
    .toBe("<none>");
  expect(castToString(sub.exactcast(x, fnP([TMissing], TMissing))))
    .toBe("<none>");
  // Itself, whichever way.
  expect(castToString(sub.downcast(x, TMissing))).toBe("X");
});

Deno.test("an unbounded variable has no function above it either", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(TUnknown, "X");
  expect(castToString(sub.upcast(FVar(X, "X"), fnP([TMissing], TMissing))))
    .toBe("<none>");
});

Deno.test("a bad type satisfies any demand", () => {
  // A report already stands, so nothing here is failed a second time.
  const { sub } = fixture();
  expect(castToString(sub.upcast(TBad, ListP(TMissing)))).toBe("List[<bad>]");
  expect(castToString(sub.downcast(TBad, fnP([Bool], TMissing))))
    .toBe("Bool -> <bad>");
});

Deno.test("a parameter list of the wrong length costs its own positions", () => {
  // Arity is a disagreement at the positions that are not shared, not a wall.
  // The answer has the pattern's arity -- the caller asked for that shape and
  // reads the parts off it -- and the parts that do line up keep their real
  // answers, which is the rule the rest of the walk follows.
  const { sub } = fixture();
  const tooFew = sub.upcast(fn([Bool], Bool), fnP([Bool, Bool], TMissing));
  expect(tooFew.verdict).toBe("no");
  expect(typeToString(tooFew.type)).toBe("(Bool, Bool) -> Bool");

  const tooMany = sub.upcast(fn([Bool, Bool], Bool), fnP([Bool], TMissing));
  expect(tooMany.verdict).toBe("no");
  expect(typeToString(tooMany.type)).toBe("Bool -> Bool");

  // Quantifying a different number of variables is a wall, though: the two
  // parameter lists stand under different binders, so their positions do not
  // correspond and neither can be read in the other's scope.
  const quantified = sub.upcast(
    fn([Bool], Bool),
    TFun([mkTypeParamInfo("A", TUnknown)], [TMissing], TMissing),
  );
  expect(quantified.verdict).toBe("no");
});

Deno.test("a cast is shape-exact, so arity is part of the pattern", () => {
  const { sub } = fixture();
  expect(castToString(sub.upcast(fn([Bool], Bool), fnP([TMissing], TMissing))))
    .toBe("Bool -> Bool");
  expect(
    castToString(
      sub.upcast(fn([Bool], Bool), fnP([TMissing, TMissing], TMissing)),
    ),
  ).toBe("<none>");
  expect(castToString(sub.upcast(List(Bool), ListP(TMissing))))
    .toBe("List[Bool]");
  expect(castToString(sub.upcast(Bool, ListP(TMissing)))).toBe("<none>");
});

Deno.test("a declined cast answers with the shape that was asked for", () => {
  // Total, the way the relation is -- and the shape survives, so a `match` on
  // the answer still has a datatype to check its arms against. `<bad>` stands
  // only where the pattern said nothing, and cannot go on to be blamed.
  const { sub } = fixture();
  const declined = sub.upcast(Bool, ListP(TMissing));
  expect(declined.verdict).toBe("no");
  expect(typeToString(declined.type)).toBe("List[<bad>]");

  // A pattern written in full leaves nothing to fill: this is exactly what
  // `check` does today by returning its expected type after reporting.
  const mismatch = sub.upcast(Bool, Int);
  expect(mismatch.verdict).toBe("no");
  expect(typeToString(mismatch.type)).toBe("Int");

  // Deeper failures rebuild at the top, rather than handing up the fragment
  // that failed.
  const inner = sub.upcast(fn([Bool], Bool), fnP([Bool], ListP(TMissing)));
  expect(inner.verdict).toBe("no");
  expect(typeToString(inner.type)).toBe("Bool -> List[<bad>]");
});

Deno.test("a bad type answers with the demanded shape too", () => {
  const { sub } = fixture();
  const cast = sub.upcast(TBad, ListP(TMissing));
  expect(cast.verdict).toBe("yes");
  expect(typeToString(cast.type)).toBe("List[<bad>]");
});

Deno.test("a cast out of fuel says so, rather than reporting a mismatch", () => {
  // The distinction the whole `Verdict` exists for: a spent tank is the
  // checker's limit, and calling it a mismatch would blame the program.
  const { context } = fixture();
  const starved = new Subtyper(context, 0);
  expect(starved.upcast(Bool, Bool).verdict).toBe("exhausted");
});

Deno.test("a quantified parameter is opened, so its bound can be read", () => {
  // Without opening, the result stands at a `BVar`, which has no bound -- so a
  // pattern asking it for a shape could never be answered however tightly the
  // binder bounded it. Opened, it promotes the way any variable does.
  const { sub } = fixture();
  const idish = fn([Bool], Bool);
  const type = TFun([mkTypeParamInfo("Y", idish)], [Bool], BVar(0));
  const pattern = TFun(
    [mkTypeParamInfo("X", idish)],
    [Bool],
    fnP([TMissing], TMissing),
  );
  expect(castToString(sub.upcast(type, pattern)))
    .toBe("[X <: Bool -> Bool](Bool) -> Bool -> Bool");
});

Deno.test("a part that cannot be cast costs itself and not its siblings", () => {
  // Nothing fails outright, so the walk carries on and keeps what it found:
  // the parameter is the shape that was asked for, and the result beside it is
  // still the real answer rather than collateral.
  const { sub } = fixture();
  const partial = sub.upcast(fn([Bool], Bool), fnP([Int], TMissing));
  expect(partial.verdict).toBe("no");
  expect(typeToString(partial.type)).toBe("Int -> Bool");
});

Deno.test("a variable pattern is answered, not promoted past", () => {
  // Promotion supplies a shape, so it has no business in front of a leaf: the
  // relation answers those and promotes on its own, and it knows `X <: X`,
  // which promoting here would lose. Over-exposing loses every pair whose
  // answer is the variable itself.
  const { context, sub } = fixture();
  const X = FVar(context.pushTypeVar(Bool, "X"), "X");
  const Y = FVar(context.pushTypeVar(X, "Y"), "Y");
  expect(castToString(sub.upcast(X, X))).toBe("X");
  expect(castToString(sub.upcast(Y, X))).toBe("X");
  expect(castToString(sub.downcast(X, X))).toBe("X");
  // An unbounded variable would promote straight to top, so this is the case
  // that fails loudest without the guard.
  const U = FVar(context.pushTypeVar(TUnknown, "U"), "U");
  expect(castToString(sub.upcast(U, U))).toBe("U");
  // Still promoted when a shape really is wanted.
  const F = FVar(context.pushTypeVar(fn([Bool], Bool), "F"), "F");
  expect(castToString(sub.upcast(F, fnP([TMissing], TMissing))))
    .toBe("Bool -> Bool");
});

Deno.test("a cast that succeeds is related to its input, always", () => {
  // The property the direction *means*, checked over a grid rather than by
  // choosing examples: an answer going up must sit above what it came from,
  // one going down below it, and an invariant one on both sides. This is what
  // catches a rule that moves `type` where it may not -- the shape of the
  // over-exposure bug, whatever form it takes next.
  //
  // Unsolved EVars are left out: they answer by mode rather than by structure,
  // so a grid says more about `probe` than about the cast.
  const { context, sub } = fixture();
  const X = FVar(context.pushTypeVar(Bool, "X"), "X");
  const U = FVar(context.pushTypeVar(TUnknown, "U"), "U");
  const F = FVar(context.pushTypeVar(fn([Bool], Bool), "F"), "F");

  const types: readonly Type[] = [
    TUnknown,
    TNever,
    TBad,
    X,
    U,
    F,
    Bool,
    fn([Bool], Bool),
    List(Bool),
    TFun([mkTypeParamInfo("A", TUnknown)], [BVar(0)], BVar(0)),
  ];
  const patterns: readonly TypePattern[] = [
    TMissing,
    TUnknown,
    TNever,
    TBad,
    X,
    Bool,
    Int,
    fnP([TMissing], TMissing),
    fnP([Bool], TMissing),
    ListP(TMissing),
    TFun([mkTypeParamInfo("A", TUnknown)], [TMissing], TMissing),
  ];

  let succeeded = 0;
  for (const type of types) {
    for (const pattern of patterns) {
      // Nothing demanded, and nothing already blamed, must never decline.
      expect(sub.upcast(type, TMissing).type).toBe(type);
      expect(sub.upcast(TBad, pattern).verdict).toBe("yes");

      const up = sub.upcast(type, pattern);
      if (up.verdict === "yes") {
        succeeded++;
        expect(sub.isSubtype(type, up.type)).toBe("yes");
      }
      const down = sub.downcast(type, pattern);
      if (down.verdict === "yes") {
        succeeded++;
        expect(sub.isSubtype(down.type, type)).toBe("yes");
      }
      const exact = sub.exactcast(type, pattern);
      if (exact.verdict === "yes") {
        succeeded++;
        expect(sub.isSubtype(type, exact.type)).toBe("yes");
        expect(sub.isSubtype(exact.type, type)).toBe("yes");
      }
    }
  }
  // A grid that stopped relating anything would pass vacuously.
  expect(succeeded).toBeGreaterThan(100);
});
