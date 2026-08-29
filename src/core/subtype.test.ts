import { expect } from "@std/expect";
import {
  mkFileId,
  mkPosition,
  reportError,
} from "../diagnostics/diagnostic.ts";
import { Context, type EVarEntry } from "./context.ts";
import { type DatatypeInfo, Declarations } from "./context.ts";
import { Subtyper } from "./subtype.ts";
import {
  badUnder,
  BVar,
  FVar,
  type Level,
  mkDataName,
  mkTypeParamInfo,
  TData,
  TFun,
  TMissing,
  TNever,
  TRef,
  TUnknown,
  type Type,
  type TypePattern,
  typeToString,
  type Variance,
} from "./types.ts";

/** Somewhere for a diagnostic to point at; no test reads it back. */
const somewhere = mkPosition(mkFileId(0), 1, 1);

/** A `<bad>` to hand the relation, under a report a test stands in for. */
const TBad = badUnder(reportError("something was already wrong", somewhere));

/** Note where an EVar stands and solve it, which `withEVars` does in one go. */
function solveAt(sub: Subtyper, entry: EVarEntry, variance: Variance): string {
  entry.noteOccurrence(variance);
  return typeToString(sub.solveEVar(entry, somewhere));
}

/** What the subtyper said about what it recorded, as `severity: message`. */
function saidBy(sub: Subtyper): string[] {
  return sub.diagnostics.map((d) => `${d.severity}: ${d.message}`);
}

const CellP = (arg: TypePattern) => TData(mkDataName("Cell"), [arg]);
const ListP = (arg: TypePattern) => TData(mkDataName("List"), [arg]);
const SinkP = (arg: TypePattern) => TData(mkDataName("Sink"), [arg]);
const fnP = (params: readonly TypePattern[], result: TypePattern) =>
  TFun([], params, result);

/**
 * A cast's answer, or `<none>` when it declined -- which reads better in a
 * table of results than the `<bad>` that stands in for it.
 *
 * A cast has no verdict to read: declining *is* saying so, so what was said is
 * what tells. Taken and cleared, so the next row of a table starts from
 * silence.
 */
function castToString(sub: Subtyper, type: Type): string {
  return sub.diagnostics.splice(0).length === 0 ? typeToString(type) : "<none>";
}

/**
 * The three casts. A position is required of every cast, so these only save
 * repeating the one the tests all point at.
 */
const up = (sub: Subtyper, type: Type, pattern: TypePattern) =>
  sub.upcast(type, pattern, somewhere);
const down = (sub: Subtyper, type: Type, pattern: TypePattern) =>
  sub.downcast(type, pattern, somewhere);
const exact = (sub: Subtyper, type: Type, pattern: TypePattern) =>
  sub.exactcast(type, pattern, somewhere);

const Bool = TData(mkDataName("Bool"));
const Int = TData(mkDataName("Int"));
const Cell = (arg: Type) => TData(mkDataName("Cell"), [arg]);
const RefP = (arg: TypePattern) => TRef(arg);
const List = (arg: Type) => TData(mkDataName("List"), [arg]);
const Sink = (arg: Type) => TData(mkDataName("Sink"), [arg]);
const fn = (params: readonly Type[], result: Type) => TFun([], params, result);

/**
 * A one-parameter datatype whose variance is *stated* rather than inferred.
 * This file's subject is what the relation does with a variance once it has
 * one; where the variance comes from is `elaborate.test.ts`.
 */
function declare(name: string, variance: Variance): DatatypeInfo {
  return {
    name: mkDataName(name),
    params: [{ hint: "A", named: true, at: somewhere, variance }],
    ctors: [],
    initialized: true,
    at: somewhere,
  };
}

/**
 * One of each, so a walk that reads the wrong slot or forgets to compose shows
 * up as a difference rather than as a coincidence.
 */
function fixture(): { context: Context; sub: Subtyper } {
  const declarations = new Declarations();
  declarations.addDatatype(declare("Cell", 0));
  declarations.addDatatype(declare("List", 1));
  declarations.addDatatype(declare("Sink", -1));
  const context = new Context(declarations);
  return { context, sub: new Subtyper(context) };
}

Deno.test("everything is below unknown and above never", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(Bool, TUnknown)).toBe(true);
  expect(sub.isSubtype(TNever, Bool)).toBe(true);
  expect(sub.isSubtype(TUnknown, Bool)).toBe(false);
});

Deno.test("a bad type relates to anything, in both directions", () => {
  // One unresolved name must not become an error at every use of it.
  const { sub } = fixture();
  expect(sub.isSubtype(TBad, Bool)).toBe(true);
  expect(sub.isSubtype(Bool, TBad)).toBe(true);
});

Deno.test("a bad type flows into an EVar rather than short-circuiting", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  expect(sub.isSubtype(TBad, a.ref)).toBe(true);
  // Recorded, so the EVar solves to `<bad>` instead of looking unconstrained.
  expect(a.lower.map(typeToString)).toEqual(["<bad>"]);
});

Deno.test("an argument moves the way its own parameter says", () => {
  const { sub } = fixture();
  // Nominal either way, so the names must still agree; what changes is what
  // is asked of the arguments once they do.
  expect(sub.isSubtype(List(TNever), List(TUnknown))).toBe(true);
  expect(sub.isSubtype(List(TUnknown), List(TNever))).toBe(false);
  expect(sub.isSubtype(Sink(TUnknown), Sink(TNever))).toBe(true);
  expect(sub.isSubtype(Sink(TNever), Sink(TUnknown))).toBe(false);
  expect(sub.isSubtype(List(Bool), Sink(Bool))).toBe(false);
});

Deno.test("a cell is invariant without consulting anything", () => {
  const { sub } = fixture();
  // Two cells are the same type when their arguments are, and nothing else --
  // no name to agree on, no table to read, no round in which the answer could
  // still be moving.
  expect(sub.isSubtype(TRef(Bool), TRef(Bool))).toBe(true);
  expect(sub.isSubtype(TRef(TNever), TRef(TUnknown))).toBe(false);
  expect(sub.isSubtype(TRef(TUnknown), TRef(TNever))).toBe(false);
  // And it absorbs, so a covariant argument under one may not move either.
  expect(sub.isSubtype(TRef(List(TNever)), TRef(List(TUnknown)))).toBe(false);
  expect(sub.isSubtype(List(TRef(Bool)), List(TRef(Bool)))).toBe(true);
});

Deno.test("nothing sits between two cells of different types", () => {
  const { sub } = fixture();
  expect(typeToString(sub.join(TRef(Bool), TRef(Bool)))).toBe("Ref[Bool]");
  expect(typeToString(sub.join(TRef(Bool), TRef(Int)))).toBe("unknown");
  expect(typeToString(sub.meet(TRef(Bool), TRef(Int)))).toBe("never");
  expect(typeToString(sub.join(TRef(Bool), Cell(Bool)))).toBe("unknown");
});

Deno.test("a cell has no extreme, so lifting one into it warns", () => {
  const { sub } = fixture();
  expect(typeToString(up(sub, TNever, RefP(TMissing)))).toBe("Ref[never]");
  expect(saidBy(sub)).toEqual([
    "warning: no least Ref[?] to cast never to: a Ref's argument is " +
    "invariant, so it was taken to be never",
  ]);
  // Nor a widest, so a hole in one takes the cell with it.
  expect(typeToString(sub.widestMatching(RefP(TMissing)))).toBe("unknown");
});

Deno.test("an argument's position composes with the pair's own", () => {
  const { sub } = fixture();
  // A `List` under a `Sink` is read the other way round, and a `Sink` under a
  // `Sink` the right way round again -- which is composition, not a merge.
  expect(sub.isSubtype(Sink(List(TUnknown)), Sink(List(TNever)))).toBe(true);
  expect(sub.isSubtype(Sink(Sink(TNever)), Sink(Sink(TUnknown)))).toBe(true);
  // Equivalence absorbs whatever a parameter says, `0` composing to `0`: a
  // covariant argument is no freer here than an invariant one.
  expect(castToString(sub, exact(sub, List(TNever), ListP(TUnknown))))
    .toBe("<none>");
  expect(castToString(sub, exact(sub, List(Bool), ListP(Bool))))
    .toBe("List[Bool]");
});

Deno.test("a datatype is invariant in its arguments", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(Cell(Bool), Cell(Bool))).toBe(true);
  expect(sub.isSubtype(Cell(TNever), Cell(TUnknown))).toBe(false);
  expect(sub.isSubtype(Cell(Bool), Cell(Int))).toBe(false);
});

Deno.test("functions are contravariant in parameters, covariant in results", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(fn([TUnknown], TNever), fn([Bool], TUnknown)))
    .toBe(true);
  expect(sub.isSubtype(fn([TNever], Bool), fn([Bool], Bool))).toBe(false);
  expect(sub.isSubtype(fn([Bool], TUnknown), fn([Bool], Bool))).toBe(false);
});

Deno.test("arity is part of the type", () => {
  const { sub } = fixture();
  expect(sub.isSubtype(fn([Bool], Bool), fn([Bool, Bool], Bool))).toBe(false);
  expect(
    sub.isSubtype(
      TFun([mkTypeParamInfo("A", TUnknown)], [], Bool),
      fn([], Bool),
    ),
  )
    .toBe(false);
});

Deno.test("a type variable is promoted to its bound, but only on the left", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(Bool, "X");
  expect(sub.isSubtype(FVar(X, "X"), Bool)).toBe(true);
  expect(sub.isSubtype(Bool, FVar(X, "X"))).toBe(false);
});

Deno.test("promotion follows a chain of bounds", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(Bool, "X");
  const Y = context.pushTypeVar(FVar(X, "X"), "Y");
  expect(sub.isSubtype(FVar(Y, "Y"), Bool)).toBe(true);
  expect(typeToString(sub.expose(FVar(Y, "Y")))).toBe("Bool");
});

Deno.test("bounds are contravariant, which is full Fsub not kernel", () => {
  const { sub } = fixture();
  // `[A <: unknown]() -> Bool  <:  [A <: Bool]() -> Bool`: the right assumes
  // less of A, so the left, which assumes nothing, is the more general.
  const loose = TFun([mkTypeParamInfo("A", TUnknown)], [], Bool);
  const tight = TFun([mkTypeParamInfo("A", Bool)], [], Bool);
  expect(sub.isSubtype(loose, tight)).toBe(true);
  expect(sub.isSubtype(tight, loose)).toBe(false);
});

Deno.test("a quantifier's body is compared under fresh variables", () => {
  const { sub } = fixture();
  const identity = TFun([mkTypeParamInfo("A", TUnknown)], [BVar(0)], BVar(0));
  expect(sub.isSubtype(identity, identity)).toBe(true);
  const toUnknown = TFun(
    [mkTypeParamInfo("A", TUnknown)],
    [BVar(0)],
    TUnknown,
  );
  expect(sub.isSubtype(identity, toUnknown)).toBe(true);
  expect(sub.isSubtype(toUnknown, identity)).toBe(false);
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

  expect(sub.isSubtype(Bool, a.ref)).toBe(true);
  expect(sub.isSubtype(a.ref, TUnknown)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["Bool"]);
  // `?a <: unknown` is discharged by the top rule before any bound is recorded.
  expect(a.upper.length).toBe(0);
});

Deno.test("several lower bounds join into one solution", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, a.ref);
  sub.isSubtype(Int, a.ref);
  // Nothing relates Bool and Int, and there is no union, so the join is top.
  expect(solveAt(sub, a, 1)).toBe("unknown");
});

Deno.test("a lower bound is joined, not overwritten by the last constraint", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(TNever, a.ref);
  sub.isSubtype(Bool, a.ref);
  expect(solveAt(sub, a, 1)).toBe("Bool");
});

Deno.test("a variable in scope is recorded as itself, not as its bound", () => {
  // The rigid variable stands to the left, so ?a may name it. Promoting it
  // first would bound ?a by Bool and lose every solution naming X.
  const context = new Context();
  const X = context.pushTypeVar(Bool, "X");
  const sub = new Subtyper(context);
  const a = context.pushEVar("a");

  expect(sub.isSubtype(FVar(X, "X"), a.ref)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["X"]);
});

Deno.test("between two EVars the constraint lands on the righthand one", () => {
  // ?a is to the left of ?b, so only ?b may mention ?a.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const b = context.pushEVar("b");

  expect(sub.isSubtype(a.ref, b.ref)).toBe(true);
  expect(b.lower.map(typeToString)).toEqual(["?a"]);
  expect(a.upper.length).toBe(0);
});

Deno.test("avoidance widens an out-of-scope variable to its bound", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  // X is introduced *after* ?a, so ?a's solution may not mention it.
  const X = context.pushTypeVar(Bool, "X");

  expect(sub.isSubtype(FVar(X, "X"), a.ref, somewhere)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["Bool"]);
});

Deno.test("avoidance falls back to top when a variable has no useful bound", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(TUnknown, "X");
  expect(sub.isSubtype(FVar(X, "X"), a.ref, somewhere)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["unknown"]);
  // Silently: standing aside for a bound is what avoidance is for, and the
  // bound being top makes it coarser, not a different thing.
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("avoidance swaps direction at a contravariant position", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(Bool, "X");

  // Widening `(X) -> X` means *narrowing* the parameter: `(never) -> Bool`
  // accepts more arguments, so it is the supertype.
  expect(sub.isSubtype(fn([FVar(X, "X")], FVar(X, "X")), a.ref, somewhere))
    .toBe(true);
  expect(a.lower.map(typeToString)).toEqual([
    "never -> Bool",
  ]);
  // The parameter went to bottom, which keeps none of `X`; the result stood
  // aside for `Bool`. Each part collapsed where it stood, rather than taking
  // the arrow down with it.
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("an invariant position pins an EVar with one constraint", () => {
  // Both bounds from one recording, and one walk to get them: `#eqtype` is
  // what an invariant argument asks, not two subtypings.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");

  expect(sub.isSubtype(Cell(Bool), Cell(a.ref))).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["Bool"]);
  expect(a.upper.map(typeToString)).toEqual(["Bool"]);
});

Deno.test("an equation it cannot avoid decides the EVar as bad", () => {
  // An equation has no direction to give ground in, so where a part is out of
  // scope the variable is settled: widening it one way and narrowing it the
  // other would give a pair that cannot meet. Said here, where the cause is
  // still in hand, rather than left for the solver to notice as two extremes
  // that do not fit.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(Bool, "X");

  expect(sub.isSubtype(Cell(FVar(X, "X")), Cell(a.ref), somewhere)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["<bad>"]);
  expect(a.upper.map(typeToString)).toEqual(["<bad>"]);
  expect(saidBy(sub)).toEqual([
    "error: cannot infer the type argument a from X: it mentions something " +
    "this type argument cannot name, and an invariant position admits no " +
    "wider guess, so give it explicitly",
  ]);
});

Deno.test("avoidance cannot touch an invariant argument, so it collapses", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(Bool, "X");

  // `Cell[X]` has no in-scope supertype but top: widening the argument would
  // change the type, invariance being the whole point.
  expect(sub.isSubtype(Cell(FVar(X, "X")), a.ref, somewhere)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["unknown"]);
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("avoidance widens a covariant argument rather than collapsing", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const X = context.pushTypeVar(Bool, "X");

  // Upward, `X` stands aside for its bound, and a covariant argument carries
  // that -- so a `List` survives where the invariant `Cell` above had nothing
  // over it but top.
  expect(sub.isSubtype(List(FVar(X, "X")), a.ref, somewhere)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["List[Bool]"]);
  // Downward there is no lower bound to appeal to, so the direction that
  // survives is the one the contravariant argument flips *into* upward.
  expect(sub.isSubtype(a.ref, Sink(FVar(X, "X")), somewhere)).toBe(true);
  expect(a.upper.map(typeToString)).toEqual(["Sink[Bool]"]);
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("a constraint naming a sibling is approximated, and said so", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const b = context.pushEVar("b");

  // `Cell[?b] <: ?a` would need ?a's solution to mention ?b, which has no
  // solution yet. There is no bound to stand aside for, so ?b takes the
  // argument, and the invariant argument takes `Cell` with it.
  expect(sub.isSubtype(Cell(b.ref), a.ref, somewhere)).toBe(true);
  expect(a.lower.map(typeToString)).toEqual(["unknown"]);
  expect(saidBy(sub)).toEqual([
    "warning: the type argument b cannot appear in another type argument's " +
    "bound; give it explicitly if what was inferred is not what was meant",
  ]);
});

Deno.test("join and meet agree with the relation on ordered pairs", () => {
  const { sub } = fixture();
  expect(typeToString(sub.join(TNever, Bool))).toBe("Bool");
  expect(typeToString(sub.join(Bool, TUnknown))).toBe("unknown");
  expect(typeToString(sub.meet(TUnknown, Bool))).toBe("Bool");
  expect(typeToString(sub.meet(Bool, TNever))).toBe("never");
});

Deno.test("two datatypes meet argumentwise where an argument can move", () => {
  const { sub } = fixture();
  // Nominal, so the name has to agree either way; what a shared name buys is
  // an argument each side can give ground in.
  expect(typeToString(sub.join(List(Bool), List(TNever)))).toBe("List[Bool]");
  expect(typeToString(sub.meet(List(Bool), List(TUnknown)))).toBe("List[Bool]");
  // Contravariant, so a join *meets* the argument, as a parameter does.
  expect(typeToString(sub.join(Sink(Bool), Sink(TNever)))).toBe("Sink[never]");
  expect(typeToString(sub.meet(Sink(Bool), Sink(TUnknown))))
    .toBe("Sink[unknown]");
  // Invariant, so unless the two are already the same type there is no `Cell`
  // between them and the answer is the extreme.
  expect(typeToString(sub.join(Cell(Bool), Cell(TNever)))).toBe("unknown");
  expect(typeToString(sub.meet(Cell(Bool), Cell(Bool)))).toBe("Cell[Bool]");
  expect(typeToString(sub.join(List(Bool), Sink(Bool)))).toBe("unknown");
});

Deno.test("top and bottom meet an EVar without constraining it", () => {
  // Both are decided by shape, before the relation is consulted. Asking the
  // relation would answer with a *constraint* -- `unknown <: ?a` recorded as a
  // lower bound -- which is true, useless, and not something anyone asked for:
  // a lattice operation must not write on its operands.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const evar = a.ref;
  expect(typeToString(sub.join(TNever, evar))).toBe("?a");
  expect(typeToString(sub.join(evar, TUnknown))).toBe("unknown");
  expect(typeToString(sub.meet(TUnknown, evar))).toBe("?a");
  expect(typeToString(sub.meet(evar, TNever))).toBe("never");
  expect(a.lower).toEqual([]);
  expect(a.upper).toEqual([]);
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

Deno.test("the lattice does not promote an EVar to a bound it has not got", () => {
  // A variable has no shape of its own, so `join` stands it aside for its
  // bound -- but an EVar has constraints where a rigid variable has a bound,
  // and there is nothing there to stand aside for. So it joins with itself and
  // nothing else, which leaves top.
  //
  // Not a no-write guarantee: the lattice is never handed a type naming an
  // EVar in the first place. It joins a `match`'s arms and the bounds already
  // recorded, and those are complete and EVar-free. What used to be `probe`
  // enforced this from the inside; the invariant makes it unnecessary.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  const evar = a.ref;
  expect(typeToString(sub.join(evar, Bool))).toBe("unknown");
  expect(typeToString(sub.meet(evar, Bool))).toBe("never");
  expect(typeToString(sub.join(evar, evar))).toBe("?a");
  expect(a.lower).toEqual([]);
  expect(a.upper).toEqual([]);
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
  const sub = new Subtyper(context, [], 20);
  // The two differ only at the very bottom, so nothing short-circuits and the
  // budget runs out first. Reporting this as `false` would blame the program for
  // the checker's limit.
  expect(sub.isSubtype(nest(50, Bool), nest(50, Int))).toBeUndefined();
});

Deno.test("the budget is per query, so one deep ask does not poison the next", () => {
  const context = new Context();
  const sub = new Subtyper(context, [], 20);
  expect(sub.isSubtype(nest(50, Bool), nest(50, Int))).toBeUndefined();
  expect(sub.isSubtype(Bool, TUnknown)).toBe(true);
  expect(typeToString(sub.join(TNever, Bool))).toBe("Bool");
});

Deno.test("a nest of datatypes costs one walk, not one per direction", () => {
  // Invariance relates each argument both ways round. Asking that as two
  // subtypings would walk the whole argument twice at every level, so this
  // pair would cost `2^20` and exhaust any budget; one `#eqtype` walk spends
  // about two steps a level.
  const sub = new Subtyper(new Context(), [], 50);
  let deep: Type = Bool;
  for (let i = 0; i < 20; i++) deep = Cell(deep);
  expect(sub.isSubtype(deep, deep)).toBe(true);
});

Deno.test("a comparison within the budget still decides", () => {
  const context = new Context();
  const sub = new Subtyper(context, [], 2000);
  expect(sub.isSubtype(nest(50, Bool), nest(50, Bool))).toBe(true);
  expect(sub.isSubtype(nest(50, Bool), nest(50, Int))).toBe(false);
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
  sub.isSubtype(a.ref, Bool);

  expect(solveAt(sub, a, -1)).toBe("Bool");
});

Deno.test("a covariant occurrence takes the lower bound", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, a.ref);

  expect(solveAt(sub, a, 1)).toBe("Bool");
});

Deno.test("a covariant EVar with only an upper bound takes bottom", () => {
  // Principal, and the point of asking where it occurs at all: nothing demanded a
  // larger type, so the smallest the constraints admit is the answer.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(a.ref, Bool);

  expect(solveAt(sub, a, 1)).toBe("never");
});

Deno.test("an invariant occurrence bounded from one side takes it", () => {
  // Nothing was recorded from above, so `unknown` is the default and not a
  // demand -- there is nothing for `Bool` to be weighed against, and nothing
  // to say.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, a.ref);
  expect(solveAt(sub, a, 0)).toBe("Bool");
  expect(saidBy(sub)).toEqual([]);

  // Bounded from both sides by the same type, there is likewise nothing to
  // choose.
  const b = context.pushEVar("b");
  sub.isSubtype(Bool, b.ref);
  sub.isSubtype(b.ref, Bool);
  expect(solveAt(sub, b, 0)).toBe("Bool");
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("two invariant demands that differ take the lower, and say so", () => {
  // Both bounds were asked for and they are not equivalent, so neither is
  // above the other in the result. `Bool` satisfies every constraint, which is
  // why this is a warning rather than a refusal, and it is not the only type
  // that would, which is why it is said.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(fn([Bool], Bool), a.ref);
  sub.isSubtype(a.ref, fn([TNever], Bool));
  expect(solveAt(sub, a, 0)).toBe("Bool -> Bool");
  expect(saidBy(sub)).toEqual([
    "warning: the type argument a occurs invariantly, and the arguments " +
    "bound it between Bool -> Bool and never -> Bool, so it was taken to be " +
    "Bool -> Bool; give it explicitly if that is not what was meant",
  ]);
});

Deno.test("occurring nowhere is not the invariant case", () => {
  // Nothing downstream can tell which bound it took, so nothing is hidden by
  // taking one -- the demand.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, a.ref);

  expect(typeToString(sub.solveEVar(a, somewhere))).toBe("Bool");
});

Deno.test("bounds with nothing between them are a conflict, not a choice", () => {
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  sub.isSubtype(Bool, a.ref);
  sub.isSubtype(a.ref, Int);

  expect(solveAt(sub, a, 1)).toBe("<bad>");
  expect(saidBy(sub)).toEqual([
    "error: cannot infer the type argument a: it is bounded below by Bool " +
    "and above by Int, and no type is both",
  ]);
});

Deno.test("an EVar nothing constrained spans the lattice, silently", () => {
  // With nothing recorded the two bounds are the seeds of the folds, which
  // span the whole lattice, and the occurrence picks between them as it picks
  // between any pair. Nothing to say: every type satisfies no constraints, so
  // the extreme the occurrence asks for is the answer rather than a guess.
  const { context, sub } = fixture();
  const a = context.pushEVar("a");
  expect(solveAt(sub, a, 1)).toBe("never");
  const b = context.pushEVar("b");
  expect(solveAt(sub, b, -1)).toBe("unknown");
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("one batch's EVars may not depend on each other", () => {
  // Where an EVar occurs is read off the result type alone, so a sibling in a
  // pending bound would be a dependency the selection cannot see.
  const { context, sub } = fixture();
  const [a, b] = context.pushEVarBatch(["a", "b"]);
  if (a === undefined || b === undefined) throw new Error("batch of two");

  expect(sub.isSubtype(a.ref, b.ref, somewhere)).toBe(true);
  expect(b.lower.map(typeToString)).toEqual(["unknown"]);
  expect(a.upper.length).toBe(0);
  expect(saidBy(sub)).toEqual([
    "warning: the type argument a cannot appear in another type argument's " +
    "bound; give it explicitly if what was inferred is not what was meant",
  ]);
});

Deno.test("the bar for a refused dependency is the batch, not the context", () => {
  // An EVar pushed before the batch is ordinary: it is not a sibling, so the
  // selection that cannot see a sibling has nothing to miss. The checker no
  // longer builds this -- the batch is pushed after every argument is
  // checked, so two batches never overlap -- but the rule is the batch's
  // and is stated as such, and a bar of "any EVar anywhere" would be a
  // different rule that happened to agree.
  const { context, sub } = fixture();
  const outer = context.pushEVar("A");
  const [inner] = context.pushEVarBatch(["B"]);
  if (inner === undefined) throw new Error("batch of one");

  expect(sub.isSubtype(outer.ref, inner.ref)).toBe(true);
  expect(inner.lower.map(typeToString)).toEqual(["?A"]);
});

Deno.test("a missing part takes whatever the type has there", () => {
  const { sub } = fixture();
  expect(castToString(sub, up(sub, Bool, TMissing))).toBe("Bool");
  expect(castToString(sub, down(sub, Bool, TMissing))).toBe("Bool");
  expect(castToString(sub, exact(sub, Bool, TMissing))).toBe("Bool");
});

Deno.test("a written pattern matches only itself, and the direction decides", () => {
  const { sub } = fixture();
  // `Bool <: unknown`, so `unknown` is reachable going up but not down.
  expect(castToString(sub, up(sub, Bool, TUnknown))).toBe("unknown");
  expect(castToString(sub, down(sub, Bool, TUnknown))).toBe("<none>");
  expect(castToString(sub, down(sub, TUnknown, Bool))).toBe("Bool");
  expect(castToString(sub, up(sub, Bool, Int))).toBe("<none>");
});

Deno.test("a cast fills a function pointwise, flipping at the parameters", () => {
  const { sub } = fixture();
  const idish = fn([Bool], Bool);
  expect(castToString(sub, up(sub, idish, fnP([TMissing], TMissing))))
    .toBe("Bool -> Bool");
  // Nothing on the left, so the pattern alone decides: least going up means
  // the smallest result and -- parameters being contravariant -- the largest
  // parameter.
  expect(castToString(sub, up(sub, TNever, fnP([TMissing], TMissing))))
    .toBe("unknown -> never");
  expect(castToString(sub, down(sub, TUnknown, fnP([TMissing], TMissing))))
    .toBe("never -> unknown");
});

Deno.test("an invariant cast is not either of the other two", () => {
  // The case that makes the third direction necessary. A datatype argument is
  // invariant, so recursing into it may not move -- but it must still recurse,
  // since the argument pattern has a missing part to fill from the type.
  const { sub } = fixture();
  const listOfId = Cell(fn([Bool], Bool));
  expect(castToString(sub, down(sub, listOfId, CellP(fnP([TMissing], Bool)))))
    .toBe("Cell[Bool -> Bool]");
  expect(castToString(sub, up(sub, listOfId, CellP(fnP([Bool], TMissing)))))
    .toBe("Cell[Bool -> Bool]");
  // Written and disagreeing: invariance has nowhere to go.
  expect(castToString(sub, up(sub, listOfId, CellP(fnP([TMissing], Int)))))
    .toBe("<none>");
});

Deno.test("an invariant missing part costs a report, not the answer", () => {
  // Nothing is greatest among the types a `Cell` can be of, so an extreme
  // lifted into one has to choose the argument. The extreme it came from is
  // the choice, and it is a real answer -- every `Cell` is above `never` --
  // so what the invariance costs is a report about the choice, not the shape.
  const { sub } = fixture();
  expect(typeToString(up(sub, TNever, CellP(TMissing)))).toBe("Cell[never]");
  expect(saidBy(sub)).toEqual([
    "warning: no least Cell[?] to cast never to: Cell's argument A is " +
    "invariant, so it was taken to be never",
  ]);
  sub.diagnostics.length = 0;

  // Nested, the walk fills the rest of the shape rather than stopping at the
  // first argument it had to choose.
  expect(typeToString(up(sub, TNever, CellP(CellP(TMissing)))))
    .toBe("Cell[Cell[never]]");
  sub.diagnostics.length = 0;

  // With every argument written there is nothing to choose, so the same lift
  // is an answer with nothing to say about it.
  expect(castToString(sub, down(sub, TUnknown, CellP(Bool)))).toBe(
    "Cell[Bool]",
  );
  expect(castToString(sub, up(sub, TNever, CellP(Bool)))).toBe("Cell[Bool]");
});

Deno.test("a variable stands aside for its bound going up, and not down", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(fn([Bool], Bool), "X");
  const x = FVar(X, "X");
  expect(castToString(sub, up(sub, x, fnP([TMissing], TMissing))))
    .toBe("Bool -> Bool");
  // Nothing structural sits under a variable, so there is no answer below it
  // -- and inventing one from the pattern would build a type not under `X`.
  expect(castToString(sub, down(sub, x, fnP([TMissing], TMissing))))
    .toBe("<none>");
  expect(castToString(sub, exact(sub, x, fnP([TMissing], TMissing))))
    .toBe("<none>");
  // Itself, whichever way.
  expect(castToString(sub, down(sub, x, TMissing))).toBe("X");
});

Deno.test("an unbounded variable has no function above it either", () => {
  const { context, sub } = fixture();
  const X = context.pushTypeVar(TUnknown, "X");
  expect(castToString(sub, up(sub, FVar(X, "X"), fnP([TMissing], TMissing))))
    .toBe("<none>");
});

Deno.test("a bad type satisfies any demand", () => {
  // A report already stands, so nothing here is failed a second time.
  const { sub } = fixture();
  expect(castToString(sub, up(sub, TBad, CellP(TMissing)))).toBe("Cell[<bad>]");
  expect(castToString(sub, down(sub, TBad, fnP([Bool], TMissing))))
    .toBe("Bool -> <bad>");
});

Deno.test("a parameter list of the wrong length costs its own positions", () => {
  // Arity is a disagreement at the positions that are not shared, not a wall.
  // The answer has the pattern's arity -- the caller asked for that shape and
  // reads the parts off it -- and the parts that do line up keep their real
  // answers, which is the rule the rest of the walk follows.
  const { sub } = fixture();
  const tooFew = up(sub, fn([Bool], Bool), fnP([Bool, Bool], TMissing));
  expect(typeToString(tooFew)).toBe("(Bool, Bool) -> Bool");
  // Said once, by count: the position with no partner is not a mismatch of its
  // own, and reporting there would make one complaint out of every gap.
  expect(saidBy(sub)).toEqual(["error: expected 2 parameters, found 1"]);
  sub.diagnostics.length = 0;

  const tooMany = up(sub, fn([Bool, Bool], Bool), fnP([Bool], TMissing));
  expect(typeToString(tooMany)).toBe("Bool -> Bool");
  expect(saidBy(sub)).toEqual(["error: expected 1 parameter, found 2"]);

  // Quantifying a different number of variables is a wall, though: the two
  // parameter lists stand under different binders, so their positions do not
  // correspond and neither can be read in the other's scope.
  const quantified = TFun(
    [mkTypeParamInfo("A", TUnknown)],
    [TMissing],
    TMissing,
  );
  expect(castToString(sub, up(sub, fn([Bool], Bool), quantified)))
    .toBe("<none>");
});

Deno.test("a cast is shape-exact, so arity is part of the pattern", () => {
  const { sub } = fixture();
  expect(
    castToString(sub, up(sub, fn([Bool], Bool), fnP([TMissing], TMissing))),
  )
    .toBe("Bool -> Bool");
  expect(
    castToString(
      sub,
      up(sub, fn([Bool], Bool), fnP([TMissing, TMissing], TMissing)),
    ),
  ).toBe("<none>");
  expect(castToString(sub, up(sub, Cell(Bool), CellP(TMissing))))
    .toBe("Cell[Bool]");
  expect(castToString(sub, up(sub, Bool, CellP(TMissing)))).toBe("<none>");
});

Deno.test("a declined cast answers with the shape that was asked for", () => {
  // Total, the way the relation is -- and the shape survives, so a `match` on
  // the answer still has a datatype to check its arms against. `<bad>` stands
  // only where the pattern said nothing, and cannot go on to be blamed.
  const { sub } = fixture();
  const declined = up(sub, Bool, CellP(TMissing));
  expect(typeToString(declined)).toBe("Cell[<bad>]");

  // A pattern written in full leaves nothing to fill: this is exactly what
  // `check` does today by returning its expected type after reporting.
  const mismatch = up(sub, Bool, Int);
  expect(typeToString(mismatch)).toBe("Int");

  // Deeper failures rebuild at the top, rather than handing up the fragment
  // that failed.
  const inner = up(sub, fn([Bool], Bool), fnP([Bool], CellP(TMissing)));
  expect(typeToString(inner)).toBe("Bool -> Cell[<bad>]");

  // Three declines, each said where it happened rather than once at the top.
  expect(saidBy(sub).length).toBe(3);
});

Deno.test("a bad type answers with the demanded shape too", () => {
  const { sub } = fixture();
  expect(castToString(sub, up(sub, TBad, CellP(TMissing))))
    .toBe("Cell[<bad>]");
});

Deno.test("a cast given a position says which part it could not reach", () => {
  // The `<bad>` a failed cast plants stands for a report already made, so the
  // report is made here. The part is what is named: the whole arrow agrees
  // everywhere but the result, and saying so at the arrow would hide that.
  const { sub } = fixture();
  const cast = up(sub, fn([Bool], Bool), fnP([Bool], Int));
  expect(typeToString(cast)).toBe("Bool -> Int");
  expect(saidBy(sub)).toEqual(["error: expected Int, found Bool"]);
});

Deno.test("the widest type matching a pattern fills by variance", () => {
  const { sub } = fixture();
  const widest = (pattern: TypePattern) =>
    typeToString(sub.widestMatching(pattern));

  // Nothing written, so nothing constrains: top.
  expect(widest(TMissing)).toBe("unknown");
  // A complete pattern is already the answer.
  expect(widest(fnP([Bool], Int))).toBe("Bool -> Int");
  // Each hole takes the extreme that makes the whole largest, which flips
  // going into a parameter.
  expect(widest(fnP([Bool], TMissing))).toBe("Bool -> unknown");
  expect(widest(fnP([TMissing], Bool))).toBe("never -> Bool");
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("a hole in a directed argument has a widest filling too", () => {
  const { sub } = fixture();
  expect(typeToString(sub.widestMatching(ListP(TMissing))))
    .toBe("List[unknown]");
  expect(typeToString(sub.widestMatching(SinkP(TMissing)))).toBe("Sink[never]");
});

Deno.test("no widest Cell, so a hole in one takes the datatype with it", () => {
  // The argument is invariant, so there is nothing to widen it to and the
  // whole type gives way -- silently, since this answers a question about a
  // pattern and reads no program that could be wrong.
  const { sub } = fixture();
  expect(typeToString(sub.widestMatching(CellP(TMissing)))).toBe("unknown");
  expect(saidBy(sub)).toEqual([]);
});

Deno.test("an extreme lifts into an argument that has an extreme", () => {
  const { sub } = fixture();
  // The least `List` is a `List` of the least thing; the least `Sink` is a
  // `Sink` of the greatest, the argument flipping what the lift is looking
  // for. Neither invents anything, so neither says anything.
  expect(castToString(sub, up(sub, TNever, ListP(TMissing))))
    .toBe("List[never]");
  expect(castToString(sub, up(sub, TNever, SinkP(TMissing))))
    .toBe("Sink[unknown]");
  expect(castToString(sub, down(sub, TUnknown, ListP(TMissing))))
    .toBe("List[unknown]");
  expect(castToString(sub, down(sub, TUnknown, SinkP(TMissing))))
    .toBe("Sink[never]");
  // And nested, where the two flips cancel.
  expect(castToString(sub, up(sub, TNever, SinkP(SinkP(TMissing)))))
    .toBe("Sink[Sink[never]]");
});

Deno.test("a cast out of an extreme warns rather than failing", () => {
  // An extreme sits under -- or over -- every type there is, so a cast in its
  // own direction can always be made and a failure here would report the
  // checker's inability to name *one* answer as the program's mistake. Dual
  // to the lift out of `never`, and reported the same way.
  const { sub } = fixture();
  expect(typeToString(down(sub, TUnknown, CellP(TMissing))))
    .toBe("Cell[unknown]");
  expect(saidBy(sub)).toEqual([
    "warning: no greatest Cell[?] to cast unknown to: Cell's argument A is " +
    "invariant, so it was taken to be unknown",
  ]);
});

Deno.test("a cast out of fuel says so, rather than reporting a mismatch", () => {
  // A spent tank is the checker's limit, and calling it a mismatch would blame
  // the program -- so it keeps its own words. The only decline a cast can make
  // about the whole ask rather than about a part, which is why it is the only
  // one the entry point files.
  const { context } = fixture();
  const starved = new Subtyper(context, [], 0);
  expect(typeToString(starved.upcast(Bool, Bool, somewhere))).toBe("Bool");
  expect(saidBy(starved)).toEqual([
    "error: gave up casting Bool to Bool: too deeply nested",
  ]);
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
  expect(castToString(sub, up(sub, type, pattern)))
    .toBe("[X <: Bool -> Bool](Bool) -> Bool -> Bool");
});

Deno.test("a part that cannot be cast costs itself and not its siblings", () => {
  // Nothing fails outright, so the walk carries on and keeps what it found:
  // the parameter is the shape that was asked for, and the result beside it is
  // still the real answer rather than collateral.
  const { sub } = fixture();
  const partial = up(sub, fn([Bool], Bool), fnP([Int], TMissing));
  expect(typeToString(partial)).toBe("Int -> Bool");
  expect(saidBy(sub)).toEqual(["error: expected Int, found Bool"]);
});

Deno.test("a variable pattern is answered, not promoted past", () => {
  // Promotion supplies a shape, so it has no business in front of a leaf: the
  // relation answers those and promotes on its own, and it knows `X <: X`,
  // which promoting here would lose. Over-exposing loses every pair whose
  // answer is the variable itself.
  const { context, sub } = fixture();
  const X = FVar(context.pushTypeVar(Bool, "X"), "X");
  const Y = FVar(context.pushTypeVar(X, "Y"), "Y");
  expect(castToString(sub, up(sub, X, X))).toBe("X");
  expect(castToString(sub, up(sub, Y, X))).toBe("X");
  expect(castToString(sub, down(sub, X, X))).toBe("X");
  // An unbounded variable would promote straight to top, so this is the case
  // that fails loudest without the guard.
  const U = FVar(context.pushTypeVar(TUnknown, "U"), "U");
  expect(castToString(sub, up(sub, U, U))).toBe("U");
  // Still promoted when a shape really is wanted.
  const F = FVar(context.pushTypeVar(fn([Bool], Bool), "F"), "F");
  expect(castToString(sub, up(sub, F, fnP([TMissing], TMissing))))
    .toBe("Bool -> Bool");
});

Deno.test("a cast that succeeds is related to its input, always", () => {
  // The property the direction *means*, checked over a grid rather than by
  // choosing examples: an answer going up must sit above what it came from,
  // one going down below it, and an invariant one on both sides. This is what
  // catches a rule that moves `type` where it may not -- the shape of the
  // over-exposure bug, whatever form it takes next.
  //
  // Unsolved EVars are left out: a cast is never handed one, so a row for it
  // would pin behavior nothing can reach.
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
    Cell(Bool),
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
    CellP(TMissing),
    TFun([mkTypeParamInfo("A", TUnknown)], [TMissing], TMissing),
  ];

  let succeeded = 0;
  for (const type of types) {
    for (const pattern of patterns) {
      // Nothing demanded, and nothing already blamed, must never decline.
      expect(castToString(sub, up(sub, type, TMissing)))
        .toBe(typeToString(type));
      expect(castToString(sub, up(sub, TBad, pattern))).not.toBe("<none>");

      // `castToString` is what says whether a cast declined -- it drains what
      // was said -- so an answer kept for a second look is cast again.
      const higher = castToString(sub, up(sub, type, pattern));
      if (higher !== "<none>") {
        succeeded++;
        expect(sub.isSubtype(type, up(sub, type, pattern))).toBe(true);
      }
      const lower = castToString(sub, down(sub, type, pattern));
      if (lower !== "<none>") {
        succeeded++;
        expect(sub.isSubtype(down(sub, type, pattern), type)).toBe(true);
      }
      const same = castToString(sub, exact(sub, type, pattern));
      if (same !== "<none>") {
        succeeded++;
        expect(sub.isSubtype(type, exact(sub, type, pattern))).toBe(true);
        expect(sub.isSubtype(exact(sub, type, pattern), type)).toBe(true);
      }
      sub.diagnostics.length = 0;
    }
  }
  // A grid that stopped relating anything would pass vacuously.
  expect(succeeded).toBeGreaterThan(100);
});
