/**
 * Subtyping, and the lattice operations that go with it.
 *
 * Full Fsub, not kernel: comparing two quantifiers relates their bounds
 * contravariantly rather than demanding they match. That is the expressive
 * choice and also the undecidable one -- the bound comparison can grow without
 * bound -- so every query runs on a fuel counter and may answer `exhausted`.
 * That third answer is load-bearing: reporting "gave up" as "these types are
 * unrelated" would blame the program for the checker's limit.
 *
 * The relation is not a predicate. Meeting an unsolved EVar records a
 * constraint on it, so `isSubtype` mutates the context. Nothing is solved on
 * sight, though -- bounds accumulate, and the checker's `#solveEVars` calls
 * `solveEVar` here once the whole batch is in, which is why no operation ever
 * has to be undone.
 *
 * `join` and `meet` mutate for the same reason, `#relate` being how they test
 * the pair they are given. Joining two types that mention an open EVar records
 * constraints on it, which is worth knowing where a lattice operation reads as
 * a question -- taking the LUB of a `match`'s arms, say.
 */

import type { Context } from "./context.ts";
import {
  alphaEq,
  closeFrom,
  FVar,
  isClosed,
  type Level,
  mkTypeParamInfo,
  openMany,
  type Polarity,
  TBad,
  TFun,
  TNever,
  TUnknown,
  type Type,
  type TypeParamInfo,
} from "./types.ts";

/**
 * `no` means the program is wrong; `exhausted` and `interdependent` mean the
 * checker declined to decide, and each wants its own message. Only `yes`
 * succeeds, so callers testing a relation -- `join` does -- treat the rest
 * alike without ever mistaking a limit for a mismatch.
 */
export type Verdict = "yes" | "no" | "exhausted" | "interdependent";

/**
 * Steps allowed per top-level query. A real signature needs a handful; this is
 * bounded well below the call stack, since exhaustion has to be *reported* and
 * a stack overflow cannot be.
 */
const FUEL = 2000;

export class Subtyper {
  #fuel: number;

  /** `budget` is injectable so a test can reach exhaustion without a type
   * deep enough to trouble the stack on its way there. */
  constructor(readonly context: Context, readonly budget: number = FUEL) {
    this.#fuel = budget;
  }

  /**
   * Promote a type to its bound repeatedly, until it is not a variable. A
   * bound may only mention entries to its left, so the level strictly
   * decreases and this terminates without a counter.
   */
  expose(type: Type): Type {
    let current = this.#head(type);
    while (current.kind === "FVar") {
      current = this.#head(this.context.upperBoundAt(current.level));
    }
    return current;
  }

  /** Does `left <: right` hold? Resets the fuel, so this is a *top-level* ask. */
  isSubtype(left: Type, right: Type): Verdict {
    return this.#resetFuel(() => this.#relate(left, right));
  }

  /**
   * The fuel is per query, not per call, so everything reachable from one ask
   * shares a budget -- including the relation tests `join` runs. Public entry
   * points reset it; the `#`-prefixed workers never do, or a nested test would
   * hand the outer query a fresh tank and defeat the counter.
   */
  #resetFuel<T>(run: () => T): T {
    this.#fuel = this.budget;
    return run();
  }

  /**
   * Resolve just enough to dispatch: follow a solved EVar at the head and stop.
   * A full `apply` here would rewrite the entire type at every step --
   * quadratic, and deep enough to overflow the stack before the fuel counter
   * ever got a chance to report. Children are resolved by the recursive calls
   * that reach them.
   */
  #head(type: Type): Type {
    let current = type;
    while (current.kind === "EVar") {
      const solution = this.context.evarAt(current.level).solution;
      if (solution === undefined) return current;
      current = solution;
    }
    return current;
  }

  #relate(left: Type, right: Type): Verdict {
    if (this.#fuel-- <= 0) return "exhausted";

    const s = this.#head(left);
    const t = this.#head(right);

    // Vacuous either way, so nothing is learned and nothing is recorded.
    if (t.kind === "TUnknown" || s.kind === "TNever") return "yes";
    if (alphaEq(s, t)) return "yes";

    // An unsolved EVar takes a constraint instead of an answer. When both are,
    // the one standing further right records it: the other is to its left and
    // so is in scope, while the reverse would not be.
    //
    // This runs *before* the `TBad` rule on purpose. A bad type has to flow
    // into the bounds, so the EVar solves to `TBad` too. Short-circuiting here
    // would leave it unconstrained, and the checker would then report that it
    // could not infer a type argument -- blaming the program a second time for
    // an error already reported.
    if (s.kind === "EVar" && t.kind === "EVar") {
      return s.level >= t.level
        ? this.#constrain(s.level, "upper", t)
        : this.#constrain(t.level, "lower", s);
    }
    if (s.kind === "EVar") return this.#constrain(s.level, "upper", t);
    if (t.kind === "EVar") return this.#constrain(t.level, "lower", s);

    // A bad type stands for a report already made, so it relates to anything.
    // Letting it fail here would blame the program twice for one mistake.
    if (s.kind === "TBad" || t.kind === "TBad") return "yes";

    // Only the left is promoted. Promoting the right would relate `X <: Y`
    // whenever their bounds happened to meet, which is unsound.
    // An unbounded variable promotes to `unknown`, which the top rule above
    // has already turned down for this `t` -- so the recursion answers "no"
    // there, and nothing here has to.
    if (s.kind === "FVar") {
      return this.#relate(this.context.upperBoundAt(s.level), t);
    }

    if (s.kind === "TData" && t.kind === "TData") {
      // Invariant: a datatype's parameters have no declared variance, so
      // `List[never]` is not a `List[unknown]`.
      if (s.name !== t.name || s.args.length !== t.args.length) return "no";
      for (const [i, arg] of s.args.entries()) {
        const other = t.args[i] ?? TBad;
        // Invariance is *mutual* subtyping, not `alphaEq`. The difference only
        // shows against an EVar: `List[?a] <: List[Int]` must leave ?a with
        // both bounds, where an equality test would quietly constrain nothing
        // and then fail.
        const there = this.#relate(arg, other);
        if (there !== "yes") return there;
        const back = this.#relate(other, arg);
        if (back !== "yes") return back;
      }
      return "yes";
    }

    if (s.kind === "TFun" && t.kind === "TFun") return this.#relateFun(s, t);
    return "no";
  }

  #relateFun(
    s: Extract<Type, { kind: "TFun" }>,
    t: Extract<Type, { kind: "TFun" }>,
  ): Verdict {
    // Arity is part of the type, for parameters and for the quantifier alike.
    if (s.typeParams.length !== t.typeParams.length) return "no";
    if (s.params.length !== t.params.length) return "no";

    // Full Fsub: bounds are contravariant. Kernel Fsub would demand `alphaEq`
    // here and be decidable; this is the trade named at the top of the file.
    for (const [j, binder] of t.typeParams.entries()) {
      const mine = s.typeParams[j];
      if (mine === undefined) return "no";
      const verdict = this.#relate(binder.bound, mine.bound);
      if (verdict !== "yes") return verdict;
    }

    // Open both under one group of fresh variables, carrying the *right*
    // side's bounds -- those are the weaker assumption, so what holds under
    // them holds under the left's too.
    // Bounds are parallel -- already in the enclosing scope -- so they are
    // pushed as they stand, with no opening of their own.
    //
    // Nameless: the variable is reached through the `FVar` built here, and
    // nothing elaborates surface syntax mid-comparison, so a name would only
    // be one nothing could ask for. `hint` still prints.
    return this.context.inScope(() => {
      const opened = t.typeParams.map((binder) =>
        FVar(this.context.pushTypeVar(binder.bound), binder.hint)
      );
      for (const [j, param] of t.params.entries()) {
        const mine = s.params[j];
        if (mine === undefined) return "no";
        // Parameters are contravariant.
        const verdict = this.#relate(
          openMany(param, opened),
          openMany(mine, opened),
        );
        if (verdict !== "yes") return verdict;
      }
      return this.#relate(
        openMany(s.result, opened),
        openMany(t.result, opened),
      );
    });
  }

  /**
   * Record `type` as a bound of the EVar at `level`, avoiding first. Anything
   * the EVar cannot see has to go, and which direction is safe depends on the
   * side: a lower bound may only be widened, an upper bound only narrowed.
   */
  #constrain(level: Level, side: "lower" | "upper", type: Type): Verdict {
    // Fully resolved first: a solved EVar may stand for something perfectly in
    // scope, and judging it by its own level would reject that wrongly.
    const resolved = this.context.apply(type);
    const batch = this.context.evarAt(level).batch;

    // Interdependence is decided over the whole type, before any widening, and
    // against the *batch* rather than this variable's own level -- so a sibling
    // is refused in either direction. An unsolved EVar has no value yet, so
    // nothing can be said in terms of it; unlike a rigid variable it has no
    // bound to widen to, so quietly collapsing it to top would drop the
    // constraint on the floor. See `EVarEntry.batch`.
    if (this.#mentionsUnsolvedEVarFrom(resolved, batch)) {
      this.context.refuseConstraint(level);
      return "interdependent";
    }

    // Avoidance is about *scope*, so it keeps this EVar's own level as its bar:
    // a solution may mention anything to its left, siblings having just been
    // ruled out above.
    const avoided = side === "lower"
      ? this.#promote(resolved, level)
      : this.#demote(resolved, level);
    if (avoided === undefined) {
      this.context.refuseConstraint(level);
      return "interdependent";
    }
    this.context.addConstraint(level, side, avoided);
    return "yes";
  }

  /**
   * Does `type` mention an unsolved EVar at or beyond `from`? Everything here
   * has been through `apply`, so an EVar still standing is unsolved by that
   * alone.
   *
   * "From", not "later": the bar is a batch's first level, so a *sibling*
   * counts even standing to the left of the variable being constrained.
   */
  #mentionsUnsolvedEVarFrom(type: Type, from: number): boolean {
    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      case "BVar":
      case "FVar":
        return false;
      case "EVar":
        return type.level >= from;
      case "TFun":
        return type.typeParams.some((b) =>
          this.#mentionsUnsolvedEVarFrom(b.bound, from)
        ) ||
          type.params.some((p) => this.#mentionsUnsolvedEVarFrom(p, from)) ||
          this.#mentionsUnsolvedEVarFrom(type.result, from);
      case "TData":
        return type.args.some((arg) =>
          this.#mentionsUnsolvedEVarFrom(arg, from)
        );
    }
  }

  /**
   * The least supertype of `type` closed by `levels`, or `undefined` if none
   * can be built.
   *
   * This is the avoidance problem. A constraint picked up under a binder may
   * mention variables that binder introduced, and those cannot appear in a
   * solution that outlives it -- so each is replaced by something in scope,
   * upward here and downward in `demote`, swapping at every contravariant
   * position.
   */
  #promote(type: Type, levels: number): Type | undefined {
    return this.#avoid(type, levels, true);
  }

  /** The greatest subtype closed by `levels`. Dual to `#promote`. */
  #demote(type: Type, levels: number): Type | undefined {
    return this.#avoid(type, levels, false);
  }

  #avoid(type: Type, levels: number, up: boolean): Type | undefined {
    if (isClosed(type, levels)) return type;

    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      case "BVar":
        return type;
      case "FVar": {
        if (type.level < levels) return type;
        // Upward, a variable's declared bound is the nearest thing it is
        // known to sit under; downward there is no lower bound to appeal to,
        // so bottom is all that is left.
        if (!up) return TNever;
        return this.#avoid(this.context.upperBoundAt(type.level), levels, true);
      }
      case "EVar":
        // Unreachable from `#constrain`, which rejects a type mentioning an
        // unsolved EVar from the batch onward before any of this runs -- a
        // stricter bar, the batch beginning at or before `levels`. Kept because
        // the `TData` case below cannot ask: it collapses to top or bottom
        // without looking, so an EVar inside an invariant argument would be
        // dropped silently rather than reaching this branch at all. That is the
        // hole the pre-pass exists to cover, and this is what it would cost.
        //
        // An unsolved EVar out of scope is the interdependent case: its
        // solution is not known yet, so no bound can be given in terms of it,
        // and widening to top would silently throw the constraint away.
        return type.level < levels ? type : undefined;
      case "TData": {
        // Arguments are invariant, so neither direction may touch them. If one
        // mentions something out of scope, the whole type collapses.
        return type.args.every((arg) => isClosed(arg, levels))
          ? type
          : (up ? TUnknown : TNever);
      }
      case "TFun": {
        const typeParams = [];
        for (const binder of type.typeParams) {
          // A bound sits in a contravariant position, like a parameter.
          const avoided = this.#avoid(binder.bound, levels, !up);
          if (avoided === undefined) return undefined;
          typeParams.push(mkTypeParamInfo(binder.hint, avoided));
        }
        const params = [];
        for (const param of type.params) {
          const avoided = this.#avoid(param, levels, !up);
          if (avoided === undefined) return undefined;
          params.push(avoided);
        }
        const result = this.#avoid(type.result, levels, up);
        if (result === undefined) return undefined;
        return TFun(typeParams, params, result);
      }
    }
  }

  /**
   * Least upper bound. Falls back to `unknown` rather than inventing a union:
   * there is no union type, so an inexact answer has to be the sound one.
   */
  join(left: Type, right: Type): Type {
    return this.#resetFuel(() => this.#join(left, right));
  }

  #join(left: Type, right: Type): Type {
    const s = this.#head(left);
    const t = this.#head(right);
    if (s.kind === "TBad" || t.kind === "TBad") return TBad;
    if (this.#relate(s, t) === "yes") return t;
    if (this.#relate(t, s) === "yes") return s;

    // Two unrelated functions still meet at an arrow, pointwise.
    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, true) ?? TUnknown;
    }
    return TUnknown;
  }

  /** Greatest lower bound. Falls back to `never`, dual to `join`. */
  meet(left: Type, right: Type): Type {
    return this.#resetFuel(() => this.#meet(left, right));
  }

  #meet(left: Type, right: Type): Type {
    const s = this.#head(left);
    const t = this.#head(right);
    if (s.kind === "TBad" || t.kind === "TBad") return TBad;
    if (this.#relate(s, t) === "yes") return s;
    if (this.#relate(t, s) === "yes") return t;

    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, false) ?? TNever;
    }
    return TNever;
  }

  /** `#join` when `up`, `#meet` otherwise -- so one arrow case serves both. */
  #lattice(left: Type, right: Type, up: boolean): Type {
    return up ? this.#join(left, right) : this.#meet(left, right);
  }

  /**
   * Join or meet two arrows pointwise, or `undefined` where their shapes leave
   * nothing better than top or bottom to say.
   *
   * Every position flips but the result: parameters are contravariant, so a
   * join *meets* them, and so are binder bounds -- the joined quantifier must
   * be usable at every instantiation both sides admit, which is the meet of
   * their bounds, the direction `#relateFun` relates them in.
   *
   * Quantified arrows are joined under their binders rather than given up on.
   * Both sides are opened at one fresh group carrying the combined bounds --
   * the same trick as `#relateFun`, except that here a *type* comes back out,
   * so it is closed again over the group on the way. Only the arities have no
   * answer: an arrow of two parameters and one of three share no arrow at all.
   */
  #latticeFun(
    s: Extract<Type, { kind: "TFun" }>,
    t: Extract<Type, { kind: "TFun" }>,
    up: boolean,
  ): Type | undefined {
    if (s.typeParams.length !== t.typeParams.length) return undefined;
    if (s.params.length !== t.params.length) return undefined;

    return this.context.inScope((mark) => {
      // Bounds are parallel -- they read in the enclosing scope -- so they are
      // combined before anything is pushed, and need no closing after.
      const typeParams: TypeParamInfo[] = [];
      for (const [j, binder] of s.typeParams.entries()) {
        const other = t.typeParams[j];
        if (other === undefined) return undefined;
        typeParams.push(
          mkTypeParamInfo(
            binder.hint,
            this.#lattice(binder.bound, other.bound, !up),
          ),
        );
      }

      const opened = typeParams.map((binder) =>
        FVar(this.context.pushTypeVar(binder.bound), binder.hint)
      );

      const params: Type[] = [];
      for (const [j, param] of s.params.entries()) {
        const other = t.params[j];
        if (other === undefined) return undefined;
        params.push(
          closeFrom(
            this.#lattice(
              openMany(param, opened),
              openMany(other, opened),
              !up,
            ),
            mark,
          ),
        );
      }

      const result = closeFrom(
        this.#lattice(
          openMany(s.result, opened),
          openMany(t.result, opened),
          up,
        ),
        mark,
      );
      return TFun(typeParams, params, result);
    });
  }

  /**
   * The join of every lower bound, or `never` if there are none.
   *
   * `solve`-prefixed because this computes a candidate solution, where
   * `Context.upperBoundAt` reads a binder's declared bound. Same words
   * otherwise, and the two are not the same question.
   */
  solveLowerBoundOf(level: Level): Type {
    const entry = this.context.evarAt(level);
    return this.#resetFuel(() =>
      entry.lower.reduce((a, b) => this.#join(a, b), TNever)
    );
  }

  /** The meet of every upper bound, or `unknown` if there are none. Dual to
   * `solveLowerBoundOf`. */
  solveUpperBoundOf(level: Level): Type {
    const entry = this.context.evarAt(level);
    return this.#resetFuel(() =>
      entry.upper.reduce((a, b) => this.#meet(a, b), TUnknown)
    );
  }

  /**
   * Solve one EVar, given how it occurs in the type the application hands back.
   *
   * Both bounds are computed, never one: they are peers, and which is the
   * answer is what `polarity` decides. `never` and `unknown` are not fallbacks
   * but the honest defaults -- an EVar with no lower bound really is above
   * bottom, and one with no upper really is below top.
   *
   * Then, in order:
   *
   * 1. `lower <: upper`, or the constraints have no solution at all. This is
   *    the check that keeps a callee's declared bound honest, that bound being
   *    an upper constraint like any other.
   * 2. The selection. Covariant occurrences take the *lower* bound: it is the
   *    smallest type the constraints admit, so it is the most informative
   *    result, which is what makes the answer principal rather than merely
   *    sound. Contravariant ones take the upper bound, dually.
   *
   * Occurring both ways, or inside an invariant `TData` argument, the bounds
   * must *agree*: widening either way breaks the other, so unless they meet
   * there is no principal choice and the checker declines rather than picking.
   * Taking the lower bound would be sound -- step 1 has already placed it under
   * every upper bound -- and that is exactly the objection. Silently settling
   * on a type that merely happens to work leaves the author with a program that
   * checks for a reason nothing states, and no sign that a choice was made on
   * their behalf. The explicit type argument they would have written is both
   * the fix and the record of it.
   *
   * It is a real cost, and falls on staged calls in particular:
   *
   *     let apply = fn [A](x: A) -> fn (f: (A) -> A) -> f(x)
   *     apply[Bool](True)(fn (y) -> y)
   *
   * `?A` occurs invariantly in `((A) -> A) -> A` -- covariantly as the result,
   * contravariantly inside the parameter -- and `True` bounds it only from
   * below, so the first list cannot settle it and the annotation is required.
   *
   * A variable occurring nowhere in the result is not this case: nothing
   * downstream can tell which bound it took, so the lower one is taken for
   * being the *demand*, something that really flowed in.
   */
  solveEVar(level: Level, polarity: Polarity): EVarSolution {
    const entry = this.context.evarAt(level);
    if (entry.lower.length === 0 && entry.upper.length === 0) {
      return { kind: "unconstrained" };
    }

    const lower = this.solveLowerBoundOf(level);
    const upper = this.solveUpperBoundOf(level);

    const verdict = this.isSubtype(lower, upper);
    if (verdict !== "yes") return { kind: "conflict", lower, upper, verdict };

    if (polarity === "covariant") return { kind: "solved", type: lower };
    if (polarity === "contravariant") return { kind: "solved", type: upper };

    if (polarity === "invariant") {
      // One direction is the check above; this is the other. Together they make
      // the bounds equivalent, and then either may be taken.
      const back = this.isSubtype(upper, lower);
      if (back !== "yes") return { kind: "disagrees", lower, upper };
      return { kind: "solved", type: lower };
    }

    // Occurring nowhere: the demand first.
    return {
      kind: "solved",
      type: entry.lower.length > 0 ? lower : upper,
    };
  }
}

/**
 * What solving one EVar came to. Three of the four are the checker declining,
 * each for its own reason and so each wanting its own message -- which is why
 * this comes back as a value rather than being reported here: `Subtyper` has no
 * diagnostics, and the relation should not acquire any.
 */
export type EVarSolution =
  | { readonly kind: "solved"; readonly type: Type }
  /** Nothing was recorded, so every type would do and none is right. */
  | { readonly kind: "unconstrained" }
  /** No type is above the lower bound and below the upper one. */
  | {
    readonly kind: "conflict";
    readonly lower: Type;
    readonly upper: Type;
    readonly verdict: Verdict;
  }
  /**
   * The bounds are satisfiable but unequal, at a position that needs them
   * equal. Not a mistake in the program's types -- it is the checker declining
   * to choose where no choice is principal, and asking for the type argument.
   */
  | {
    readonly kind: "disagrees";
    readonly lower: Type;
    readonly upper: Type;
  };

/** Convenience for the common `=== "yes"` test. */
export function holds(verdict: Verdict): boolean {
  return verdict === "yes";
}
