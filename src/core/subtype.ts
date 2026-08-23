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
 * An EVar is not a node here. A variable is an `FVar` naming a level, and the
 * entry at that level says whether it is rigid -- a declared bound, never
 * solved -- or one still being inferred. Every rule that would read a bound
 * has to ask, which is what `#rigid` is for: promotion, exposure, and
 * avoidance are all things only a rigid variable admits.
 *
 * The relation is not a predicate. Meeting an unsolved EVar records a
 * constraint on it, so `isSubtype` mutates the context. Nothing is solved on
 * sight, though -- bounds accumulate, and `withEVars` solves the whole batch
 * once the last one is in, which is why no operation ever has to be undone.
 *
 * `join` and `meet` do not, and are the only operations here that read as
 * plain questions. They are structural: heads that cannot be ordered by
 * looking at them settle for top or bottom, and only a variable -- whose order
 * lives in its bound, not its head -- is worth asking the relation about.
 *
 * They record nothing because they are never handed a type naming an EVar. An
 * EVar entry stands only across `#applyCall`, and inside that window the only
 * types naming one are the two the checker relates on purpose: an argument
 * against its parameter, and the result against the expected type. Everything
 * else there is EVar-free by construction -- patterns hide the type parameters
 * behind missing parts, arguments come back complete, and a recorded bound has
 * been avoided already.
 */

import type { Context } from "./context.ts";
import {
  allPairs,
  alphaEq,
  BVar,
  closeFrom,
  flip,
  FVar,
  impossible,
  isClosed,
  type Level,
  mkTypeParamInfo,
  openMany,
  type Polarity,
  TBad,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
  type TypeParamInfo,
  type TypePattern,
} from "./types.ts";

/**
 * Which way a cast travels, and so which relation it has to satisfy.
 * `Polarity` without `none`: every position a cast reaches is one it answers
 * for. Named after polarities rather than "up"/"down" so the cast shares
 * `flip` with `openAt` -- the fourth traversal that has to agree with the
 * other three about what a position is.
 */
export type CastDirection = Exclude<Polarity, "none">;

/**
 * A cast's answer. Total, the way the relation is total: there is always a
 * type, and the verdict says whether it was found or stood in.
 *
 * `TBad` stands in and matches every pattern, so the postcondition -- what
 * comes back has the shape that was asked for -- holds whatever happened. The
 * verdict is separate because a cast declines for the same three reasons the
 * relation does.
 */
export type Cast = {
  readonly type: Type;
  readonly verdict: Verdict;
};

const castFound = (type: Type): Cast => ({ type, verdict: "yes" });

/**
 * A pattern read back as a type, `<bad>` standing wherever it said nothing,
 * and a verdict saying whether it had to stand anywhere. One walk, because the
 * shape is the same either way: building it and asking what had to be invented
 * are the same question.
 *
 * Keeping the shape is the point: `List[<bad>]` is still a datatype, so a
 * `match` on it can be checked for membership and exhaustiveness where a bare
 * `<bad>` could only be waved through.
 *
 * Nothing is *asserted* by the parts it invents -- `<bad>` relates to anything
 * and none of them can go on to be blamed -- which is what separates this from
 * choosing an arbitrary type. What it costs is the verdict, the caller's to
 * report.
 */
export function castComplete(pattern: TypePattern): Cast {
  switch (pattern.kind) {
    case "TMissing":
      return { type: TBad, verdict: "no" };
    case "TFun": {
      let verdict: Verdict = "yes";
      const typeParams: TypeParamInfo[] = [];
      for (const binder of pattern.typeParams) {
        const bound = castComplete(binder.bound);
        verdict = bothVerdicts(verdict, bound.verdict);
        typeParams.push(mkTypeParamInfo(binder.hint, bound.type));
      }
      const params: Type[] = [];
      for (const param of pattern.params) {
        const built = castComplete(param);
        verdict = bothVerdicts(verdict, built.verdict);
        params.push(built.type);
      }
      const result = castComplete(pattern.result);
      verdict = bothVerdicts(verdict, result.verdict);
      return { type: TFun(typeParams, params, result.type), verdict };
    }
    case "TData": {
      let verdict: Verdict = "yes";
      const args: Type[] = [];
      for (const arg of pattern.args) {
        const built = castComplete(arg);
        verdict = bothVerdicts(verdict, built.verdict);
        args.push(built.type);
      }
      return { type: TData(pattern.name, args), verdict };
    }
    default:
      return castFound(completeLeaf(pattern));
  }
}

/**
 * The extreme in a direction: the largest type going down, the smallest going
 * up. Invariant has none, which is why `#castHead` cannot lift a datatype the
 * way it lifts a function.
 */
const extremeFor = (dir: CastDirection): Type =>
  dir === "contravariant" ? TUnknown : TNever;

/**
 * A cast that declined, still answering with the shape that was asked for. The
 * verdict is the caller's, since a part may decline for a reason `castComplete`
 * never sees -- a spent fuel tank, or a relation that gave up.
 */
const castFailed = (pattern: TypePattern, verdict: Verdict): Cast => ({
  type: castComplete(pattern).type,
  verdict,
});

/**
 * Two verdicts about parts of one question. Every part has to hold, so the
 * least willing answer wins: a part that is definitely wrong settles it, and a
 * limit reached elsewhere is reported only when nothing was actually wrong.
 */
const VERDICT_ORDER: readonly Verdict[] = [
  "yes",
  "exhausted",
  "interdependent",
  "no",
];

function bothVerdicts(left: Verdict, right: Verdict): Verdict {
  return VERDICT_ORDER.indexOf(left) >= VERDICT_ORDER.indexOf(right)
    ? left
    : right;
}

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

/**
 * A leaf pattern read back as a type. Nothing in a leaf *could* be missing,
 * but the parameter does not narrow, so this is one honest switch rather than
 * a cast.
 */
function completeLeaf(
  pattern: Exclude<TypePattern, { kind: "TFun" | "TData" | "TMissing" }>,
): Type {
  switch (pattern.kind) {
    case "TUnknown":
      return TUnknown;
    case "TNever":
      return TNever;
    case "TBad":
      return TBad;
    case "BVar":
      return BVar(pattern.index);
    case "FVar":
      return FVar(pattern.level, pattern.hint);
  }
}

export class Subtyper {
  #fuel: number;

  /** `budget` is injectable so a test can reach exhaustion without a type
   * deep enough to trouble the stack on its way there. */
  constructor(readonly context: Context, readonly budget: number = FUEL) {
    this.#fuel = budget;
  }

  /**
   * Promote a type variable to its bound repeatedly until what is left is not
   * one. A bound may only mention entries to its left, so the level strictly
   * decreases and this terminates without a counter.
   *
   * Only for a type in a *left* position -- one being used, not one being asked
   * for. `X <: Bool` says every X is a Bool, so a value of type X may be used
   * as one; it says nothing in reverse, so a checking rule's expected type is
   * taken as written.
   *
   * Rigid variables only. An EVar has constraints, not a bound, and a shape it
   * has not been given yet is not one it can stand aside for.
   */
  expose(type: Type): Type {
    let current = type;
    while (this.#rigid(current)) {
      current = this.context.upperBoundAt(current.level);
    }
    return current;
  }

  /**
   * Is this variable one still being inferred? Every rule that reads a
   * variable's *bound* has to ask: `FVar` alone never licenses promotion,
   * since an EVar has no bound to promote to.
   */
  #isEVar(level: Level): boolean {
    return this.context.evarOrUndefined(level) !== undefined;
  }

  /** A variable that may stand aside for its declared bound. */
  #rigid(type: Type): type is Extract<Type, { kind: "FVar" }> {
    return type.kind === "FVar" && !this.#isEVar(type.level);
  }

  /** Does `left <: right` hold? Resets the fuel, so this is a *top-level* ask. */
  isSubtype(left: Type, right: Type): Verdict {
    return this.#query(() => this.#subtype(left, right));
  }

  /**
   * Begin a top-level query: a fresh tank. Fuel is per query, not per call, so
   * everything reachable from one ask shares a budget. The `#`-prefixed
   * workers never reset, or a nested test would defeat the counter.
   */
  #query<T>(run: () => T): T {
    this.#fuel = this.budget;
    return run();
  }

  #subtype(s: Type, t: Type): Verdict {
    if (this.#fuel-- <= 0) return "exhausted";

    // Top and bottom, whatever stands opposite: vacuous either way, so nothing
    // is learned and nothing is recorded -- in particular no constraint against
    // an EVar on the other side, which is why this comes first.
    if (t.kind === "TUnknown" || s.kind === "TNever") return "yes";

    // Reflexivity is not tested up front: every case below either walks both
    // types anyway or settles by comparing two levels. Each carries its own.

    // An unsolved EVar takes a constraint instead of an answer, and one side
    // records it: the same selection `#join` and `#meet` make, on the same
    // grounds. When both are EVars the one standing further right records,
    // since the other is to its left and so in scope, while the reverse would
    // not be. The same one on both sides is reflexivity -- constraining it by
    // itself would be a bound that says nothing and cannot be avoided out of.
    //
    // Before the `TBad` rule on purpose: a bad type has to flow into the
    // bounds so the EVar solves to `TBad` too. Short-circuiting would leave it
    // unconstrained and report a second time about an error already reported.
    //
    // No mode guards the recording, because reaching an EVar at all is
    // conditional on there being one: only the two constraint-collecting asks
    // in `#applyCall` are ever handed a type that names one.
    const tEVar = t.kind === "FVar" && this.#isEVar(t.level)
      ? t.level
      : undefined;
    if (s.kind === "FVar" && this.#isEVar(s.level)) {
      if (s.level === tEVar) return "yes";
      if (tEVar === undefined || s.level > tEVar) {
        return this.#constrain(s.level, "upper", t);
      }
    }
    if (tEVar !== undefined) return this.#constrain(tEVar, "lower", s);

    // A bad type stands for a report already made, so it relates to anything.
    // Letting it fail here would blame the program twice for one mistake.
    if (s.kind === "TBad" || t.kind === "TBad") return "yes";

    // Only the left is promoted. Promoting the right would relate `X <: Y`
    // whenever their bounds happened to meet, which is unsound.
    // An unbounded variable promotes to `unknown`, which the top rule above
    // has already turned down for this `t` -- so the recursion answers "no"
    // there, and nothing here has to.
    if (this.#rigid(s)) {
      // The same variable, before promoting: `X <: X` holds by reflexivity, and
      // going to the bound would lose it -- nothing relates `X`'s bound back to
      // `X`, so the recursion would answer "no" for a pair that plainly holds.
      if (t.kind === "FVar" && s.level === t.level) return "yes";
      return this.#subtype(this.context.upperBoundAt(s.level), t);
    }

    if (s.kind === "TData" && t.kind === "TData") {
      // Invariant: a datatype's parameters have no declared variance, so
      // `List[never]` is not a `List[unknown]`.
      if (s.name !== t.name || s.args.length !== t.args.length) return "no";
      for (const [i, arg] of s.args.entries()) {
        const verdict = this.#equiv(arg, t.args[i] ?? TBad);
        if (verdict !== "yes") return verdict;
      }
      return "yes";
    }

    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#subtypeFun(s, t);
    }
    return "no";
  }

  /**
   * Mutual subtyping: what an invariant position demands. A datatype argument
   * today, a reference cell later -- one answer, so the two cannot drift.
   *
   * `alphaEq` first, as a fast path and nothing more: it answers "yes" or says
   * nothing, so the relation still decides every pair it turns down. It earns
   * its walk because skipping it costs `2^depth` on a nest compared with
   * itself.
   *
   * It is not a decision procedure for this. `TBad` relates to everything, an
   * unsolved EVar records a bound instead of answering, and a `never`-bounded
   * variable is equivalent to `never` and to every other one of its kind -- so
   * two names the author wrote apart can be the same type, and only the
   * relation sees it.
   */
  #equiv(s: Type, t: Type): Verdict {
    if (alphaEq(s, t)) return "yes";
    const there = this.#subtype(s, t);
    if (there !== "yes") return there;
    return this.#subtype(t, s);
  }

  /**
   * Elementwise equivalence of two argument lists. The lattice wants a boolean
   * where `#subtype` wants a verdict: "exhausted" there means the two could not
   * be shown equal, which is what the caller does with "no" as well.
   */
  #equivArgs(s: readonly Type[], t: readonly Type[]): boolean {
    return allPairs(s, t, (a, b) => this.#equiv(a, b) === "yes");
  }

  #subtypeFun(
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
      const verdict = this.#subtype(binder.bound, mine.bound);
      if (verdict !== "yes") return verdict;
    }

    // Open both under one group of fresh variables carrying the *right* side's
    // bounds -- the weaker assumption, so what holds under them holds under
    // the left's too. Bounds are parallel, already in the enclosing scope, so
    // they are pushed as they stand.
    //
    // Nameless: nothing elaborates surface syntax mid-comparison, so the
    // variable is reached only through the `FVar` built here. `hint` prints.
    return this.context.inScope(() => {
      const opened = t.typeParams.map((binder) =>
        FVar(this.context.pushTypeVar(binder.bound), binder.hint)
      );
      for (const [j, param] of t.params.entries()) {
        const mine = s.params[j];
        if (mine === undefined) return "no";
        // Parameters are contravariant.
        const verdict = this.#subtype(
          openMany(param, opened),
          openMany(mine, opened),
        );
        if (verdict !== "yes") return verdict;
      }
      return this.#subtype(
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
    // No `apply` first: a batch is solved only after the last constraint is
    // in, so nothing reaching here can mention a *solved* EVar.
    const batch = this.context.evarAt(level).batch;

    // Interdependence is decided over the whole type, before any widening, and
    // against the *batch* rather than this variable's own level -- so a
    // sibling is refused in either direction. Unlike a rigid variable an EVar
    // has no bound to widen to, so collapsing it to top would drop the
    // constraint on the floor. See `EVarEntry.batch`.
    //
    // Both sides are marked: they are parties to one rejected dependency, and
    // a sibling left unmarked goes on to report that nothing constrained it.
    const siblings = this.#unsolvedEVarsFrom(type, batch);
    if (siblings.length > 0) {
      this.context.noteReported(level);
      for (const sibling of siblings) this.context.noteReported(sibling);
      return "interdependent";
    }

    // Avoidance is about *scope*, so it keeps this EVar's own level as its bar:
    // a solution may mention anything to its left, siblings having just been
    // ruled out above.
    const avoided = this.#avoid(type, level, side === "lower" ? "up" : "down");
    if (avoided === undefined) {
      this.context.noteReported(level);
      return "interdependent";
    }
    this.context.addConstraint(level, side, avoided);
    return "yes";
  }

  /**
   * Every unsolved EVar `type` mentions at or beyond `from`.
   *
   * "From", not "later": the bar is a batch's first level, so a *sibling*
   * counts even standing to the left of the variable being constrained.
   *
   * The levels and not a yes-or-no, because callers also have to mark what
   * they found -- one traversal answering both.
   */
  #unsolvedEVarsFrom(type: Type, from: number): Level[] {
    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      case "BVar":
        return [];
      case "FVar":
        return type.level >= from && this.#isEVar(type.level)
          ? [type.level]
          : [];
      case "TFun":
        return [
          ...type.typeParams.flatMap((b) =>
            this.#unsolvedEVarsFrom(b.bound, from)
          ),
          ...type.params.flatMap((p) => this.#unsolvedEVarsFrom(p, from)),
          ...this.#unsolvedEVarsFrom(type.result, from),
        ];
      case "TData":
        return type.args.flatMap((arg) => this.#unsolvedEVarsFrom(arg, from));
    }
  }

  /**
   * The least supertype of `type` closed by `levels` going `"up"`, the greatest
   * subtype going `"down"`, or `undefined` if none can be built.
   *
   * This is the avoidance problem. A constraint picked up under a binder may
   * mention variables that binder introduced, and those cannot appear in a
   * solution that outlives it -- so each is replaced by something in scope,
   * widening a lower bound and narrowing an upper one, swapping direction at
   * every contravariant position.
   */
  #avoid(type: Type, levels: number, dir: "up" | "down"): Type | undefined {
    if (isClosed(type, levels)) return type;

    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      case "BVar":
        return type;
      case "FVar": {
        if (type.level < levels) return type;
        // An EVar out of scope is the interdependent case: nothing can be
        // said in terms of a variable with no value yet, and widening to top
        // would throw the constraint away.
        //
        // Unreachable from `#constrain`, whose pre-pass rejects such a type at
        // a stricter bar. Kept because the `TData` case below collapses
        // without looking, so an EVar inside an invariant argument would be
        // dropped silently -- the hole the pre-pass exists to cover.
        if (this.#isEVar(type.level)) return undefined;
        // Upward, a variable's declared bound is the nearest thing it is
        // known to sit under; downward there is no lower bound to appeal to,
        // so bottom is all that is left.
        if (dir === "down") return TNever;
        return this.#avoid(this.context.upperBoundAt(type.level), levels, dir);
      }
      case "TData": {
        // Arguments are invariant, so neither direction may touch them. If one
        // mentions something out of scope, the whole type collapses.
        return type.args.every((arg) => isClosed(arg, levels))
          ? type
          : (dir === "up" ? TUnknown : TNever);
      }
      case "TFun": {
        const flipped = dir === "up" ? "down" : "up";
        const typeParams = [];
        for (const binder of type.typeParams) {
          // A bound sits in a contravariant position, like a parameter.
          const avoided = this.#avoid(binder.bound, levels, flipped);
          if (avoided === undefined) return undefined;
          typeParams.push(mkTypeParamInfo(binder.hint, avoided));
        }
        const params = [];
        for (const param of type.params) {
          const avoided = this.#avoid(param, levels, flipped);
          if (avoided === undefined) return undefined;
          params.push(avoided);
        }
        const result = this.#avoid(type.result, levels, dir);
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
    return this.#query(() => this.#join(left, right));
  }

  #join(s: Type, t: Type): Type {
    if (s.kind === "TBad" || t.kind === "TBad") return TBad;
    if (s.kind === "TUnknown" || t.kind === "TUnknown") return TUnknown;
    if (s.kind === "TNever") return t;
    if (t.kind === "TNever") return s;

    // A variable has no shape of its own, so it stands aside for its bound --
    // sound upward, and no relation has to be asked. Two of them promote the
    // one declared later, whose bound may name the earlier but never the
    // reverse, so the recursion walks down the context and stops.
    if (s.kind === "FVar" && t.kind === "FVar" && s.level === t.level) return s;
    if (this.#rigid(s) && (!this.#rigid(t) || s.level > t.level)) {
      return this.#join(this.context.upperBoundAt(s.level), t);
    }
    if (this.#rigid(t)) {
      return this.#join(s, this.context.upperBoundAt(t.level));
    }

    // Two unrelated functions still meet at an arrow, pointwise.
    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, true) ?? TUnknown;
    }

    // Datatypes are nominal and their arguments invariant, so there is no
    // structure left to walk: either the two are the same type or they have
    // nothing above them but top. `#equiv` and not `alphaEq`, since a
    // `never`-bounded variable is equivalent to types it is not spelled like.
    if (s.kind === "TData" && t.kind === "TData") {
      return s.name === t.name && this.#equivArgs(s.args, t.args)
        ? s
        : TUnknown;
    }

    // A `BVar` is only itself, though no binder is open here for one to
    // escape from.
    if (s.kind === "BVar" && t.kind === "BVar" && s.index === t.index) return s;
    return TUnknown;
  }

  /** Greatest lower bound. Falls back to `never`, dual to `join`. */
  meet(left: Type, right: Type): Type {
    return this.#query(() => this.#meet(left, right));
  }

  #meet(s: Type, t: Type): Type {
    if (s.kind === "TBad" || t.kind === "TBad") return TBad;
    if (s.kind === "TNever" || t.kind === "TNever") return TNever;
    if (s.kind === "TUnknown") return t;
    if (t.kind === "TUnknown") return s;

    // Downward a variable may not stand aside for its bound: nothing says the
    // bound sits under it, so meeting there would invent a subtype. All that
    // can be said is whether the variable is already below the other, which is
    // the relation's question.
    //
    // Asked once, of the same side `#join` promotes: only a variable sits
    // under a variable, and of two only the one declared later.
    if (s.kind === "FVar" && t.kind === "FVar" && s.level === t.level) return s;
    if (this.#rigid(s) && (!this.#rigid(t) || s.level > t.level)) {
      return this.#subtype(s, t) === "yes" ? s : TNever;
    }
    if (this.#rigid(t)) {
      return this.#subtype(t, s) === "yes" ? t : TNever;
    }

    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, false) ?? TNever;
    }

    // Dual to `#join`: invariance leaves equivalence as the only question to
    // ask about two datatypes, and nothing below.
    if (s.kind === "TData" && t.kind === "TData") {
      return s.name === t.name && this.#equivArgs(s.args, t.args) ? s : TNever;
    }

    if (s.kind === "BVar" && t.kind === "BVar" && s.index === t.index) return s;
    return TNever;
  }

  // ------------------------------------------------------------------- casts

  /**
   * The least supertype of `type` matching `pattern`. This is how a checking
   * rule learns what it asked for: the pattern says the shape, the type says
   * the content, and the cast is the nearest thing that is both.
   */
  upcast(type: Type, pattern: TypePattern): Cast {
    return this.#query(() => this.#cast(type, pattern, "covariant"));
  }

  /** The greatest subtype of `type` matching `pattern`. Dual to `upcast`. */
  downcast(type: Type, pattern: TypePattern): Cast {
    return this.#query(() => this.#cast(type, pattern, "contravariant"));
  }

  /**
   * The type equivalent to `type` and matching `pattern`. Neither of the other
   * two: an invariant position may not move at all, so this can only read
   * missing parts off `type` and check that everything written agrees.
   *
   * A third direction, not a composition of the other two. A datatype argument
   * is invariant, yet a cast must still recurse into it:
   * `downcast(List[(Bool) -> Bool], List[(?) -> Bool])` has an answer, found
   * by filling the missing part from the type without moving. Either of the
   * other two would be free to move where movement is unsound, and stopping at
   * alpha-equality would refuse every pattern holding a missing part.
   */
  exactcast(type: Type, pattern: TypePattern): Cast {
    return this.#query(() => this.#cast(type, pattern, "invariant"));
  }

  /**
   * Walks the *pattern*, since the pattern says which shape is wanted, and
   * asks `type` to keep up.
   *
   * Nothing here fails outright: a part that cannot be cast contributes the
   * shape asked for with `<bad>` in it and a verdict saying so, and the walk
   * carries on -- a mismatched parameter costs the parameter, not the result
   * beside it. The verdicts combine and the caller reports once.
   */
  #cast(type: Type, pattern: TypePattern, dir: CastDirection): Cast {
    if (this.#fuel-- <= 0) return castFailed(pattern, "exhausted");

    // Three kinds of demand, and the pattern is what says which. Nothing is
    // read off `type` until the demand is known, which is what keeps a rule
    // meant for one kind from running in front of another.
    switch (pattern.kind) {
      // Nothing demanded, so nothing moves -- whatever stands there is the
      // answer. Also the only case that reads content out of `type`, which is
      // how an invariant position, unable to move at all, still answers.
      case "TMissing":
        return castFound(type);

      // A shape is demanded. Only here may `type` be moved to produce one, and
      // both ways of moving it live in `#castHead`.
      case "TFun": {
        const head = this.#castHead(type, pattern, dir);
        const from = head.type;
        // Quantifying a different number of variables leaves nothing to walk
        // into: the two parameter lists stand under different binders, so
        // their positions do not correspond. A different number of
        // *parameters* is not like that -- those share binders, so the shared
        // positions are cast and the mismatch costs only the rest, which is
        // what `#castFun` does.
        if (
          from.kind !== "TFun" ||
          from.typeParams.length !== pattern.typeParams.length
        ) {
          return castFailed(pattern, "no");
        }
        const built = this.#castFun(from, pattern, dir);
        return {
          type: built.type,
          verdict: bothVerdicts(head.verdict, built.verdict),
        };
      }

      case "TData": {
        const head = this.#castHead(type, pattern, dir);
        const from = head.type;
        if (
          from.kind !== "TData" || from.name !== pattern.name ||
          from.args.length !== pattern.args.length
        ) {
          return castFailed(pattern, "no");
        }
        // Arguments are invariant however deep they sit, as `openAt` says by
        // passing `invariant` and never flipping out of it again.
        //
        // The head's verdict is folded in rather than returned on, and every
        // argument is walked even where the head already filled one:
        // re-entering a filled argument is a no-op, `<bad>` being absorbing,
        // where returning early would assume the head filled the list whole.
        let verdict: Verdict = head.verdict;
        const args: Type[] = [];
        for (const [i, want] of pattern.args.entries()) {
          const mine = from.args[i] ?? impossible("an argument per argument");
          const arg = this.#cast(mine, want, "invariant");
          verdict = bothVerdicts(verdict, arg.verdict);
          args.push(arg.type);
        }
        return { type: TData(from.name, args), verdict };
      }

      // A leaf is written in full, so it matches only itself and the whole
      // question is whether `type` reaches it in this direction. Left to the
      // relation whole, which promotes a variable on its own and knows
      // `X <: X` -- both lost by moving `type` first.
      //
      // `default` and not six arms, but not a hole either: `completeLeaf`
      // enumerates the same six with no default, so a new kind stops the
      // compiler there.
      default: {
        const leaf = completeLeaf(pattern);
        const verdict = dir === "covariant"
          ? this.#subtype(type, leaf)
          : dir === "contravariant"
          ? this.#subtype(leaf, type)
          : this.#equiv(type, leaf);
        return verdict === "yes"
          ? castFound(leaf)
          : castFailed(pattern, verdict);
      }
    }
  }

  /**
   * What `type` offers when a shape is wanted, as a type the shape cases can
   * take apart -- so every way of getting there ends in the same structural
   * walk, and there is no second traversal to keep in step with this one.
   *
   * A variable has no shape of its own. Going up it stands aside for its
   * bound, the same promotion `#join` makes; going down or standing still it
   * may not, so it is handed on unchanged and fails the shape test.
   *
   * Top going down and bottom going up have no head either, for the opposite
   * reason: the left says nothing and the pattern alone decides. There the
   * extreme is *lifted* into the shape asked for, one level deep, and the
   * ordinary walk lifts again wherever it meets the extreme further in.
   */
  #castHead(
    type: Type,
    pattern: Extract<TypePattern, { kind: "TFun" | "TData" }>,
    dir: CastDirection,
  ): Cast {
    // A report already stands, so a bad type has whatever shape is demanded:
    // a third way of standing aside, beside promotion and lifting an extreme.
    // Only needed where a shape is demanded, a demanded leaf going to the
    // relation, which knows `<bad>` on its own.
    //
    // The type but never the verdict: filling a missing part from something
    // already bad invents nothing, where lifting an extreme is a choice.
    if (type.kind === "TBad") return castFound(castComplete(pattern).type);
    if (this.#rigid(type) && dir === "covariant") {
      return this.#castHead(
        this.context.upperBoundAt(type.level),
        pattern,
        dir,
      );
    }
    if (
      !((type.kind === "TUnknown" && dir === "contravariant") ||
        (type.kind === "TNever" && dir === "covariant"))
    ) {
      return castFound(type);
    }

    // A function's parts have variance, so each has an extreme of its own and
    // the lift is total: the greatest arrow takes the smallest parameters and
    // the largest result, and the walk that follows lifts again wherever it
    // meets an extreme further in.
    if (pattern.kind === "TFun") {
      const inner = extremeFor(flip(dir));
      return castFound(TFun(
        pattern.typeParams.map((b) => mkTypeParamInfo(b.hint, inner)),
        pattern.params.map(() => inner),
        extremeFor(dir),
      ));
    }

    // A datatype's arguments do not: nothing is greatest among the types a
    // `List` can be of, so there is no greatest `List`. The shape is lifted
    // all the same, so a `match` still has a datatype to work with; what the
    // invariance costs is the verdict, which `castComplete` withholds exactly
    // when something had to be invented.
    return castComplete(pattern);
  }

  /**
   * Both binders are opened under one group of fresh variables, the way
   * `#latticeFun` and `#subtypeFun` open theirs. Comparing under their indices
   * instead would leave a parameter at a `BVar`, which has no bound to read.
   */
  #castFun(
    type: Extract<Type, { kind: "TFun" }>,
    pattern: Extract<TypePattern, { kind: "TFun" }>,
    dir: CastDirection,
  ): Cast {
    const inner = flip(dir);
    return this.context.inScope((mark) => {
      let verdict: Verdict = "yes";

      // Bounds are parallel -- they read in the enclosing scope -- so they are
      // cast before anything is pushed, and need no closing after. They are
      // contravariant, like the parameters.
      const typeParams: TypeParamInfo[] = [];
      for (const [j, want] of pattern.typeParams.entries()) {
        const mine = type.typeParams[j] ?? impossible("a binder per binder");
        const bound = this.#cast(mine.bound, want.bound, inner);
        verdict = bothVerdicts(verdict, bound.verdict);
        // The hint is print-only, and the pattern's is the one an author wrote
        // when there was an annotation to write it in.
        typeParams.push(mkTypeParamInfo(want.hint, bound.type));
      }

      const opened = typeParams.map((binder) =>
        FVar(this.context.pushTypeVar(binder.bound, binder.hint), binder.hint)
      );

      // The pattern's arity, which is what was asked for: a position only the
      // pattern has is filled from the pattern alone, one only `type` has is
      // dropped, and either costs the verdict.
      if (type.params.length !== pattern.params.length) verdict = "no";
      const params: Type[] = [];
      for (const [i, want] of pattern.params.entries()) {
        const mine = type.params[i];
        if (mine === undefined) {
          verdict = "no";
          // Already in the binder's own scope, having never been opened.
          params.push(castComplete(want).type);
          continue;
        }
        const param = this.#cast(
          openMany(mine, opened),
          openMany<number>(want, opened),
          inner,
        );
        verdict = bothVerdicts(verdict, param.verdict);
        params.push(closeFrom(param.type, mark));
      }

      const result = this.#cast(
        openMany(type.result, opened),
        openMany<number>(pattern.result, opened),
        dir,
      );
      verdict = bothVerdicts(verdict, result.verdict);
      return {
        type: TFun(typeParams, params, closeFrom(result.type, mark)),
        verdict,
      };
    });
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
   * be usable at every instantiation both sides admit.
   *
   * Quantified arrows are joined under their binders, both sides opened at one
   * fresh group carrying the combined bounds, as in `#subtypeFun` -- except
   * that a *type* comes back out, so it is closed again over the group. Only
   * the arities have no answer.
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
   * `Context.upperBoundAt` reads a binder's declared bound.
   */
  solveLowerBoundOf(level: Level): Type {
    const entry = this.context.evarAt(level);
    return this.#query(
      () => entry.lower.reduce((a, b) => this.#join(a, b), TNever),
    );
  }

  /** The meet of every upper bound, or `unknown` if there are none. Dual to
   * `solveLowerBoundOf`. */
  solveUpperBoundOf(level: Level): Type {
    const entry = this.context.evarAt(level);
    return this.#query(
      () => entry.upper.reduce((a, b) => this.#meet(a, b), TUnknown),
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
   * Taking the lower bound would be sound -- step 1 placed it under every
   * upper bound -- and that is the objection: it would settle silently on a
   * type that merely happens to work. The explicit type argument the author
   * would write is both the fix and the record of it.
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
   *
   * The relation tests here mutate, as everywhere -- but never this batch.
   * Every recorded bound is closed by `batch`, so no sibling can pick up a
   * bound while its neighbours are being decided, which is what would make the
   * order of this loop matter.
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

  /**
   * Push one EVar behind each of `hints`, run `body` over them, then solve the
   * batch and substitute the answers into the type it returned.
   *
   * The scope and the variables, and nothing else -- not even their declared
   * bounds, which are a constraint like any other and the caller's to record,
   * along with which types to open, where the polarity lies, and what to
   * relate. This owns only the part a caller could get wrong: a batch is
   * pushed together, decided together, and gone before anything outside can
   * see it.
   *
   * That is the invariant the rest of the file rests on. Nothing outside this
   * method holds a type naming an EVar, which is what lets the relation record
   * without asking whether it is allowed to, and the lattice join without
   * checking its operands.
   *
   * Batches never nest. A nested application is checked before `body` runs --
   * an argument's pattern hides the type parameters rather than naming them --
   * so a constraint mentioning an EVar can only mean a sibling.
   *
   * Reporting is the caller's: a failure names a type argument but no position,
   * and `Subtyper` has no diagnostics.
   */
  withEVars(
    hints: readonly string[],
    body: (evars: readonly EVarRef[]) => Type,
  ): { result: Type; failures: readonly TypeArgFailure[] } {
    return this.context.inScope(() => {
      const levels = this.context.pushEVarBatch(hints);
      // `?A`, not `A`. An EVar is an ordinary `FVar`, so the `?` a diagnostic
      // shows is put on here, at the one place that knows which it is.
      const evars = hints.map((hint, j) =>
        FVar(levels[j] ?? impossible("a level per hint"), `?${hint}`)
      );

      const result = body(evars);

      const failures: TypeArgFailure[] = [];
      for (const level of levels) {
        const entry = this.context.evarAt(level);
        // A refused constraint was reported where it was refused, so whatever
        // bounds got through describe a variable already given up on: solving
        // from them could only tell the same mistake a second time.
        if (entry.reported) {
          this.context.setSolution(level, TBad);
          continue;
        }
        const solved = this.solveEVar(level, entry.polarity);
        if (solved.kind === "solved") {
          this.context.setSolution(level, solved.type);
          continue;
        }
        // Every failure solves to `TBad`. Checking against a bad type always
        // succeeds, so one type argument nobody could infer does not go on to
        // fail again wherever the result is used.
        failures.push({ hint: entry.hint, reason: solved });
        this.context.setSolution(level, TBad);
      }

      return { result: this.context.apply(result), failures };
    });
  }
}

/**
 * An EVar as a type: an `FVar` whose level the context holds an EVar at. Not
 * just `Type`, because a caller needs the `level` to say anything about it.
 */
export type EVarRef = Extract<Type, { kind: "FVar" }>;

/**
 * A type argument the batch could not settle, and why. Carries the hint so a
 * message can name it; the position belongs to the caller.
 */
export type TypeArgFailure = {
  readonly hint: string;
  readonly reason: Exclude<EVarSolution, { kind: "solved" }>;
};

/**
 * What solving one EVar came to. Three of the four are the checker declining,
 * each wanting its own message -- which is why this comes back as a value:
 * `Subtyper` has no diagnostics and should not acquire any.
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
