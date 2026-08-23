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
 * `join` and `meet` do not, and are the only operations here that can be read
 * as plain questions. They are structural: heads that cannot be ordered by
 * looking at them settle for top or bottom, and only a variable -- whose order
 * lives in its bound, not its head -- is worth asking the relation about. That
 * ask runs in `probe` mode, where an unsolved EVar answers instead of
 * recording; taking the LUB of a `match`'s arms would otherwise pick up a
 * constraint from whichever side happened to be tested first.
 */

import type { Context } from "./context.ts";
import {
  allPairs,
  alphaEq,
  BVar,
  closeFrom,
  EVar,
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
 * for. Naming them after polarities rather than "up"/"down" is what lets the
 * cast share `flip` with `openAt`, which is the fourth traversal that has to
 * agree with the other three about what a position is.
 */
export type CastDirection = Exclude<Polarity, "none">;

/**
 * A cast's answer. Total, the way the relation is total: there is always a
 * type, and the verdict says whether it was found or stood in.
 *
 * `TBad` stands in, and matches every pattern -- so a caller's postcondition,
 * that what comes back has the shape that was asked for, holds whatever
 * happened. The verdict is separate because a cast declines for the same three
 * reasons the relation does, and reporting a spent fuel tank as a mismatch
 * would blame the program for the checker's limit.
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
 * The shape is what makes this worth having. `check` already returns its
 * expected type after reporting a mismatch -- the position demanded that
 * shape, and whatever reads the answer was written against it -- so handing
 * back a bare `<bad>` would throw away what the caller itself supplied. A
 * `match` is where the difference shows: `List[<bad>]` is still a datatype, so
 * its arms can be checked for membership and exhaustiveness, where `<bad>` can
 * only be waved through.
 *
 * Nothing is *asserted* by the parts it invents: `<bad>` is the one type that
 * relates to anything, and none of them can go on to be blamed. That is what
 * separates this from choosing an arbitrary type, which would report a second
 * time wherever the choice turned out wrong. What it costs instead is the
 * verdict, which is the caller's to report.
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
 * Two verdicts about parts of one question, as `bothPolarities` combines two
 * occurrences. Every part has to hold, so the least willing answer wins: a
 * part that is definitely wrong settles it whatever the others said, and a
 * limit reached elsewhere is only reported when nothing was actually wrong.
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
 * What the relation does when it reaches an unsolved EVar.
 *
 * `collect` is the relation proper: the EVar takes a bound instead of an
 * answer, which is how an argument list says what a type parameter must be.
 * `probe` asks without writing, and answers `no` for "not known to hold" --
 * there is no bound to consult on a variable nothing has decided yet.
 *
 * Only the lattice probes. It is asked as a question, and an answer that
 * silently constrained one of its operands would depend on which side it tried
 * first. `no` there costs precision and never soundness: the caller widens to
 * top or narrows to bottom, where the relation proper would have accepted a
 * wrong program.
 */
export type EVarMode = "collect" | "probe";

/**
 * Steps allowed per top-level query. A real signature needs a handful; this is
 * bounded well below the call stack, since exhaustion has to be *reported* and
 * a stack overflow cannot be.
 */
const FUEL = 2000;

/**
 * A leaf pattern read back as a type. Rebuilt case by case rather than cast:
 * a leaf has no parts, so nothing in it *could* be missing, but the parameter
 * does not narrow -- and one honest switch is cheaper than the walk a checked
 * cast would need to earn.
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
    case "EVar":
      return EVar(pattern.level, pattern.hint);
  }
}

export class Subtyper {
  #fuel: number;

  /** What the relation does with an unsolved EVar; see `EVarMode`. Set by the
   * public entry points, which are the only places that know why they ask. */
  #mode: EVarMode = "collect";

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
   * as one; it says nothing in reverse, so a checking rule's expected type must
   * be taken as written, and there is nothing here for it to call.
   *
   * No substitution on the way. Nothing this class is handed mentions a solved
   * EVar -- see `#constrain` -- so following one would be a step that never
   * happens, and `#assertUnsolved` says so rather than quietly taking it.
   */
  expose(type: Type): Type {
    let current = type;
    this.#assertUnsolved(current);
    while (current.kind === "FVar") {
      current = this.context.upperBoundAt(current.level);
      this.#assertUnsolved(current);
    }
    return current;
  }

  /**
   * A solved EVar standing where the relation can see it is a checker bug: the
   * one place they are solved applies and truncates immediately afterwards, so
   * what escapes is the solution and never the variable.
   *
   * The head alone, which is where dispatch happens. Anything deeper is reached
   * by a recursive call that asks again, or by `#unsolvedEVarsFrom`, which asks
   * about a whole type at once.
   */
  #assertUnsolved(type: Type): void {
    if (type.kind !== "EVar") return;
    const entry = this.context.evarAt(type.level);
    if (entry.solution !== undefined) {
      throw new Error(
        `?${entry.hint} is solved, but reached the relation unsubstituted`,
      );
    }
  }

  /** Does `left <: right` hold? Resets the fuel, so this is a *top-level* ask. */
  isSubtype(left: Type, right: Type): Verdict {
    return this.#query("collect", () => this.#subtype(left, right));
  }

  /**
   * Begin a top-level query: a fresh tank, and a mode for the whole of it.
   *
   * The fuel is per query, not per call, so everything reachable from one ask
   * shares a budget -- including the relation tests the lattice runs. The
   * `#`-prefixed workers never reset, or a nested test would hand the outer
   * query a fresh tank and defeat the counter. The mode is restored rather
   * than set, so a query nested inside another leaves it as it found it.
   */
  #query<T>(mode: EVarMode, run: () => T): T {
    const outer = this.#mode;
    this.#fuel = this.budget;
    this.#mode = mode;
    try {
      return run();
    } finally {
      this.#mode = outer;
    }
  }

  #subtype(s: Type, t: Type): Verdict {
    if (this.#fuel-- <= 0) return "exhausted";
    // Dispatch reads these two heads, so this is where the invariant is asked
    // about: what stands here has to be a variable still open, not the shadow
    // of one already decided.
    this.#assertUnsolved(s);
    this.#assertUnsolved(t);

    // Top and bottom, whatever stands opposite: vacuous either way, so nothing
    // is learned and nothing is recorded -- in particular no constraint against
    // an EVar on the other side, which is why this comes first.
    if (t.kind === "TUnknown" || s.kind === "TNever") return "yes";

    // Reflexivity is not tested up front. A structural equality test walks both
    // types, and every case below either has to walk them anyway or can settle
    // the question by comparing two levels -- so a test at the top would be one
    // traversal spent to save the ones that were already cheap. Each case
    // carries its own instead.

    // An unsolved EVar takes a constraint instead of an answer, and one side
    // records it: the same selection `#join` and `#meet` make, on the same
    // grounds. When both are EVars the one standing further right records,
    // since the other is to its left and so in scope, while the reverse would
    // not be. The same one on both sides is reflexivity -- constraining it by
    // itself would be a bound that says nothing and cannot be avoided out of.
    //
    // This runs *before* the `TBad` rule on purpose. A bad type has to flow
    // into the bounds, so the EVar solves to `TBad` too. Short-circuiting here
    // would leave it unconstrained, and the checker would then report that it
    // could not infer a type argument -- blaming the program a second time for
    // an error already reported.
    if (s.kind === "EVar" && t.kind === "EVar" && s.level === t.level) {
      return "yes";
    }
    // Only `collect` records. A probe drops through: nothing may be written,
    // and a variable nothing has decided yet holds no bound to read, so it
    // takes its answer from the rules below, which decline it.
    if (this.#mode === "collect") {
      if (s.kind === "EVar" && (t.kind !== "EVar" || s.level > t.level)) {
        return this.#constrain(s.level, "upper", t);
      }
      if (t.kind === "EVar") return this.#constrain(t.level, "lower", s);
    }

    // A bad type stands for a report already made, so it relates to anything.
    // Letting it fail here would blame the program twice for one mistake.
    if (s.kind === "TBad" || t.kind === "TBad") return "yes";

    // Only the left is promoted. Promoting the right would relate `X <: Y`
    // whenever their bounds happened to meet, which is unsound.
    // An unbounded variable promotes to `unknown`, which the top rule above
    // has already turned down for this `t` -- so the recursion answers "no"
    // there, and nothing here has to.
    if (s.kind === "FVar") {
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
   * itself -- each level would relate its pair twice.
   *
   * It is not a decision procedure for this, and the difference is wider than
   * holes. `TBad` relates to everything because a report already stands, and an
   * unsolved EVar records a bound instead of answering -- so `Ref[?a] <:
   * Ref[Int]` has to reach `#subtype` twice to leave ?a bounded on both sides.
   * But bottom makes it wider still: a variable bounded by `never` promotes to
   * it, and `never` is under everything, so such a variable is equivalent to
   * `never` and to every other one of its kind. Two names the author wrote
   * apart can be the same type, and only the relation sees it.
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
    // No `apply` first. Nothing reaching here can mention a *solved* EVar, and
    // `#unsolvedEVarsFrom` says so rather than trusting it: a bound is closed
    // by its batch, so it cannot name a sibling at all; an enclosing batch is
    // solved strictly after this one finishes; and a nested application applies
    // and truncates before it returns anything. Substituting first would have
    // been a no-op that hid all three.
    const batch = this.context.evarAt(level).batch;

    // Interdependence is decided over the whole type, before any widening, and
    // against the *batch* rather than this variable's own level -- so a sibling
    // is refused in either direction. An unsolved EVar has no value yet, so
    // nothing can be said in terms of it; unlike a rigid variable it has no
    // bound to widen to, so quietly collapsing it to top would drop the
    // constraint on the floor. See `EVarEntry.batch`.
    // Both sides are marked, not just the one being constrained. The two are
    // parties to one rejected dependency, and a sibling left unmarked goes on
    // to report that nothing constrained it -- the same mistake, told twice,
    // the second time about a variable that was never the problem.
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
   * "Unsolved" is checked, not filtered for: a constrained type may not mention
   * a solved EVar at all, and the traversal that would have had to skip one
   * says so instead. See `#constrain` for why that holds.
   *
   * "From", not "later": the bar is a batch's first level, so a *sibling*
   * counts even standing to the left of the variable being constrained.
   *
   * The levels and not a yes-or-no, because the callers that ask also have to
   * mark what they found -- one traversal answering both.
   */
  #unsolvedEVarsFrom(type: Type, from: number): Level[] {
    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      case "BVar":
      case "FVar":
        return [];
      case "EVar": {
        const entry = this.context.evarAt(type.level);
        if (entry.solution !== undefined) {
          throw new Error(
            `?${entry.hint} is solved, but stands in a type being ` +
              `constrained: it should have been substituted away`,
          );
        }
        return type.level >= from ? [type.level] : [];
      }
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
        // Upward, a variable's declared bound is the nearest thing it is
        // known to sit under; downward there is no lower bound to appeal to,
        // so bottom is all that is left.
        if (dir === "down") return TNever;
        return this.#avoid(this.context.upperBoundAt(type.level), levels, dir);
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
    return this.#query("probe", () => this.#join(left, right));
  }

  #join(s: Type, t: Type): Type {
    if (s.kind === "TBad" || t.kind === "TBad") return TBad;
    if (s.kind === "TUnknown" || t.kind === "TUnknown") return TUnknown;
    if (s.kind === "TNever") return t;
    if (t.kind === "TNever") return s;

    // A variable has no shape of its own, so it stands aside for its bound and
    // the join goes on there -- sound upward, since the bound is a supertype,
    // and no relation has to be asked. Two of them promote the one declared
    // later: its bound may name the earlier one, never the reverse, so the
    // recursion walks down the context and stops. One against itself joins
    // there, which also keeps an unbounded variable off the walk to `unknown`.
    if (s.kind === "FVar" && t.kind === "FVar" && s.level === t.level) return s;
    if (s.kind === "FVar" && (t.kind !== "FVar" || s.level > t.level)) {
      return this.#join(this.context.upperBoundAt(s.level), t);
    }
    if (t.kind === "FVar") {
      return this.#join(s, this.context.upperBoundAt(t.level));
    }

    // Two unrelated functions still meet at an arrow, pointwise.
    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, true) ?? TUnknown;
    }

    // Datatypes are nominal and their arguments invariant, so there is no
    // structure left to walk: either the two are the same type or they have
    // nothing above them but top. Invariance asks `#equiv` and not `alphaEq`,
    // since a `never`-bounded variable is equivalent to types it is not
    // spelled like -- and the probe keeps that question from recording.
    if (s.kind === "TData" && t.kind === "TData") {
      return s.name === t.name && this.#equivArgs(s.args, t.args)
        ? s
        : TUnknown;
    }

    // An unsolved EVar joins with itself and nothing else: it stands for a type
    // not yet chosen, and no bound of it may be read here -- this is where
    // `probe` declines. A `BVar` is likewise only itself, though no binder is
    // open at this point for one to escape from.
    if (s.kind === "EVar" && t.kind === "EVar" && s.level === t.level) return s;
    if (s.kind === "BVar" && t.kind === "BVar" && s.index === t.index) return s;
    return TUnknown;
  }

  /** Greatest lower bound. Falls back to `never`, dual to `join`. */
  meet(left: Type, right: Type): Type {
    return this.#query("probe", () => this.#meet(left, right));
  }

  #meet(s: Type, t: Type): Type {
    if (s.kind === "TBad" || t.kind === "TBad") return TBad;
    if (s.kind === "TNever" || t.kind === "TNever") return TNever;
    if (s.kind === "TUnknown") return t;
    if (t.kind === "TUnknown") return s;

    // Downward a variable may not stand aside for its bound: nothing says the
    // bound sits under it, so meeting there would invent a subtype. All that
    // can be said is whether the variable is already below the other, which is
    // a question for the relation -- asked in `probe`, so the other operand
    // picks up no constraint from having been tested.
    //
    // Asked once, and of the same side `#join` promotes. Only a variable can
    // sit under a variable, since nothing else reaches one from below; and of
    // two, only the one declared later, whose bound may name the earlier. So
    // the other direction is the question whose answer is already known, and
    // one against itself is an answer without asking.
    if (s.kind === "FVar" && t.kind === "FVar" && s.level === t.level) return s;
    if (s.kind === "FVar" && (t.kind !== "FVar" || s.level > t.level)) {
      return this.#subtype(s, t) === "yes" ? s : TNever;
    }
    if (t.kind === "FVar") {
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

    if (s.kind === "EVar" && t.kind === "EVar" && s.level === t.level) return s;
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
    return this.#query("collect", () => this.#cast(type, pattern, "covariant"));
  }

  /** The greatest subtype of `type` matching `pattern`. Dual to `upcast`. */
  downcast(type: Type, pattern: TypePattern): Cast {
    return this.#query(
      "collect",
      () => this.#cast(type, pattern, "contravariant"),
    );
  }

  /**
   * The type equivalent to `type` and matching `pattern`. Neither of the other
   * two: an invariant position may not move at all, so this can only read
   * missing parts off `type` and check that everything written agrees.
   *
   * A third direction, and not a composition of the other two. A datatype
   * argument is invariant, so a cast has to recurse into it *somehow* --
   * `downcast(List[(Bool) -> Bool], List[(?) -> Bool])` has an answer, and it
   * is found by filling the argument's missing part from the type without
   * moving. Neither `upcast` nor `downcast` may be used there, since either
   * would be free to move at a position where movement is unsound; and
   * stopping at alpha-equality would call the pattern unmatched whenever it
   * held a missing part, which is the case that matters.
   */
  exactcast(type: Type, pattern: TypePattern): Cast {
    return this.#query("collect", () => this.#cast(type, pattern, "invariant"));
  }

  /**
   * Walks the *pattern*, since the pattern says which shape is wanted, and
   * asks `type` to keep up.
   *
   * Nothing here fails outright. A part that cannot be cast contributes the
   * shape that was asked for with `<bad>` in it and a verdict saying so, and
   * the walk carries on -- so a mismatched parameter costs the parameter and
   * not the result beside it. The verdicts combine, and the caller reports
   * once, since a type carries no position to report a part at.
   */
  #cast(type: Type, pattern: TypePattern, dir: CastDirection): Cast {
    if (this.#fuel-- <= 0) return castFailed(pattern, "exhausted");
    // Same invariant the relation asks about, and for the same reason: what
    // stands here has to be a variable still open, not the shadow of one
    // already decided.
    this.#assertUnsolved(type);

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
        // Quantifying a different number of variables is a different shape,
        // and there is nothing to walk into: the two parameter lists stand
        // under different binders, so their positions do not correspond and
        // one cannot even be read in the other's scope.
        //
        // A different number of *parameters* is not like that. Those live
        // under the same binders, so the positions that are shared correspond
        // and can be cast; the mismatch costs the ones that are not, the same
        // way every other disagreement in this walk costs its own part.
        // `#castFun` answers with the pattern's arity and says `no`.
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
        // Arguments are invariant however deep they sit, which is what
        // `openAt` says by passing `invariant` here and never flipping out of
        // it again.
        //
        // The head's verdict is folded in rather than returned on, and the
        // walk runs over every argument even when the head already filled
        // one. Re-entering a filled argument costs nothing and changes
        // nothing -- `<bad>` is absorbing, so the rule at the top of `#cast`
        // hands back the same `<bad>` it was given. Returning early instead
        // would be assuming the head had filled the argument list *whole*,
        // which is true only while every argument is invariant.
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

      // A leaf is demanded, written in full, so it matches only itself: the
      // answer is the leaf and the whole question is whether `type` reaches it
      // in this direction. That is the relation's question, and it is left
      // whole -- the relation promotes a variable on its own, and knows
      // `X <: X`, which moving `type` first would lose.
      //
      // `default` rather than six arms, and it is not a hole: `completeLeaf`
      // enumerates the same six with no default of its own, so a new kind of
      // type stops the compiler there.
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
   * bound, sound because the bound is a supertype, the same promotion `#join`
   * makes; going down or standing still it may not, and nothing else reaches a
   * variable from below, so it is handed on unchanged and fails the shape test
   * it cannot meet.
   *
   * Top going down and bottom going up have no head either, but for the
   * opposite reason: everything is below top and above bottom, so the left
   * says nothing at all and the pattern alone decides. There the extreme is
   * *lifted* into the shape the pattern asks for, one level deep, and the
   * ordinary walk fills the rest -- lifting again wherever it meets the
   * extreme further in.
   */
  #castHead(
    type: Type,
    pattern: Extract<TypePattern, { kind: "TFun" | "TData" }>,
    dir: CastDirection,
  ): Cast {
    // A report already stands, so a bad type has whatever shape is demanded --
    // a third way of standing aside, beside promotion and lifting an extreme,
    // and it belongs here with them rather than in front of the walk. It is
    // needed only where a shape is demanded, which is exactly where this is
    // reached: a demanded leaf goes to the relation, which knows `<bad>` on
    // its own and carries it to whatever the leaf constrains, so one mistake
    // does not become two.
    //
    // Only the type is taken, never the verdict: filling a missing part from
    // something already bad invents nothing. That is the whole difference from
    // lifting an extreme, where the same filling is a choice and does cost the
    // verdict.
    if (type.kind === "TBad") return castFound(castComplete(pattern).type);
    if (type.kind === "FVar" && dir === "covariant") {
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
    // all the same -- `MutList[Sing[?]]` still comes back as
    // `MutList[Sing[<bad>]]`, and a `match` on that has a datatype to work
    // with. What the invariance costs is the verdict, which `castComplete`
    // withholds exactly when something had to be invented. The gap `#avoid`
    // names when it says an invariant argument cannot be touched at all.
    return castComplete(pattern);
  }

  /**
   * Both binders are opened under one group of fresh variables, the way
   * `#latticeFun` and `#subtypeFun` open theirs. Comparing the two under their
   * indices instead would leave a parameter standing at a `BVar`, which has no
   * bound to read -- so a pattern asking a quantified parameter for a shape
   * could never be answered, however tightly the binder bounded it.
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

      // The pattern's arity, which is what was asked for: a position the
      // pattern wants and `type` does not have is filled from the pattern
      // alone, one `type` has and the pattern does not is dropped, and either
      // costs the verdict.
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
   * be usable at every instantiation both sides admit, which is the meet of
   * their bounds, the direction `#subtypeFun` relates them in.
   *
   * Quantified arrows are joined under their binders rather than given up on.
   * Both sides are opened at one fresh group carrying the combined bounds --
   * the same trick as `#subtypeFun`, except that here a *type* comes back out,
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
    return this.#query(
      "probe",
      () => entry.lower.reduce((a, b) => this.#join(a, b), TNever),
    );
  }

  /** The meet of every upper bound, or `unknown` if there are none. Dual to
   * `solveLowerBoundOf`. */
  solveUpperBoundOf(level: Level): Type {
    const entry = this.context.evarAt(level);
    return this.#query(
      "probe",
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
   *
   * The relation tests here mutate, as everywhere -- but never this batch.
   * Every recorded bound is closed by `batch`, so the only EVars either bound
   * can mention belong to an *enclosing* argument list, and a constraint
   * reaching one of those is a real requirement travelling outward: the outer
   * variable genuinely has to admit what this one was solved to. What cannot
   * happen is a sibling picking up a bound while its neighbours are being
   * decided, which is the case that would make the order of this loop matter.
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
