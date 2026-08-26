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
 * has to ask the entry, and takes what it finds there: promotion, exposure and
 * avoidance want a bound, and only a rigid variable has one, where recording a
 * constraint wants the EVar entry itself.
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

import {
  type Diagnostic,
  type Position,
  reportError,
  reportWarning,
} from "../diagnostics/diagnostic.ts";
import type { ConstraintSide, Context, EVarEntry } from "./context.ts";
import {
  allPairs,
  closeFrom,
  completeLeafPattern,
  completePattern,
  flip,
  FVar,
  type FVarRef,
  impossible,
  isClosed,
  mkTypeParamInfo,
  openMany,
  TBad,
  TData,
  TFun,
  TNever,
  TUnknown,
  type Type,
  type TypeParamInfo,
  type TypePattern,
  typeToString,
  type Variance,
} from "./types.ts";

/**
 * What a top-level ask came to: it holds, it does not, or -- `undefined` --
 * the checker declined to decide and wants its own message.
 *
 * The relation's answer, and only the relation's: asking whether one type is
 * under another is a question with an answer, where a cast is a *rewriting*,
 * and every way one can decline is a fact about a part it reports on the spot.
 *
 * The third case cannot be folded into `true` the way `TBad` folds a reported
 * mistake into the relation. That works because the marker rides in the type,
 * where everything downstream can still see it; a relation has no such
 * carrier, and `solveEVar` is the caller that proves it -- it answers `TBad`
 * on exhaustion, which it can only do because the verdict reached it.
 *
 * Only the boundary is three-valued. Inside, a relation answers `boolean` and
 * exhaustion unwinds as an exception, so no interior test can mistake a spent
 * tank for a mismatch.
 */
export type Verdict = boolean | undefined;

/**
 * Thrown when the fuel runs out, caught by `Subtyper.#query`.
 *
 * An exception and not an answer: exhaustion is a property of the whole query,
 * not of the pair being compared, so there is nothing a caller could
 * *locally* do with it. Returned, it had to be threaded through every
 * combination, and `#join` and `#meet` both read it as "unrelated" and settled
 * for an extreme -- a definite answer manufactured from a limit.
 */
class FuelExhausted extends Error {
  constructor() {
    super("subtyping fuel exhausted");
  }
}

/**
 * Steps allowed per top-level query. A real signature needs a handful; this is
 * bounded well below the call stack, since exhaustion has to be *reported* and
 * a stack overflow cannot be.
 */
const FUEL = 2000;

export class Subtyper {
  #fuel: number;

  /**
   * Where to say whatever gets said, installed by `#query` and by `withEVars`
   * -- a batch's own position, narrowed to one argument's or one cast's for
   * the length of that ask. Ambient because the sites that record sit under
   * recursions no position could be threaded through: `#constrain` under the
   * relation, `#castFailed` under the cast.
   *
   * Undefined is a real state and not a missing one: an ask that passes no
   * position is a *query* about two types, with no program behind it to blame.
   * The cast family reads it that way and stays silent; the recording sites
   * under the relation cannot be reached without one, and say so.
   */
  #at: Position | undefined;

  /**
   * `diagnostics` is the checker's own array, shared rather than copied, the
   * way the elaborator shares it: what is recorded here is said here.
   *
   * Not the answers -- a `Verdict` goes back as a value, since only the caller
   * knows whether `no` is a failure or information. These are the *mutations*:
   * a bound widened, a constraint refused, an EVar settled. Those happened
   * whatever the ask was for, and whether each is sound is known here and
   * nowhere else, so the severity is decided here too.
   *
   * `budget` is injectable so a test can reach exhaustion without a type deep
   * enough to trouble the stack on its way there.
   */
  constructor(
    readonly context: Context,
    readonly diagnostics: Diagnostic[] = [],
    readonly budget: number = FUEL,
  ) {
    this.#fuel = budget;
  }

  // --------------------------------------------------------------- variables

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
   * Rigid variables only, and an EVar reaching here is a checker bug rather
   * than a case: exposing is asked when a rule needs a *shape* -- an arrow to
   * take apart, a datatype to match on -- and an EVar is not one. It has
   * constraints, not a bound, so there is nothing to stand aside for.
   */
  expose(type: Type): Type {
    let current = type;
    while (current.kind === "FVar") {
      current = (this.context.typeVarAt(current) ??
        impossible("exposing a type that still names an EVar")).bound;
    }
    return current;
  }

  /**
   * The bound `type` may stand aside for, or `undefined` if it may not: it is
   * no variable, or it names an EVar, which has constraints rather than a
   * bound and no shape yet to stand aside with.
   *
   * The bound and not a yes-or-no, because every rule that asks wants it.
   * Unbounded stores `TUnknown`, so a rigid variable always has one, and
   * `undefined` says only that promotion does not apply.
   */
  #declaredBoundOf(type: Type): Type | undefined {
    if (type.kind !== "FVar") return undefined;
    return this.context.typeVarAt(type)?.bound;
  }

  // ----------------------------------------------------------- error reporting

  /**
   * Begin a top-level query: a fresh tank, a place to say things, and the only
   * point exhaustion is caught. Fuel is per query, not per call, so everything
   * reachable from one ask shares a budget; the `#`-prefixed workers never
   * reset, or a nested test would defeat the counter.
   *
   * The position is installed here and not by each entry point because it is
   * the same fact as the fuel: what one top-level ask covers. `at` left out
   * keeps the one already standing, so a query nested inside another -- a cast
   * that goes to the relation for a leaf -- still says where it is.
   *
   * `onExhausted` is asked for rather than assumed: what not knowing looks
   * like is the one thing `#query` cannot derive from the ask -- a verdict, an
   * extreme, a report and the demanded shape.
   */
  #query<T>(
    at: Position | undefined,
    run: () => T,
    onExhausted: () => T,
  ): T {
    const outerFuel = this.#fuel;
    const outerAt = this.#at;
    this.#fuel = this.budget;
    if (at !== undefined) this.#at = at;
    try {
      return run();
    } catch (error) {
      if (error instanceof FuelExhausted) return onExhausted();
      throw error;
    } finally {
      this.#fuel = outerFuel;
      this.#at = outerAt;
    }
  }

  /** Spend one step, or unwind. */
  #spend(): void {
    if (this.#fuel-- <= 0) throw new FuelExhausted();
  }

  /**
   * File a diagnostic about something recorded. An error where proceeding
   * would settle the program's meaning arbitrarily, a warning where the loss
   * runs one way and any later failure can still be explained by it.
   */
  #file(
    severity: "error" | "warning",
    message: string,
    where: Position | undefined = this.#at,
  ): void {
    const at = where ??
      impossible("nothing records outside an ask that said where it was");
    this.diagnostics.push(
      severity === "error"
        ? reportError(message, at)
        : reportWarning(message, at),
    );
  }

  // ------------------------------------------------------------ the relation

  /**
   * Does `left <: right` hold? A *top-level* ask: fresh fuel, and `at` says
   * where anything recorded on the way came from.
   *
   * `at` is optional because not every ask has a narrower place to point at
   * than the one already installed -- a declared bound and an expected type
   * are the whole application's, where an argument is its own. An ask that
   * records nothing needs none at all, which is every ask with no EVar under
   * it.
   */
  isSubtype(left: Type, right: Type, at?: Position): Verdict {
    return this.#query(
      at,
      () => this.#subtype(left, right),
      () => undefined,
    );
  }

  #subtype(s: Type, t: Type): boolean {
    this.#spend();

    // Top and bottom, whatever stands opposite: vacuous either way, so nothing
    // is learned and nothing is recorded -- in particular no constraint against
    // an EVar on the other side, which is why this comes first.
    if (t.kind === "TUnknown" || s.kind === "TNever") return true;

    // Reflexivity is not tested up front: every case below either walks both
    // types anyway or settles by comparing two levels. Each carries its own.

    // An unsolved EVar takes a constraint instead of an answer, and the side
    // it is on says which bound. The right is tried first, so of two EVars the
    // one standing further right records: the other is to its left and so in
    // scope, where the reverse would name a variable the recorder cannot see.
    // A rigid variable promotes only after that -- an EVar is better off with
    // the variable it was handed than with that variable's bound, which would
    // lose every solution naming a type parameter.
    //
    // Before the `TBad` rule on purpose: a bad type has to flow into the
    // bounds so the EVar solves to `TBad` too. Short-circuiting would leave it
    // unconstrained and report a second time about an error already reported.
    //
    // No mode guards the recording: only the two constraint-collecting asks in
    // `#applyCall` are ever handed a type that names an EVar.
    if (t.kind === "FVar") {
      if (s.kind === "FVar" && s.level === t.level) return true;
      const tEntry = this.context.evarAt(t);
      if (tEntry !== undefined) return this.#constrain(tEntry, "lower", s);
    }
    if (s.kind === "FVar") {
      const sEntry = this.context.entryAt(s);
      if (sEntry.kind === "TypeVar") return this.#subtype(sEntry.bound, t);
      if (sEntry.kind === "EVar") return this.#constrain(sEntry, "upper", t);
    }

    // A bad type stands for a report already made, so it relates to anything.
    // Letting it fail here would blame the program twice for one mistake.
    if (s.kind === "TBad" || t.kind === "TBad") return true;

    if (s.kind === "TData" && t.kind === "TData") {
      // Invariant: a datatype's parameters have no declared variance, so
      // `List[never]` is not a `List[unknown]`.
      return s.name === t.name && this.#eqtypeArgs(s.args, t.args);
    }

    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#relateFun(s, t, 1);
    }
    return false;
  }

  /**
   * Mutual subtyping: what an invariant position demands. A datatype argument
   * today, a reference cell later -- one answer, so the two cannot drift.
   *
   * A walk of its own and not two calls to `#subtype`: each way round would
   * walk the whole type, and since a datatype argument comes back here, a nest
   * compared with itself would cost `2^depth`. It also lets an EVar take both
   * bounds from one constraint, where two passes would record them apart.
   *
   * It is not a decision procedure for this. `TBad` relates to everything, an
   * unsolved EVar records a bound instead of answering, and a `never`-bounded
   * variable is equivalent to `never` and to every other one of its kind -- so
   * two names the author wrote apart can be the same type, and only the
   * relation sees it.
   */
  #eqtype(s: Type, t: Type): boolean {
    this.#spend();

    // The variables come first, as in `#subtype` and for the same reason: an
    // EVar takes a constraint rather than an answer, and would otherwise be
    // read as a shape it has not got. `both` at one go, an invariant position
    // pinning the variable rather than bounding it.
    if (t.kind === "FVar") {
      if (s.kind === "FVar" && s.level === t.level) return true;
      const tEntry = this.context.evarAt(t);
      if (tEntry !== undefined) return this.#constrain(tEntry, "both", s);
    }
    if (s.kind === "FVar") {
      const sEntry = this.context.evarAt(s);
      if (sEntry !== undefined) return this.#constrain(sEntry, "both", t);
    }

    if (s.kind === "TBad" || t.kind === "TBad") return true;

    // The extremes are leaves with nothing to walk, and `never` is the one a
    // rigid variable can reach: `X <: never` makes `X` empty, so it *is*
    // `never`. Asking it of `#subtype` puts the variable on the left, which is
    // the side promotion is sound on. Nothing dual holds for `unknown` -- every
    // type is under it -- so that case is the two spellings and no more.
    if (s.kind === "TUnknown" && t.kind === "TUnknown") return true;
    if (s.kind === "TNever") return this.#subtype(t, TNever);
    if (t.kind === "TNever") return this.#subtype(s, TNever);

    if (s.kind === "TData" && t.kind === "TData") {
      return s.name === t.name && this.#eqtypeArgs(s.args, t.args);
    }
    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#relateFun(s, t, 0);
    }
    return false;
  }

  /** Elementwise equivalence of two argument lists. */
  #eqtypeArgs(s: readonly Type[], t: readonly Type[]): boolean {
    return allPairs(s, t, (a, b) => this.#eqtype(a, b));
  }

  /**
   * Relate `s` to `t` at a position of `variance`: under it, over it, or the
   * same as it. The one place the two relations are told apart, so every rule
   * that has a position to name can be written once.
   */
  #relate(s: Type, t: Type, variance: Variance): boolean {
    if (variance === 0) return this.#eqtype(s, t);
    return variance > 0 ? this.#subtype(s, t) : this.#subtype(t, s);
  }

  /**
   * Two arrows, related at a position of `variance`. Shared because an arrow's
   * shape is the same question either way -- the arities, the bounds, the
   * parameters, the result -- and only the position each part sits at differs,
   * which `variance` already says. Invariance flips to itself, so the same
   * walk asks for equivalence throughout.
   *
   * Arity is part of the type, for parameters and for the quantifier alike;
   * `allPairs` is what turns a mismatch down.
   */
  #relateFun(
    s: Extract<Type, { kind: "TFun" }>,
    t: Extract<Type, { kind: "TFun" }>,
    variance: Variance,
  ): boolean {
    // Full Fsub: a bound sits in a contravariant position, like a parameter.
    // Kernel Fsub would demand `alphaEq` here and be decidable; this is the
    // trade named at the top of the file.
    const flipped = flip(variance);
    const bounds = allPairs(
      s.typeParams,
      t.typeParams,
      (mine, binder) => this.#relate(mine.bound, binder.bound, flipped),
    );
    if (!bounds) return false;

    // Open both under one group of fresh variables carrying the *right* side's
    // bounds -- the weaker assumption, so what holds under them holds under
    // the left's too, and under equivalence the two are the same bounds
    // anyway. Bounds are parallel, already in the enclosing scope, so they are
    // pushed as they stand.
    //
    // Nameless: nothing elaborates surface syntax mid-comparison, so the
    // variable is reached only through the `FVar` built here. `hint` prints.
    return this.context.inScope(() => {
      const opened = t.typeParams.map((binder) =>
        FVar(this.context.pushTypeVar(binder.bound), binder.hint)
      );
      const params = allPairs(
        s.params,
        t.params,
        (mine, param) =>
          this.#relate(
            openMany(mine, opened),
            openMany(param, opened),
            flipped,
          ),
      );
      return params && this.#relate(
        openMany(s.result, opened),
        openMany(t.result, opened),
        variance,
      );
    });
  }

  // --------------------------------------------------------------- avoidance

  /**
   * Record `type` as a bound of `evar`, avoiding first.
   * Anything the EVar cannot see has to go, and which direction is safe
   * depends on the side: a lower bound may only be widened, an upper bound
   * only narrowed.
   *
   * Always `true`: this answers no question about the two types, it records
   * one, and there is no verdict for "I was asked something I could not write
   * down". Something is always written down -- at worst an extreme, which
   * constrains nothing and is reported where it is put.
   */
  #constrain(evar: EVarEntry, side: ConstraintSide, type: Type): boolean {
    // No `apply` first: a batch is solved only after the last constraint is
    // in, so nothing reaching here can mention a *solved* EVar.
    //
    // The bar is where the batch begins and not this EVar's own level: a
    // solution may mention anything to the batch's left, but a sibling is out
    // of bounds in either direction -- selection reads the result type alone,
    // so a sibling standing in a pending bound is a dependency it cannot see.
    // The levels between are that batch and nothing else, so no rigid variable
    // loses scope by the wider bar.
    if (side !== "both") {
      const dir = side === "lower" ? 1 : -1;
      // A bound has a direction to give ground in, so it always lands.
      evar.addConstraint(side, this.#avoid(type, evar.batch, dir)!);
      return true;
    }

    // An equation has no direction to give ground in, so where a part is out
    // of scope there is nothing to record it as -- and no second try either:
    // widening the equation into a lower bound and narrowing it into an upper
    // one would give a pair that cannot meet, since only a part that collapsed
    // gets here and a strict widening never sits under the matching strict
    // narrowing. The variable is decided, so decide it here, where the cause
    // is still in hand: `TBad` both ways, and the report that makes it true.
    const pinned = this.#avoid(type, evar.batch, 0);
    if (pinned === undefined) {
      this.#file(
        "error",
        `cannot infer the type argument ${evar.hint} from ` +
          `${typeToString(type)}: it mentions a variable bound inside this ` +
          `call, and an invariant position admits no wider guess, so give it ` +
          `explicitly`,
      );
      evar.addConstraint("both", TBad);
      return true;
    }
    evar.addConstraint("both", pinned);
    return true;
  }

  /**
   * The least supertype of `type` closed by `levels` going up, the greatest
   * subtype going down, or -- invariantly, where there is no direction to
   * travel in -- `undefined` if `type` is not already closed.
   *
   * This is the avoidance problem. A constraint picked up under a binder may
   * mention variables that binder introduced, and those cannot appear in a
   * solution that outlives it -- so each is replaced by something in scope,
   * swapping direction at every contravariant position.
   *
   * The outer half of the walk: it takes what `#avoidPart` could not name and
   * puts an extreme there. Every recursion goes through here, so a part that
   * runs out of room collapses at the smallest node that has room for it,
   * rather than taking its parents down with it.
   */
  #avoid(type: Type, levels: number, dir: Variance): Type | undefined {
    const avoided = this.#avoidPart(type, levels, dir);
    if (avoided !== undefined) return avoided;
    if (dir === 0) return undefined;
    return dir > 0 ? TUnknown : TNever;
  }

  /**
   * `type` rebuilt out of parts in scope, or `undefined` where it cannot be:
   * an EVar, which has constraints rather than a bound to stand aside for, or
   * anything at all in an invariant position, which admits no wider guess.
   * A compound goes with any part that could not be named, since half a type
   * is not a type.
   *
   * The scope test is this walk itself and not a closedness check up front:
   * closedness reads levels, and a `BVar` has none -- a binder inside `type`
   * is in scope wherever `type` goes, and asking about it in level terms gets
   * the wrong answer.
   */
  #avoidPart(type: Type, levels: number, dir: Variance): Type | undefined {
    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      // Bound by something inside `type`, so it travels with it.
      case "BVar":
        return type;
      case "FVar": {
        if (type.level < levels) return type;
        const entry = this.context.entryAt(type);
        if (entry.kind === "EVar") {
          // Said here and not by the caller: only the walk knows which part
          // was the problem, and what stands in its place is the outer half's
          // business. An unsolved EVar has no bound to appeal to, so this is
          // as near as the answer gets.
          this.#file(
            "warning",
            `the type argument ${entry.hint} cannot appear in another type ` +
              `argument's bound, so the constraint mentioning it was ` +
              `approximated`,
          );
          return undefined;
        }
        if (entry.kind !== "TypeVar") {
          impossible("a type naming a term variable's level");
        }
        // Upward, a variable's declared bound is the nearest thing it is
        // known to sit under; downward there is no lower bound to appeal to,
        // so nothing of the variable survives.
        if (dir <= 0) return undefined;
        return this.#avoid(entry.bound, levels, dir);
      }
      case "TData": {
        // A datatype's arguments have no declared variance, so each is asked
        // invariantly however this node was reached: an argument that cannot
        // be named exactly takes the whole type with it.
        const args = [];
        for (const arg of type.args) {
          const avoided = this.#avoid(arg, levels, 0);
          if (avoided === undefined) return undefined;
          args.push(avoided);
        }
        return TData(type.name, args);
      }
      case "TFun": {
        const flipped = flip(dir);
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

  // --------------------------------------------------------- joins and meets

  /**
   * Least upper bound. Falls back to `unknown` rather than inventing a union:
   * there is no union type, so an inexact answer has to be the sound one.
   */
  join(left: Type, right: Type): Type {
    // Exhausted, top is the sound answer: it is above everything.
    return this.#query(
      undefined,
      () => this.#join(left, right),
      () => TUnknown,
    );
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
    const sBound = this.#declaredBoundOf(s);
    const tBound = this.#declaredBoundOf(t);
    const sIsLater = s.kind === "FVar" && t.kind === "FVar" &&
      s.level > t.level;
    if (sBound !== undefined && (tBound === undefined || sIsLater)) {
      return this.#join(sBound, t);
    }
    if (tBound !== undefined) return this.#join(s, tBound);

    // Two unrelated functions still meet at an arrow, pointwise.
    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, true) ?? TUnknown;
    }

    // Datatypes are nominal and their arguments invariant, so there is no
    // structure left to walk: either the two are the same type or they have
    // nothing above them but top. `#eqtype` and not `alphaEq`, since a
    // `never`-bounded variable is equivalent to types it is not spelled like.
    if (s.kind === "TData" && t.kind === "TData") {
      return s.name === t.name && this.#eqtypeArgs(s.args, t.args)
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
    return this.#query(undefined, () => this.#meet(left, right), () => TNever);
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
    const sIsLater = s.kind === "FVar" && t.kind === "FVar" &&
      s.level > t.level;
    const sPromotes = this.#declaredBoundOf(s) !== undefined;
    const tPromotes = this.#declaredBoundOf(t) !== undefined;
    if (sPromotes && (!tPromotes || sIsLater)) {
      return this.#subtype(s, t) ? s : TNever;
    }
    if (tPromotes) return this.#subtype(t, s) ? t : TNever;

    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, false) ?? TNever;
    }

    // Dual to `#join`: invariance leaves equivalence as the only question to
    // ask about two datatypes, and nothing below.
    if (s.kind === "TData" && t.kind === "TData") {
      return s.name === t.name && this.#eqtypeArgs(s.args, t.args) ? s : TNever;
    }

    if (s.kind === "BVar" && t.kind === "BVar" && s.index === t.index) return s;
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

  // ------------------------------------------------------------------- casts

  /**
   * A part of a cast that could not be reached: said in place, and answered
   * with the shape that was asked for.
   *
   * The missing parts are filled with `TBad`, and `TBad` is the checker's word
   * for *a report already stands* -- so planting one is a recording like any
   * other, and this is where the report it promises gets made.
   */
  #castFailed(type: Type, pattern: TypePattern, message?: string): Type {
    this.#sayCastFailed(type, pattern, message);
    return completePattern(pattern).type;
  }

  /**
   * The saying on its own, for the one loss with no part to stand in for it:
   * a parameter count, a fact about the list rather than about a position.
   *
   * Silent when the ask gave no position, which is what tells a *check* from a
   * *query*: `downcast(TUnknown, expected)` asks what a pattern admits at its
   * widest, reads no program that could be wrong, and passes none for that
   * reason.
   */
  #sayCastFailed(type: Type, pattern: TypePattern, message?: string): void {
    if (this.#at === undefined) return;
    this.#file(
      "error",
      message ??
        `expected ${typeToString(pattern)}, found ${typeToString(type)}`,
    );
  }

  /**
   * The least supertype of `type` matching `pattern`. This is how a checking
   * rule learns what it asked for: the pattern says the shape, the type says
   * the content, and the cast is the nearest thing that is both.
   */
  upcast(type: Type, pattern: TypePattern, at?: Position): Type {
    return this.#castQuery(type, pattern, 1, at);
  }

  /** The greatest subtype of `type` matching `pattern`. Dual to `upcast`. */
  downcast(type: Type, pattern: TypePattern, at?: Position): Type {
    return this.#castQuery(type, pattern, -1, at);
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
  exactcast(type: Type, pattern: TypePattern, at?: Position): Type {
    return this.#castQuery(type, pattern, 0, at);
  }

  /**
   * One top-level cast, in whichever direction, and the one place a cast can
   * give up on the whole ask rather than on a part.
   *
   * Exhaustion is the only such reason left, and it is the checker's limit
   * rather than the program's mistake -- so it is said in those words, and the
   * shape asked for still comes back, since a caller has no more use for a
   * hole here than anywhere else.
   */
  #castQuery(
    type: Type,
    pattern: TypePattern,
    dir: Variance,
    at: Position | undefined,
  ): Type {
    return this.#query(
      at,
      () => this.#cast(type, pattern, dir),
      () =>
        this.#castFailed(
          type,
          pattern,
          `gave up casting ${typeToString(type)} to ${
            typeToString(pattern)
          }: too deeply nested`,
        ),
    );
  }

  /**
   * Walks the *pattern*, since the pattern says which shape is wanted, and
   * asks `type` to keep up.
   *
   * Nothing here fails outright: a part that cannot be cast reports itself and
   * contributes the shape asked for with `<bad>` in it, and the walk carries
   * on -- a mismatched parameter costs the parameter, not the result beside
   * it, and each says so in its own words.
   */
  #cast(type: Type, pattern: TypePattern, dir: Variance): Type {
    this.#spend();

    // Three kinds of demand, and the pattern is what says which. Nothing is
    // read off `type` until the demand is known, which is what keeps a rule
    // meant for one kind from running in front of another.
    switch (pattern.kind) {
      // Nothing demanded, so nothing moves -- whatever stands there is the
      // answer. Also the only case that reads content out of `type`, which is
      // how an invariant position, unable to move at all, still answers.
      case "TMissing":
        return type;

      // A shape is demanded. Only here may `type` be moved to produce one, and
      // both ways of moving it live in `#castHead`.
      case "TFun": {
        const from = this.#castHead(type, pattern, dir);
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
          return this.#castFailed(type, pattern);
        }
        return this.#castFun(from, pattern, dir);
      }

      case "TData": {
        const from = this.#castHead(type, pattern, dir);
        if (
          from.kind !== "TData" || from.name !== pattern.name ||
          from.args.length !== pattern.args.length
        ) {
          return this.#castFailed(type, pattern);
        }
        // Arguments are invariant however deep they sit, as `openAt` says by
        // passing `0` and never flipping out of it again.
        //
        // Every argument is walked even where the head already filled one:
        // re-entering a filled argument is a no-op, `<bad>` being absorbing,
        // where returning early would assume the head filled the list whole.
        const args = pattern.args.map((want, i) =>
          this.#cast(
            from.args[i] ?? impossible("an argument per argument"),
            want,
            0,
          )
        );
        return TData(from.name, args);
      }

      // A leaf is written in full, so it matches only itself and the whole
      // question is whether `type` reaches it in this direction. Left to the
      // relation whole, which promotes a variable on its own and knows
      // `X <: X` -- both lost by moving `type` first.
      //
      // `default` and not six arms, but not a hole either: `completeLeafPattern`
      // enumerates the same six with no default, so a new kind stops the
      // compiler there.
      default: {
        const leaf = completeLeafPattern(pattern);
        const holds = dir > 0
          ? this.#subtype(type, leaf)
          : dir < 0
          ? this.#subtype(leaf, type)
          : this.#eqtype(type, leaf);
        return holds ? leaf : this.#castFailed(type, pattern);
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
    dir: Variance,
  ): Type {
    // A report already stands, so a bad type has whatever shape is demanded:
    // a third way of standing aside, beside promotion and lifting an extreme.
    // Only needed where a shape is demanded, a demanded leaf going to the
    // relation, which knows `<bad>` on its own.
    //
    // The shape but never a report: filling a missing part from something
    // already bad invents nothing, where lifting an extreme is a choice.
    if (type.kind === "TBad") return completePattern(pattern).type;
    const bound = this.#declaredBoundOf(type);
    if (bound !== undefined && dir > 0) {
      return this.#castHead(bound, pattern, dir);
    }
    if (
      !((type.kind === "TUnknown" && dir < 0) ||
        (type.kind === "TNever" && dir > 0))
    ) {
      return type;
    }

    // A function's parts have variance, so each has an extreme of its own and
    // the lift is total: the greatest arrow takes the smallest parameters and
    // the largest result, and the walk that follows lifts again wherever it
    // meets an extreme further in.
    if (pattern.kind === "TFun") {
      // Only a direction reaches here -- an invariant position moves neither
      // way, and the guard above let nothing else through -- so each part has
      // an extreme, taken at the flip of `dir` inside and at `dir` itself for
      // the result.
      const inner = dir > 0 ? TUnknown : TNever;
      return TFun(
        pattern.typeParams.map((b) => mkTypeParamInfo(b.hint, inner)),
        pattern.params.map(() => inner),
        dir < 0 ? TUnknown : TNever,
      );
    }

    // A datatype's arguments do not: nothing is greatest among the types a
    // `List` can be of, so there is no greatest `List`. The shape is lifted
    // all the same, so a `match` still has a datatype to work with; what the
    // invariance costs is a report, which `already` is what decides: a shape
    // that had to be invented is one the cast did not find.
    const filled = completePattern(pattern);
    if (filled.already) return filled.type;
    return this.#castFailed(
      type,
      pattern,
      `cannot tell what ${typeToString(type)} is a ${pattern.name} of: a ` +
        `datatype's arguments are invariant, so ${typeToString(pattern)} has ` +
        `no ${dir > 0 ? "least" : "greatest"} solution -- write it out`,
    );
  }

  /**
   * Both binders are opened under one group of fresh variables, the way
   * `#latticeFun` and `#subtypeFun` open theirs. Comparing under their indices
   * instead would leave a parameter at a `BVar`, which has no bound to read.
   */
  #castFun(
    type: Extract<Type, { kind: "TFun" }>,
    pattern: Extract<TypePattern, { kind: "TFun" }>,
    dir: Variance,
  ): Type {
    const inner = flip(dir);
    return this.context.inScope((mark) => {
      // Bounds are parallel -- they read in the enclosing scope -- so they are
      // cast before anything is pushed, and need no closing after. They are
      // contravariant, like the parameters.
      const typeParams: TypeParamInfo[] = [];
      for (const [j, want] of pattern.typeParams.entries()) {
        const mine = type.typeParams[j] ?? impossible("a binder per binder");
        const bound = this.#cast(mine.bound, want.bound, inner);
        // The hint is print-only, and the pattern's is the one an author wrote
        // when there was an annotation to write it in.
        typeParams.push(mkTypeParamInfo(want.hint, bound));
      }

      const opened = typeParams.map((binder) =>
        FVar(this.context.pushTypeVar(binder.bound, binder.hint), binder.hint)
      );

      // The pattern's arity, which is what was asked for: a position only the
      // pattern has is filled from the pattern alone, one only `type` has is
      // dropped. Said once, by count, rather than once per position that had
      // no partner.
      if (type.params.length !== pattern.params.length) {
        this.#sayCastFailed(
          type,
          pattern,
          `expected ${pattern.params.length} parameter${
            pattern.params.length === 1 ? "" : "s"
          }, found ${type.params.length}`,
        );
      }
      const params: Type[] = [];
      for (const [i, want] of pattern.params.entries()) {
        const mine = type.params[i];
        if (mine === undefined) {
          // The count above already said so, and said it better.
          // Already in the binder's own scope, having never been opened.
          params.push(completePattern(want).type);
          continue;
        }
        const param = this.#cast(
          openMany(mine, opened),
          openMany<unknown>(want, opened),
          inner,
        );
        params.push(closeFrom(param, mark));
      }

      const result = this.#cast(
        openMany(type.result, opened),
        openMany<unknown>(pattern.result, opened),
        dir,
      );
      return TFun(typeParams, params, closeFrom(result, mark));
    });
  }

  // --------------------------------------------------------- solving a batch

  /**
   * The join of every lower bound, or `never` if there are none.
   *
   * `solve`-prefixed because this computes a candidate solution, where
   * `#declaredBoundOf` reads a binder's declared bound.
   */
  solveLowerBoundOf(entry: EVarEntry): Type {
    // Exhausted, the join it could not finish is at most top -- the same
    // answer `join` itself gives up with, and one the solve reports on.
    return this.#query(
      undefined,
      () => entry.lower.reduce((a, b) => this.#join(a, b), TNever),
      () => TUnknown,
    );
  }

  /** The meet of every upper bound, or `unknown` if there are none. Dual to
   * `solveLowerBoundOf`. */
  solveUpperBoundOf(entry: EVarEntry): Type {
    return this.#query(
      undefined,
      () => entry.upper.reduce((a, b) => this.#meet(a, b), TUnknown),
      () => TNever,
    );
  }

  /**
   * Solve one EVar, given how it occurs in the type the application hands back.
   *
   * Both bounds are computed, never one: they are peers, and which is the
   * answer is what the entry's occurrences decide. `never` and `unknown` are not fallbacks
   * but the honest defaults -- an EVar with no lower bound really is above
   * bottom, and one with no upper really is below top.
   *
   * `lower <: upper` first, or the constraints have no solution at all --
   * which is also the check that keeps a callee's declared bound honest, that
   * bound being an upper constraint like any other. Then the selection:
   * covariant occurrences take the *lower* bound, the smallest type the
   * constraints admit and so the most informative, which is what makes the
   * answer principal rather than merely sound; contravariant ones take the
   * upper, dually.
   *
   * Occurring both ways, or inside an invariant `TData` argument, the bounds
   * must *agree*: widening either way breaks the other, so unless they meet
   * there is no principal choice and the checker declines rather than picking.
   * An error and not a warning, though either bound would check: at an
   * invariant occurrence the two results are *incomparable*, so a pick is not
   * a coarser answer but an arbitrary one, and every later diagnostic would be
   * an artifact of it. The explicit type argument the author would write is
   * both the fix and the record of it.
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
   * A variable nothing constrained at all is a warning, not a failure. Every
   * type satisfies no constraints, so the selection is sound and even
   * principal where the variable occurs one way; what it is not is
   * *actionable*, since the `never` or `unknown` it settles on is a type the
   * author never wrote and will meet again further out.
   *
   * The relation tests here mutate, as everywhere -- but never this batch.
   * Every recorded bound is closed by `batch`, so no sibling can pick up a
   * bound while its neighbours are being decided, which is what would make the
   * order of this loop matter.
   */
  solveEVar(entry: EVarEntry, at: Position): Type {
    const { covariantly, contravariantly } = entry;

    if (entry.lower.length === 0 && entry.upper.length === 0) {
      // The bounds are `never` and `unknown`, and the occurrence picks between
      // them as it would between any two. Occurring both ways there is nothing
      // to disagree about, nothing having been demanded, so the smaller stands.
      const type = contravariantly && !covariantly ? TUnknown : TNever;
      this.#file(
        "warning",
        `nothing constrains the type argument ${entry.hint}, so it was taken ` +
          `to be ${typeToString(type)}; give it explicitly if that is not ` +
          `what was meant`,
        at,
      );
      return type;
    }

    const lower = this.solveLowerBoundOf(entry);
    const upper = this.solveUpperBoundOf(entry);

    const verdict = this.isSubtype(lower, upper);
    if (verdict !== true) {
      this.#file(
        "error",
        verdict === undefined
          // The checker's limit, not the program's mistake.
          ? `gave up inferring the type argument ${entry.hint}: comparing ` +
            `${typeToString(lower)} with ${typeToString(upper)} ran too deep`
          : `cannot infer the type argument ${entry.hint}: it is bounded ` +
            `below by ${typeToString(lower)} and above by ` +
            `${typeToString(upper)}, and no type is both`,
        at,
      );
      return TBad;
    }

    if (covariantly && !contravariantly) return lower;
    if (contravariantly && !covariantly) return upper;

    if (covariantly && contravariantly) {
      // One direction is the check above; this is the other. Together they make
      // the bounds equivalent, and then either may be taken.
      if (this.isSubtype(upper, lower) === true) return lower;
      this.#file(
        "error",
        `cannot infer the type argument ${entry.hint}: it occurs ` +
          `invariantly, and the arguments bound it only between ` +
          `${typeToString(lower)} and ${typeToString(upper)}, so no choice ` +
          `is the general one; give it explicitly`,
        at,
      );
      return TBad;
    }

    // Occurring nowhere: the demand first.
    return entry.lower.length > 0 ? lower : upper;
  }

  /**
   * Push one EVar behind each of `hints`, run `body` over them, then solve the
   * batch and hand the answers back in order.
   *
   * The solutions and not a substituted type: the caller still holds the
   * unopened result the batch was instantiated from, so opening *that* with
   * them is one ordinary substitution, where carrying a type back out would
   * need a second mechanism to put the answers into it.
   *
   * The scope and the variables, and nothing else -- not even their declared
   * bounds, which are a constraint like any other and the caller's to record,
   * along with which types to open, where each variable occurs, and what to
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
   * `at` is where the batch stands -- the application as a whole -- and the
   * default for anything filed under it, which a single argument's own ask
   * narrows for its own length.
   */
  withEVars(
    hints: readonly string[],
    at: Position,
    body: (evars: readonly FVarRef[]) => void,
  ): readonly Type[] {
    const outer = this.#at;
    this.#at = at;
    try {
      return this.context.inScope(() => {
        const batch = this.context.pushEVarBatch(hints);
        body(batch.map((entry) => entry.ref));
        return batch.map((entry) => this.#solutionFor(entry, at));
      });
    } finally {
      this.#at = outer;
    }
  }

  /**
   * What one member of a batch came to.
   *
   * A variable given up on answers `TBad`, and needs nothing special here to:
   * whoever gave up recorded `TBad` as the bound, and it stays `TBad` through
   * the lattice. Checking against a bad type always succeeds, so one type
   * argument nobody could infer does not go on to fail again wherever the
   * result is used.
   */
  #solutionFor(entry: EVarEntry, at: Position): Type {
    const solved = this.solveEVar(entry, at);
    // The batch bar, not this variable's level: a solution is built from bounds
    // already closed by it, and a sibling riding out would leave a variable
    // standing in a type after its scope has been popped.
    if (!isClosed(solved, entry.batch)) {
      throw new Error(
        `solution for ?${entry.hint} escapes: it mentions something at or ` +
          `past level ${entry.batch}, where its batch begins`,
      );
    }
    return solved;
  }
}
