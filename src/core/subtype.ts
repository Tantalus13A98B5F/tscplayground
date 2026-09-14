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
  argVarianceOf,
  badUnder,
  closeFrom,
  completeLeafPattern,
  completePattern,
  composeVariance,
  type DataHead,
  type Direction,
  flip,
  FVar,
  type FVarRef,
  impossible,
  isClosed,
  mkTypeParamInfo,
  openMany,
  TData,
  TFun,
  TNever,
  TRef,
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
 * *locally* do with it, and an interior test that could read it would settle
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
   * Undefined only before the first top-level ask installs one. Every site
   * that records needs a position and says so rather than dropping what it had
   * to say: a report that goes nowhere is worse than none, since `TBad` is
   * written on the promise that one stands.
   */
  #at: Position | undefined;

  /**
   * Where the live batch begins, while one is live: the bar `isClosed` is
   * asked against by `#assertNoEVar`, and undefined wherever no batch is open.
   *
   * It exists for the sentence `withEVars` ends on -- nothing outside that
   * method holds a type naming an EVar -- which the lattice operations rely on
   * by *not* checking their operands. A relied-on invariant that nothing tests
   * is a promise; this is the test.
   *
   * Vacuous on today's suite -- nothing joins while a batch is open, a match
   * in argument position being the way one would -- so it is a tripwire for
   * later rather than a check that currently catches anything.
   */
  #liveBatch: number | undefined;

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

  /** `Foo`'s parameter `index`, as a diagnostic names it. */
  #argName(type: DataHead, index: number): string {
    return `${type.name}'s argument ${type.params[index]?.hint ?? index + 1}`;
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
   * An EVar has constraints rather than a bound, so it stops the walk like any
   * other type with nothing to stand aside for, and the shape the caller
   * wanted fails to appear -- a report rather than a crash. Asking is still a
   * mistake: exposing is for when a rule needs a *shape*, an arrow to take
   * apart or a datatype to match on, and an EVar is not one.
   */
  expose(type: Type): Type {
    let current = type;
    for (;;) {
      const bound = this.#declaredBoundOf(current);
      if (bound === undefined) return current;
      current = bound;
    }
  }

  /**
   * The bound `type` may stand aside for, or `undefined` if it may not: it is
   * no variable, or it names an EVar, which has constraints rather than a
   * bound and no shape yet to stand aside with.
   *
   * The bound and not a yes-or-no. Unbounded stores `TUnknown`, so a rigid
   * variable always has one, and `undefined` says only that promotion does not
   * apply.
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
  ): Diagnostic {
    const at = where ??
      impossible("nothing records outside an ask that said where it was");
    const diagnostic = severity === "error"
      ? reportError(message, at)
      : reportWarning(message, at);
    this.diagnostics.push(diagnostic);
    return diagnostic;
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
    const witness = this.#sayCastFailed(type, pattern, message);
    return completePattern(pattern, () => badUnder(witness));
  }

  /**
   * The saying on its own, for the one loss with no part to stand in for it:
   * a parameter count, a fact about the list rather than about a position.
   */
  #sayCastFailed(
    type: Type,
    pattern: TypePattern,
    message?: string,
  ): Diagnostic {
    return this.#file(
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
  upcast(type: Type, pattern: TypePattern, at: Position): Type {
    return this.#castQuery(type, pattern, 1, at);
  }

  /** The greatest subtype of `type` matching `pattern`. Dual to `upcast`. */
  downcast(type: Type, pattern: TypePattern, at: Position): Type {
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
  exactcast(type: Type, pattern: TypePattern, at: Position): Type {
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
    at: Position,
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
    // meant for one kind from running in front of another -- and in
    // particular keeps promotion out of the two cases that must not move.
    switch (pattern.kind) {
      // Nothing demanded, so nothing moves -- whatever stands there is the
      // answer. Also the only case that reads content out of `type`, which is
      // how an invariant position, unable to move at all, still answers.
      case "TMissing":
        return type;

      // A shape is demanded, and `#castHead` is the one place that says what
      // a head with none of its own offers instead.
      case "TFun": {
        const from = this.#castHead(type, dir);
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
          return this.#castStandsAside(from, type, pattern, dir);
        }
        return this.#castFun(from, pattern, dir);
      }

      case "TData": {
        const from = this.#castHead(type, dir);
        if (
          from.kind !== "TData" || from.name !== pattern.name ||
          from.args.length !== pattern.args.length
        ) {
          return this.#castStandsAside(from, type, pattern, dir);
        }
        // An argument stands where its parameter's variance says, composed
        // with wherever this node itself stands -- the same rule `openWith`
        // follows, so a position means the same thing to both.
        //
        // Every argument is walked even where the head already filled one:
        // re-entering a filled argument is a no-op, `<bad>` being absorbing,
        // where returning early would assume the head filled the list whole.
        const args = pattern.args.map((want, i) =>
          this.#cast(
            from.args[i] ?? impossible("an argument per argument"),
            want,
            composeVariance(dir, argVarianceOf(pattern, i)),
          )
        );
        return TData(from, args);
      }

      case "TRef": {
        const from = this.#castHead(type, dir);
        if (from.kind !== "TRef") {
          return this.#castStandsAside(from, type, pattern, dir);
        }
        // A cell's argument moves neither way, however this node was reached.
        return TRef(this.#cast(from.arg, pattern.arg, 0));
      }

      // A leaf is written in full, so it matches only itself and the whole
      // question is whether `type` reaches it in this direction. Left to the
      // relation whole, which promotes a variable on its own and knows
      // `X <: X` -- both lost by moving `type` first.
      //
      // `default` and not five arms, but not a hole either:
      // `completeLeafPattern` enumerates the same five with no default, so a
      // new kind stops the compiler there.
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
   * What `type` offers where a shape is demanded, as a type the shape cases
   * can take apart -- so every way of getting there ends in the same
   * structural walk, and there is no second traversal to keep in step.
   *
   * A variable has no shape of its own. Going up it stands aside for its
   * bound, the same promotion `#join` makes, and whole rather than a step at
   * a time, nothing between an `FVar` and its bound having anything to say
   * here. Going down or standing still it may not move, so it is handed on
   * unchanged and fails the shape test at the call.
   *
   * Only where a shape is demanded, and that is the point of it being here
   * rather than at the top of `#cast`. A missing part answers with what stood
   * in the position, so promoting first would answer with something the
   * position never held; and a leaf goes to the relation whole, which
   * promotes on its own and knows `X <: X`, both lost by moving `type` first.
   */
  #castHead(type: Type, dir: Variance): Type {
    return dir > 0 ? this.expose(type) : type;
  }

  /**
   * A head that is no such shape. Two of those are answers rather than
   * failures, and both for one reason: they sit under -- or over -- every
   * type of every shape, so nothing the pattern asks of them is in question.
   *
   * `<bad>` is below and above everything, so it answers in every direction,
   * the invariant one included, and a report already stands to license it. An
   * extreme answers only the way the cast moves: `never` going up, `unknown`
   * going down, which is the same vacuous case `#subtype` returns true for on
   * its first line -- so the cast and the relation agree here by construction
   * rather than by coincidence. An invariant ask has no direction and so no
   * extreme of its own.
   *
   * Each stands *whole*, and this is what used to build the pattern's shape
   * around it. There is nobody to build it for: a shape a cast returns is
   * load-bearing on the failure path, where `#castFailed` puts `<bad>` in the
   * parts it could not reach, and nothing downstream can tell a `never` from
   * the `List[never]` it is about to be compared against, or a `<bad>` from a
   * `List[<bad>]` that checking against succeeds either way. Building it cost
   * a choice at every invariant part, and a report about the choice.
   *
   * Anything else reached the wrong head: said in place, and answered with
   * the shape that was asked for, which is `#castFailed`.
   */
  #castStandsAside(
    head: Type,
    type: Type,
    pattern: TypePattern,
    dir: Variance,
  ): Type {
    if (head.kind === "TBad") return head;
    if (dir !== 0 && head.kind === (dir > 0 ? "TNever" : "TUnknown")) {
      return head;
    }
    return this.#castFailed(type, pattern);
  }

  /**
   * Both binders are opened under one group of fresh variables, the way
   * `#latticeFun` and `#relateFun` open theirs. Comparing under their indices
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
      const spare = type.params.length === pattern.params.length
        ? undefined
        : badUnder(this.#sayCastFailed(
          type,
          pattern,
          `expected ${pattern.params.length} parameter${
            pattern.params.length === 1 ? "" : "s"
          }, found ${type.params.length}`,
        ));
      const params: Type[] = [];
      for (const [i, want] of pattern.params.entries()) {
        const mine = type.params[i];
        if (mine === undefined) {
          // Already in the binder's own scope, having never been opened.
          params.push(completePattern(
            want,
            () => spare ?? impossible("a spare parameter at a matching arity"),
          ));
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
      return this.#relateData(s, t, 1);
    }

    // A cell is invariant whichever relation asked, `0` composing to `0`.
    if (s.kind === "TRef" && t.kind === "TRef") {
      return this.#eqtype(s.arg, t.arg);
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
      return this.#relateData(s, t, 0);
    }
    if (s.kind === "TRef" && t.kind === "TRef") {
      return this.#eqtype(s.arg, t.arg);
    }
    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#relateFun(s, t, 0);
    }
    return false;
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
   * Two datatypes, related at a position of `variance`. Nominal, so the names
   * have to agree and there is nothing to unfold; what is left is the
   * arguments, each taken at its own parameter's variance composed with
   * wherever the pair itself stands.
   *
   * Which is why equivalence needs no case of its own: `0` absorbs, so asking
   * two datatypes to be the same asks it of every argument whatever its
   * parameter says.
   *
   * Arity is part of the type -- an arity mismatch is reported where the type
   * was written, so a `Foo[A]` and a `Foo[A, B]` reaching here simply do not
   * relate.
   */
  #relateData(
    s: Extract<Type, { kind: "TData" }>,
    t: Extract<Type, { kind: "TData" }>,
    variance: Variance,
  ): boolean {
    return s.name === t.name && allPairs(
      s.args,
      t.args,
      (a, b, i) =>
        this.#relate(
          a,
          b,
          composeVariance(variance, argVarianceOf(s, i)),
        ),
    );
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

  // ----------------------------------------------------- constraint collection

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
      const witness = this.#file(
        "error",
        `cannot infer the type argument ${evar.hint} from ` +
          `${typeToString(type)}: it mentions something this type argument ` +
          `cannot name, and an invariant position admits no wider guess, so ` +
          `give it explicitly`,
      );
      evar.addConstraint("both", badUnder(witness));
      return true;
    }
    evar.addConstraint("both", pinned);
    return true;
  }

  /**
   * The widest type matching `pattern`, which is what a pattern says when read
   * as an upper bound: each missing part becomes the extreme for its variance,
   * so only the written parts constrain. A complete pattern gives itself back.
   *
   * The CLTI paper reads a result pattern by downcasting top to it. Invariance
   * is why we did not: an invariant part has no extreme of its own, so there
   * was nothing for a downcast of `unknown` to put there, and both answers
   * tried are wrong for a bound -- planting `<bad>` blames the author for a
   * mistake nobody made, and picking a side keeps the shape and loses
   * principality.
   *
   * `#cast` now declines to do either, and that settles it the other way
   * round: `unknown` going down is under nothing it could be asked about, so
   * it is returned whole before the pattern is read at all, and downcasting
   * top is the identity for *every* pattern rather than partial at an
   * invariant one. The two walks want opposite things from a hole -- a cast
   * has a type to read one off, where this has only the pattern, so filling
   * from the position's variance is the whole job here and no longer any of
   * the cast's.
   *
   * Avoidance with the bar above everything, so no variable is ever out of
   * scope and a missing part is the only thing left that cannot be kept. The
   * two really are one walk -- what a part may be is settled by `levels`, and
   * a query about a pattern alone is the case where nothing is barred.
   *
   * `context.size` and not some sentinel above every level: a type read here
   * stands in this context, so nothing in it is at or past the watermark.
   *
   * Total, needing no `undefined` case of its own: the ask has a direction, so
   * the outer half always has an extreme to put down -- and an argument with a
   * direction has one too, so a missing `List[?]` is `List[unknown]`. Only an
   * *invariant* argument has none, and there the whole type gives way to
   * `unknown`: no widest one of those exists to name.
   */
  widestMatching(pattern: TypePattern): Type {
    return this.#avoid(pattern, this.context.size, 1) ??
      impossible("a directed avoidance with nothing to put down");
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
  #avoid(type: TypePattern, levels: number, dir: Variance): Type | undefined {
    const avoided = this.#avoidPart(type, levels, dir);
    if (avoided !== undefined) return avoided;
    if (dir === 0) return undefined;
    return dir > 0 ? TUnknown : TNever;
  }

  /**
   * `type` rebuilt out of parts in scope, or `undefined` where it cannot be:
   * a missing part, which was never written; an EVar, which has constraints
   * rather than a bound to stand aside for; or anything at all in an invariant
   * position, which admits no wider guess. A compound goes with any part that
   * could not be named, since half a type is not a type.
   *
   * The scope test is this walk itself and not a closedness check up front:
   * closedness reads levels, and a `BVar` has none -- a binder inside `type`
   * is in scope wherever `type` goes, and asking about it in level terms gets
   * the wrong answer.
   */
  #avoidPart(
    type: TypePattern,
    levels: number,
    dir: Variance,
  ): Type | undefined {
    switch (type.kind) {
      // Nothing written, so there is nothing to keep: the outer half puts the
      // extreme for the position here, which is the whole of what completing a
      // pattern by variance amounts to.
      case "TMissing":
        return undefined;
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
          // The occurrence and nothing else. Only the walk knows which
          // variable was in the way, and only the walk is sure it *was* in the
          // way -- what becomes of the part is the outer half's business, and
          // an enclosing invariant position may see the part off entirely.
          this.#file(
            "warning",
            `the type argument ${entry.hint} cannot appear in another type ` +
              `argument's bound; give it explicitly if what was inferred is ` +
              `not what was meant`,
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
        // An argument with a direction widens like anything else; an
        // invariant one has to be named exactly.
        const args = [];
        for (const [i, arg] of type.args.entries()) {
          const avoided = this.#avoid(
            arg,
            levels,
            composeVariance(dir, argVarianceOf(type, i)),
          );
          if (avoided === undefined) return undefined;
          args.push(avoided);
        }
        return TData(type, args);
      }
      case "TRef": {
        const avoided = this.#avoid(type.arg, levels, 0);
        return avoided === undefined ? undefined : TRef(avoided);
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
   * there is no union type, so an inexact answer has to be the sound one. That
   * is a decision and not a gap -- `docs/clti.md` costs the union and declines
   * it, the short of it being that a union pays for itself in its eliminator
   * and our one eliminator is nominal and one level.
   *
   * Exhaustion takes that same fallback and says nothing: top is above
   * everything, so the answer stays sound, but a match whose arms ran too deep
   * joins to `unknown` and the coercion after it blames the program.
   */
  /**
   * A lattice operation may not be handed a type naming an EVar of the live
   * batch. `#lattice` at an invariant position asks `#eqtype`, which records
   * against an EVar on either side before it tests anything else -- so an
   * operand naming one would turn a join into a constraint, which is a thing
   * no caller of `join` is asking for and nothing would notice.
   *
   * Solving is not a case: `solveEVar` folds bounds that `addConstraint`
   * already held to the same bar, and it runs with the batch popped.
   *
   * A failure is a checker bug rather than a program error, so it throws.
   */
  #assertNoEVar(what: string, types: readonly Type[]): void {
    const floor = this.#liveBatch;
    if (floor === undefined) return;
    for (const type of types) {
      if (isClosed(type, floor)) continue;
      throw new Error(
        `${what}: an operand names an EVar of the batch beginning at level ` +
          `${floor}`,
      );
    }
  }

  join(left: Type, right: Type): Type {
    this.#assertNoEVar("join", [left, right]);
    return this.#query(
      undefined,
      () => this.#join(left, right),
      () => TUnknown,
    );
  }

  /** Greatest lower bound. Falls back to `never`, dual to `join`. */
  meet(left: Type, right: Type): Type {
    this.#assertNoEVar("meet", [left, right]);
    return this.#query(undefined, () => this.#meet(left, right), () => TNever);
  }

  /**
   * The join of every type in `types`, or `never` if there are none: a whole
   * demand at once, where `join` takes two of it.
   *
   * The seed is the answer for an empty list and an honest one -- nothing to
   * be above really does leave bottom -- so a fold and not a special case.
   *
   * A tank of its own, like `join`, since a caller with a list to fold is
   * making one ask. `#joinMany` is the same fold inside whatever tank is
   * already standing, which is what solving an EVar wants: joining its lower
   * constraints, meeting its upper ones and comparing the two are parts of one
   * ask, not three.
   *
   * Running dry answers `unknown` and *warns*, where the other top-level asks
   * error: `unknown` is genuinely above every type in the list, so the answer
   * is sound and only imprecise, and a warning is what this file says of a
   * loss the program may go on from. It is why there is no `TBad` here to hand
   * back -- `badUnder` takes errors alone, and rightly, since nothing was
   * settled arbitrarily. Whatever fails downstream on the widened answer is
   * explained by this line.
   */
  joinMany(types: readonly Type[], at?: Position): Type {
    this.#assertNoEVar("joinMany", types);
    return this.#query(at, () => this.#joinMany(types), () => {
      this.#file(
        "warning",
        `gave up joining ${types.length} types: too deeply nested, so their ` +
          `join was taken to be unknown`,
      );
      return TUnknown;
    });
  }

  /** The meet of every type in `types`, or `unknown` if there are none. Dual
   * to `joinMany`. */
  meetMany(types: readonly Type[]): Type {
    this.#assertNoEVar("meetMany", types);
    return this.#query(undefined, () => this.#meetMany(types), () => TNever);
  }

  #joinMany(types: readonly Type[]): Type {
    return types.reduce((a, b) => this.#join(a, b), TNever);
  }

  #meetMany(types: readonly Type[]): Type {
    return types.reduce((a, b) => this.#meet(a, b), TUnknown);
  }

  /**
   * The pair ordered so that whichever side may stand aside comes first. Only
   * a variable stands aside at all, and of two it is the one declared later,
   * whose bound may name the earlier but never the reverse -- so promoting it
   * walks down the context and stops.
   *
   * Kinds and levels only, and the whole of the question: both lattice
   * operations ask it, so asking it here leaves each of them one branch where
   * it had a mirrored pair, and spares the context a lookup it cannot answer.
   */
  #promoterFirst(s: Type, t: Type): readonly [Type, Type] {
    if (t.kind !== "FVar") return [s, t];
    if (s.kind !== "FVar" || t.level > s.level) return [t, s];
    return [s, t];
  }

  #join(s: Type, t: Type): Type {
    if (s.kind === "TBad") return s;
    if (t.kind === "TBad") return t;
    if (s.kind === "TUnknown" || t.kind === "TUnknown") return TUnknown;
    if (s.kind === "TNever") return t;
    if (t.kind === "TNever") return s;

    // A variable has no shape of its own, so it stands aside for its bound:
    // sound upward, and no relation has to be asked.
    if (s.kind === "FVar" && t.kind === "FVar" && s.level === t.level) return s;
    const [promoter, other] = this.#promoterFirst(s, t);
    const bound = this.#declaredBoundOf(promoter);
    if (bound !== undefined) return this.#join(bound, other);

    // Two unrelated functions still meet at an arrow, pointwise.
    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, 1) ?? TUnknown;
    }

    if (s.kind === "TData" && t.kind === "TData") {
      return this.#latticeData(s, t, 1) ?? TUnknown;
    }

    // Nothing is above two cells of different types: a cell's argument is the
    // invariant position written as a literal, so it asks `#lattice` what an
    // invariant datatype argument asks, and collapses the same way.
    if (s.kind === "TRef" && t.kind === "TRef") {
      const arg = this.#lattice(s.arg, t.arg, 0);
      return arg === undefined ? TUnknown : TRef(arg);
    }

    // A `BVar` is only itself, though no binder is open here for one to
    // escape from.
    if (s.kind === "BVar" && t.kind === "BVar" && s.index === t.index) return s;
    return TUnknown;
  }

  #meet(s: Type, t: Type): Type {
    if (s.kind === "TBad") return s;
    if (t.kind === "TBad") return t;
    if (s.kind === "TNever" || t.kind === "TNever") return TNever;
    if (s.kind === "TUnknown") return t;
    if (t.kind === "TUnknown") return s;

    // Downward a variable may not stand aside for its bound: nothing says the
    // bound sits under it, so meeting there would invent a subtype. All that
    // can be said is whether the variable is already below the other, which is
    // the relation's question -- asked once, of the side `#join` would have
    // promoted.
    if (s.kind === "FVar" && t.kind === "FVar" && s.level === t.level) return s;
    const [promoter, other] = this.#promoterFirst(s, t);
    if (this.#declaredBoundOf(promoter) !== undefined) {
      return this.#subtype(promoter, other) ? promoter : TNever;
    }

    if (s.kind === "TFun" && t.kind === "TFun") {
      return this.#latticeFun(s, t, -1) ?? TNever;
    }

    if (s.kind === "TData" && t.kind === "TData") {
      return this.#latticeData(s, t, -1) ?? TNever;
    }

    if (s.kind === "TRef" && t.kind === "TRef") {
      const arg = this.#lattice(s.arg, t.arg, 0);
      return arg === undefined ? TNever : TRef(arg);
    }

    if (s.kind === "BVar" && t.kind === "BVar" && s.index === t.index) return s;
    return TNever;
  }

  /**
   * Join or meet at a position. `dir` is the lattice's own direction -- `+1`
   * to join, `-1` to meet -- already composed with the variance of wherever
   * the pair stands, which is how one entry point serves a covariant argument,
   * a contravariant one, and an arrow whose every part but the result flips.
   *
   * `undefined` at an invariant position, and only there: a part that may not
   * move has one answer if the two sides are already equivalent and none
   * otherwise. `#eqtype` and not `alphaEq`, since a `never`-bounded variable is
   * equivalent to types it is not spelled like. The same three-state reading
   * `#relate` takes, and for the same reason -- there is no third answer to a
   * position that is stuck.
   *
   * Asked at a `Direction` there is no such position, so the answer is a type
   * and the first signature says so: the callers that flip and compose their
   * way down an arrow never have a case to handle, and the one reading a
   * datatype argument always does.
   *
   * An overload and not a conditional return type: `0 extends D ? ... : ...`
   * says the same thing at the call sites, but the body cannot be checked
   * against it for an unresolved `D` and needs a cast on the way out, where an
   * overloaded implementation is still checked against its own signature.
   */
  #lattice(left: Type, right: Type, dir: Direction): Type;
  #lattice(left: Type, right: Type, dir: Variance): Type | undefined;
  #lattice(left: Type, right: Type, dir: Variance): Type | undefined {
    if (dir === 0) return this.#eqtype(left, right) ? left : undefined;
    return dir > 0 ? this.#join(left, right) : this.#meet(left, right);
  }

  /**
   * Join or meet two datatypes argumentwise, or `undefined` where their shapes
   * leave nothing better than top or bottom to say.
   *
   * Nominal, so two names that differ have nothing between them either way --
   * there is no structure to walk and no third datatype to appeal to. Same
   * name, and each argument goes where its parameter's variance sends it,
   * which is `#lattice`'s question and not this one's: a covariant argument
   * the way the pair went, a contravariant one the other way, and an invariant
   * one nowhere. That last has no answer, so neither does the datatype around
   * it -- there is no `Foo` between two that disagree on an argument that
   * cannot move.
   */
  #latticeData(
    s: Extract<Type, { kind: "TData" }>,
    t: Extract<Type, { kind: "TData" }>,
    dir: Direction,
  ): Type | undefined {
    if (s.name !== t.name || s.args.length !== t.args.length) return undefined;
    const args = [];
    for (const [i, mine] of s.args.entries()) {
      const other = t.args[i] ?? impossible("arities agree above");
      const arg = this.#lattice(
        mine,
        other,
        composeVariance(dir, argVarianceOf(s, i)),
      );
      if (arg === undefined) return undefined;
      args.push(arg);
    }
    return TData(s, args);
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
   * fresh group carrying the combined bounds, as in `#relateFun` -- except
   * that a *type* comes back out, so it is closed again over the group. Only
   * the arities have no answer.
   */
  #latticeFun(
    s: Extract<Type, { kind: "TFun" }>,
    t: Extract<Type, { kind: "TFun" }>,
    dir: Direction,
  ): Type | undefined {
    if (s.typeParams.length !== t.typeParams.length) return undefined;
    if (s.params.length !== t.params.length) return undefined;

    return this.context.inScope((mark) => {
      // Bounds are parallel -- they read in the enclosing scope -- so they are
      // combined before anything is pushed, and need no closing after.
      // A direction flips to a direction, so no part of an arrow is ever
      // asked for at an invariant position and none of these can decline.
      const inner = flip(dir);

      const typeParams: TypeParamInfo[] = [];
      for (const [j, binder] of s.typeParams.entries()) {
        const other = t.typeParams[j];
        if (other === undefined) return undefined;
        typeParams.push(
          mkTypeParamInfo(
            binder.hint,
            this.#lattice(binder.bound, other.bound, inner),
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
              inner,
            ),
            mark,
          ),
        );
      }

      const result = closeFrom(
        this.#lattice(
          openMany(s.result, opened),
          openMany(t.result, opened),
          dir,
        ),
        mark,
      );
      return TFun(typeParams, params, result);
    });
  }

  // --------------------------------------------------------- solving a batch

  /**
   * Solve one EVar, given how it occurs in the type the application hands back.
   *
   * Both bounds are computed, never one: they are peers, and which is the
   * answer is what the entry's occurrences decide. The lower is the join of
   * every lower constraint and the upper the meet of every upper one, so a
   * later constraint narrows the range rather than replacing what stood there.
   *
   * `lower <: upper` first, or the constraints have no solution at all --
   * which is also the check that keeps a callee's declared bound honest, that
   * bound being an upper constraint like any other. Then the selection:
   * covariant occurrences take the *lower* bound, the smallest type the
   * constraints admit and so the most informative, which is what makes the
   * answer principal rather than merely sound; contravariant ones take the
   * upper, dually.
   *
   * Occurring both ways, or inside an invariant `TData` argument, neither
   * bound is the answer by position, since widening either way breaks the
   * other. Three cases, and only the last is a choice at all.
   *
   * Bounded from one side only, the other bound is the *default* extreme --
   * `never` or `unknown` recorded by nobody -- and no evidence to weigh
   * against a demand. The demand decides, silently, nothing having been
   * chosen. This is what settles a staged call:
   *
   *     let apply = fn [A](x: A) -> fn (f: (A) -> A) -> f(x)
   *     apply(True)(fn (y) -> y)
   *
   * `?A` occurs invariantly in `((A) -> A) -> A` -- covariantly as the result,
   * contravariantly inside the parameter -- and `True` bounds it only from
   * below, so `Bool` is the only type any argument asked for.
   *
   * Bounded from both sides by equivalent types, there is likewise nothing to
   * choose and either may be taken.
   *
   * Bounded from both sides by types that differ, the two results are
   * *incomparable*, so the lower bound is taken for being the demand and a
   * warning says it was. A warning and not a failure: every constraint is
   * satisfied by that choice, so nothing downstream is unsound -- what it is
   * not is *principal*, and a settling that went unsaid would hide that a
   * choice was made where the author is the one who knows.
   *
   * A variable occurring nowhere in the result is not this case at all: the
   * solution goes into the result type and the result type has no place for
   * it, so nothing can tell the bounds apart and no choice is one. It takes
   * the lower for having nothing to argue with.
   *
   * A variable nothing constrained at all is not a further case: both bounds
   * are then the default extreme, and the occurrence reads that pair as it
   * reads any other. `Nil()` is `List[never]` because that is what the program
   * says, not a guess standing in for what an author left out.
   *
   * The relation tests here mutate, as everywhere -- but never this batch.
   * Every recorded bound is closed by `batch`, so no sibling can pick up a
   * bound while its neighbours are being decided, which is what would make the
   * order of this loop matter.
   *
   * One tank for the whole of it. Joining the bounds, meeting them and
   * comparing the two are parts of one ask, not three asks that happen to
   * follow each other, and running dry in any of them is the same event: the
   * checker's limit, said in those words and answered with `TBad`, which is
   * the one answer that cannot go on to be wrong somewhere else.
   */
  solveEVar(entry: EVarEntry, at: Position): Type {
    return this.#query(at, () => this.#solveEVar(entry), () => {
      return badUnder(this.#file(
        "error",
        `gave up inferring the type argument ${entry.hint}: its constraints ` +
          `ran too deep`,
      ));
    });
  }

  /** `solveEVar` inside its tank, so every relation below spends the one. */
  #solveEVar(entry: EVarEntry): Type {
    const { covariantly, contravariantly } = entry;
    const lower = this.#joinMany(entry.lower);
    const upper = this.#meetMany(entry.upper);

    if (!this.#subtype(lower, upper)) {
      return badUnder(this.#file(
        "error",
        `cannot infer the type argument ${entry.hint}: it is bounded below ` +
          `by ${typeToString(lower)} and above by ${typeToString(upper)}, ` +
          `and no type is both`,
      ));
    }

    // Below here the bounds are ordered, so every answer satisfies every
    // constraint and the only question left is which is the *general* one.
    if (covariantly && !contravariantly) return lower;
    if (contravariantly && !covariantly) return upper;

    if (covariantly && contravariantly) {
      // One side demanded, the other left at its default: no choice to make.
      if (entry.upper.length === 0) return lower;
      if (entry.lower.length === 0) return upper;

      // With the check above, this makes the bounds equivalent: either does.
      if (this.#subtype(upper, lower)) return lower;

      // Two demands that differ, so the choice is real and gets said.
      this.#file(
        "warning",
        `the type argument ${entry.hint} occurs invariantly, and the ` +
          `arguments bound it between ${typeToString(lower)} and ` +
          `${typeToString(upper)}, so it was taken to be ` +
          `${typeToString(lower)}; give it explicitly if that is not what ` +
          `was meant`,
      );
      return lower;
    }

    // Occurring nowhere, so nothing can tell the bounds apart.
    return lower;
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
      // The scope covers the collecting and not the deciding. Every bound is
      // closed by `batch` when it is recorded, so a solution is built from
      // types that never named the entries anyway -- and solving with them
      // already popped is what makes the check below structural rather than a
      // promise. What the entries still carry is their own bounds, which are
      // ordinary objects and outlive the levels that held them.
      const batch = this.context.inScope(() => {
        // Read before the push, which is where `EVarEntry` reads its own
        // `batch` from, so the two agree by construction. Restored rather than
        // cleared: batches never nest, and a `finally` that assumed so would
        // be the one place saying it twice.
        const outerBatch = this.#liveBatch;
        this.#liveBatch = this.context.size;
        try {
          const entries = this.context.pushEVarBatch(hints);
          body(entries.map((entry) => entry.ref));
          return entries;
        } finally {
          this.#liveBatch = outerBatch;
        }
      });

      // A variable given up on answers `TBad`, and needs nothing special to:
      // whoever gave up recorded `TBad` as the bound, and it stays `TBad`
      // through the lattice. Checking against a bad type always succeeds, so
      // one type argument nobody could infer does not fail again wherever the
      // result is used.
      const solutions = batch.map((entry) => this.solveEVar(entry, at));
      this.context.assertClosed("a batch's solutions", solutions);
      return solutions;
    } finally {
      this.#at = outer;
    }
  }
}
