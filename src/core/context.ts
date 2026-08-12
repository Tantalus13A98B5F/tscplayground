/**
 * The typing context: a single *ordered* list holding type variables, EVars,
 * and term bindings.
 *
 * Order is the point twice over. An EVar's solution may only mention
 * entries strictly to its left, so well-scopedness is a position comparison
 * rather than a side table that can be forgotten. And a free variable's
 * identity *is* its position -- a de Bruijn level -- so allocating one is
 * `size`, resolving one is an array index, and there is no counter anywhere.
 *
 * Entries are stored outermost-first, so "to the left" is "at a lower level".
 * An entry does not carry its own level: the position is the level, and a
 * stored copy could only desync with it.
 *
 * Mutable, and deliberately so: the checker threads one context through the
 * whole run, and scopes end by truncation. There is no marker entry -- a saved
 * `size` *is* the marker, exact where a search for a marker entry could come up
 * empty.
 *
 * Truncation reuses levels, so anything outliving a scope must have been closed
 * or substituted first. That is a checker invariant, not a hope: `assertClosed`
 * checks it at every exit, and turns what would be a silent alias into a loud
 * failure.
 *
 * Nothing here backtracks. Subtyping collects bounds and solves once per
 * argument list rather than speculatively, so no operation is ever undone.
 */

import {
  isClosed,
  type Level,
  mkBinder,
  mkLevel,
  TData,
  TFun,
  type Type,
} from "./types.ts";

export type Entry =
  /**
   * `X <: bound` -- rigid, never solved.
   *
   * `name` is load-bearing where `Binder.hint` is decoration, and it is not
   * spent by the time an entry gets here: elaboration is not a pass that runs
   * to completion first. A type written inside a term -- a parameter's
   * annotation, a bound on a `fn`'s own type parameter -- is elaborated when
   * checking reaches it, against this context, because the binder it sits
   * under is only in scope then. So `lookupTypeVar` resolves against these
   * names for as long as checking runs.
   */
  | { readonly kind: "TypeVar"; readonly name: string; readonly bound: Type }
  /**
   * `?a`, or `?a = solution` once solved.
   *
   * Constraints accumulate here rather than being solved on sight: a whole
   * argument list contributes before anything is decided, so the solution is
   * the join of the lower bounds rather than whichever argument came first.
   * Every recorded bound is already avoided -- closed by this EVar's own level
   * -- so `solve` can never be handed something out of scope.
   */
  | {
    readonly kind: "EVar";
    readonly name: string;
    readonly lower: Type[];
    readonly upper: Type[];
    readonly solution?: Type;
  }
  /** `x : type` */
  | { readonly kind: "TermVar"; readonly name: string; readonly type: Type };

/** What resolving a name in the term namespace yields. */
export type TermBinding = {
  readonly level: Level;
  readonly type: Type;
};

/** What resolving a name in the type namespace yields. */
export type TypeBinding = {
  readonly level: Level;
  readonly bound: Type;
};

export type SolveFailure =
  /** `level` is not an EVar of this context. */
  | { readonly kind: "unbound" }
  /** It already has a solution. */
  | { readonly kind: "alreadySolved"; readonly existing: Type }
  /**
   * `type` mentions something bound at or after it, so the solution would
   * escape its scope. That covers `type` mentioning the variable itself, which
   * sits at its own level and so is not to the left of it either.
   */
  | { readonly kind: "escapes" };

export class Context {
  readonly #entries: Entry[] = [];

  /**
   * How many entries are in scope, and equally the next level to be handed
   * out. Save one to open a scope, pass it to `truncate` to close it.
   */
  get size(): number {
    return this.#entries.length;
  }

  /** Read-only view, for tests and diagnostics. Nothing should mutate it. */
  get entries(): readonly Entry[] {
    return this.#entries;
  }

  /** Append at the right -- the innermost position -- and hand back its level. */
  push(entry: Entry): Level {
    this.#entries.push(entry);
    return mkLevel(this.#entries.length - 1);
  }

  pushTypeVar(name: string, bound: Type): Level {
    return this.push({ kind: "TypeVar", name, bound });
  }

  pushEVar(name: string): Level {
    return this.push({ kind: "EVar", name, lower: [], upper: [] });
  }

  /** The EVar at `level`, or `undefined` if that is not what lives there. */
  evarAt(level: Level): Extract<Entry, { kind: "EVar" }> | undefined {
    const entry = this.#entries[level];
    return entry?.kind === "EVar" ? entry : undefined;
  }

  /**
   * Record `T <: ?a` or `?a <: T`. The bound must already be avoided -- closed
   * by `level` -- since an EVar's constraints may only mention what stands to
   * its left, exactly as its eventual solution must.
   *
   * `level` and not the mark the whole batch was inserted at, which would be
   * the stronger bar: no constraint mentioning *any* EVar of its own batch.
   * That is deliberate. Leftward is not the interdependent case -- it is a
   * dependency order the solver already follows, solving ascending and
   * applying each solution before storing it, so `?a` is concrete by the time
   * `?b` is decided. What is genuinely circular always points rightward too,
   * and `#constrain` refuses it there. Tightening to the batch mark would cost
   * `?a <: ?b` and buy nothing.
   */
  addConstraint(level: Level, side: "lower" | "upper", type: Type): void {
    const entry = this.evarAt(level);
    if (entry === undefined) return;
    // Not `assertClosed`: the bar is this EVar's level, not the context's
    // watermark, and everything to its right is legitimately still standing.
    if (!isClosed(type, level)) {
      throw new Error(
        `bound on ?${entry.name}: mentions something at or past level ${level}`,
      );
    }
    entry[side].push(type);
  }

  pushTermVar(name: string, type: Type): Level {
    return this.push({ kind: "TermVar", name, type });
  }

  /**
   * Drop everything pushed since `size`. Ends a scope in one step; whatever was
   * introduced inside it goes away together.
   */
  truncate(size: number): void {
    this.#entries.length = Math.min(size, this.#entries.length);
  }

  /**
   * Run `body` in a scope of its own, handing it the mark and truncating to it
   * however the body leaves -- returning or throwing.
   *
   * The `finally` is not there to make a throw recoverable. Everything thrown
   * in this checker is a bug, and the run is over. It is there so that the bug
   * reported is the first one: a scope abandoned mid-flight leaves entries
   * standing that the next `assertClosed` would trip over, and *that* failure
   * is what would surface, naming a scope with nothing wrong with it.
   *
   * Being one form also makes the pairing visible. A mark taken and truncated
   * fifty lines apart is a pairing only a reader keeps track of.
   *
   * Close inside, assert outside. `mark` is the scope's own business, so what
   * the body hands back is already abstracted over it and nothing downstream
   * needs the number; the assertion then reads against the context as it
   * stands, which is what `assertClosed` asks about.
   */
  inScope<T>(body: (mark: number) => T): T {
    const mark = this.size;
    try {
      return body(mark);
    } finally {
      this.truncate(mark);
    }
  }

  /**
   * Assert that `types` are closed under the context *as it now stands* -- the
   * scope-exit check, to be asked once a scope has ended. No mark to pass: the
   * watermark a survivor must sit under is `size`, and the context is the one
   * that knows it. A caller repeating its own `mark` here could only repeat it
   * wrongly.
   *
   * `depth` is not decoration. What outlives a scope is usually something the
   * scope was just abstracted *into*, so a constructor's fields legitimately
   * carry `BVar j` for each of the datatype's parameters and must be checked at
   * `depth = arity`. Only a self-contained type checks at zero.
   *
   * A failure is a checker bug, not a program error, so it throws rather than
   * joining the diagnostics.
   */
  assertClosed(what: string, types: readonly Type[], depth = 0): void {
    for (const type of types) {
      if (!isClosed(type, this.size, depth)) {
        throw new Error(
          `${what}: a type escaped a scope closed by ` +
            `${this.size} levels and ${depth} binders`,
        );
      }
    }
  }

  /**
   * The *declared* upper bound of the type variable at `level`, or `undefined`
   * if that is not what lives there. Named for the side it takes because a
   * bounded-below type variable would want the other, and `boundOf` would then
   * name neither.
   *
   * Not to be confused with `Subtyper.upperBoundOf`, which is the same words
   * about a different thing: the meet of an EVar's collected upper constraints.
   * This one reads a binder, that one solves.
   */
  upperBoundOf(level: Level): Type | undefined {
    const entry = this.#entries[level];
    return entry?.kind === "TypeVar" ? entry.bound : undefined;
  }

  /**
   * Resolve `name` in the term namespace, innermost binding first -- so an
   * inner binder shadows an outer one rather than colliding with it.
   */
  lookupTerm(name: string): TermBinding | undefined {
    for (let i = this.#entries.length - 1; i >= 0; i--) {
      const entry = this.#entries[i];
      if (entry?.kind === "TermVar" && entry.name === name) {
        return { level: mkLevel(i), type: entry.type };
      }
    }
    return undefined;
  }

  /**
   * Resolve `name` in the type namespace, innermost first. Type variables live
   * in their own namespace, so a type variable and a term variable may share a
   * name without either hiding the other.
   */
  lookupTypeVar(name: string): TypeBinding | undefined {
    for (let i = this.#entries.length - 1; i >= 0; i--) {
      const entry = this.#entries[i];
      if (entry?.kind === "TypeVar" && entry.name === name) {
        return { level: mkLevel(i), bound: entry.bound };
      }
    }
    return undefined;
  }

  /**
   * Solve `level := type` in place, or explain why not -- `undefined` means it
   * took. The escape check is what the ordering buys: a solution may only
   * mention entries strictly to the left, which is `isClosed(type, level)`.
   * No separate occurs check, that being the same question about one level.
   */
  setSolution(level: Level, type: Type): SolveFailure | undefined {
    const entry = this.#entries[level];
    if (entry?.kind !== "EVar") return { kind: "unbound" };
    if (entry.solution !== undefined) {
      return { kind: "alreadySolved", existing: entry.solution };
    }
    if (!isClosed(type, level)) return { kind: "escapes" };

    this.#entries[level] = { ...entry, solution: type };
    return undefined;
  }

  /**
   * Apply the context as a substitution: replace every solved EVar by
   * its solution, repeatedly, since one solution may mention another.
   *
   * Termination rests on the escape check in `solve`: a solution only mentions
   * EVars to its left, so the chain strictly decreases in level.
   */
  apply(type: Type): Type {
    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      case "BVar":
      case "FVar":
        return type;
      case "EVar": {
        // Two questions, so two `undefined`s, and they must not be conflated:
        // no EVar at that level is a checker bug, an unsolved one is the
        // ordinary case. Asking through `evarAt` keeps them apart.
        const solution = this.evarAt(type.level)?.solution;
        return solution === undefined ? type : this.apply(solution);
      }
      case "TFun":
        return TFun(
          type.typeParams.map((b) => mkBinder(b.hint, this.apply(b.bound))),
          type.params.map((param) => this.apply(param)),
          this.apply(type.result),
        );
      case "TData":
        return TData(type.name, type.args.map((arg) => this.apply(arg)));
    }
  }
}
