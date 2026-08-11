/**
 * The typing context: a single *ordered* list holding universals, EVars,
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
 * or substituted first. That is a checker invariant, not a hope: `assertLeft`
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
  occurs,
  TData,
  TFun,
  type Type,
} from "./types.ts";

export type Entry =
  /**
   * `X <: bound` -- rigid, never solved. `name` is what elaboration resolves a
   * source type name against, so unlike `Binder.hint` it is load-bearing
   * rather than decoration.
   */
  | { readonly kind: "Universal"; readonly name: string; readonly bound: Type }
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
  /** `type` mentions the variable itself; solving would build an infinite type. */
  | { readonly kind: "occurs" }
  /**
   * `type` mentions something bound at or after it, so the solution would
   * escape its scope.
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

  entryAt(level: Level): Entry | undefined {
    return this.#entries[level];
  }

  /** Append at the right -- the innermost position -- and hand back its level. */
  push(entry: Entry): Level {
    this.#entries.push(entry);
    return mkLevel(this.#entries.length - 1);
  }

  pushUniversal(name: string, bound: Type): Level {
    return this.push({ kind: "Universal", name, bound });
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
   */
  addBound(level: Level, side: "lower" | "upper", type: Type): void {
    const entry = this.evarAt(level);
    if (entry === undefined) return;
    this.assertClosed(`bound on ?${entry.name}`, [type], level);
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

  /** The entries pushed since `size`, innermost last. */
  since(size: number): readonly Entry[] {
    return this.#entries.slice(size);
  }

  /**
   * Assert that `types` may outlive a scope ending at `levels` -- none may
   * mention a level the truncation is about to drop, nor carry a `BVar` beyond
   * `depth` enclosing binders.
   *
   * `depth` is not decoration. What outlives a scope is usually something the
   * scope was just abstracted *into*, so a constructor's fields legitimately
   * carry `BVar j` for each of the datatype's parameters and must be checked at
   * `depth = arity`. Only a self-contained type checks at zero.
   *
   * A failure is a checker bug, not a program error, so it throws rather than
   * joining the diagnostics.
   */
  assertClosed(
    what: string,
    types: readonly Type[],
    levels: number,
    depth = 0,
  ): void {
    for (const type of types) {
      if (!isClosed(type, levels, depth)) {
        throw new Error(
          `${what}: a type escaped a scope closed by ` +
            `${levels} levels and ${depth} binders`,
        );
      }
    }
  }

  /** Upper bound of the universal at `level`, or `undefined` if it is not one. */
  boundOf(level: Level): Type | undefined {
    const entry = this.#entries[level];
    return entry?.kind === "Universal" ? entry.bound : undefined;
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
      if (entry?.kind === "Universal" && entry.name === name) {
        return { level: mkLevel(i), bound: entry.bound };
      }
    }
    return undefined;
  }

  /** Solution of the EVar at `level`, or `undefined` if unsolved. */
  solutionOf(level: Level): Type | undefined {
    const entry = this.#entries[level];
    return entry?.kind === "EVar" ? entry.solution : undefined;
  }

  /**
   * Solve `level := type` in place, or explain why not -- `undefined` means it
   * took. The escape check is what the ordering buys: a solution may only
   * mention entries strictly to the left, which is `isClosed(type, level)`.
   */
  solve(level: Level, type: Type): SolveFailure | undefined {
    const entry = this.#entries[level];
    if (entry?.kind !== "EVar") return { kind: "unbound" };
    if (entry.solution !== undefined) {
      return { kind: "alreadySolved", existing: entry.solution };
    }
    if (occurs(level, type)) return { kind: "occurs" };
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
        const solution = this.solutionOf(type.level);
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
