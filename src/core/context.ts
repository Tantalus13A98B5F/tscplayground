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
 * `size` *is* the marker.
 *
 * Truncation reuses levels, so anything outliving a scope must have been closed
 * or substituted first. `assertClosed` checks that at every exit.
 *
 * Reads and writes by level are total. A level comes from a `push` or off a
 * node the checker built, so one naming nothing -- or naming an entry of the
 * wrong kind -- is a checker bug and throws. Resolving a *name* is the other
 * question, and that one may legitimately come back empty.
 *
 * One namespace across all of it. A term variable, a constructor, and a type
 * variable of the same name shadow each other rather than coexisting, so the
 * innermost binding is always the answer and being the wrong kind makes a name
 * unusable rather than sending the lookup further out. Type *declarations* are
 * the other namespace, unshadowable, and live in `Declarations`.
 *
 * Not every entry has a name. An EVar and the variables subtyping opens a
 * quantifier under are reached from a node carrying their level, so what they
 * carry is a `hint` that prints and nothing resolves.
 *
 * Nothing here backtracks. Subtyping collects bounds and solves once per
 * argument list rather than speculatively, so no operation is ever undone.
 */

import {
  bothPolarities,
  isClosed,
  type Level,
  mkLevel,
  mkTypeParamInfo,
  type Polarity,
  TData,
  TFun,
  type Type,
} from "./types.ts";

/**
 * `X <: bound` -- rigid, never solved.
 *
 * `name` is load-bearing where `TypeParamInfo.hint` is decoration. Elaboration
 * is not a pass that runs to completion first -- a type written inside a term
 * is elaborated when checking reaches it, against this context -- so
 * `lookupTypeVar` resolves against these names for as long as checking runs.
 *
 * `undefined` where nothing will ever resolve one: the variables subtyping
 * opens a pair of quantifiers under, and the wildcard `_`. Nameless and not
 * `name: ""`, so the type says which entries can be looked up.
 */
export type TypeVarEntry = {
  readonly kind: "TypeVar";
  readonly name: string | undefined;
  readonly bound: Type;
};

/**
 * `?a`, or `?a = solution` once solved.
 *
 * Constraints accumulate here rather than being solved on sight: a whole
 * argument list contributes before anything is decided, so the solution is
 * the join of the lower bounds rather than whichever argument came first.
 * Every recorded bound is already avoided -- closed by this EVar's `batch` --
 * so `setSolution` can never be handed something out of scope.
 *
 * Most of this entry is written after it is pushed and read once the batch is
 * solved: `lower` and `upper` grow, `polarity` combines, `reported` latches.
 * `solution` is written once, so it is `readonly` and solving replaces the
 * entry -- a guardrail against an assignment that missed `setSolution`.
 *
 * `hint` and not `name`: an EVar is reached from an `FVar` carrying its level,
 * never by name, so this is what a diagnostic prints and nothing else.
 */
export type EVarEntry = {
  readonly kind: "EVar";
  readonly hint: string;
  /**
   * Where the group this EVar was created with begins -- one argument list's
   * worth, and the unit `Subtyper.withEVars` decides at once.
   *
   * Carried because a constraint may not mention *any* EVar of its own batch,
   * not merely one to its right. Leftward looks harmless, the solver going
   * ascending, but `?a`'s choice is made by polarity in the *result type*
   * alone, blind to `?a` standing inside `?b`'s pending bounds. Refusing the
   * dependency keeps every batch a set of independent variables, which is the
   * condition under which per-variable polarity is the whole story.
   *
   * Stated as the batch's rule even though nothing tells batch from context
   * apart any more -- `withEVars` runs only once every argument is checked, so
   * two batches never overlap -- because the group deciding together is what
   * makes the dependency unseeable.
   */
  readonly batch: number;
  readonly lower: Type[];
  readonly upper: Type[];
  /**
   * How this EVar occurs in the type its application hands back, which is what
   * decides between its two bounds.
   *
   * Recorded by the opening that puts the variable into that result. `none`
   * until noted, and `none` forever for a variable the result never mentions:
   * the two are the same answer, since nothing downstream can tell which bound
   * such a variable took.
   */
  polarity: Polarity;
  /**
   * Whether a constraint refused as interdependent already accounts for this
   * EVar. Without it such a variable looks like one nothing ever tried to
   * constrain, and the solver tells the same mistake a second time, naming a
   * type parameter where the first telling named what the author wrote.
   */
  reported: boolean;
  readonly solution?: Type;
};

/** `x : type`, or the wildcard `_`, which binds a position and no name. */
export type TermVarEntry = {
  readonly kind: "TermVar";
  readonly name: string | undefined;
  readonly type: Type;
};

/** What the context holds, in one ordered list. */
export type Entry = TypeVarEntry | EVarEntry | TermVarEntry;

/**
 * What resolving a name yields: the level is the binding's *identity*, the
 * entry what sits there. `E` narrows it, so `lookupTerm` reaches a `type`
 * without a second test.
 */
export type Binding<E extends Entry = Entry> = {
  readonly level: Level;
  readonly entry: E;
};

export class Context {
  readonly #entries: Entry[] = [];

  /**
   * Every named entry's levels, innermost last, so resolving a name is the top
   * of its stack rather than a scan back through the whole context.
   *
   * Truncation knows exactly which entries it drops and pops them on the way
   * out, so nothing persistent is needed: O(1) amortised per binding.
   */
  readonly #levelsByName = new Map<string, Level[]>();

  /**
   * How many entries are in scope, and equally the next level to be handed
   * out. Save one to open a scope, pass it to `truncate` to close it.
   */
  get size(): number {
    return this.#entries.length;
  }

  /**
   * The entries, for tests and diagnostics. `readonly` covers the array only,
   * so what stops a caller writing through an entry is that entry's own fields.
   */
  get entries(): readonly Entry[] {
    return this.#entries;
  }

  /**
   * Append at the right -- the innermost position -- and hand back its level,
   * indexing the entry under its name if it has one.
   */
  #push(entry: Entry): Level {
    const level = mkLevel(this.#entries.length);
    this.#entries.push(entry);

    const name = entry.kind === "EVar" ? undefined : entry.name;
    if (name !== undefined) {
      const levels = this.#levelsByName.get(name);
      if (levels === undefined) this.#levelsByName.set(name, [level]);
      else levels.push(level);
    }
    return level;
  }

  /**
   * A rigid type variable. Omit `name` for one nothing reaches: subtyping
   * opening a quantifier, or a wildcard parameter. It still holds a position,
   * so its `BVar` has something to open onto -- unnameable, not absent.
   */
  pushTypeVar(bound: Type, name?: string): Level {
    return this.#push({ kind: "TypeVar", name, bound });
  }

  /**
   * A whole batch of EVars at once -- one per type parameter of the callee
   * being instantiated, which is the only place they arise.
   *
   * Pushed together so `batch` cannot be got wrong: it is the size before the
   * first, so every member agrees on where the group starts.
   */
  pushEVarBatch(hints: readonly string[]): Level[] {
    const batch = this.size;
    return hints.map((hint) =>
      this.#push({
        kind: "EVar",
        hint,
        batch,
        lower: [],
        upper: [],
        polarity: "none",
        reported: false,
      })
    );
  }

  /**
   * A batch of one: its batch begins at its own level, so it has no siblings
   * to be refused a dependency on. Two of these are two batches, not one.
   *
   * Only tests reach for this; the checker instantiates a whole callee.
   */
  pushEVar(hint: string): Level {
    const [level] = this.pushEVarBatch([hint]);
    if (level === undefined) throw new Error("pushEVar pushed nothing");
    return level;
  }

  /**
   * The entry at `level`. Total: a level comes from a `push` or off a node the
   * checker built, so naming nothing -- or an entry of the wrong kind -- is a
   * checker bug. `lookup` is where a question may come back empty.
   */
  #entryAt<K extends Entry["kind"]>(
    level: Level,
    kind: K,
  ): Extract<Entry, { kind: K }> {
    const entry = this.#entries[level];
    if (entry === undefined) {
      throw new Error(
        `level ${level} names no entry: the context holds ${this.size}`,
      );
    }
    if (entry.kind !== kind) {
      throw new Error(
        `level ${level} holds a ${entry.kind}, asked for a ${kind}`,
      );
    }
    return entry as Extract<Entry, { kind: K }>;
  }

  /** The EVar at `level`. Total, so the level must name one. */
  evarAt(level: Level): EVarEntry {
    return this.#entryAt(level, "EVar");
  }

  /**
   * The EVar at `level`, or `undefined` if the level holds something else.
   *
   * The one read by level allowed to come back empty, because an `FVar` does
   * not say which kind it names -- rigid variables and EVars share the level
   * space. Every rule that treats a variable as rigid asks this first;
   * `evarAt` stays total for the callers that already know.
   */
  evarOrUndefined(level: Level): EVarEntry | undefined {
    const entry = this.#entries[level];
    if (entry === undefined) {
      throw new Error(
        `level ${level} names no entry: the context holds ${this.size}`,
      );
    }
    return entry.kind === "EVar" ? entry : undefined;
  }

  /**
   * Record `T <: ?a` or `?a <: T`. The bound must already be avoided -- closed
   * by `level` -- since an EVar's constraints may only mention what stands to
   * its left, exactly as its eventual solution must.
   *
   * The bar is the *batch*, not the level: between the two stand only this
   * EVar's siblings, and a sibling is refused even leftward (see
   * `EVarEntry.batch`). A caller decides that first and reports it as
   * `interdependent` where it is the program's doing, so reaching here with
   * one is a checker bug and throws.
   */
  addConstraint(level: Level, side: "lower" | "upper", type: Type): void {
    const entry = this.evarAt(level);
    // Not `assertClosed`: the bar is this batch, not the context's watermark,
    // and everything to its right is legitimately still standing.
    if (!isClosed(type, entry.batch)) {
      throw new Error(
        `bound on ?${entry.hint}: mentions something at or past level ` +
          `${entry.batch}, where its batch begins`,
      );
    }
    entry[side].push(type);
  }

  /**
   * Note that this EVar stands at `polarity` in its application's result,
   * combining with wherever else it stands: two occurrences that disagree make
   * it invariant, which is the case admitting no principal choice.
   */
  notePolarity(level: Level, polarity: Polarity): void {
    const entry = this.evarAt(level);
    entry.polarity = bothPolarities(entry.polarity, polarity);
  }

  /**
   * Note that a diagnostic already accounts for this EVar. Recorded on the
   * variable because that is what the solver will be looking at, long after the
   * argument that caused it has been left behind.
   */
  noteReported(level: Level): void {
    this.evarAt(level).reported = true;
  }

  /** The same for a term: omit `name` for a wildcard, which binds a position
   * and nothing else. */
  pushTermVar(type: Type, name?: string): Level {
    return this.#push({ kind: "TermVar", name, type });
  }

  /**
   * Drop everything pushed since `size`. Ends a scope in one step; whatever was
   * introduced inside it goes away together.
   *
   * Innermost first, so each name's stack is unwound in the order it was built
   * and the binding revealed is the one that was shadowed.
   */
  truncate(size: number): void {
    const target = Math.min(size, this.#entries.length);
    for (let i = this.#entries.length - 1; i >= target; i--) {
      const entry = this.#entries[i];
      const name = entry === undefined || entry.kind === "EVar"
        ? undefined
        : entry.name;
      if (name === undefined) continue;
      const levels = this.#levelsByName.get(name);
      levels?.pop();
      if (levels?.length === 0) this.#levelsByName.delete(name);
    }
    this.#entries.length = target;
  }

  /**
   * Run `body` in a scope of its own, handing it the mark and truncating to it
   * however the body leaves -- returning or throwing.
   *
   * The `finally` does not make a throw recoverable; everything thrown here is
   * a bug and the run is over. It is so that the bug reported is the *first*
   * one: a scope abandoned mid-flight leaves entries standing that the next
   * `assertClosed` would trip over, naming a scope with nothing wrong with it.
   *
   * Close inside, assert outside. What the body hands back is already
   * abstracted over `mark`, so the assertion reads against the context as it
   * stands.
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
   * watermark a survivor must sit under is `size`.
   *
   * `depth` is not decoration. What outlives a scope is usually something the
   * scope was just abstracted *into*, so a constructor's fields carry `BVar j`
   * per datatype parameter and must be checked at `depth = arity`.
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
   * The *declared* upper bound of the type variable at `level`. Total, like
   * every read by level -- and total in a second sense: an unbounded variable
   * stores `TUnknown`, so there is no "no bound" answer either.
   *
   * Not `Subtyper.solveUpperBoundOf`, which meets an EVar's collected upper
   * constraints. This one reads a binder, that one solves.
   */
  upperBoundAt(level: Level): Type {
    return this.#entryAt(level, "TypeVar").bound;
  }

  /** The innermost binding of `name`, whatever kind it turned out to be. */
  lookup(name: string): Binding | undefined {
    const levels = this.#levelsByName.get(name);
    const level = levels?.[levels.length - 1];
    if (level === undefined) return undefined;
    const entry = this.#entries[level];
    return entry === undefined ? undefined : { level, entry };
  }

  /**
   * Resolve `name` as a term. The lookup stops at the innermost binding, so a
   * type variable of the same name does not hide behind it -- it shadows, and
   * the answer is that `name` is not a term here.
   */
  lookupTerm(name: string): Binding<TermVarEntry> | undefined {
    const found = this.lookup(name);
    return found?.entry.kind === "TermVar"
      ? { level: found.level, entry: found.entry }
      : undefined;
  }

  /**
   * The same, as a type variable. `undefined` does not settle the name: type
   * *declarations* are the other namespace, so `#elaborateName` goes on to ask
   * the aliases and datatypes, which no binder here can shadow.
   */
  lookupTypeVar(name: string): Binding<TypeVarEntry> | undefined {
    const found = this.lookup(name);
    return found?.entry.kind === "TypeVar"
      ? { level: found.level, entry: found.entry }
      : undefined;
  }

  /**
   * Solve `level := type` in place. The escape check is what the ordering
   * buys: a solution may only mention entries strictly to the left, which is
   * `isClosed(type, level)`. No separate occurs check, that being the same
   * question about one level.
   *
   * Throws rather than reporting: solving twice, solving a level holding no
   * EVar, and solving to something that escapes are all checker bugs.
   */
  setSolution(level: Level, type: Type): void {
    const entry = this.evarAt(level);
    if (entry.solution !== undefined) {
      throw new Error(`?${entry.hint} is already solved`);
    }
    if (!isClosed(type, level)) {
      throw new Error(
        `solution for ?${entry.hint} escapes: it mentions something at or ` +
          `past level ${level}`,
      );
    }
    this.#entries[level] = { ...entry, solution: type };
  }

  /**
   * Apply the context as a substitution: replace every solved EVar by its
   * solution.
   *
   * Called from exactly one place, the end of `Subtyper.withEVars`, which is
   * the whole of an EVar's life: a batch is pushed, two relations record
   * against it, it is solved, and this carries the answers out. Nothing
   * upstream holds a type naming one.
   *
   * One pass, no chain to follow: a solution is built from recorded bounds,
   * `#constrain` refuses a bound mentioning any EVar of the batch, and two
   * batches never overlap.
   */
  apply(type: Type): Type {
    switch (type.kind) {
      case "TUnknown":
      case "TNever":
      case "TBad":
      case "BVar":
        return type;
      case "FVar": {
        // A rigid variable substitutes to itself, and an unsolved EVar stands
        // as it is -- so the level is asked, and both non-answers are the same
        // answer.
        const entry = this.evarOrUndefined(type.level);
        const solution = entry?.solution;
        return solution ?? type;
      }
      case "TFun":
        return TFun(
          type.typeParams.map((b) =>
            mkTypeParamInfo(b.hint, this.apply(b.bound))
          ),
          type.params.map((param) => this.apply(param)),
          this.apply(type.result),
        );
      case "TData":
        return TData(type.name, type.args.map((arg) => this.apply(arg)));
    }
  }
}
