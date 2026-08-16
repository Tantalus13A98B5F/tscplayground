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
 * Reads by level are total, and writes too. A level comes from a `push` or off
 * a node the checker built, so one naming nothing -- or naming an entry of the
 * wrong kind -- is a checker bug, and these throw rather than returning an
 * `undefined` a caller would have to invent an answer for. Resolving a *name*
 * is the other question, and that one may legitimately come back empty.
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
  isClosed,
  type Level,
  mkLevel,
  mkTypeParamInfo,
  TData,
  TFun,
  type Type,
} from "./types.ts";

/**
 * `X <: bound` -- rigid, never solved.
 *
 * `name` is load-bearing where `TypeParamInfo.hint` is decoration, and is
 * not spent by the time an entry gets here: elaboration is not a pass that runs
 * to completion first. A type written inside a term -- a parameter's
 * annotation, a bound on a `fn`'s own type parameter -- is elaborated when
 * checking reaches it, against this context, because the binder it sits
 * under is only in scope then. So `lookupTypeVar` resolves against these
 * names for as long as checking runs.
 *
 * `undefined` where nothing will ever resolve one: the variables subtyping
 * opens a pair of quantifiers under, and the wildcard `_`. Those are reached
 * from an `FVar` that already carries the level. Nameless and not
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
 * Every recorded bound is already avoided -- closed by this EVar's own level
 * -- so `setSolution` can never be handed something out of scope.
 *
 * `lower` and `upper` grow all through an argument list, so they are pushed
 * in place. `solution` is written once, so it is `readonly` and solving
 * replaces the entry -- a guardrail, not a guarantee: it catches an assignment
 * written by someone who missed `setSolution`, and TypeScript drops the
 * modifier the moment the entry is read at a type that lacks it.
 *
 * `hint` and not `name`: an EVar is reached from an `EVar` node carrying its
 * level, never by name, so this is what a diagnostic prints and nothing else.
 */
export type EVarEntry = {
  readonly kind: "EVar";
  readonly hint: string;
  /**
   * Where the group this EVar was created with begins -- one argument list's
   * worth, and the unit `#solveEVars` decides at once.
   *
   * Carried because a constraint may not mention *any* EVar of its own batch,
   * not merely one to its right. Leftward looks harmless -- the solver goes
   * ascending, so `?a` would be decided before `?b` reads it -- but the choice
   * it makes for `?a` is made by polarity in the *result type* alone, blind to
   * `?a` standing inside `?b`'s pending bounds. A principal choice there can
   * still be the wrong one here, and the failure surfaces as a bound conflict
   * on `?b` that names nothing the author wrote. Refusing the dependency keeps
   * every batch a set of independent variables, which is the condition under
   * which per-variable polarity is the whole story.
   *
   * Only within a batch. An EVar of an *enclosing* argument list is already
   * solved or will be solved later by its own batch, and depending on one is
   * ordinary -- it is how a bare lambda's parameter type gets fixed.
   */
  readonly batch: number;
  readonly lower: Type[];
  readonly upper: Type[];
  /**
   * Whether a constraint on this EVar was refused rather than recorded -- the
   * interdependent case, already reported where it was refused.
   *
   * Without it the variable is indistinguishable from one nothing ever tried to
   * constrain, and the solver reports a second time that it cannot be inferred.
   * That is the same mistake twice, and the second telling names the type
   * parameter rather than the argument that caused it.
   */
  refused: boolean;
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
 * What resolving a name yields, the two halves not being peers: the level is
 * the binding's *identity*, the entry merely what sits there. `E` narrows it,
 * so `lookupTerm` reaches a `type` without a second test.
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
   * Nothing persistent is needed to survive `truncate`: truncation knows
   * exactly which entries it drops, and pops them on the way out. Each is
   * pushed once and popped at most once, so this costs O(1) amortised per
   * binding where a resolution alone used to cost O(size).
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
   * The entries, for tests and diagnostics. `readonly` covers the array only --
   * its length and which entries are in it -- so what stops a caller writing
   * through one is that entry's own fields, nothing here.
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
   * The group is pushed together so that `batch` cannot be got wrong: it is the
   * size before the first, so every member agrees on where the group starts,
   * where a mark passed in by a caller could drift from the pushes it describes.
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
        refused: false,
      })
    );
  }

  /**
   * A batch of one, which is what a lone EVar is: its batch begins at its own
   * level, so it has no siblings to be refused a dependency on. Two of these
   * are two batches, not one -- an argument list's worth must go through
   * `pushEVarBatch` to be a batch.
   */
  pushEVar(hint: string): Level {
    const [level] = this.pushEVarBatch([hint]);
    if (level === undefined) throw new Error("pushEVar pushed nothing");
    return level;
  }

  /**
   * The entry at `level`. Total: a level is only ever obtained from a `push`
   * or carried on a node the checker built, so one that names nothing -- or
   * names an entry of the wrong kind -- is a checker bug, and reads by level
   * say so rather than handing back an `undefined` a caller has to invent an
   * answer for. Resolving a *name* is the question that may legitimately come
   * back empty; `lookup` is where that is asked.
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
   * Record `T <: ?a` or `?a <: T`. The bound must already be avoided -- closed
   * by `level` -- since an EVar's constraints may only mention what stands to
   * its left, exactly as its eventual solution must.
   *
   * The bar is the *batch*, not the level. Between the two stand only this
   * EVar's own siblings -- a batch is pushed contiguously -- so the two bars
   * agree on every type variable and differ on exactly one thing: a sibling.
   * See `EVarEntry.batch` for why a sibling is refused even leftward.
   *
   * A caller is expected to have decided that already, and to have reported it
   * as `interdependent` where it is the program's doing. Reaching here with one
   * is a checker bug, so this throws.
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
   * Note that a constraint on this EVar was refused. Recorded on the variable
   * because that is what the solver will be looking at, long after the argument
   * that caused it has been left behind.
   */
  refuseConstraint(level: Level): void {
    this.evarAt(level).refused = true;
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
   * The *declared* upper bound of the type variable at `level`. Total, like
   * every read by level -- and total in a second sense: an unbounded variable
   * stores `TUnknown`, so there is no "no bound" answer either.
   *
   * Named for the side it takes, leaving room for a lower bound to be added
   * beside it under its own name. `boundOf` would then name neither.
   *
   * Not to be confused with `Subtyper.solveUpperBoundOf`, which is about a
   * different thing: the meet of an EVar's collected upper constraints. This
   * one reads a binder, that one solves.
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
   * Throws rather than reporting, for the reason the reads do. Solving twice,
   * solving a level that holds no EVar, and solving to something that escapes
   * are all checker bugs -- the solver decides each EVar once, at a point it
   * chose, from bounds `addConstraint` already checked. A returned failure
   * would only be a failure every caller ignored.
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
   * Apply the context as a substitution: replace every solved EVar by
   * its solution, repeatedly, since one solution may mention another.
   *
   * The recursion is load-bearing, and not in the way one batch would suggest.
   * Within a batch it is dead by construction: a constraint may not mention a
   * sibling at all, so no solution can name one.
   *
   * Chains come from *nested* argument lists. An inner one is solved while an
   * outer EVar is still open, and a bare lambda's parameter takes that outer
   * EVar as its type directly -- so in
   *
   *     let id = fn [B](y: B) -> y
   *     let f = fn [A](g: (A) -> A, a: A) -> g(a)
   *     f(fn (x) -> id(x), True)
   *
   * `?B := ?A` is stored with `?A` unsolved, and only the later `?A := Bool`
   * makes it a type. One hop, through a batch boundary.
   *
   * Termination rests on the escape check in `setSolution`: a solution only
   * mentions EVars to its left, so the chain strictly decreases in level.
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
        // One `undefined` now, and it means the ordinary thing: unsolved. The
        // other question -- whether the level holds an EVar at all -- is the
        // read itself, and it throws rather than answering.
        const solution = this.evarAt(type.level).solution;
        return solution === undefined ? type : this.apply(solution);
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
