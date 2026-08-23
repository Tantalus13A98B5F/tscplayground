/**
 * Internal type representation. Locally nameless: `BVar` under binders, `FVar`
 * free in the context. Invariants: a `BVar` never escapes into the context, an
 * `FVar` never appears under an unopened binder, and only `open*`/`close*` touch
 * index arithmetic.
 *
 * `TFun` is the only binder: quantification fuses into the arrow, so there is no
 * bare `forall`. Binders are n-ary and simultaneous -- the j-th variable is
 * `BVar j`, no telescope reversal. `params` and `result` sit inside the binder;
 * bounds are *parallel*, outside it, so a bound may name an enclosing binder but
 * never one of its own group.
 *
 * Variance lives here too, and opening is where it is read: a rule is told the
 * polarity of every position it fills, so a caller learns where a variable
 * stood without walking the answer again. `isClosed` threads `depth` the same
 * way, and `Subtyper`'s avoidance flips direction at the same places -- three
 * traversals that have to agree about what a position is.
 */

/**
 * A free variable's identity *is* its position in the context, so a level needs
 * no allocator: the next one is the context's size. Type variables and EVars
 * share the space, because scoping compares the two against each other: a
 * solution may only mention what stands to its left, whichever kind that is.
 *
 * Sharing the space is why they share a node. An `FVar` names a level and
 * nothing more; whether that level holds a rigid variable or one still being
 * inferred is the entry's business, asked through `Context.evarOrUndefined`.
 * A `kind` on the node would have been a second copy of that answer, and two
 * copies of one fact can disagree.
 */
export type Level = number & { readonly __brand: "Level" };
export type DataName = string & { readonly __brand: "DataName" };

export const mkLevel = (n: number): Level => n as Level;

/**
 * Say that a case cannot arise, and fail loudly if it does.
 *
 * For the index lookups the type checker cannot see through: two lists built to
 * the same length, or an opening reaching no index its binder did not bind.
 * `?? TBad` would satisfy the compiler equally, and that is the objection --
 * `TBad` means *an error was reported here*, and spending it on a case where
 * none was leaves the reader unable to tell the two apart.
 *
 * Returns `never`, so it composes with `??` at any type without a type
 * argument to keep in step.
 */
export function impossible(what: string): never {
  throw new Error(`${what}: a case that cannot arise, did`);
}
export const mkDataName = (s: string): DataName => s as DataName;

/**
 * One of a `TFun`'s quantified parameters. `hint` is for printing only -- the
 * variable itself is an index -- which is what distinguishes this from the
 * surface `BindingIdent`, whose text is a name something resolves against.
 */
export type TypeParamInfoMaybe<M> = {
  readonly hint: string;
  readonly bound: TypeMaybe<M>;
};

export type TypeParamInfo = TypeParamInfoMaybe<never>;

/**
 * The `TMissing` case, present only when `M` is inhabited. The conditional is
 * distributive, and distributing over `never` yields `never` -- so the case is
 * not merely uninhabitable at `TypeMaybe<never>`, it is *gone*, and a walk over
 * a complete type neither needs an arm for it nor is allowed one.
 */
type MissingPart<M> = M extends never ? never
  : { readonly kind: "TMissing" };

/**
 * A type, or a *pattern* -- a type with parts not yet supplied. `M` says
 * whether a missing part is possible, and the two instantiations are the names
 * anyone reads: `Type` and `TypePattern`.
 *
 * Since arrays here are `readonly` and so covariant, a complete type flows into
 * a pattern position with no coercion, which is the direction that matters --
 * subtyping and constraint solving take complete types only, and the compiler
 * is what says so. The reverse does not narrow: excluding `kind === "TMissing"`
 * does not change the parameter, so going from a pattern to a type is a walk
 * and a checked cast, not a test.
 */
export type TypeMaybe<M> =
  | { readonly kind: "TUnknown" } // Top
  | { readonly kind: "TNever" } // Bottom
  | { readonly kind: "TBad" } // failure to resolve, can be used arbitrarily
  | { readonly kind: "BVar"; readonly index: number }
  | { readonly kind: "FVar"; readonly level: Level; readonly hint: string }
  /**
   * `[b0 <: B0, ..] (params) -> result`, uncurried and possibly polymorphic.
   * Arity is part of the type, so `(A, B) -> C` and `A -> B -> C` are unrelated.
   * An empty `typeParams` is the monomorphic arrow; requiring the parameter list
   * keeps a quantifier off a non-function, which is the value restriction.
   */
  | {
    readonly kind: "TFun";
    readonly typeParams: readonly TypeParamInfoMaybe<M>[];
    readonly params: readonly TypeMaybe<M>[];
    readonly result: TypeMaybe<M>;
  }
  /** Saturated nominal constructor. Primitives are the nullary case. */
  | {
    readonly kind: "TData";
    readonly name: DataName;
    readonly args: readonly TypeMaybe<M>[];
  }
  | MissingPart<M>;

/** A complete type: every part supplied. */
export type Type = TypeMaybe<never>;

/** A type with parts not yet supplied. What a checking rule pushes inward. */
export type TypePattern = TypeMaybe<number>;

export const TMissing: TypePattern = { kind: "TMissing" };

export const TUnknown: Type = { kind: "TUnknown" };
export const TNever: Type = { kind: "TNever" };
export const TBad: Type = { kind: "TBad" };

export function BVar(index: number): Type {
  return { kind: "BVar", index };
}

export function FVar(
  level: Level,
  hint: string,
): Extract<Type, { kind: "FVar" }> {
  return { kind: "FVar", level, hint };
}

/**
 * Pass an empty `typeParams` for the monomorphic arrow.
 *
 * Generic in `M` so that building from patterns gives a pattern and building
 * from types gives a type, without two constructors that differ only there.
 */
export function TFun<M = never>(
  typeParams: readonly TypeParamInfoMaybe<M>[],
  params: readonly TypeMaybe<M>[],
  result: TypeMaybe<M>,
): TypeMaybe<M> {
  return { kind: "TFun", typeParams, params, result };
}

export function TData<M = never>(
  name: DataName,
  args: readonly TypeMaybe<M>[] = [],
): TypeMaybe<M> {
  return { kind: "TData", name, args };
}

export function mkTypeParamInfo<M = never>(
  hint: string,
  bound: TypeMaybe<M>,
): TypeParamInfoMaybe<M> {
  return { hint, bound };
}

/**
 * Where a variable occurs, by variance. `none` is not-at-all, and is the
 * identity: a variable occurring nowhere constrains nothing.
 */
export type Polarity = "none" | "covariant" | "contravariant" | "invariant";

/**
 * `flip` at the type level, so a caller that started from a narrower set of
 * polarities gets one back. A cast travels in a direction and has to keep
 * knowing it is not `none`.
 */
export type Flip<P extends Polarity> = P extends "covariant" ? "contravariant"
  : P extends "contravariant" ? "covariant"
  : P;

/** Contravariant positions swap the two directions and fix the other two. */
export function flip<P extends Polarity>(polarity: P): Flip<P> {
  if (polarity === "covariant") return "contravariant" as Flip<P>;
  if (polarity === "contravariant") return "covariant" as Flip<P>;
  return polarity as Flip<P>;
}

/**
 * Two occurrences of one variable. Disagreeing is what makes it invariant --
 * neither direction can be widened without breaking the other.
 */
export function bothPolarities(left: Polarity, right: Polarity): Polarity {
  if (left === "none") return right;
  if (right === "none") return left;
  return left === right ? left : "invariant";
}

/**
 * What an opening puts in a bound variable's place, told the index and *where
 * it stands*.
 *
 * A rule rather than an array because the two things a caller may want at a
 * variable's position are both things an array cannot express: the replacement
 * may depend on the polarity of the position, and reaching one may be worth
 * recording. `#applyCall` does the second -- it learns each EVar's polarity in
 * the result while putting it there, rather than walking the answer again to
 * ask -- and a substitution that reads the first is what this is
 * shaped for.
 *
 * Called once per *occurrence*, so a variable appearing twice is offered twice,
 * at each polarity it stands in. A rule that records has to combine them; one
 * that only replaces need not care.
 */
export type OpenRule<M = never> = (
  index: number,
  polarity: Polarity,
) => TypeMaybe<M>;

/**
 * Replace the variables of the nearest enclosing binder. A datatype binds its
 * parameters the same way, so instantiating a constructor and a quantifier are
 * one operation.
 *
 * `here` is the polarity of the position being rebuilt, threaded exactly as
 * `isClosed` threads `depth` -- and flipped at the same places `#avoid` swaps
 * direction on, which is what keeps the two agreeing about what a position is.
 */
function openAt<M>(
  type: TypeMaybe<M>,
  depth: number,
  rule: OpenRule<M>,
  here: Polarity,
): TypeMaybe<M> {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "TMissing":
    case "FVar":
      return type;
    case "BVar":
      // Bound by a binder inside the one being opened: leave it alone.
      return type.index < depth ? type : rule(type.index - depth, here);
    case "TFun": {
      // Bounds are parallel, so they stay at `depth`; only what the binder
      // scopes over -- the parameters and the result -- moves inward. Both
      // bounds and parameters are contravariant; the result alone is not.
      const inner = depth + type.typeParams.length;
      return TFun(
        type.typeParams.map((b) =>
          mkTypeParamInfo(b.hint, openAt(b.bound, depth, rule, flip(here)))
        ),
        type.params.map((param) => openAt(param, inner, rule, flip(here))),
        openAt(type.result, inner, rule, here),
      );
    }
    case "TData":
      // Not a binder, but skipping it leaves stale `BVar`s and nothing objects.
      // Arguments are invariant, and `invariant` survives every flip below it,
      // so everything inside one is invariant however deep it sits.
      return TData(
        type.name,
        type.args.map((arg) => openAt(arg, depth, rule, "invariant")),
      );
  }
}

/**
 * Open a binder by rule, reading the whole type as a covariant position.
 *
 * The general form. `openMany` is this with a rule that only looks up, which is
 * every caller that has nothing to learn on the way.
 */
export function openWith<M = never>(
  type: TypeMaybe<M>,
  rule: OpenRule<M>,
): TypeMaybe<M> {
  return openAt(type, 0, rule, "covariant");
}

/** Instantiate a binder's variables, `BVar j` taking `replacements[j]`. */
export function openMany<M = never>(
  type: TypeMaybe<M>,
  replacements: readonly TypeMaybe<M>[],
): TypeMaybe<M> {
  return openWith<M>(type, (index) => {
    const replacement = replacements[index];
    // Every caller opens a binder at its own arity, so a miss is a checker bug
    // rather than a program error -- and answering `TBad` would hide it, that
    // being the one type checking against anything.
    if (replacement === undefined) {
      throw new Error(
        `open: BVar ${index} of this binder, but only ` +
          `${replacements.length} replacements`,
      );
    }
    return replacement;
  });
}

/** Sugar for a single-variable binder. */
export function open<M = never>(
  type: TypeMaybe<M>,
  replacement: TypeMaybe<M>,
): TypeMaybe<M> {
  return openMany(type, [replacement]);
}

/**
 * An EVar is an `FVar` like any other here, so one at or past the mark would be
 * captured into the binder rather than left standing. Nothing reaches this with
 * one: `withEVars` decides every member of its batch -- to `TBad` where it
 * cannot -- and the application substitutes them away before its scope exits.
 */
function closeAt<M>(
  type: TypeMaybe<M>,
  depth: number,
  mark: number,
): TypeMaybe<M> {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "TMissing":
    case "BVar":
      return type;
    case "FVar": {
      const at = type.level - mark;
      return at >= 0 ? BVar(depth + at) : type;
    }
    case "TFun": {
      const inner = depth + type.typeParams.length;
      return TFun(
        type.typeParams.map((b) =>
          mkTypeParamInfo(b.hint, closeAt(b.bound, depth, mark))
        ),
        type.params.map((param) => closeAt(param, inner, mark)),
        closeAt(type.result, inner, mark),
      );
    }
    case "TData":
      return TData(
        type.name,
        type.args.map((arg) => closeAt(arg, depth, mark)),
      );
  }
}

/**
 * Abstract every level at or above `mark` into a binder, `mark + j` becoming
 * `BVar j`. A scope is always a contiguous run of context entries, so this
 * needs no set of identities and no membership test -- and being one call over
 * the whole group, it cannot collapse the group onto a single index the way an
 * iterated single-variable close would.
 *
 * No count, because there is nothing above the group to spare: a caller closes
 * exactly what it pushed at `mark`, and an `FVar` names a type variable, never
 * one of the term variables a caller may have pushed on top of the group.
 */
export function closeFrom<M = never>(
  type: TypeMaybe<M>,
  mark: number,
): TypeMaybe<M> {
  return closeAt(type, 0, mark);
}

/**
 * Well-formedness, both bounds at once: is `type` closed under `levels` free
 * variables and `depth` enclosing binders? Every free level must be `< levels`
 * and every `BVar` index `< depth`, counting inward as binders are entered.
 *
 * One predicate rather than two because the two bounds are never independent.
 * The interesting uses need a non-zero `depth`: a constructor's fields are
 * stored closed over its datatype's parameters, so checking one means asking
 * for `levels = 0, depth = arity`, which a bare "locally closed" check -- fixed
 * at depth zero -- cannot express.
 *
 * At `depth = 0` this is the scope-exit assertion: nothing surviving a
 * `truncate` to `mark` may mention a level `>= mark`. It is also exactly the
 * escape check `setSolution` needs, so both rest on one traversal.
 */
export function isClosed<M>(
  type: TypeMaybe<M>,
  levels: number,
  depth = 0,
): boolean {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    // A missing part binds nothing and names nothing, so it is closed under
    // anything -- it is a leaf that happens to have no content at all.
    case "TMissing":
      return true;
    case "BVar":
      return type.index < depth;
    case "FVar":
      return type.level < levels;
    case "TFun": {
      // Bounds are parallel, so they stay at `depth`; only what the binder
      // scopes over moves inward.
      const inner = depth + type.typeParams.length;
      return type.typeParams.every((b) => isClosed(b.bound, levels, depth)) &&
        type.params.every((param) => isClosed(param, levels, inner)) &&
        isClosed(type.result, levels, inner);
    }
    case "TData":
      return type.args.every((arg) => isClosed(arg, levels, depth));
  }
}

/**
 * Whether two lists relate elementwise. Separate from any one relation because
 * the length check and the missing-element guard are the same every time.
 */
export function allPairs<A, B>(
  left: readonly A[],
  right: readonly B[],
  relate: (a: A, b: B) => boolean,
): boolean {
  return left.length === right.length && left.every((item, i) => {
    const other = right[i];
    return other !== undefined && relate(item, other);
  });
}

/** Alpha-equivalence, free because bound variables are indices. */
export function alphaEq<M>(
  left: TypeMaybe<M>,
  right: TypeMaybe<M>,
): boolean {
  switch (left.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    // Two missing parts are equal as *patterns*, which says nothing about the
    // types that will fill them. Only a pattern is ever compared this way.
    case "TMissing":
      return right.kind === left.kind;
    case "BVar":
      return right.kind === "BVar" && left.index === right.index;
    case "FVar":
      return right.kind === "FVar" && left.level === right.level;
    case "TFun":
      // `hint` is for printing only, so not compared.
      return right.kind === "TFun" &&
        allPairs(
          left.typeParams.map((b) => b.bound),
          right.typeParams.map((b) => b.bound),
          alphaEq,
        ) &&
        allPairs(left.params, right.params, alphaEq) &&
        alphaEq(left.result, right.result);
    case "TData":
      return right.kind === "TData" &&
        left.name === right.name &&
        allPairs(left.args, right.args, alphaEq);
  }
}

function toStringAt<M>(
  type: TypeMaybe<M>,
  names: readonly string[],
): string {
  switch (type.kind) {
    case "TUnknown":
      return "unknown";
    case "TMissing":
      return "?";
    case "TNever":
      return "never";
    case "TBad":
      return "<bad>";
    case "BVar":
      // Well-formed types are closed, so an unnamed index is a bug upstream.
      return names[type.index] ?? `?${type.index}`;
    case "FVar":
      return type.hint;
    case "TFun": {
      const hints = type.typeParams.map((b) => b.hint);
      // Bounds are parallel, so they read in the *enclosing* scope.
      const bounds = type.typeParams
        .map((b) =>
          b.bound.kind === "TUnknown"
            ? b.hint
            : `${b.hint} <: ${toStringAt(b.bound, names)}`
        )
        .join(", ");
      const inner = [...hints, ...names];
      const params = type.params.map((param) => toStringAt(param, inner));
      // A lone parameter reads better bare, unless bound or itself an arrow.
      const only = type.params[0];
      const head = hints.length === 0 && params.length === 1 &&
          only !== undefined && only.kind !== "TFun"
        ? params[0]
        : `(${params.join(", ")})`;
      const quantifier = hints.length === 0 ? "" : `[${bounds}]`;
      return `${quantifier}${head} -> ${toStringAt(type.result, inner)}`;
    }
    case "TData":
      return type.args.length === 0
        ? type.name
        : `${type.name}[${
          type.args.map((arg) => toStringAt(arg, names)).join(", ")
        }]`;
  }
}

/** Render using the name hints carried on binders. */
export function typeToString<M>(type: TypeMaybe<M>): string {
  return toStringAt(type, []);
}
