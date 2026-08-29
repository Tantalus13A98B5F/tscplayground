/**
 * Internal type representation. Locally nameless: `BVar` under binders, `FVar`
 * free in the context. Invariants: a `BVar` never escapes into the context, an
 * `FVar` never appears under an unopened binder, and only `open*`/`close*` touch
 * index arithmetic.
 *
 * `TFun` is the only binder: quantification fuses into the arrow, so there is no
 * bare `forall`. Binders are n-ary and simultaneous -- the j-th variable is
 * `BVar j`. `params` and `result` sit inside the binder; bounds are *parallel*,
 * outside it, so a bound may name an enclosing binder but never one of its own
 * group.
 *
 * Variance lives here too, and opening is where it is read: a rule is told the
 * variance of every position it fills. `isClosed` threads `depth` the same way,
 * and `Subtyper`'s avoidance flips direction at the same places -- three
 * traversals that have to agree about what a position is.
 */

import type { Diagnostic } from "../diagnostics/diagnostic.ts";

/**
 * A free variable's identity *is* its position in the context, so a level needs
 * no allocator: the next one is the context's size. Type variables and EVars
 * share the space, because scoping compares the two against each other: a
 * solution may only mention what stands to its left, whichever kind that is.
 *
 * Sharing the space is why they share a node. An `FVar` names a level and
 * nothing more; whether that level holds a rigid variable or one still being
 * inferred is the entry's business, asked through `Context.evarAt`.
 */
export type Level = number & { readonly __brand: "Level" };
export type DataName = string & { readonly __brand: "DataName" };

export const mkLevel = (n: number): Level => n as Level;

/**
 * Say that a case cannot arise, and fail loudly if it does. For the index
 * lookups the type checker cannot see through: two lists built to the same
 * length, or an opening reaching no index its binder did not bind. Not `TBad`,
 * which means *an error was reported here* and would hide the bug.
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
 * The `TMissing` case, present only when `M` is inhabited. Distributing over
 * `never` yields `never`, so at `TypeMaybe<never>` the case is *gone*: a walk
 * over a complete type neither needs an arm for it nor is allowed one.
 */
type MissingPart<M> = M extends never ? never
  : { readonly kind: "TMissing" };

/**
 * A type, or a *pattern* -- a type with parts not yet supplied. `M` is a switch,
 * not carried data: only inhabited-versus-`never` is ever asked, and nothing
 * reads it. The two instantiations are the names anyone reads: `Type` and
 * `TypePattern`.
 *
 * Arrays here are `readonly` and so covariant, so a complete type flows into a
 * pattern position with no coercion. The reverse does not narrow: going from a
 * pattern to a type is a walk and a checked cast, not a test.
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
  /**
   * `Ref[T]`, a mutable cell. Its own kind rather than a `TData` the checker
   * declares for itself, because almost nothing a datatype is would be true of
   * it: it has no constructors, nothing takes one apart, and its argument is
   * invariant for a reason no walk over constructor fields could find --
   * `get!` reads a `T` out where `set!` puts one in, and neither of those is a
   * field.
   *
   * So the invariance is written where every walk can see it, as a literal
   * `0`, rather than stipulated in a table and looked up. A cell is a type
   * *former* like the arrow, not a nominal type, which is also why it carries
   * no name: two `Ref`s are the same type when their arguments are.
   */
  | { readonly kind: "TRef"; readonly arg: TypeMaybe<M> }
  | MissingPart<M>;

/** A complete type: every part supplied. */
export type Type = TypeMaybe<never>;

/** A type with parts not yet supplied. What a checking rule pushes inward. */
export type TypePattern = TypeMaybe<unknown>;

export const TMissing: TypePattern = { kind: "TMissing" };

export const TUnknown: Type = { kind: "TUnknown" };
export const TNever: Type = { kind: "TNever" };

/**
 * A type known to *be* `<bad>`. What `badUnder` hands back, so a rule holding
 * one can say so in its own signature rather than re-testing the kind.
 */
export type BadType = Extract<Type, { kind: "TBad" }>;

/**
 * A type nothing can be said about. Not exported: the only way to one is
 * `badUnder`, so every `<bad>` in a checked program carries a diagnostic that
 * put it there.
 */
const TBad: BadType = { kind: "TBad" };

/**
 * `<bad>` under the diagnostic that licenses it.
 *
 * `TBad` relates to everything, which is only sound because it means *a report
 * already stands*: nothing built from one can go on to be blamed, and nothing
 * downstream will say a second thing about it. So the witness is the whole
 * point -- the caller passes the diagnostic it filed, and a `<bad>` with no
 * report behind it cannot be written.
 *
 * An error, and not a warning: a warning is something the program may go on
 * from, so it licenses nothing to stop saying. Nor `info`.
 *
 * Propagating an existing one needs nothing: `<bad>` is a singleton and its
 * witness is whatever put it there, so a rule that already holds one hands
 * that same value on.
 */
export function badUnder(witness: Diagnostic): BadType {
  if (witness.severity !== "error") {
    impossible(`a <bad> witnessed by a ${witness.severity}`);
  }
  return TBad;
}

export function BVar(index: number): Type {
  return { kind: "BVar", index };
}

/**
 * A type known to *be* a variable. Nearly everything reached by level is
 * reached from one of these, so it is what the context's reads and the rules
 * that promote a variable ask for -- a level on its own says which entry but
 * not that anything pointed at it.
 */
export type FVarRef = Extract<Type, { kind: "FVar" }>;

export function FVar(level: Level, hint: string): FVarRef {
  return { kind: "FVar", level, hint };
}

/**
 * Pass an empty `typeParams` for the monomorphic arrow. Generic in `M` so that
 * building from patterns gives a pattern and from types gives a type.
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

export function TRef<M = never>(arg: TypeMaybe<M>): TypeMaybe<M> {
  return { kind: "TRef", arg };
}

export function mkTypeParamInfo<M = never>(
  hint: string,
  bound: TypeMaybe<M>,
): TypeParamInfoMaybe<M> {
  return { hint, bound };
}

/**
 * Where a position stands, and so which way a type filling it may move: `1` a
 * covariant one, `-1` a contravariant one, `0` an invariant one, which may not
 * move at all.
 *
 * Numbers because the only operation is flipping, and flipping is negation --
 * which is also why `0` is its own flip, and so why a position inside an
 * invariant one stays invariant however deep below it sits. Testing is by
 * sign.
 *
 * Not what a *variable* comes to: that is a set of the positions it was found
 * in, which `EVarEntry` keeps, and whose empty case has no variance to name.
 */
export type Variance = -1 | 0 | 1;

/**
 * Contravariant positions swap the two directions and fix invariance.
 *
 * Negation, which is why invariance needs no case: `0` is its own flip.
 */
export function flip(variance: Variance): Variance {
  return -variance as Variance;
}

/**
 * A position reached through another position: multiplication, which is why
 * `flip` is the special case of composing with a contravariant one, and why
 * `0` absorbs -- anything inside an invariant position is invariant, however
 * deep below it sits.
 */
export function composeVariance(outer: Variance, inner: Variance): Variance {
  return (outer * inner) as Variance;
}

/**
 * How a datatype's `index`th argument may move. A rule and not the table
 * itself: variance is read off a declaration, and declarations are built on
 * top of this file rather than known to it.
 *
 * `invariantArgs` is the answer where there is nothing to consult, and is what
 * every argument had before variance was inferred: sound, since an invariant
 * argument demands the most and so concludes the least.
 */
export type ArgVariance = (name: DataName, index: number) => Variance;

export const invariantArgs: ArgVariance = () => 0;

/**
 * What an opening puts in a bound variable's place, told the index and *where
 * it stands*. A rule rather than an array so the replacement may depend on the
 * variance, and so reaching a position can be recorded: `#applyCall` learns
 * where each EVar stands in the result while putting it there.
 *
 * Called once per *occurrence*, so a variable appearing twice is offered twice,
 * at each position it stands in. A rule that records has to combine them.
 */
export type OpenRule<M = never> = (
  index: number,
  variance: Variance,
) => TypeMaybe<M>;

/**
 * Replace the variables of the nearest enclosing binder. A datatype binds its
 * parameters the same way, so instantiating a constructor and a quantifier are
 * one operation.
 *
 * `here` is the variance of the position being rebuilt, flipped at the same
 * places `#avoid` swaps direction on -- the two have to agree about what a
 * position is.
 */
function openAt<M>(
  type: TypeMaybe<M>,
  depth: number,
  rule: OpenRule<M>,
  here: Variance,
  args: ArgVariance,
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
          mkTypeParamInfo(
            b.hint,
            openAt(b.bound, depth, rule, flip(here), args),
          )
        ),
        type.params.map((param) =>
          openAt(param, inner, rule, flip(here), args)
        ),
        openAt(type.result, inner, rule, here, args),
      );
    }
    case "TData":
      // Not a binder, but skipping it leaves stale `BVar`s and nothing objects.
      // An argument stands where its parameter's variance says, composed with
      // wherever this node itself stands.
      return TData(
        type.name,
        type.args.map((arg, i) =>
          openAt(
            arg,
            depth,
            rule,
            composeVariance(here, args(type.name, i)),
            args,
          )
        ),
      );
    // Invariant, written here rather than looked up: a cell's argument moves
    // neither way, and `0` is its own flip, so everything below it is
    // invariant however deep it sits.
    case "TRef":
      return TRef(openAt(type.arg, depth, rule, 0, args));
  }
}

/**
 * Open a binder by rule, reading the whole type as a covariant position. The
 * general form; `openMany` is this with a rule that only looks up.
 */
export function openWith<M = never>(
  type: TypeMaybe<M>,
  rule: OpenRule<M>,
  args: ArgVariance = invariantArgs,
): TypeMaybe<M> {
  return openAt(type, 0, rule, 1, args);
}

/** Instantiate a binder's variables, `BVar j` taking `replacements[j]`. */
export function openMany<M = never>(
  type: TypeMaybe<M>,
  replacements: readonly TypeMaybe<M>[],
): TypeMaybe<M> {
  return openWith<M>(type, (index) => {
    const replacement = replacements[index];
    // Every caller opens a binder at its own arity, so a miss is a checker bug
    // rather than a program error.
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
    case "TRef":
      return TRef(closeAt(type.arg, depth, mark));
  }
}

/**
 * Abstract every level at or above `mark` into a binder, `mark + j` becoming
 * `BVar j`. A scope is always a contiguous run of context entries, so this needs no set
 * of identities and no membership test, and one call over the whole group
 * cannot collapse it onto a single index the way an iterated close would.
 *
 * No count: a caller closes exactly what it pushed at `mark`, and an `FVar`
 * names a type variable, never a term variable pushed on top of the group.
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
 * A non-zero `depth` is what a constructor's fields need: they are stored
 * closed over their datatype's parameters, so checking one asks for
 * `levels = 0, depth = arity`.
 *
 * At `depth = 0` this is the scope-exit assertion -- nothing surviving a
 * `truncate` to `mark` may mention a level `>= mark` -- and equally the bar an
 * EVar's constraints and solution are held to, which is its batch.
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
    case "TRef":
      return isClosed(type.arg, levels, depth);
  }
}

/**
 * A pattern read back as a type, `<bad>` standing wherever it said nothing.
 *
 * Keeping the shape is the point: `List[<bad>]` is still a datatype, so a
 * `match` on it can be checked for membership and exhaustiveness where a bare
 * `<bad>` could only be waved through. Nothing is *asserted* by the parts it
 * invents -- `<bad>` relates to anything and none of them can go on to be
 * blamed -- which is what separates this from choosing an arbitrary type.
 *
 * `bad` is asked for only where a part is missing, and asked at most once
 * however many are: what a caller does there is report, and the report is
 * about the pattern rather than about any one hole in it. A pattern that was
 * complete never calls it, which is how a caller learns it invented nothing --
 * the question it used to ask as `already`.
 */
export function completePattern(
  pattern: TypePattern,
  bad: () => Type,
): Type {
  let reported: Type | undefined;
  const once = () => reported ??= bad();

  const walk = (pattern: TypePattern): Type => {
    switch (pattern.kind) {
      case "TMissing":
        return once();
      case "TFun":
        return TFun(
          pattern.typeParams.map((binder) =>
            mkTypeParamInfo(binder.hint, walk(binder.bound))
          ),
          pattern.params.map(walk),
          walk(pattern.result),
        );
      case "TData":
        return TData(pattern.name, pattern.args.map(walk));
      case "TRef":
        return TRef(walk(pattern.arg));
      default:
        return completeLeafPattern(pattern);
    }
  };
  return walk(pattern);
}

/**
 * A leaf pattern read back as a type. Nothing in a leaf *could* be missing,
 * but the parameter does not narrow, so this is one honest switch rather than
 * a cast.
 */
export function completeLeafPattern(
  pattern: Exclude<
    TypePattern,
    { kind: "TFun" | "TData" | "TRef" | "TMissing" }
  >,
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

/**
 * Whether two lists relate elementwise. Separate from any one relation because
 * the length check and the missing-element guard are the same every time.
 */
export function allPairs<A, B>(
  left: readonly A[],
  right: readonly B[],
  relate: (a: A, b: B, index: number) => boolean,
): boolean {
  return left.length === right.length && left.every((item, i) => {
    const other = right[i];
    return other !== undefined && relate(item, other, i);
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
    case "TRef":
      return right.kind === "TRef" && alphaEq(left.arg, right.arg);
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
    case "TRef":
      return `Ref[${toStringAt(type.arg, names)}]`;
  }
}

/** Render using the name hints carried on binders. */
export function typeToString<M>(type: TypeMaybe<M>): string {
  return toStringAt(type, []);
}
