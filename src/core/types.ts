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
 */

/**
 * A free variable's identity *is* its position in the context, so a level needs
 * no allocator: the next one is the context's size. Type variables and EVars
 * share the space, because scoping compares the two against each other: a
 * solution may only mention what stands to its left, whichever kind that is.
 * So one level names one entry, and the entry's kind says which it is -- ask
 * `Context.upperBoundAt` or `evarAt`, each of which asks and narrows at once,
 * and neither of which answers: a level naming the wrong kind is a bug.
 */
export type Level = number & { readonly __brand: "Level" };
export type DataName = string & { readonly __brand: "DataName" };

export const mkLevel = (n: number): Level => n as Level;
export const mkDataName = (s: string): DataName => s as DataName;

/**
 * One of a `TFun`'s quantified parameters. `hint` is for printing only -- the
 * variable itself is an index -- which is what distinguishes this from the
 * surface `BindingIdent`, whose text is a name something resolves against.
 */
export type TypeParamInfo = {
  readonly hint: string;
  readonly bound: Type;
};

export type Type =
  | { readonly kind: "TUnknown" } // Top
  | { readonly kind: "TNever" } // Bottom
  | { readonly kind: "TBad" } // failure to resolve, can be used arbitrarily
  | { readonly kind: "BVar"; readonly index: number }
  | { readonly kind: "FVar"; readonly level: Level; readonly hint: string }
  | { readonly kind: "EVar"; readonly level: Level; readonly hint: string }
  /**
   * `[b0 <: B0, ..] (params) -> result`, uncurried and possibly polymorphic.
   * Arity is part of the type, so `(A, B) -> C` and `A -> B -> C` are unrelated.
   * An empty `typeParams` is the monomorphic arrow; requiring the parameter list
   * keeps a quantifier off a non-function, which is the value restriction.
   */
  | {
    readonly kind: "TFun";
    readonly typeParams: readonly TypeParamInfo[];
    readonly params: readonly Type[];
    readonly result: Type;
  }
  /** Saturated nominal constructor. Primitives are the nullary case. */
  | {
    readonly kind: "TData";
    readonly name: DataName;
    readonly args: readonly Type[];
  };

export const TUnknown: Type = { kind: "TUnknown" };
export const TNever: Type = { kind: "TNever" };
export const TBad: Type = { kind: "TBad" };

export function BVar(index: number): Type {
  return { kind: "BVar", index };
}

export function FVar(level: Level, hint: string): Type {
  return { kind: "FVar", level, hint };
}

export function EVar(level: Level, hint: string): Type {
  return { kind: "EVar", level, hint };
}

/** Pass an empty `typeParams` for the monomorphic arrow. */
export function TFun(
  typeParams: readonly TypeParamInfo[],
  params: readonly Type[],
  result: Type,
): Type {
  return { kind: "TFun", typeParams, params, result };
}

export function TData(name: DataName, args: readonly Type[] = []): Type {
  return { kind: "TData", name, args };
}

export function mkTypeParamInfo(hint: string, bound: Type): TypeParamInfo {
  return { hint, bound };
}

/**
 * Replace the variables of the nearest enclosing binder. A datatype binds its
 * parameters the same way, so instantiating a constructor and a quantifier are
 * one operation.
 */
function openAt(
  type: Type,
  depth: number,
  replacements: readonly Type[],
): Type {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "FVar":
    case "EVar":
      return type;
    case "BVar": {
      // Bound by a binder inside the one being opened: leave it alone.
      if (type.index < depth) return type;
      const replacement = replacements[type.index - depth];
      // Every caller opens a binder at its own arity, so a miss is a checker
      // bug rather than a program error -- and answering `TBad` would hide it,
      // that being the one type checking against anything.
      if (replacement === undefined) {
        throw new Error(
          `open: BVar ${type.index} under ${depth} binders, ` +
            `but only ${replacements.length} replacements`,
        );
      }
      return replacement;
    }
    case "TFun": {
      // Bounds are parallel, so they stay at `depth`; only what the binder
      // scopes over -- the parameters and the result -- moves inward.
      const inner = depth + type.typeParams.length;
      return TFun(
        type.typeParams.map((b) =>
          mkTypeParamInfo(b.hint, openAt(b.bound, depth, replacements))
        ),
        type.params.map((param) => openAt(param, inner, replacements)),
        openAt(type.result, inner, replacements),
      );
    }
    case "TData":
      // Not a binder, but skipping it leaves stale `BVar`s and nothing objects.
      return TData(
        type.name,
        type.args.map((arg) => openAt(arg, depth, replacements)),
      );
  }
}

/** Instantiate a binder's variables, `BVar j` taking `replacements[j]`. */
export function openMany(type: Type, replacements: readonly Type[]): Type {
  return openAt(type, 0, replacements);
}

/** Sugar for a single-variable binder. */
export function open(type: Type, replacement: Type): Type {
  return openAt(type, 0, [replacement]);
}

function closeAt(
  type: Type,
  depth: number,
  mark: number,
): Type {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "BVar":
    case "EVar":
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
export function closeFrom(type: Type, mark: number): Type {
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
export function isClosed(type: Type, levels: number, depth = 0): boolean {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
      return true;
    case "BVar":
      return type.index < depth;
    case "FVar":
    case "EVar":
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
 * Where a variable occurs, by variance. `none` is not-at-all, and is the
 * identity: a variable occurring nowhere constrains nothing.
 */
export type Polarity = "none" | "covariant" | "contravariant" | "invariant";

/** Contravariant positions swap the two directions and fix the other two. */
function flip(polarity: Polarity): Polarity {
  if (polarity === "covariant") return "contravariant";
  if (polarity === "contravariant") return "covariant";
  return polarity;
}

/**
 * Two occurrences of one variable. Disagreeing is what makes it invariant --
 * neither direction can be widened without breaking the other.
 */
function bothPolarities(left: Polarity, right: Polarity): Polarity {
  if (left === "none") return right;
  if (right === "none") return left;
  return left === right ? left : "invariant";
}

function polarityAt(type: Type, level: Level, here: Polarity): Polarity {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "BVar":
      return "none";
    // Kind-agnostic: levels are one space, so this asks about the *position*
    // and lets the caller know which kind lives there.
    case "FVar":
    case "EVar":
      return type.level === level ? here : "none";
    case "TFun": {
      // Parameters and binder bounds are contravariant, the result covariant --
      // the same split `#avoid` swaps direction on.
      const parts = [
        ...type.typeParams.map((b) => polarityAt(b.bound, level, flip(here))),
        ...type.params.map((param) => polarityAt(param, level, flip(here))),
        polarityAt(type.result, level, here),
      ];
      return parts.reduce(bothPolarities, "none");
    }
    case "TData":
      // Arguments are invariant, so an occurrence anywhere inside one is
      // invariant however deep it sits: `invariant` survives every flip.
      return type.args
        .map((arg) => polarityAt(arg, level, "invariant"))
        .reduce(bothPolarities, "none");
  }
}

/**
 * How the variable at `level` occurs in `type`, reading the whole type as a
 * covariant position.
 *
 * This is what makes a solution *principal* rather than merely sound. A
 * variable occurring only covariantly can take its lower bound -- the smallest
 * type the constraints admit, and so the most informative result -- while one
 * occurring only contravariantly takes its upper. Occurring both ways, or
 * inside an invariant `TData` argument, no choice is free: the two bounds have
 * to agree.
 */
export function polarityOf(level: Level, type: Type): Polarity {
  return polarityAt(type, level, "covariant");
}

function allPairs(
  left: readonly Type[],
  right: readonly Type[],
  relate: (a: Type, b: Type) => boolean,
): boolean {
  return left.length === right.length && left.every((item, i) => {
    const other = right[i];
    return other !== undefined && relate(item, other);
  });
}

/** Alpha-equivalence, free because bound variables are indices. */
export function alphaEq(left: Type, right: Type): boolean {
  switch (left.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
      return right.kind === left.kind;
    case "BVar":
      return right.kind === "BVar" && left.index === right.index;
    case "FVar":
      return right.kind === "FVar" && left.level === right.level;
    case "EVar":
      return right.kind === "EVar" && left.level === right.level;
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

function toStringAt(type: Type, names: readonly string[]): string {
  switch (type.kind) {
    case "TUnknown":
      return "unknown";
    case "TNever":
      return "never";
    case "TBad":
      return "<bad>";
    case "BVar":
      // Well-formed types are closed, so an unnamed index is a bug upstream.
      return names[type.index] ?? `?${type.index}`;
    case "FVar":
      return type.hint;
    case "EVar":
      return `?${type.hint}`;
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
export function typeToString(type: Type): string {
  return toStringAt(type, []);
}
