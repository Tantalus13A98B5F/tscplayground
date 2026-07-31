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

export type VarId = number & { readonly __brand: "VarId" };
export type EVarId = number & { readonly __brand: "EVarId" };
export type DataName = string & { readonly __brand: "DataName" };

export const mkVarId = (n: number): VarId => n as VarId;
export const mkEVarId = (n: number): EVarId => n as EVarId;
export const mkDataName = (s: string): DataName => s as DataName;

export type Binder = {
  readonly hint: string;
  readonly bound: Type;
};

export type Type =
  | { readonly kind: "TUnknown" } // Top
  | { readonly kind: "TNever" } // Bottom
  | { readonly kind: "TBad" } // failure to resolve, can be used arbitrarily
  | { readonly kind: "BVar"; readonly index: number }
  | { readonly kind: "FVar"; readonly id: VarId; readonly hint: string }
  | { readonly kind: "EVar"; readonly id: EVarId; readonly hint: string }
  /**
   * `[b0 <: B0, ..] (params) -> result`, uncurried and possibly polymorphic.
   * Arity is part of the type, so `(A, B) -> C` and `A -> B -> C` are unrelated.
   * An empty `typeParams` is the monomorphic arrow; requiring the parameter list
   * keeps a quantifier off a non-function, which is the value restriction.
   */
  | {
    readonly kind: "TFun";
    readonly typeParams: readonly Binder[];
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

export function FVar(id: VarId, hint: string): Type {
  return { kind: "FVar", id, hint };
}

export function EVar(id: EVarId, hint: string): Type {
  return { kind: "EVar", id, hint };
}

/** Pass an empty `typeParams` for the monomorphic arrow. */
export function TFun(
  typeParams: readonly Binder[],
  params: readonly Type[],
  result: Type,
): Type {
  return { kind: "TFun", typeParams, params, result };
}

export function TData(name: DataName, args: readonly Type[] = []): Type {
  return { kind: "TData", name, args };
}

export function mkBinder(hint: string, bound: Type): Binder {
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
      // `TBad` only on an arity disagreement, which earlier passes reject.
      return replacements[type.index - depth] ?? TBad;
    }
    case "TFun": {
      // Bounds are parallel, so they stay at `depth`; only what the binder
      // scopes over -- the parameters and the result -- moves inward.
      const inner = depth + type.typeParams.length;
      return TFun(
        type.typeParams.map((b) =>
          mkBinder(b.hint, openAt(b.bound, depth, replacements))
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

function closeAt(type: Type, depth: number, ids: readonly VarId[]): Type {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "BVar":
    case "EVar":
      return type;
    case "FVar": {
      const at = ids.indexOf(type.id);
      return at === -1 ? type : BVar(depth + at);
    }
    case "TFun": {
      const inner = depth + type.typeParams.length;
      return TFun(
        type.typeParams.map((b) =>
          mkBinder(b.hint, closeAt(b.bound, depth, ids))
        ),
        type.params.map((param) => closeAt(param, inner, ids)),
        closeAt(type.result, inner, ids),
      );
    }
    case "TData":
      return TData(type.name, type.args.map((arg) => closeAt(arg, depth, ids)));
  }
}

/**
 * Abstract free variables *simultaneously*: `ids[j]` becomes `BVar j`. Not
 * iterated `close`, which would run every call at depth 0 and collapse
 * everything onto index 0. `ids` must be pairwise distinct.
 */
export function closeMany(type: Type, ids: readonly VarId[]): Type {
  return closeAt(type, 0, ids);
}

/** Sugar for a single-variable binder. */
export function close(type: Type, id: VarId): Type {
  return closeAt(type, 0, [id]);
}

/**
 * Replace free variables by identity, all at once -- iterating would substitute
 * later replacements into earlier ones. Touches no indices, an `FVar` being an
 * identity rather than a position.
 *
 * Precondition: `ids` pairwise distinct, every replacement locally closed, or a
 * dangling `BVar` is captured by whatever binder it lands under.
 */
export function substMany(
  type: Type,
  ids: readonly VarId[],
  replacements: readonly Type[],
): Type {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "BVar":
    case "EVar":
      return type;
    case "FVar": {
      const at = ids.indexOf(type.id);
      return at === -1 ? type : replacements[at] ?? type;
    }
    case "TFun":
      return TFun(
        type.typeParams.map((b) =>
          mkBinder(b.hint, substMany(b.bound, ids, replacements))
        ),
        type.params.map((param) => substMany(param, ids, replacements)),
        substMany(type.result, ids, replacements),
      );
    case "TData":
      return TData(
        type.name,
        type.args.map((arg) => substMany(arg, ids, replacements)),
      );
  }
}

/** Sugar for substituting a single free variable. */
export function substFVar(type: Type, id: VarId, replacement: Type): Type {
  return substMany(type, [id], [replacement]);
}

/** The occurs check. */
export function occurs(id: EVarId, type: Type): boolean {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "BVar":
    case "FVar":
      return false;
    case "EVar":
      return type.id === id;
    case "TFun":
      return type.typeParams.some((b) => occurs(id, b.bound)) ||
        type.params.some((param) => occurs(id, param)) ||
        occurs(id, type.result);
    case "TData":
      return type.args.some((arg) => occurs(id, arg));
  }
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
      return right.kind === "FVar" && left.id === right.id;
    case "EVar":
      return right.kind === "EVar" && left.id === right.id;
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
