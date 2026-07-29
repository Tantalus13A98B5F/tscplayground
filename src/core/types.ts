/**
 * Internal type representation. Locally nameless: `BVar` under binders, `FVar`
 * free in the context. Invariants: a `BVar` never escapes into the context, an
 * `FVar` never appears under an unopened binder, and only `open*`/`close*` touch
 * index arithmetic.
 *
 * Binders are n-ary and *simultaneous* -- the j-th variable is `BVar j`, no
 * telescope reversal -- so `TAll`'s bounds are parallel. Nest quantifiers when a
 * bound must mention another variable of the same one.
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
   * Uncurried: `(params) -> result`. Arity is part of the type, so `(A, B) -> C`
   * and `A -> B -> C` are unrelated and a mismatch is an arity diagnostic.
   */
  | {
    readonly kind: "TFun";
    readonly params: readonly Type[];
    readonly result: Type;
  }
  /** `forall b0 <: B0, .., bn <: Bn. body`, the j-th variable being `BVar j`. */
  | {
    readonly kind: "TAll";
    readonly binders: readonly Binder[];
    readonly body: Type;
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

export function TFun(params: readonly Type[], result: Type): Type {
  return { kind: "TFun", params, result };
}

/** Normalizes `forall . T` to `T`, so no `TAll` ever quantifies nothing. */
export function TAll(binders: readonly Binder[], body: Type): Type {
  return binders.length === 0 ? body : { kind: "TAll", binders, body };
}

export function TData(name: DataName, args: readonly Type[] = []): Type {
  return { kind: "TData", name, args };
}

export function mkBinder(hint: string, bound: Type): Binder {
  return { hint, bound };
}

/**
 * Replace the variables of the nearest enclosing binder. A datatype declaration
 * binds its parameters the same way, with no enclosing node, so instantiating a
 * constructor and a quantifier are one operation.
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
    case "TFun":
      return TFun(
        type.params.map((param) => openAt(param, depth, replacements)),
        openAt(type.result, depth, replacements),
      );
    case "TAll":
      // Bounds are parallel, so only the body moves inward -- by the full arity.
      return TAll(
        type.binders.map((b) =>
          mkBinder(b.hint, openAt(b.bound, depth, replacements))
        ),
        openAt(type.body, depth + type.binders.length, replacements),
      );
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
    case "TFun":
      return TFun(
        type.params.map((param) => closeAt(param, depth, ids)),
        closeAt(type.result, depth, ids),
      );
    case "TAll":
      return TAll(
        type.binders.map((b) => mkBinder(b.hint, closeAt(b.bound, depth, ids))),
        closeAt(type.body, depth + type.binders.length, ids),
      );
    case "TData":
      return TData(type.name, type.args.map((arg) => closeAt(arg, depth, ids)));
  }
}

/**
 * Abstract free variables *simultaneously*: `ids[j]` becomes `BVar j`. Not
 * iterated `close` -- both calls run at depth 0 and the second leaves the
 * first's `BVar` alone, collapsing everything onto index 0. `ids` must be
 * pairwise distinct.
 */
export function closeMany(type: Type, ids: readonly VarId[]): Type {
  return closeAt(type, 0, ids);
}

/** Sugar for a single-variable binder. */
export function close(type: Type, id: VarId): Type {
  return closeAt(type, 0, [id]);
}

/**
 * Replace free variables by identity, all at once. Simultaneous, unlike
 * iterating, which would substitute later replacements into earlier ones.
 * Touches no indices: an `FVar` is an identity, not a position.
 *
 * Precondition: `ids` pairwise distinct, every replacement locally closed -- a
 * dangling `BVar` would be captured by whatever binder it lands under.
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
        type.params.map((param) => substMany(param, ids, replacements)),
        substMany(type.result, ids, replacements),
      );
    case "TAll":
      return TAll(
        type.binders.map((b) =>
          mkBinder(b.hint, substMany(b.bound, ids, replacements))
        ),
        substMany(type.body, ids, replacements),
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
      return type.params.some((param) => occurs(id, param)) ||
        occurs(id, type.result);
    case "TAll":
      return type.binders.some((b) => occurs(id, b.bound)) ||
        occurs(id, type.body);
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
      return right.kind === "TFun" &&
        allPairs(left.params, right.params, alphaEq) &&
        alphaEq(left.result, right.result);
    case "TAll":
      // `hint` is for printing only, so not compared.
      return right.kind === "TAll" &&
        allPairs(
          left.binders.map((b) => b.bound),
          right.binders.map((b) => b.bound),
          alphaEq,
        ) &&
        alphaEq(left.body, right.body);
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
      const params = type.params.map((param) => toStringAt(param, names));
      // A lone parameter reads better bare, unless it is itself an arrow.
      const only = type.params[0];
      const head = params.length === 1 && only !== undefined &&
          only.kind !== "TFun" && only.kind !== "TAll"
        ? params[0]
        : `(${params.join(", ")})`;
      return `${head} -> ${toStringAt(type.result, names)}`;
    }
    case "TAll": {
      const hints = type.binders.map((b) => b.hint);
      const bounds = type.binders
        .map((b) => `${b.hint} <: ${toStringAt(b.bound, names)}`)
        .join(", ");
      // The j-th variable is `BVar j`, so hints go in front, in binder order.
      return `forall ${bounds}. ${toStringAt(type.body, [...hints, ...names])}`;
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
