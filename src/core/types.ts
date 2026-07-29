/**
 * Internal type representation.
 *
 * Locally nameless: variables bound by an enclosing binder are `BVar` (de Bruijn
 * index), variables standing free in the context are `FVar` (stable identity).
 * The invariant that makes this pay off:
 *
 *   - a `BVar` never escapes into the context;
 *   - an `FVar` never appears under a binder that has not been opened.
 *
 * `open` and `close` are the only functions permitted to touch index arithmetic.
 * Everything else goes through them.
 */

export type VarId = number & { readonly __brand: "VarId" };
export type EVarId = number & { readonly __brand: "EVarId" };
export type DataName = string & { readonly __brand: "DataName" };

export const mkVarId = (n: number): VarId => n as VarId;
export const mkEVarId = (n: number): EVarId => n as EVarId;
export const mkDataName = (s: string): DataName => s as DataName;

export type Type =
  /** Top. */
  | { readonly kind: "TUnknown" }
  /** Bottom. */
  | { readonly kind: "TNever" }
  /**
   * The type of an expression whose type could not be determined. Absorbing in
   * both directions -- `TBad <: T` and `T <: TBad` -- so one failure does not
   * cascade into a diagnostic at every subsequent use. Never shown to the user.
   */
  | { readonly kind: "TBad" }
  | { readonly kind: "BVar"; readonly index: number }
  | { readonly kind: "FVar"; readonly id: VarId; readonly hint: string }
  /** An unsolved existential variable; the solution lives in the context. */
  | { readonly kind: "EVar"; readonly id: EVarId; readonly hint: string }
  | { readonly kind: "TFun"; readonly from: Type; readonly to: Type }
  /** `forall X <: bound. body` -- `body` refers to X as `BVar 0`. */
  | {
    readonly kind: "TAll";
    readonly hint: string;
    readonly bound: Type;
    readonly body: Type;
  }
  /**
   * A saturated nominal type constructor: `args.length` always equals the
   * arity of the declaration named `name`. Primitives are the nullary case,
   * declared in the prelude, so they need no separate node.
   */
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

export function TFun(from: Type, to: Type): Type {
  return { kind: "TFun", from, to };
}

export function TAll(hint: string, bound: Type, body: Type): Type {
  return { kind: "TAll", hint, bound, body };
}

export function TData(name: DataName, args: readonly Type[] = []): Type {
  return { kind: "TData", name, args };
}

/**
 * Replace the variables bound by the nearest enclosing binder, where that
 * binder's i-th variable is `BVar i`.
 *
 * `TAll` binds one variable. A datatype declaration binds all its parameters
 * *simultaneously* rather than as nested binders, so instantiating a
 * constructor's field types passes the whole argument list at once.
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
      // Only reachable if a `TData` node's arity disagrees with its declaration,
      // which the declaration pass is responsible for rejecting first.
      return replacement ?? TBad;
    }
    case "TFun":
      return TFun(
        openAt(type.from, depth, replacements),
        openAt(type.to, depth, replacements),
      );
    case "TAll":
      // The bound sits outside the scope of the variable it bounds, so only the
      // body goes one level deeper.
      return TAll(
        type.hint,
        openAt(type.bound, depth, replacements),
        openAt(type.body, depth + 1, replacements),
      );
    case "TData":
      // Not a binder, but very much a traversal case: skipping this would leave
      // stale `BVar`s inside type arguments, and nothing would complain.
      return TData(
        type.name,
        type.args.map((arg) => openAt(arg, depth, replacements)),
      );
  }
}

/** Instantiate the nearest binder's variable with `replacement`. */
export function open(type: Type, replacement: Type): Type {
  return openAt(type, 0, [replacement]);
}

/** Instantiate a simultaneous binding, `BVar i` taking `replacements[i]`. */
export function openMany(type: Type, replacements: readonly Type[]): Type {
  return openAt(type, 0, replacements);
}

function closeAt(type: Type, depth: number, id: VarId): Type {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "BVar":
    case "EVar":
      return type;
    case "FVar":
      return type.id === id ? BVar(depth) : type;
    case "TFun":
      return TFun(closeAt(type.from, depth, id), closeAt(type.to, depth, id));
    case "TAll":
      return TAll(
        type.hint,
        closeAt(type.bound, depth, id),
        closeAt(type.body, depth + 1, id),
      );
    case "TData":
      return TData(type.name, type.args.map((arg) => closeAt(arg, depth, id)));
  }
}

/** Abstract the free variable `id`, turning it back into the nearest `BVar`. */
export function close(type: Type, id: VarId): Type {
  return closeAt(type, 0, id);
}

/** Does the existential `id` occur in `type`? The occurs check. */
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
      return occurs(id, type.from) || occurs(id, type.to);
    case "TAll":
      return occurs(id, type.bound) || occurs(id, type.body);
    case "TData":
      return type.args.some((arg) => occurs(id, arg));
  }
}

/** Structural equality. Alpha-equivalence is free: bound variables are indices. */
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
        alphaEq(left.from, right.from) && alphaEq(left.to, right.to);
    case "TAll":
      // `hint` is for printing only and deliberately not compared.
      return right.kind === "TAll" &&
        alphaEq(left.bound, right.bound) && alphaEq(left.body, right.body);
    case "TData":
      return right.kind === "TData" &&
        left.name === right.name &&
        left.args.length === right.args.length &&
        left.args.every((arg, i) => {
          const other = right.args[i];
          return other !== undefined && alphaEq(arg, other);
        });
  }
}

function toStringAt(type: Type, names: readonly string[]): string {
  switch (type.kind) {
    case "TUnknown":
      return "unknown";
    case "TNever":
      return "never";
    case "TBad":
      // Should be filtered out before display; visible only in dumps.
      return "<bad>";
    case "BVar":
      // Well-formed types are closed, so an unnamed index means a bug upstream.
      return names[type.index] ?? `?${type.index}`;
    case "FVar":
      return type.hint;
    case "EVar":
      return `?${type.hint}`;
    case "TFun": {
      const from = type.from.kind === "TFun" || type.from.kind === "TAll"
        ? `(${toStringAt(type.from, names)})`
        : toStringAt(type.from, names);
      return `${from} -> ${toStringAt(type.to, names)}`;
    }
    case "TAll":
      return `forall ${type.hint} <: ${toStringAt(type.bound, names)}. ${
        toStringAt(type.body, [type.hint, ...names])
      }`;
    case "TData":
      return type.args.length === 0
        ? type.name
        : `${type.name}[${
          type.args.map((arg) => toStringAt(arg, names)).join(", ")
        }]`;
  }
}

/** Render a type using the name hints carried on binders. */
export function typeToString(type: Type): string {
  return toStringAt(type, []);
}
