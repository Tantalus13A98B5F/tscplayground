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
 * `open*` and `close*` are the only functions permitted to touch index
 * arithmetic. Everything else goes through them.
 *
 * Binders are n-ary and their bindings are *simultaneous*: the j-th variable of
 * a binder is `BVar j`, with no telescope reversal. `TAll`'s bounds are
 * therefore parallel -- a bound may not mention another variable of the same
 * quantifier. Nest quantifiers when you need that dependency.
 */

export type VarId = number & { readonly __brand: "VarId" };
export type EVarId = number & { readonly __brand: "EVarId" };
export type DataName = string & { readonly __brand: "DataName" };

export const mkVarId = (n: number): VarId => n as VarId;
export const mkEVarId = (n: number): EVarId => n as EVarId;
export const mkDataName = (s: string): DataName => s as DataName;

/** One variable of a `TAll`, with its upper bound. */
export interface Binder {
  readonly hint: string;
  readonly bound: Type;
}

/**
 * A quantifier's variables. Non-empty by construction: `forall . T` is just
 * `T`, and allowing it would mean every consumer has to handle a quantifier
 * that quantifies nothing. Elaboration is responsible for rejecting or
 * collapsing an empty binder list before it reaches this representation.
 *
 * (A nullary *function* type is a different matter -- `() -> Bool` is a real
 * type, so `TFun` takes a plain array.)
 */
export type Binders = readonly [Binder, ...Binder[]];

/**
 * Map over a quantifier's binders. Exists so that the one cast needed to
 * preserve non-emptiness lives in a single place rather than at every
 * traversal: `map` preserves length, but its type does not say so.
 */
export function mapBinders(
  binders: Binders,
  f: (binder: Binder) => Binder,
): Binders {
  return binders.map(f) as unknown as Binders;
}

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
  /**
   * `forall b0 <: B0, ..., bn <: Bn. body`, where `body` refers to the j-th
   * variable as `BVar j`. Bounds are parallel: they are outside the scope of
   * every variable the quantifier introduces, including earlier ones.
   */
  | {
    readonly kind: "TAll";
    readonly binders: Binders;
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

export function TFun(params: readonly Type[], result: Type): Type {
  return { kind: "TFun", params, result };
}

export function TAll(binders: Binders, body: Type): Type {
  return { kind: "TAll", binders, body };
}

export function TData(name: DataName, args: readonly Type[] = []): Type {
  return { kind: "TData", name, args };
}

/** Convenience for the common single-variable quantifier. */
export function mkBinder(hint: string, bound: Type): Binder {
  return { hint, bound };
}

/**
 * Replace the variables bound by the nearest enclosing binder, where that
 * binder's j-th variable is `BVar j`.
 *
 * A datatype declaration binds all its parameters this way too -- fields are
 * stored with params as `BVar 0..n-1` and no enclosing node -- so instantiating
 * a constructor is the same operation as instantiating a quantifier.
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
      // Only reachable if a node's arity disagrees with its binder or its
      // declaration, which earlier passes are responsible for rejecting.
      return replacement ?? TBad;
    }
    case "TFun":
      return TFun(
        type.params.map((param) => openAt(param, depth, replacements)),
        openAt(type.result, depth, replacements),
      );
    case "TAll":
      // Bounds are parallel, so they stay at this depth; only the body moves
      // inward, and by the full arity of the quantifier at once.
      return TAll(
        mapBinders(
          type.binders,
          (b) => mkBinder(b.hint, openAt(b.bound, depth, replacements)),
        ),
        openAt(type.body, depth + type.binders.length, replacements),
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
        mapBinders(
          type.binders,
          (b) => mkBinder(b.hint, closeAt(b.bound, depth, ids)),
        ),
        closeAt(type.body, depth + type.binders.length, ids),
      );
    case "TData":
      return TData(type.name, type.args.map((arg) => closeAt(arg, depth, ids)));
  }
}

/**
 * Abstract several free variables *simultaneously*: `ids[j]` becomes `BVar j`.
 *
 * Not the same as iterating `close`. Two `close` calls both run at depth 0, and
 * the second leaves the `BVar` produced by the first alone, so both variables
 * collapse onto index 0. Iterating is only correct when a binder node is
 * wrapped around the result between calls, which is what advances the depth.
 *
 * `ids` must be pairwise distinct.
 */
export function closeMany(type: Type, ids: readonly VarId[]): Type {
  return closeAt(type, 0, ids);
}

/** Sugar for a single-variable binder. */
export function close(type: Type, id: VarId): Type {
  return closeAt(type, 0, [id]);
}

/**
 * Replace free variables by identity, all at once: `ids[j]` becomes
 * `replacements[j]`.
 *
 * Simultaneous, which is *not* what iterating the single-variable version
 * gives you -- that would substitute later replacements into earlier ones.
 *
 * Unlike `open`, this touches no indices: an `FVar` carries an identity rather
 * than a position, so nothing shifts when a replacement lands under a binder.
 *
 * Precondition: `ids` pairwise distinct, and every replacement locally closed.
 * A dangling `BVar` in a replacement would be captured by whatever binder it
 * is substituted under.
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
        mapBinders(
          type.binders,
          (b) => mkBinder(b.hint, substMany(b.bound, ids, replacements)),
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
        allPairs(left.params, right.params, alphaEq) &&
        alphaEq(left.result, right.result);
    case "TAll":
      // `hint` is for printing only and deliberately not compared.
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
      const params = type.params.map((param) => toStringAt(param, names));
      // A lone parameter reads better bare, but not when it is itself a
      // function or a quantifier, where the arrow would be ambiguous.
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
      // The j-th variable is `BVar j`, so hints go in front in binder order.
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

/** Render a type using the name hints carried on binders. */
export function typeToString(type: Type): string {
  return toStringAt(type, []);
}
