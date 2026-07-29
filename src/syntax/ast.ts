/**
 * Surface syntax: the calculus as the user writes it.
 *
 * This is deliberately *not* `core/types.ts`. The differences are the whole
 * reason both exist:
 *
 *   - Names, not identities. `A` and `Pair` are both strings here; only
 *     elaboration knows which is a variable and which a declaration, since
 *     forward references mean the declaration table is incomplete until the
 *     file is.
 *   - A `Position` on every node, `Type` having none by design -- so any
 *     diagnostic pointing at source must be raised during elaboration, while
 *     the surface node is still in hand. `at` is where the node *starts*.
 *   - Sugar. Omitted bounds, omitted annotations, holes.
 *
 * Naming: core kinds are `T`-prefixed (`TFun`, `TAll`), surface kinds are
 * `Type`-suffixed (`FunType`, `AllType`). Elaboration handles both at once and
 * the two must never be confusable at a glance.
 */

import type { Position } from "../diagnostics/diagnostic.ts";

/** A name written in source, with the place it was written. */
export type Name = {
  readonly text: string;
  readonly at: Position;
};

/** Syntactic types. */
export type TypeNode =
  /** `unknown` -- top. */
  | { readonly kind: "UnknownType"; readonly at: Position }
  /** `never` -- bottom. */
  | { readonly kind: "NeverType"; readonly at: Position }
  /**
   * `A`, or `Pair[A, B]`. One node for type variables *and* saturated data
   * applications, since the parser cannot tell them apart without the
   * declaration table. Elaboration resolves it: in scope gives an `FVar`,
   * declared gives a `TData` after an arity check, neither gives `TBad`.
   */
  | {
    readonly kind: "NameType";
    readonly name: Name;
    readonly args: readonly TypeNode[];
    readonly at: Position;
  }
  /** `(A, B) -> C`, or `A -> B`. Arity is significant; see `TFun`. */
  | {
    readonly kind: "FunType";
    readonly params: readonly TypeNode[];
    readonly result: TypeNode;
    readonly at: Position;
  }
  /** `forall A <: B, C. body`. Rejected if it binds nothing; see `Binders`. */
  | {
    readonly kind: "AllType";
    readonly binders: readonly TypeBinder[];
    readonly body: TypeNode;
    readonly at: Position;
  }
  /** `_` -- elaborates to a fresh existential. The user-facing handle on inference. */
  | { readonly kind: "HoleType"; readonly at: Position }
  /**
   * Parser recovery, so one unparseable annotation does not abort the file.
   * Elaborates to `TBad` *without* a second diagnostic -- the parser already
   * reported it.
   */
  | { readonly kind: "BadType"; readonly at: Position };

/**
 * One variable of a `forall`. The bound is optional in source -- `forall A. T`
 * means `A <: unknown` -- and elaboration fills it in. The core's
 * `Binder.bound` stays mandatory: sugar lives on this side.
 */
export type TypeBinder = {
  readonly name: Name;
  readonly bound?: TypeNode;
  readonly at: Position;
};

/** Terms. */
export type Term =
  | { readonly kind: "Var"; readonly name: Name; readonly at: Position }
  /**
   * `\(x: A, y) => body`. N-ary to match `TFun`, so that `\(x, y) => e` and
   * `\x => \y => e` are writable as the distinct things they now are.
   * Annotations are optional; an omitted one becomes a fresh existential.
   */
  | {
    readonly kind: "Abs";
    readonly params: readonly Param[];
    readonly body: Term;
    readonly at: Position;
  }
  /** `f(a, b)`. */
  | {
    readonly kind: "App";
    readonly callee: Term;
    readonly args: readonly Term[];
    readonly at: Position;
  }
  /** `/\A <: B. body` -- explicit type abstraction. */
  | {
    readonly kind: "TypeAbs";
    readonly binders: readonly TypeBinder[];
    readonly body: Term;
    readonly at: Position;
  }
  /**
   * `f[A, B]` -- explicit instantiation. Implicit instantiation at `App` is
   * intended too, but this node stays because full F-sub needs it.
   */
  | {
    readonly kind: "TypeApp";
    readonly callee: Term;
    readonly args: readonly TypeNode[];
    readonly at: Position;
  }
  /**
   * `(term : A)`. Not sugar: in a bidirectional checker this is the only way to
   * enter checking mode from synthesis mode.
   */
  | {
    readonly kind: "Ann";
    readonly term: Term;
    readonly type: TypeNode;
    readonly at: Position;
  }
  /** `let x = bound in body`, or `let x : A = bound in body`. */
  | {
    readonly kind: "Let";
    readonly name: Name;
    readonly annotation?: TypeNode;
    readonly bound: Term;
    readonly body: Term;
    readonly at: Position;
  }
  /**
   * `C(a, b)`, saturated. Constructors are nominal and declared, so there is no
   * literal form: `true` is `Con("true", [])` over a nullary `Bool`.
   */
  | {
    readonly kind: "Con";
    readonly name: Name;
    readonly args: readonly Term[];
    readonly at: Position;
  }
  /** `match scrutinee { arms }`. */
  | {
    readonly kind: "Match";
    readonly scrutinee: Term;
    readonly arms: readonly Arm[];
    readonly at: Position;
  }
  /** Parser recovery. Synthesizes `TBad` without a second diagnostic. */
  | { readonly kind: "BadTerm"; readonly at: Position };

/** A lambda parameter. An omitted annotation is what inference is for. */
export type Param = {
  readonly name: Name;
  readonly annotation?: TypeNode;
  readonly at: Position;
};

export type Arm = {
  readonly pattern: Pattern;
  readonly body: Term;
  readonly at: Position;
};

/**
 * One level deep: a constructor's arguments are plain binders, not nested
 * patterns. Non-recursive data gains little from nesting, and one level makes
 * exhaustiveness a set-membership test rather than Maranget's algorithm.
 */
export type Pattern =
  /** `_` */
  | { readonly kind: "PWild"; readonly at: Position }
  /** `x` -- an irrefutable catch-all that binds the scrutinee. */
  | { readonly kind: "PVar"; readonly name: Name; readonly at: Position }
  /** `C(x, y)` -- saturated, and `x`/`y` bind the fields. */
  | {
    readonly kind: "PCon";
    readonly name: Name;
    readonly binders: readonly Name[];
    readonly at: Position;
  };

/**
 * `data Pair[A, B] = MkPair(A, B)`.
 *
 * Top-level only. `params` are the binding site: elaboration mints a fresh
 * `VarId` for each, elaborates the fields, then closes over them in *declared*
 * order -- which is why `closeMany` takes its order from the caller.
 *
 * Non-recursive in v1, so the declaration graph must be a DAG. That check
 * belongs with the declaration table, not here.
 */
export type DataDecl = {
  readonly name: Name;
  readonly params: readonly Name[];
  readonly constructors: readonly ConDecl[];
  readonly at: Position;
};

export type ConDecl = {
  readonly name: Name;
  readonly fields: readonly TypeNode[];
  readonly at: Position;
};

/** A whole source file: declarations, then the term to check. */
export type Program = {
  readonly decls: readonly DataDecl[];
  readonly term: Term;
  readonly at: Position;
};
