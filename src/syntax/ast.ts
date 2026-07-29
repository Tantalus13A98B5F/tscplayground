/**
 * Surface syntax: names rather than identities, a `Position` on every node, and
 * sugar. Core kinds are `T`-prefixed (`TFun`), surface kinds `Type`-suffixed
 * (`FunType`); elaboration handles both at once, so they must not be confusable.
 */

import type { Position } from "../diagnostics/diagnostic.ts";

export type Name = {
  readonly text: string;
  readonly at: Position;
};

export type TypeNode =
  /** `unknown` -- top. */
  | { readonly kind: "UnknownType"; readonly at: Position }
  /** `never` -- bottom. */
  | { readonly kind: "NeverType"; readonly at: Position }
  /**
   * `A`, or `Pair[A, B]`: type variables and data applications share a node,
   * being indistinguishable without the declaration table. Elaboration resolves
   * it to `FVar`, to `TData` after an arity check, or to `TBad`.
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
  /** `forall A <: B, C. body`. The grammar requires at least one binder. */
  | {
    readonly kind: "AllType";
    readonly binders: readonly TypeBinder[];
    readonly body: TypeNode;
    readonly at: Position;
  }
  /** Parser recovery. Elaborates to `TBad` with no second diagnostic. */
  | { readonly kind: "BadType"; readonly at: Position };

/** An omitted `bound` means `<: unknown`; the core's `Binder.bound` is required. */
export type TypeBinder = {
  readonly name: Name;
  readonly bound?: TypeNode;
  readonly at: Position;
};

export type Term =
  | { readonly kind: "Var"; readonly name: Name; readonly at: Position }
  /** `\(x: A, y) => body`. N-ary to match `TFun`. */
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
  /** `/\A <: B. body`. */
  | {
    readonly kind: "TypeAbs";
    readonly binders: readonly TypeBinder[];
    readonly body: Term;
    readonly at: Position;
  }
  /** `f[A, B]`. Implicit instantiation at `App` is intended too. */
  | {
    readonly kind: "TypeApp";
    readonly callee: Term;
    readonly args: readonly TypeNode[];
    readonly at: Position;
  }
  /**
   * `let x = bound in body`, or `let x : A = bound in body`. With no ascription
   * node the annotated form is the only way into checking mode, so checking a
   * subexpression means naming it: `f((e : A))` is `let t : A = e in f(t)`.
   */
  | {
    readonly kind: "Let";
    readonly name: Name;
    readonly annotation?: TypeNode;
    readonly bound: Term;
    readonly body: Term;
    readonly at: Position;
  }
  /** `match scrutinee { arms }`. */
  | {
    readonly kind: "Match";
    readonly scrutinee: Term;
    readonly arms: readonly Arm[];
    readonly at: Position;
  }
  /** Parser recovery. Synthesizes `TBad` with no second diagnostic. */
  | { readonly kind: "BadTerm"; readonly at: Position };

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
 * One level deep, which keeps exhaustiveness a set-membership test rather than
 * Maranget's algorithm.
 */
export type Pattern =
  | { readonly kind: "PWild"; readonly at: Position }
  /**
   * `C`, or `C(x, y)` -- always a constructor. There is no catch-all *binding*
   * form, and that absence is what disambiguates: `C` in arm position is a
   * constructor, `x` inside `C(x, y)` is a binder. Allowing a bare binder would
   * collide with nullary constructors and make a misspelling swallow every case.
   */
  | {
    readonly kind: "PCon";
    readonly name: Name;
    readonly args: readonly Name[];
    readonly at: Position;
  };

/**
 * `data Pair[A, B] = MkPair(A, B)`, top-level only.
 *
 * Contributes *term bindings* -- `MkPair : forall A, B. (A, B) -> Pair[A, B]`,
 * `true : Bool` -- so there is no constructor term form, and saturation comes
 * free from function arity. `params` are a binding site: elaboration mints a
 * fresh `VarId` for each and closes over them in *declared* order.
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

export type Program = {
  readonly decls: readonly DataDecl[];
  readonly term: Term;
  readonly at: Position;
};
