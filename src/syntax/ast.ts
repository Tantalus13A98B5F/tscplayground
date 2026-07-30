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
  /**
   * `(A, B) -> C`, or `[T <: A](B) -> C`.
   *
   * Quantifiers fuse into the arrow rather than standing alone: a bare `forall`
   * over a non-function is the unsound case once effects exist, so requiring a
   * parameter list *is* the value restriction. Arity is significant; see `TFun`.
   */
  | {
    readonly kind: "FunType";
    readonly tyParams: readonly TypeBinder[];
    readonly params: readonly TypeNode[];
    readonly result: TypeNode;
    readonly at: Position;
  }
  /** Parser recovery. Elaborates to `TBad` with no second diagnostic. */
  | { readonly kind: "BadType"; readonly at: Position };

/**
 * An omitted `bound` means `<: unknown`; the core's `Binder.bound` is required.
 * Bounds telescope: binder `j` may mention binders before it, not itself or any
 * after it.
 */
export type TypeBinder = {
  readonly name: Name;
  readonly bound?: TypeNode;
  readonly at: Position;
};

export type Term =
  | { readonly kind: "Var"; readonly name: Name; readonly at: Position }
  /** `\(x: A, y) e`, or `\[T <: A](x: T) e`. Binders fuse as in `FunType`. */
  | {
    readonly kind: "Abs";
    readonly tyParams: readonly TypeBinder[];
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
  /**
   * `f[A, B]`. Separate from `App` so `f[A]` and `f[A]()` stay distinct, and
   * must be saturated -- partial instantiation needs index arithmetic that
   * implicit instantiation at `App` makes pointless.
   */
  | {
    readonly kind: "TypeApp";
    readonly callee: Term;
    readonly args: readonly TypeNode[];
    readonly at: Position;
  }
  /**
   * `let x = e1; e2`, or `let x : A = e1; e2`. With no ascription node the
   * annotated form is the only way into checking mode, so checking a
   * subexpression means naming it.
   */
  | {
    readonly kind: "Let";
    readonly name: Name;
    readonly annotation?: TypeNode;
    readonly bound: Term;
    readonly body: Term;
    readonly at: Position;
  }
  /** `match e` followed by `| pat => body` arms, at least one. */
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
 * `data Pair[A, B] | MkPair(a: A, b: B)`, top-level only -- `parseExp` has no
 * `data` case, so that holds by absence rather than by a check.
 *
 * Contributes *term bindings* -- `MkPair : [A, B](a: A, b: B) -> Pair[A, B]`,
 * `true : Bool` -- so there is no constructor term form, and saturation comes
 * free from function arity. Declarations are unscoped: the table is built before
 * any term is elaborated and every constructor is seeded ahead of the first
 * `let`, so a type and its constructors share one scope. Among themselves they
 * telescope -- decl `j` sees only decls before it, which is what rules out
 * recursion in v1.
 */
export type DataDecl = {
  readonly name: Name;
  readonly params: readonly Name[];
  readonly constructors: readonly ConDecl[];
  readonly at: Position;
};

export type ConDecl = {
  readonly name: Name;
  readonly fields: readonly Field[];
  readonly at: Position;
};

/** The annotation is required: unlike `Param`, there is nothing to infer from. */
export type Field = {
  readonly name: Name;
  readonly annotation: TypeNode;
  readonly at: Position;
};

/** One top-level `let`, before `parseProgram` folds the chain into `term`. */
export type Bind = {
  readonly name: Name;
  readonly annotation?: TypeNode;
  readonly bound: Term;
  readonly at: Position;
};

export type Program = {
  readonly decls: readonly DataDecl[];
  readonly term: Term;
  readonly at: Position;
};
