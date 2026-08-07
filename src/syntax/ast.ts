/**
 * Surface syntax: names rather than identities, a `Position` on every node, and
 * sugar. Core kinds are `T`-prefixed (`TFun`), surface kinds `Type`-suffixed
 * (`FunType`); elaboration handles both at once, so they must not be confusable.
 */

import type { Position } from "../diagnostics/diagnostic.ts";

export type Ident = {
  readonly text: string;
  readonly at: Position;
};

/**
 * The three binding positions, differing in what an *absent* annotation means:
 * `TypeParam` defaults to `<: unknown`, `Param` opens an existential, and
 * `CtorParam` has no absent case. Two of those are opposites, so the differing
 * field names -- all that separates them under structural typing -- must stay.
 */
export type TypeParam = {
  readonly name: Ident;
  /** Parallel, not telescoping: may name an enclosing binder, never its group. */
  readonly bound?: TypeNode;
  readonly at: Position;
};

export type Param = {
  readonly name: Ident;
  readonly annotation?: TypeNode;
  readonly at: Position;
};

/** A constructor is an ordinary function, so these are literally its parameters. */
export type CtorParam = {
  readonly name: Ident;
  readonly annotation: TypeNode;
  readonly at: Position;
};

export type TypeNode =
  /** `unknown` -- top. */
  | { readonly kind: "UnknownType"; readonly at: Position }
  /** `never` -- bottom. */
  | { readonly kind: "NeverType"; readonly at: Position }
  /**
   * `A`, or `Pair[A, B]`. Variables and datatype applications share a node,
   * being indistinguishable without the declaration table; elaboration resolves
   * it to `FVar`, to `TData` after an arity check, or to `TBad`.
   */
  | {
    readonly kind: "NameType";
    readonly name: Ident;
    readonly args: readonly TypeNode[];
    readonly at: Position;
  }
  /**
   * `(A, B) -> C`, or `[T <: A](B) -> C`. Quantifiers fuse into the arrow: a
   * bare `forall` over a non-function is the unsound case once effects exist,
   * so requiring a parameter list *is* the value restriction. See `TFun`.
   */
  | {
    readonly kind: "FunType";
    readonly typeParams: readonly TypeParam[];
    readonly params: readonly TypeNode[];
    readonly result: TypeNode;
    readonly at: Position;
  }
  /**
   * A type nothing can be said about, for a name elaboration cannot resolve. It
   * becomes `TBad`, which checks against anything, so one unresolved name does
   * not fail every use of it. The parser never builds one: a type it cannot
   * read costs the item it sits in.
   */
  | { readonly kind: "BadType"; readonly at: Position };

export type TermNode =
  | { readonly kind: "Var"; readonly name: Ident; readonly at: Position }
  /** `\(x: A, y) e`, or `\[T <: A](x: T) e`. Binders fuse as in `FunType`. */
  | {
    readonly kind: "Abs";
    readonly typeParams: readonly TypeParam[];
    readonly params: readonly Param[];
    readonly body: TermNode;
    readonly at: Position;
  }
  /** `f(a, b)`. */
  | {
    readonly kind: "App";
    readonly callee: TermNode;
    readonly args: readonly TermNode[];
    readonly at: Position;
  }
  /** `f[A, B]`. Separate from `App` so `f[A]` and `f[A]()` stay distinct. */
  | {
    readonly kind: "TypeApp";
    readonly callee: TermNode;
    readonly args: readonly TypeNode[];
    readonly at: Position;
  }
  /**
   * `let x = e1; e2`, or `let x : A = e1; e2`. With no ascription node this is
   * the only way into checking mode, so checking a subexpression means naming it.
   */
  | {
    readonly kind: "Let";
    readonly name: Ident;
    readonly annotation?: TypeNode;
    readonly bound: TermNode;
    readonly body: TermNode;
    readonly at: Position;
  }
  /** `match e` followed by `| pat -> body` arms, at least one. */
  | {
    readonly kind: "Match";
    readonly scrutinee: TermNode;
    readonly arms: readonly MatchArm[];
    readonly at: Position;
  };

export type MatchArm = {
  readonly pattern: MatchPat;
  readonly body: TermNode;
  readonly at: Position;
};

/**
 * One level deep, which keeps exhaustiveness a set-membership test rather than
 * Maranget's algorithm.
 */
export type MatchPat =
  | { readonly kind: "PWild"; readonly at: Position }
  /**
   * `C`, or `C(x, y)` -- always a constructor, never a binder. There is no
   * catch-all binding form: it would collide with nullary constructors and make
   * a misspelling swallow every case.
   */
  | {
    readonly kind: "PCtor";
    readonly name: Ident;
    readonly args: readonly Ident[];
    readonly at: Position;
  };

/**
 * `datatype Pair[A, B] = | MkPair(a: A, b: B)`, top-level only -- `exp` has no
 * `datatype` case, so that holds by absence rather than by a check.
 *
 * Contributes *term bindings* (`MkPair : [A, B](a: A, b: B) -> Pair[A, B]`), so
 * there is no constructor term form and saturation follows from function arity.
 * Unscoped: every constructor is seeded before the first `let` is elaborated.
 */
export type DatatypeDecl = {
  readonly kind: "DatatypeDecl";
  readonly name: Ident;
  readonly typeParams: readonly Ident[];
  readonly ctors: readonly CtorDecl[];
  readonly at: Position;
};

export type CtorDecl = {
  readonly name: Ident;
  readonly params: readonly CtorParam[];
  readonly at: Position;
};

/**
 * `typedef Endo[A] = (A) -> A`, transparent and expanded during elaboration:
 * `typeParams` close exactly as a datatype's do, and a use opens them. Nothing
 * downstream learns aliases exist, which also means an alias gets structural
 * variance where a datatype is invariant.
 */
export type AliasDecl = {
  readonly kind: "AliasDecl";
  readonly name: Ident;
  readonly typeParams: readonly Ident[];
  readonly body: TypeNode;
  readonly at: Position;
};

/**
 * Type declarations in source order, which is significant: a declaration may
 * name only those before it, which is what rules out recursion in v1. One list
 * rather than two, since aliases and datatypes order against each other.
 */
export type TypeDecl = DatatypeDecl | AliasDecl;

/** One top-level `let`, before `parseProgram` folds the chain into `term`. */
export type LetItem = {
  readonly name: Ident;
  readonly annotation?: TypeNode;
  readonly bound: TermNode;
  readonly at: Position;
};

export type Program = {
  readonly decls: readonly TypeDecl[];
  readonly term: TermNode;
  readonly at: Position;
};
