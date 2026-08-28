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
 * An `Ident` at a binding occurrence, which may decline to name itself. The
 * record is always there; only the name inside it may not be.
 *
 * `_` is a lexical identifier, so telling the two apart is a decision the
 * parser makes once. Most of what that buys is in the positions that *cannot*
 * take one: a declaration's name and a constructor's are `Ident`, so "a
 * constructor may not be `_`" is a thing the types say rather than a check.
 *
 * Uses stay `Ident` throughout. Nothing nameless is ever indexed, so `_` in a
 * type or a term is a name that resolves to nothing, and needs no case here.
 */
export type BindingIdent = {
  /**
   * The name it binds, or `undefined` for `_`. Named as `Ident`'s is, so a
   * binding position reads the same whichever of the two sits there.
   */
  readonly text: string | undefined;
  readonly at: Position;
};

/**
 * The two binding positions, differing in what an *absent* annotation means:
 * `TypeParam` defaults to `<: unknown`, while a `Param` takes its type from the
 * checking context -- never from an EVar, so a `fn` with no annotation and no
 * expected type is an error rather than a guess. Those are different enough
 * that the differing field names -- all that separates them under structural
 * typing -- must stay.
 *
 * A constructor's parameters are not among them. It is an ordinary function,
 * and a function type names nothing, so its fields are types alone.
 */
export type TypeParam = {
  readonly name: BindingIdent;
  /** Parallel, not telescoping: may name an enclosing binder, never its group. */
  readonly bound?: TypeNode;
  readonly at: Position;
};

export type Param = {
  readonly name: BindingIdent;
  readonly annotation?: TypeNode;
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
  };

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
    readonly name: BindingIdent;
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
    readonly args: readonly BindingIdent[];
    readonly at: Position;
  };

/**
 * `datatype Pair[A, B] = | MkPair(A, B)`, top-level only -- `exp` has no
 * `datatype` case, so that holds by absence rather than by a check.
 *
 * Contributes *term bindings* (`MkPair : [A, B](A, B) -> Pair[A, B]`), so there
 * is no constructor term form and saturation follows from function arity.
 * Unscoped: every constructor is seeded before the first `let` is elaborated.
 */
export type DatatypeDecl = {
  readonly kind: "DatatypeDecl";
  readonly name: Ident;
  readonly typeParams: readonly BindingIdent[];
  readonly ctors: readonly CtorDecl[];
  readonly at: Position;
};

/**
 * Fields are types alone, positional as the patterns that take them apart are.
 * Names would be dropped on the way to `TFun`, which has none -- when a domain
 * carries names, a constructor's may come back with them.
 */
export type CtorDecl = {
  readonly name: Ident;
  readonly params: readonly TypeNode[];
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
  readonly typeParams: readonly BindingIdent[];
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
  readonly name: BindingIdent;
  readonly annotation?: TypeNode;
  readonly bound: TermNode;
  readonly at: Position;
};

export type Program = {
  readonly decls: readonly TypeDecl[];
  readonly term: TermNode;
  readonly at: Position;
};

/**
 * What to print at a binding position. A wildcard has no name, so this is a
 * hint and never a key -- `text` is what a lookup or a duplicate check asks,
 * and it is `undefined` exactly where this falls back to `_`.
 */
export function bindingHint(name: BindingIdent): string {
  return name.text ?? "_";
}
