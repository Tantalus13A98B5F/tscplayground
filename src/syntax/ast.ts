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

/**
 * One position in a domain -- an arrow's parameter, or a constructor's field --
 * and the name the author may have written on it.
 *
 * The name is documentation, and dropping it at elaboration is what keeps it
 * that: `(x: A) -> B` and `(A) -> B` are one type, so a name can never decide
 * whether two types are equal, print differently, or make a cast go another
 * way. Nothing downstream of elaboration learns names exist, exactly as with a
 * transparent alias.
 *
 * What it does buy is the spelling, which is where a dependent arrow's binder
 * goes when there is one to bind. Until then a name here scopes over nothing.
 */
export type DomainType = {
  readonly name?: BindingIdent;
  readonly type: TypeNode;
  readonly at: Position;
};

export type TypeNode =
  /** `unknown` -- top. */
  | { readonly kind: "UnknownType"; readonly at: Position }
  /** `never` -- bottom. */
  | { readonly kind: "NeverType"; readonly at: Position }
  /**
   * The type a `def` parameter was not given. Nothing an author writes; the
   * parser puts one wherever a `def` omitted an annotation, and elaboration
   * reports it and answers `bad`.
   *
   * A node rather than an absence because a `def`'s parameter has no other
   * source -- its body is inferred, or checked against its own signature, and
   * never sits where a context would know the type. Standing the omission in
   * the tree settles it once, at the binder, and lets the signature and the
   * body both be built the ordinary way.
   */
  | {
    readonly kind: "MissingParamType";
    readonly name: BindingIdent;
    readonly at: Position;
  }
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
    readonly params: readonly DomainType[];
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
  /**
   * A run of adjacent `def`s and what follows them, the run being the scope
   * over which they see each other. What `def` adds is a scope and not a shape,
   * which is why this holds a list where `Let` holds one binding.
   *
   * Named for what it is, not how it is written: the surface spells it `def`
   * and there is no `let rec` to grep for.
   */
  | {
    readonly kind: "LetRec";
    readonly defs: readonly DefItem[];
    readonly body: TermNode;
    readonly at: Position;
  }
  /** `match e` followed by `| pat -> body` arms, at least one. */
  | {
    readonly kind: "Match";
    readonly scrutinee: TermNode;
    readonly arms: readonly MatchArm[];
    /**
     * Which datatype the arms' patterns resolve against, written
     * `match xs as List with` and otherwise **filled by the checker**, which
     * knows it from the scrutinee's type.
     *
     * The one thing in this tree a later phase writes, and the exception is
     * paid for: a pattern name alone does not say which datatype it belongs
     * to once a value presents as another, and two datatypes along one chain
     * may spell a constructor the same. Nothing untyped can tell those apart,
     * so either the author says it or the checker records what it already
     * worked out -- and demanding it of the author would be demanding
     * bookkeeping, which is the thing `def`'s annotation rule exists to avoid.
     *
     * Absent where a program was not checked, or checking failed here.
     * Evaluation then falls back to the nearest datatype in the value's own
     * chain admitting the pattern's name: exact wherever the chain spells no
     * constructor twice, and a tiebreak where it does.
     */
    datatype?: string;
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
  /**
   * `datatype NonEmpty[A] <: List[A]` -- the datatype every value of this one
   * also presents as, and absent for one that presents as nothing.
   *
   * Written where a quantifier writes its bound and with the same token, which
   * is the same idea at a declaration: what may stand in for this.
   */
  readonly base?: TypeNode;
  readonly ctors: readonly CtorDecl[];
  readonly at: Position;
};

/**
 * Fields are positional, as the patterns that take them apart are, and a name
 * on one is the documentation a `DomainType` name always is -- an arrow's
 * domain and a constructor's are one syntax, so they are one rule.
 *
 * `| C` and `| C()` are *different declarations*, which is why the domain is
 * absent rather than empty for the first: a bare name declares a value of the
 * datatype, a parameter list a function of no arguments. Only a monomorphic
 * datatype may have the first, a value of a parameterised one having no single
 * type to be. Carrying the distinction here is what lets the declaration say
 * which it produces, where the field count alone cannot.
 */
export type CtorDecl = {
  readonly name: Ident;
  /** The domain, or absent for a bare name -- empty is `C()`, never `C`. */
  readonly params?: readonly DomainType[];
  /** `-> Cons(x, r)`. Required exactly where the datatype has a base. */
  readonly coercion?: TermNode;
  readonly at: Position;
};

/**
 * Which of the base's constructors a value of this one presents as, and what
 * it is built from: `| One(x: A) -> Cons(x, Nil())`.
 *
 * A constructor *name* and not a term, which is the whole of why this is
 * affordable. A term would have to be typed at the base, and subsumption
 * unpins a head -- so nothing downstream could say which of the base's
 * constructors a value presents as without asking the checker, and evaluation
 * does not ask. As a slot the answer is in the tree, and the same rule spells
 * Scala's `extends Bar(args)`.
 *
 * The *arguments* are ordinary terms, so a coercion may still compute; they
 * are checked against the named constructor's fields, and scope over the
 * fields of the constructor declaring it -- which is the first thing a
 * `DomainType`'s name has ever bound.
 */
/**
 * What a value of this constructor presents as: an ordinary term, restricted
 * so that **every tail position is a constructor of the declared base**.
 *
 * Tails distribute through `let` and `match`, so a coercion may compute and
 * may branch, and each branch is pinned on its own. The restriction is not
 * about types -- a body merely *typed* at the base would have its head unpinned
 * by subsumption, a sibling subtype's value having the base's type -- so it is
 * enforced on the tree, by `resolveCoercionTails`, which also rewrites each
 * tail name to its qualified form. Both later phases then read one tree that
 * already says which constructor was meant.
 *
 * The arguments scope over the fields of the constructor declaring it, under
 * the names the declaration gave them -- which is the first thing a
 * `DomainType`'s name has ever bound.
 */

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
/** A `Let` short of its body, and equally a member of a `LetRec`. */
/**
 * A `def`: what a `let` binds, plus the two things only a `def` has.
 *
 * `bound` is an `Abs` by construction -- a `def` always writes at least one
 * parameter list, and the parser has folded them into nested `Abs`s by here.
 * `annotation` is the signature those lists and the result type fold into, and
 * is there only when the author wrote enough for one, which is what decides
 * whether the group sees this member before its body is checked. A parameter
 * left bare carries a `MissingParamType` by here, so even that is enough.
 */
export type DefItem = {
  readonly name: BindingIdent;
  readonly annotation?: TypeNode;
  readonly bound: Extract<TermNode, { kind: "Abs" }>;
  readonly at: Position;
};
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
