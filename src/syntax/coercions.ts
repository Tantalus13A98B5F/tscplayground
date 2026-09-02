/**
 * Resolving the tails of coercion bodies, between parsing and everything else.
 *
 * A coercion is an ordinary term with one restriction: **every tail position
 * is a constructor of the declared base**, named. Tails distribute through
 * `let` and `match`, so a coercion may compute and may branch --
 *
 *     | One(x: A)  -> Cons(x, Nil())
 *     | Two(x: A)  -> let y = f x; Cons(x, y)
 *     | Some(x: A) -> match p x with | True -> Cons(x, Nil()) | False -> Nil()
 *
 * -- while what the value ends up being is still readable off the tree.
 *
 * Which is the point, and why the tail name is *rewritten* here to its
 * qualified form rather than left to each reader. Resolving it takes no types,
 * so it can happen before either consumer, and then the checker and the
 * evaluator read one tree that already says which constructor was meant. Left
 * alone, the checker would resolve `Cons` against the base while the evaluator
 * resolved it through a shadowable flat namespace, and the two would disagree
 * exactly when a `let` or a later datatype reused the name.
 *
 * Three earlier formulations were wrong and are recorded so they are not
 * retried: a body merely *typed* at the base (subsumption unpins the head -- a
 * value of a sibling subtype has the base's type, and two such declarations
 * loop at construction with a perfectly acyclic `<:`), a tail name left to
 * resolve in the term scope (a `let` shadows it), and no body at all but a
 * constructor name and arguments, which pins the head by giving up branching
 * and computation that the rewrite buys back.
 */

import type { Diagnostic, Position } from "../diagnostics/diagnostic.ts";
import { reportError } from "../diagnostics/diagnostic.ts";
import type { CtorDecl, DatatypeDecl, Program, TermNode } from "./ast.ts";
import { qualifiedCtor, QUALIFIER } from "./ast.ts";

/**
 * Rewrite every coercion tail in `program` to name its constructor through the
 * declared base, reporting the ones that are no such thing.
 *
 * A new tree rather than a mutated one: the nodes are `readonly`, and a pass
 * that rebuilds only the spines it walks costs one path per tail.
 */
export function resolveCoercionTails(
  program: Program,
): { readonly program: Program; readonly diagnostics: Diagnostic[] } {
  const diagnostics: Diagnostic[] = [];
  const decls = program.decls.map((decl) =>
    decl.kind === "DatatypeDecl" ? resolveDatatype(decl, diagnostics) : decl
  );
  return { program: { ...program, decls }, diagnostics };
}

function resolveDatatype(
  decl: DatatypeDecl,
  diagnostics: Diagnostic[],
): DatatypeDecl {
  // Only a base written as a datatype name gives a name to qualify with. One
  // written otherwise is refused during elaboration, which is also where an
  // unknown one is, so nothing is said twice by saying nothing here.
  const base = decl.base?.kind === "NameType" ? decl.base.name.text : undefined;
  if (base === undefined) return decl;
  const ctors = decl.ctors.map((ctor): CtorDecl =>
    ctor.coercion === undefined ? ctor : {
      ...ctor,
      coercion: resolveTails(ctor.coercion, base, diagnostics),
    }
  );
  return { ...decl, ctors };
}

/**
 * Rewrite the tails of one body. `let` and `match` are spines rather than
 * tails -- what a `let` evaluates to is its body, and what a `match` evaluates
 * to is the arm that fires -- so each branch is pinned on its own.
 */
function resolveTails(
  term: TermNode,
  base: string,
  diagnostics: Diagnostic[],
): TermNode {
  switch (term.kind) {
    case "Let":
    case "LetRec":
      return { ...term, body: resolveTails(term.body, base, diagnostics) };
    case "Match":
      return {
        ...term,
        arms: term.arms.map((arm) => ({
          ...arm,
          body: resolveTails(arm.body, base, diagnostics),
        })),
      };
    default:
      return resolveTail(term, base, diagnostics);
  }
}

/**
 * One tail: a constructor of `base`, applied or not.
 *
 * `Nil` and `Nil()` are different declarations, and `Nil[Bool]()` puts a type
 * application between the name and its arguments, so the name is found by
 * peeling whatever stands between rather than by matching one shape.
 */
function resolveTail(
  term: TermNode,
  base: string,
  diagnostics: Diagnostic[],
): TermNode {
  const rebuilt = rebuildHead(term, base, diagnostics);
  if (rebuilt !== undefined) return rebuilt;
  diagnostics.push(reportError(
    `a coercion ends in a constructor of ${base}, applied to its fields`,
    term.at,
  ));
  return term;
}

/** The same term with its head name qualified, or absent if it has no name. */
function rebuildHead(
  term: TermNode,
  base: string,
  diagnostics: Diagnostic[],
): TermNode | undefined {
  switch (term.kind) {
    case "Var": {
      const name = qualify(term.name.text, base, term.at, diagnostics);
      return { ...term, name: { ...term.name, text: name } };
    }
    case "App": {
      const callee = rebuildHead(term.callee, base, diagnostics);
      return callee === undefined ? undefined : { ...term, callee };
    }
    case "TypeApp": {
      const callee = rebuildHead(term.callee, base, diagnostics);
      return callee === undefined ? undefined : { ...term, callee };
    }
    default:
      return undefined;
  }
}

/**
 * `Cons` under base `List` becomes `List.Cons`. One already written that way
 * is left alone; one qualified by *another* datatype is refused, since a tail
 * naming a sibling subtype's constructor is what the rule exists to stop.
 *
 * Whether the result names anything, at any arity, is not asked here -- that
 * is the check's business, and this pass runs whether or not it will. Which is
 * also why it is not asked here: a tail naming no constructor of the base
 * would then be reported twice, once as the name that was written and once as
 * the name it was rewritten to. `unknown name List.Snoc` says both.
 */
function qualify(
  name: string,
  base: string,
  at: Position,
  diagnostics: Diagnostic[],
): string {
  if (!name.includes(QUALIFIER)) return qualifiedCtor(base, name);
  if (name.startsWith(`${base}${QUALIFIER}`)) return name;
  diagnostics.push(reportError(
    `a coercion ends in a constructor of ${base}, and ${name} is not one`,
    at,
    name.length,
  ));
  return name;
}
