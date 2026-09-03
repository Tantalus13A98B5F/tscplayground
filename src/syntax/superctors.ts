/**
 * Rewriting the tails of a super constructor body, during elaboration.
 *
 * A super constructor is an ordinary term with one restriction: **every tail
 * position is a constructor of the declared super type**, named. Tails
 * distribute through `let` and `match`, so a super constructor may compute and
 * may branch --
 *
 *     | One(x: A)  -> Cons(x, Nil())
 *     | Two(x: A)  -> let y = f x; Cons(x, y)
 *     | Some(x: A) -> match p x with | True -> Cons(x, Nil()) | False -> Nil()
 *
 * -- while what the value ends up being is still readable off the tree.
 *
 * Which is the point, and why the tail name is *rewritten* rather than left to
 * each reader. Left alone, the checker would resolve `Cons` against the super
 * type while the evaluator resolved it through a shadowable flat namespace, and
 * the two would disagree exactly when a `let` or a later datatype reused the
 * name. Written back into the tree, both read one tree that already says which
 * constructor was meant.
 *
 * The rewrite takes no types, but it does take the super type's *identity*,
 * which is a name resolved against the declaration table and not a name read
 * off the tree. So elaboration is the earliest phase that can do it, and is
 * where the two other questions about a super constructor already live: whether
 * one was written at all where a super type was, and what the super type turned
 * out to be.
 *
 * Three earlier formulations were wrong and are recorded so they are not
 * retried: a body merely *typed* at the super type (subsumption unpins the head
 * -- a value of a sibling subtype has that type too, and two such declarations
 * loop at construction with a perfectly acyclic `<:`), a tail name left to
 * resolve in the term scope (a `let` shadows it), and no body at all but a
 * constructor name and arguments, which pins the head by giving up branching
 * and computation that the rewrite buys back.
 */

import type { Diagnostic, Position } from "../diagnostics/diagnostic.ts";
import { reportError } from "../diagnostics/diagnostic.ts";
import type { TermNode } from "./ast.ts";
import { DOT, qualifiedCtor } from "./ast.ts";

/**
 * Rewrite every tail of one super constructor body to name its constructor
 * through `superType`, reporting the ones that are no such thing.
 *
 * Each tail is reached through the spine above it: `let` and `match` are
 * spines rather than tails -- what a `let` evaluates to is its body, and what
 * a `match` evaluates to is the arm that fires -- so each branch is pinned on
 * its own.
 *
 * A new tree rather than a mutated one: the nodes are `readonly`, and
 * rebuilding only the spines walked costs one path per tail.
 */
export function resolveSuperCtorTails(
  term: TermNode,
  superType: string,
  diagnostics: Diagnostic[],
): TermNode {
  switch (term.kind) {
    case "Let":
    case "LetRec":
      return {
        ...term,
        body: resolveSuperCtorTails(term.body, superType, diagnostics),
      };
    case "Match":
      return {
        ...term,
        arms: term.arms.map((arm) => ({
          ...arm,
          body: resolveSuperCtorTails(arm.body, superType, diagnostics),
        })),
      };
    default:
      return resolveTail(term, superType, diagnostics);
  }
}

/**
 * One tail: a constructor of `superType`, applied or not.
 *
 * `Nil` and `Nil()` are different declarations, and `Nil[Bool]()` puts a type
 * application between the name and its arguments, so the name is found by
 * peeling whatever stands between rather than by matching one shape.
 */
function resolveTail(
  term: TermNode,
  superType: string,
  diagnostics: Diagnostic[],
): TermNode {
  const rebuilt = rebuildHead(term, superType, diagnostics);
  if (rebuilt !== undefined) return rebuilt;
  diagnostics.push(reportError(
    `a super constructor ends in a constructor of ${superType}, applied to its fields`,
    term.at,
  ));
  return term;
}

/** The same term with its head name qualified, or absent if it has no name. */
function rebuildHead(
  term: TermNode,
  superType: string,
  diagnostics: Diagnostic[],
): TermNode | undefined {
  switch (term.kind) {
    case "Var": {
      const name = qualify(term.name.text, superType, term.at, diagnostics);
      return { ...term, name: { ...term.name, text: name } };
    }
    case "App": {
      const callee = rebuildHead(term.callee, superType, diagnostics);
      return callee === undefined ? undefined : { ...term, callee };
    }
    case "TypeApp": {
      const callee = rebuildHead(term.callee, superType, diagnostics);
      return callee === undefined ? undefined : { ...term, callee };
    }
    default:
      return undefined;
  }
}

/**
 * `Cons` under super type `List` becomes `List.Cons`. One already written that
 * way is left alone; one qualified by *another* datatype is refused, since a
 * tail naming a sibling subtype's constructor is what the rule exists to stop.
 *
 * Whether the result names anything, at any arity, is not asked here -- that
 * is the check's business, and this pass runs whether or not it will. Which is
 * also why it is not asked here: a tail naming no constructor of the super type
 * would then be reported twice, once as the name that was written and once as
 * the name it was rewritten to. `unknown name List.Snoc` says both.
 */
function qualify(
  name: string,
  superType: string,
  at: Position,
  diagnostics: Diagnostic[],
): string {
  if (!name.includes(DOT)) return qualifiedCtor(superType, name);
  if (name.startsWith(`${superType}${DOT}`)) return name;
  diagnostics.push(reportError(
    `a super constructor ends in a constructor of ${superType}, and ${name} is not one`,
    at,
    name.length,
  ));
  return name;
}
