/**
 * Cutting one argument list into rounds.
 *
 * An unannotated lambda parameter has no type of its own: it comes from the
 * pattern the argument is checked against, and at a polymorphic call that
 * pattern hides the type parameters behind missing parts. So `fold(op, z, l)`
 * cannot work in one pass -- `op`'s parameters are what `z` and `l` are about
 * to say. Currying is how that is written today; this computes it from the
 * types instead. `docs/staging.md` has the model and what it gives up.
 *
 * Two relations decide the order. An argument *requires* a type parameter
 * where it left a parameter bare in that position -- the position that reports
 * today. It *supplies* one it names anywhere else: a bare lambda's parameter
 * type **is** the solution of what it required, so relating that back says only
 * `?A <: solution(A)`, and a requirer therefore supplies its result and nothing
 * else.
 *
 * An argument nothing still waiting can supply to is one whose parameters are
 * as constrained as they will ever be, so solving them now gives up nothing.
 * That is the whole ordering criterion, and it is deliberately not a measure of
 * how constrained a parameter already is: in
 * `bar(f: (A) -> B, g: (B) -> C, w: A, x: B, y: B, z: B)`, `B` carries three
 * constraints to `A`'s one and is still the wrong one to solve first, `f`
 * supplying `B` as well.
 */

import type { Param, TermNode } from "../syntax/ast.ts";
import { openWith, TMissing, type TypePattern } from "./types.ts";

/**
 * One round. `solve` happens *before* `args` are checked -- a bare lambda
 * cannot be checked until the positions it left bare have answers -- and the
 * indices are type parameters where `args` are arguments.
 */
export type Round = {
  readonly solve: readonly number[];
  readonly args: readonly number[];
};

export type Plan = {
  readonly rounds: readonly Round[];
  /**
   * Type parameters no round demanded. Nothing waits on them, so they collect
   * from the whole list and are solved once it is done.
   */
  readonly rest: readonly number[];
};

/**
 * The enclosing binder's variables occurring in a type that sits `depth`
 * binders in. `openWith` does the walk; its rule sees each index relative to
 * the node it was handed, so the binders above that node are subtracted here,
 * and what it rebuilds is dropped.
 */
function collectVars(
  type: TypePattern,
  depth: number,
  into: Set<number>,
): void {
  openWith(type, (index) => {
    if (index >= depth) into.add(index - depth);
    return TMissing;
  });
}

/**
 * What this argument must be told before it can be checked at all.
 *
 * A co-walk of the term and the type, descending wherever they agree --
 * through curried arrows and through quantifiers alike, since nothing here is
 * elaborated or related and only indices are collected, so no context is
 * needed. `depth` is what makes a quantifier harmless: the indices stay the
 * *callee's* however many binders they are read under.
 *
 * It mirrors `#checkAbs`, which is the correctness criterion: a pattern of
 * another quantifier arity demands nothing of the lambda's parts, so neither
 * does this, and a parameter the pattern does not reach is one it says nothing
 * about. Stopping early is always safe -- the argument is then not waited for,
 * is checked with the position still missing, and reports as it does today.
 * Descending where the shapes do *not* correspond is the unsafe direction: it
 * records a requirement nothing will satisfy.
 */
function collectRequired(
  arg: TermNode,
  param: TypePattern,
  depth: number,
  into: Set<number>,
): void {
  if (arg.kind !== "Abs" || param.kind !== "TFun") return;
  if (param.typeParams.length !== arg.typeParams.length) return;

  const inner = depth + param.typeParams.length;
  for (const [j, written] of arg.params.entries()) {
    const position = param.params[j];
    if (position === undefined) continue;
    if ((written as Param).annotation !== undefined) continue;
    collectVars(position, inner, into);
  }
  collectRequired(arg.body, param.result, inner, into);
}

/** The rounds of one argument list, in order, always at least one. */
export function planStages(
  params: readonly TypePattern[],
  args: readonly TermNode[],
  typeParamCount: number,
): Plan {
  const mentions = params.map((param) => {
    const seen = new Set<number>();
    collectVars(param, 0, seen);
    return seen;
  });
  const requires = args.map((arg, i) => {
    const seen = new Set<number>();
    collectRequired(arg, params[i] ?? TMissing, 0, seen);
    return seen;
  });
  // What it can say that it was not told.
  const supplies = mentions.map((named, i) =>
    new Set([...named].filter((j) => !requires[i]?.has(j)))
  );

  const rounds: Round[] = [];
  const solved = new Set<number>();
  const checked = new Set<number>();
  let waiting = args.map((_, i) => i);

  while (waiting.length > 0) {
    const needOf = (i: number) =>
      [...requires[i] ?? []].filter((j) => !solved.has(j));
    const ready = waiting.filter((i) =>
      !waiting.some((j) =>
        j !== i && needOf(i).some((k) => supplies[j]?.has(k))
      )
    );

    if (ready.length > 0) {
      const solve = [...new Set(ready.flatMap(needOf))].sort((a, b) => a - b);
      for (const j of solve) solved.add(j);
      for (const i of ready) checked.add(i);
      rounds.push({ solve, args: ready });
      waiting = waiting.filter((i) => !checked.has(i));
      continue;
    }

    // Nothing of in-degree zero: every argument left is on or downstream of a
    // cycle, and the ordering has run out. Rather than break one -- which is a
    // choice no cheap rule makes soundly, and a wrong one settles a parameter
    // from fewer constraints than were available and then blames the next
    // argument for not conforming -- solve what an argument already checked
    // can speak to, check the rest, and let whatever still has no type report
    // where it always did.
    const speakable = new Set<number>();
    for (const i of checked) {
      for (const j of mentions[i] ?? []) if (!solved.has(j)) speakable.add(j);
    }
    const solve = [...speakable].sort((a, b) => a - b);
    for (const j of solve) solved.add(j);
    rounds.push({ solve, args: waiting });
    waiting = [];
  }

  const rest: number[] = [];
  for (let j = 0; j < typeParamCount; j += 1) if (!solved.has(j)) rest.push(j);
  if (rounds.length === 0) rounds.push({ solve: [], args: [] });
  return { rounds, rest };
}
