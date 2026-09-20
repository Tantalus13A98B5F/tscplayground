/**
 * Cutting one argument list into stages.
 *
 * An unannotated lambda parameter has no type of its own: it comes from the
 * pattern the argument is checked against, and at a polymorphic call that
 * pattern hides the type parameters behind missing parts. So `fold(op, z, l)`
 * cannot work in one pass -- `op`'s parameters are what `z` and `l` are about
 * to say. Currying is the way that is written today, and this is that same
 * staging computed from the types rather than written by the author.
 *
 * Two relations over the argument list decide it. An argument *requires* a type
 * parameter when it is a lambda with an unannotated parameter standing where
 * that type parameter does -- exactly the position that reports today. An
 * argument *mentions* one when it occurs anywhere in its parameter type, which
 * is what it can say about it once it has been checked. Requiring is therefore
 * before and mentioning after, and that asymmetry is the whole plan: `op`
 * mentions the `B` it also requires, and its vote on `B` is given up so that
 * `z`'s can be counted first.
 *
 * A type parameter is committed as late as it can be -- at the end of the last
 * stage before something waiting on it is checked -- so an argument keeps its
 * vote wherever nothing needed the answer sooner.
 */

import type { TermNode } from "../syntax/ast.ts";
import { openWith, TMissing, type TypePattern } from "./types.ts";

/**
 * One pass over the argument list.
 *
 * The three sets are three different questions and deliberately not one: an
 * argument is *checked* here, is *related* here once every type parameter its
 * own type mentions has an answer or is getting one now, and the parameters
 * *committed* here are solved when the stage closes.
 */
export type Stage = {
  /** Argument indices checked in this stage, against what is committed so far. */
  readonly args: readonly number[];
  /** Argument indices related to their parameter types at the end of it. */
  readonly relate: readonly number[];
  /** Type parameter indices solved when it closes. */
  readonly commit: readonly number[];
  /**
   * Those of `args` checked although what they require is not committed --
   * because nothing could commit it. Each one is a place an annotation would
   * unblock the rest, and the reason there is at most one per cycle.
   */
  readonly seeds: readonly number[];
};

/** The type parameters of the enclosing binder that occur in a pattern. */
function mentioned(type: TypePattern): Set<number> {
  const seen = new Set<number>();
  openWith<unknown>(type, (index) => {
    seen.add(index);
    return TMissing;
  });
  return seen;
}

/**
 * What this argument must be told before it can be checked at all.
 *
 * Only a lambda has an answer that is not empty, and only for the parameters it
 * left bare: an annotation is read from the term, so it needs nothing, which is
 * what lets `fn (a: Nat, b) -> e` wait on one type parameter instead of two.
 *
 * A parameter type with a quantifier of its own is left alone -- its positions
 * sit under a second binder, so the indices here would be the wrong ones -- and
 * a pattern that is no arrow, or is one of another quantifier arity, demands
 * nothing of the lambda's parts anyway.
 */
function required(arg: TermNode, param: TypePattern): Set<number> {
  const empty = new Set<number>();
  if (arg.kind !== "Abs") return empty;
  if (param.kind !== "TFun" || param.typeParams.length > 0) return empty;
  if (arg.typeParams.length > 0) return empty;
  const needed = new Set<number>();
  for (const [j, p] of arg.params.entries()) {
    if (p.annotation !== undefined) continue;
    const position = param.params[j];
    if (position === undefined) continue;
    for (const index of mentioned(position)) needed.add(index);
  }
  return needed;
}

/**
 * The stalled arguments that must be checked without what they require.
 *
 * Edges run from an argument to one waiting on something it mentions, so a
 * source of the condensation is a group nothing else can unblock and must hold
 * one. One from each is therefore both necessary and enough, and the leftmost
 * member is taken so that editing an unrelated argument cannot move the blame.
 *
 * Minimal only if a seed then checks; where it does not, its own requirement
 * was the mistake, and the next round stalls again and seeds again.
 */
function sourceSeeds(
  stalled: readonly number[],
  mentions: readonly ReadonlySet<number>[],
  requires: readonly ReadonlySet<number>[],
  committed: ReadonlySet<number>,
): number[] {
  const edges = new Map<number, number[]>(stalled.map((a) => [a, []]));
  for (const a of stalled) {
    for (const b of stalled) {
      const open = [...requires[b] ?? []].filter((j) => !committed.has(j));
      if (open.some((j) => mentions[a]?.has(j))) edges.get(a)?.push(b);
    }
  }

  // Tarjan, over at most the call's arity.
  const index = new Map<number, number>();
  const low = new Map<number, number>();
  const onStack = new Set<number>();
  const stack: number[] = [];
  const component = new Map<number, number>();
  let next = 0;
  let components = 0;
  const visit = (v: number): void => {
    index.set(v, next);
    low.set(v, next);
    next += 1;
    stack.push(v);
    onStack.add(v);
    for (const w of edges.get(v) ?? []) {
      if (!index.has(w)) {
        visit(w);
        low.set(v, Math.min(low.get(v) ?? 0, low.get(w) ?? 0));
      } else if (onStack.has(w)) {
        low.set(v, Math.min(low.get(v) ?? 0, index.get(w) ?? 0));
      }
    }
    if (low.get(v) === index.get(v)) {
      for (;;) {
        const w = stack.pop();
        if (w === undefined) break;
        onStack.delete(w);
        component.set(w, components);
        if (w === v) break;
      }
      components += 1;
    }
  };
  for (const v of stalled) if (!index.has(v)) visit(v);

  const hasEntry = new Set<number>();
  for (const [a, targets] of edges) {
    for (const b of targets) {
      if (component.get(a) !== component.get(b)) {
        hasEntry.add(component.get(b) ?? -1);
      }
    }
  }

  const seeds: number[] = [];
  const seeded = new Set<number>();
  for (const v of stalled) {
    const c = component.get(v) ?? -1;
    if (hasEntry.has(c) || seeded.has(c)) continue;
    seeded.add(c);
    seeds.push(v);
  }
  return seeds;
}

/**
 * The stages of one argument list, in order, always at least one.
 *
 * A list where nothing requires anything plans to a single stage that checks
 * every argument, relates every argument and commits every type parameter --
 * which is what the checker did before there were stages at all.
 */
export function planStages(
  params: readonly TypePattern[],
  args: readonly TermNode[],
  typeParamCount: number,
): readonly Stage[] {
  const mentions = params.map(mentioned);
  const requires = args.map((arg, i) => required(arg, params[i] ?? TMissing));

  const stages: Stage[] = [];
  const checked = new Set<number>();
  const related = new Set<number>();
  const committed = new Set<number>();

  while (checked.size < args.length || stages.length === 0) {
    const waiting = args.map((_, i) => i).filter((i) => !checked.has(i));
    let seeds: number[] = [];
    let taking = waiting.filter((i) =>
      [...requires[i] ?? []].every((j) => committed.has(j))
    );
    if (taking.length === 0 && waiting.length > 0) {
      seeds = sourceSeeds(waiting, mentions, requires, committed);
      taking = seeds;
    }

    for (const i of taking) checked.add(i);
    const left = args.map((_, i) => i).filter((i) => !checked.has(i));

    // Late as it can be, and never sooner than something can answer it. What
    // is wanted is whatever is still waited on; what is committed is the
    // arguments that can speak to any of it, taken whole -- an argument
    // settles every type parameter it names at once or none of them, having no
    // complete type to relate until then. Committing a wanted parameter that
    // no checked argument mentions would solve it from nothing and call the
    // answer `never`.
    //
    // At the end there is no later stage to wait for, so the rest goes in.
    const commit = new Set<number>();
    if (left.length === 0) {
      for (let j = 0; j < typeParamCount; j += 1) {
        if (!committed.has(j)) commit.add(j);
      }
    } else {
      const wanted = new Set<number>();
      for (const i of left) {
        for (const j of requires[i] ?? []) if (!committed.has(j)) wanted.add(j);
      }
      for (const i of checked) {
        if (related.has(i)) continue;
        const speaks = [...mentions[i] ?? []].filter((j) => !committed.has(j));
        if (speaks.some((j) => wanted.has(j))) {
          for (const j of speaks) commit.add(j);
        }
      }
    }
    for (const j of commit) committed.add(j);

    // An argument goes to the relation once every type parameter its parameter
    // type names has an answer; before that there is no complete type to
    // relate it against, and it loses its say on what was settled without it.
    const relate = [...checked].filter((i) =>
      !related.has(i) &&
      [...mentions[i] ?? []].every((j) => committed.has(j))
    ).sort((a, b) => a - b);
    for (const i of relate) related.add(i);

    stages.push({
      args: taking,
      relate,
      commit: [...commit].sort((a, b) => a - b),
      seeds,
    });
  }
  return stages;
}
