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

import type { TermNode } from "../syntax/ast.ts";
import {
  impossible,
  openWith,
  TMissing,
  type Type,
  type TypePattern,
} from "./types.ts";

/**
 * Solve the type parameters in `solve`, then check the arguments in `check`
 * -- in that order, since a bare lambda cannot be checked until the positions
 * it left bare have answers. `solve` indexes the callee's binders.
 */
export type Round = {
  readonly solve: readonly number[];
  readonly check: readonly StagedArg[];
};

/**
 * An argument, the parameter type it is checked at, and the three sets of type
 * parameters that decide when.
 */
export type StagedArg = {
  readonly arg: TermNode;
  readonly param: Type;
  readonly mentions: ReadonlySet<number>;
  readonly requires: ReadonlySet<number>;
  readonly supplies: ReadonlySet<number>;
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
    if (written.annotation !== undefined) continue;
    collectVars(position, inner, into);
  }
  collectRequired(arg.body, param.result, inner, into);
}

/**
 * The rounds of one argument list, in order. The last checks nothing and
 * solves what no argument required: nothing waits on those, so they collect
 * from the whole list first.
 */
export function planStages(
  params: readonly Type[],
  args: readonly TermNode[],
  typeParamCount: number,
): readonly Round[] {
  const argInfos = args.map((arg, i): StagedArg => {
    const param = params[i] ??
      impossible("the caller refuses a call of the wrong arity");
    const mentions = new Set<number>();
    collectVars(param, 0, mentions);
    const requires = new Set<number>();
    collectRequired(arg, param, 0, requires);
    // What it can say that it was not told. Disjoint from what it requires, so
    // no argument ever waits on itself.
    const supplies = mentions.difference(requires);
    return { arg, param, mentions, requires, supplies };
  });

  const rounds: Round[] = [];
  const unsolved = new Set(
    Array.from({ length: typeParamCount }, (_, j) => j),
  );
  // Solve what `wanted` names that no earlier round solved, then check
  // `checking`.
  const pushRound = (
    wanted: ReadonlySet<number>,
    checking: readonly StagedArg[],
  ) => {
    const solve = [...wanted.intersection(unsolved)];
    for (const j of solve) unsolved.delete(j);
    rounds.push({ solve, check: checking });
  };
  let waiting = argInfos;

  while (waiting.length > 0) {
    // Nothing leaves this set but by being checked, so a type parameter no
    // waiting argument supplies stays that way: what an earlier round answered
    // can never make an argument wait again.
    const supplied = new Set(waiting.flatMap((arg) => [...arg.supplies]));
    const ready = waiting.filter((arg) =>
      arg.requires.isDisjointFrom(supplied)
    );

    if (ready.length > 0) {
      const required = new Set(ready.flatMap((arg) => [...arg.requires]));
      pushRound(required, ready);
      waiting = waiting.filter((arg) => !ready.includes(arg));
    } else {
      // Nothing of in-degree zero: every argument left is on or downstream of
      // a cycle, and the ordering has run out. Rather than break one -- which
      // is a choice no cheap rule makes soundly, and a wrong one settles a
      // parameter from fewer constraints than were available and then blames
      // the next argument for not conforming -- answer what an argument
      // already checked can speak to, check the rest, and let whatever still
      // has no type report where it always did.
      const spoken = new Set(
        argInfos
          .filter((arg) => !waiting.includes(arg))
          .flatMap((arg) => [...arg.mentions]),
      );
      pushRound(spoken, waiting);
      waiting = [];
    }
  }

  pushRound(unsolved, []);
  return rounds;
}
