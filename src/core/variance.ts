/**
 * What a datatype's parameters do to its arguments, read off its constructor
 * fields rather than declared.
 *
 * Inferred and not written, because checking a written `+A` needs the same
 * walk that inferring it does -- so the inference is the part we need either
 * way, and an annotation would be a layer on top. The usual reason to demand
 * one is separate compilation, a library's variance being part of its
 * published interface; the require walk is textual and flat, so there is no
 * library boundary here to protect.
 *
 * Run once, after every datatype's constructors are in, and it writes its
 * answer into `ParamInfo.variance`. Everything downstream reads that through
 * `Declarations.argVariance`.
 */

import { type Diagnostic, reportWarning } from "../diagnostics/diagnostic.ts";
import type { DatatypeInfo } from "./declarations.ts";
import {
  type DataName,
  flip,
  impossible,
  type Type,
  type Variance,
} from "./types.ts";

/**
 * The set of positions a parameter was found in -- what the walk accumulates,
 * where a `Variance` is what it carries.
 *
 * The same four points `EVarEntry` keeps, and for the same reason: occurring
 * covariantly *and* contravariantly is what leaves an argument unable to move
 * either way, and occurring nowhere is no direction at all. Merged by `||`
 * componentwise and never composed, which is the whole of the difference from
 * a `Variance`.
 */
type Occurrence = { covariantly: boolean; contravariantly: boolean };

/** One row per datatype, one entry per parameter. */
type Table = ReadonlyMap<DataName, readonly Occurrence[]>;

/**
 * Every parameter of every datatype at the *most permissive* point, which is
 * where the fixed point starts and the only direction it moves from.
 *
 * Optimistic on purpose. Seeding at invariant would be sound and useless --
 * nothing would ever move -- whereas seeding at bivariant and only descending
 * computes the best sound answer. It cannot be wrong about a recursive
 * datatype either: in
 *
 *     datatype Opaque[A] where
 *       | Mk(Opaque[A] -> Bool)
 *
 * `A` occurs only under the recursive occurrence, every round prunes, and the
 * answer is that no program can tell an `Opaque[X]` from an `Opaque[Y]`. That
 * is correct rather than hopeful: soundness for a nominal recursive type is a
 * coinductive property, and the greatest permissive fixed point states it.
 */
function seed(datatypes: readonly DatatypeInfo[]): Map<DataName, Occurrence[]> {
  return new Map(datatypes.map((datatype) => [
    datatype.name,
    datatype.params.map(() => ({
      covariantly: false,
      contravariantly: false,
    })),
  ]));
}

function noteOccurrence(occurrence: Occurrence, variance: Variance): void {
  if (variance >= 0) occurrence.covariantly = true;
  if (variance <= 0) occurrence.contravariantly = true;
}

/** How many flags the table has set, which is what the fixed point counts. */
function flagsSet(table: Table): number {
  let total = 0;
  for (const row of table.values()) {
    for (const occurrence of row) {
      if (occurrence.covariantly) total += 1;
      if (occurrence.contravariantly) total += 1;
    }
  }
  return total;
}

/**
 * Walk one constructor field, merging what it finds into `row`.
 *
 * Entered at `+1`: a field is projected by `match` and never assigned, which
 * is why there is no contravariant entry, and why a mutable cell has to arrive
 * as a builtin rather than as a datatype this walk would have to model.
 *
 * `depth` tracks binders the way `openAt` does, because a field may hold a
 * function type of its own and those `BVar`s are not the datatype's. `snapshot`
 * is last round's table, read and never written -- see `inferDatatypeVariance`.
 */
function noteField(
  type: Type,
  depth: number,
  variance: Variance,
  row: readonly Occurrence[],
  snapshot: Table,
): void {
  switch (type.kind) {
    case "TUnknown":
    case "TNever":
    case "TBad":
    case "FVar":
      return;

    case "BVar": {
      // Bound by a binder inside the field, so it is none of the datatype's
      // parameters.
      if (type.index < depth) return;
      const occurrence = row[type.index - depth] ??
        impossible("a field closed over its datatype's parameters");
      noteOccurrence(occurrence, variance);
      return;
    }

    case "TFun": {
      const inner = depth + type.typeParams.length;
      const flipped = flip(variance);
      // Bounds are parallel, so they stay at `depth`; both they and the
      // parameters are contravariant, and the result alone is not.
      for (const binder of type.typeParams) {
        noteField(binder.bound, depth, flipped, row, snapshot);
      }
      for (const param of type.params) {
        noteField(param, inner, flipped, row, snapshot);
      }
      noteField(type.result, inner, variance, row, snapshot);
      return;
    }

    case "TData": {
      // Reading the table here is what makes this walk terminate on a
      // recursive datatype: `Foo[X]` recurses into `X`, a proper subterm, and
      // never unfolds `Foo`. Only the *table* iterates.
      const target = snapshot.get(type.name);
      type.args.forEach((arg, i) => {
        // An undeclared name is already reported; invariance asks the least of
        // this walk and so concludes the least.
        const occurrence = target?.[i] ??
          { covariantly: true, contravariantly: true };
        // Four ways to go on, and the fourth is why nothing here has to
        // compose two occurrences or flip one. A parameter nothing observes
        // contributes nothing, so the sub-walk is dropped rather than run at
        // some position it would then have to invent.
        if (occurrence.covariantly && occurrence.contravariantly) {
          noteField(arg, depth, 0, row, snapshot);
        } else if (occurrence.covariantly) {
          noteField(arg, depth, variance, row, snapshot);
        } else if (occurrence.contravariantly) {
          noteField(arg, depth, flip(variance), row, snapshot);
        }
      });
      return;
    }
  }
}

/** Every field of every datatype, once, against `snapshot`. */
function oneRound(
  datatypes: readonly DatatypeInfo[],
  snapshot: Table,
): Map<DataName, Occurrence[]> {
  const fresh = seed(datatypes);
  for (const datatype of datatypes) {
    const row = fresh.get(datatype.name) ?? impossible("a row per datatype");
    for (const ctor of datatype.ctors) {
      for (const field of ctor.fields) {
        noteField(field, 0, 1, row, snapshot);
      }
    }
  }
  return fresh;
}

/**
 * Infer every datatype's variance and write it into its parameters.
 *
 * The fixed point is **global over the table, not per datatype**: two
 * declarations may name each other, so this is one iteration over every
 * parameter of every one of them.
 *
 * It cannot diverge, so unlike subtyping it takes no fuel. Positions only ever
 * descend and a merge only ever sets a flag, so the number of flags set across
 * the whole table is a non-decreasing integer bounded by `2n` for `n`
 * parameters in all -- which is both the stopping criterion and the
 * termination argument: at most `2n` rounds change anything and one more
 * notices.
 *
 * Each round reads last round's table and writes a fresh one (Jacobi) rather
 * than updating in place. In place reaches the same fixed point and often
 * sooner, but the round *counts* are then implementation-defined, and those
 * counts are what catches a one-pass bug: round 1 of a recursive datatype is a
 * complete, plausible, unsound answer, because every recursive occurrence was
 * still being pruned.
 */
export function inferDatatypeVariance(
  datatypes: readonly DatatypeInfo[],
  diagnostics: Diagnostic[],
): void {
  let table: Table = seed(datatypes);
  for (let flags = 0;;) {
    const next = oneRound(datatypes, table);
    table = next;
    const grown = flagsSet(next);
    if (grown === flags) break;
    flags = grown;
  }

  for (const datatype of datatypes) {
    const row = table.get(datatype.name) ?? impossible("a row per datatype");
    datatype.params.forEach((param, j) => {
      const occurrence = row[j] ?? impossible("an entry per parameter");
      param.variance = varianceOf(occurrence);
      if (isPhantom(occurrence) && param.named && !anyFieldIsBad(datatype)) {
        diagnostics.push(reportWarning(
          `nothing observes the type parameter ${param.hint} of ` +
            `${datatype.name}, so it makes no difference to the type; write ` +
            `it \`_\` if that is meant`,
          param.at,
          param.hint.length,
        ));
      }
    });
  }
}

/**
 * A position read back as a `Variance`, which has to answer for bivariance and
 * has no point to answer with. It collapses to covariant: sound, and
 * incomplete only for a parameter no program can observe -- which is what the
 * phantom warning says instead, once, at the declaration that knows.
 */
function varianceOf(occurrence: Occurrence): Variance {
  if (occurrence.covariantly && occurrence.contravariantly) return 0;
  if (occurrence.contravariantly) return -1;
  return 1;
}

function isPhantom(occurrence: Occurrence): boolean {
  return !occurrence.covariantly && !occurrence.contravariantly;
}

/**
 * Whether anything in this datatype failed to elaborate. A field that did
 * stands as `<bad>` with a report already made, and a parameter that occurred
 * only there then looks unused -- so the phantom warning is dropped for the
 * whole declaration rather than blaming the author twice for one mistake. The
 * inference itself still runs.
 */
function anyFieldIsBad(datatype: DatatypeInfo): boolean {
  const holdsBad = (type: Type): boolean => {
    switch (type.kind) {
      case "TBad":
        return true;
      case "TFun":
        return type.typeParams.some((binder) => holdsBad(binder.bound)) ||
          type.params.some(holdsBad) || holdsBad(type.result);
      case "TData":
        return type.args.some(holdsBad);
      default:
        return false;
    }
  };
  return datatype.ctors.some((ctor) => ctor.fields.some(holdsBad));
}
