/**
 * The stdlib corpus, checked as the CLI would check it.
 *
 * `stdlib/` is written twice over -- once as datatypes and once as Church
 * encodings -- so that the same library exercises the inference from two
 * directions. What it is for is the *usages*: a type asserted here is a type
 * nothing in the source wrote, so a regression in local type inference shows up
 * as a changed answer rather than as an error nobody sees.
 *
 * Exactly one type argument is written under `stdlib/`: `toList` in
 * `uses-both.ga`, where staging makes the fold's initial value the argument
 * that fixes `B`, and an empty list has nothing to fix it with. Every other one
 * in both encodings is found -- from a sibling argument, from an annotation on
 * a lambda, or from the expected type -- so any of these answers changing is
 * the inference having got weaker.
 *
 * Read off the disk rather than embedded, so these are programs a reader can
 * run (`deno task run stdlib/uses-data.ga`) and so the require walk is
 * exercised on a real tree.
 */

import { expect } from "@std/expect";
import {
  checkFiles,
  type FileSystem,
  isPlainPath,
  showDiagnostic,
} from "./mod.ts";
import { typeToString } from "./core/types.ts";

const ROOT = new URL("../stdlib/", import.meta.url);

/**
 * The tree, under the same plain-path rules `cli.ts` applies: everything
 * resolves against the root, so an entry may require only what sits at or below
 * it. `extra` adds files the tree does not hold, which is how a program meant
 * to be *refused* is written without leaving a broken file in the library.
 */
function stdlibFiles(extra: Record<string, string> = {}): FileSystem {
  return {
    resolve(spec) {
      if (!isPlainPath(spec)) return undefined;
      if (spec in extra) return spec;
      try {
        return Deno.statSync(new URL(spec, ROOT)).isFile ? spec : undefined;
      } catch {
        return undefined;
      }
    },
    read(path) {
      return extra[path] ?? Deno.readTextFileSync(new URL(path, ROOT));
    },
  };
}

/** A `[type, ...located messages]` tuple, as `mod.test.ts` builds one. */
function check(
  entry: string,
  extra: Record<string, string> = {},
): [string, ...string[]] {
  const result = checkFiles(stdlibFiles(extra), entry);
  return [
    result.value === undefined ? "<none>" : typeToString(result.value),
    ...result.diagnostics.map((d) => showDiagnostic(d, result.sources)),
  ];
}

Deno.test("stdlib: the datatype encoding infers its type arguments", () => {
  // `map`'s A and B are written nowhere in `uses-data.ga` -- once found from
  // the function passed and once from the list.
  expect(check("uses-data.ga")).toEqual(["Pair[Nat, Bool]"]);
});

Deno.test("stdlib: the Church encoding needs no fixed point", () => {
  // `CPair[CNat, CNat]`, printed expanded: an alias is transparent, so nothing
  // downstream of elaboration knows the name existed to print it.
  expect(check("uses-church.ga")).toEqual([
    "[C](([A](A -> A, A) -> A, [A](A -> A, A) -> A) -> C) -> C",
  ]);
});

Deno.test("stdlib: the two encodings convert into each other", () => {
  // Church to datatype is one application; datatype to Church takes `fix`, at
  // a `B` that is itself a quantified type.
  expect(check("uses-both.ga")).toEqual(["Pair[Nat, Nat]"]);
});

Deno.test("stdlib: a Church empty list is a function, as `Nil()` is", () => {
  // The value restriction forces it: `[A]CList[A]` would be a quantifier over
  // a non-function, so an empty parameter list carries the quantifier instead
  // and each use fixes `A` at the call -- found here from the expected type,
  // which is where `Nil()` gets its argument too.
  expect(check("nil.ga", {
    "nil.ga": '#require "church/list.ga"\n' +
      "let empty : CList[CNat] = cnil()\n" +
      "empty\n",
  })).toEqual(["[B](([A](A -> A, A) -> A, B) -> B, B) -> B"]);
});

/** `data/list.ga`, with `foldr` restaged and the same call made against it. */
function restagedFold(signature: string, call: string) {
  return check("fold.ga", {
    "fold.ga": '#require "data/list.ga"\n' +
      `let f = ${signature} ->\n` +
      "  fix(fn (self: (List[A]) -> B) -> fn (ys: List[A]) ->\n" +
      "    match ys with\n" +
      "      | Nil -> z\n" +
      "      | Cons(h, t) -> op(h, self(t)))(xs);\n" +
      `${call}\n`,
  });
}

Deno.test("stdlib: a bare lambda needs its type argument fixed by an earlier list", () => {
  // Why `foldr` is `(xs)(z)(op)` and not either shorter shape. One parameter
  // list is one batch of type arguments, so a binder decides where its
  // argument becomes available -- which is the staging Scala 2 uses for
  // `foldLeft(z)(op)`, reached here for the same reason.
  const op = "fn (h, acc) -> add(h)(acc)";

  expect(restagedFold(
    "fn [A](xs: List[A]) -> fn [B](z: B) -> fn (op: (A, B) -> B)",
    `f(Cons(Z, Nil()))(Z)(${op})`,
  )).toEqual(["Nat"]);

  // One binder over both: `B` is solved at the first list with nothing
  // constraining it, so it is `never` and everything after is refused.
  expect(
    restagedFold(
      "fn [A, B](xs: List[A]) -> fn (z: B) -> fn (op: (A, B) -> B)",
      `f(Cons(Z, Nil()))(Z)(${op})`,
    )[1],
  ).toBe("fold.ga:7:19: error: expected never, found Nat");

  // Both in one list: they are one batch, `op` is checked before `z` has
  // contributed, and `acc` has no type yet.
  expect(
    restagedFold(
      "fn [A](xs: List[A]) -> fn [B](z: B, op: (A, B) -> B)",
      `f(Cons(Z, Nil()))(Z, ${op})`,
    )[1],
  ).toBe(
    "fold.ga:7:29: error: cannot infer a type for acc: annotate it, or use " +
      "this function where its parameter types are known",
  );
});

Deno.test("stdlib: fusing a Church nil's two binders does not work", () => {
  // The alternative `church/list.ga` records as refused. One binder over A and
  // B together is not `CList[A]`, which quantifies B alone, and quantifiers
  // fuse into the arrow so there is no partial instantiation between them.
  expect(check("fused.ga", {
    "fused.ga": '#require "church/list.ga"\n' +
      "let fused = fn [A, B](c: (A, B) -> B, n: B) -> n\n" +
      "let empty : CList[CNat] = fused\n" +
      "empty\n",
  })).toEqual([
    "[B](([A](A -> A, A) -> A, B) -> B, B) -> B",
    "fused.ga:3:27: error: expected [B](([A](A -> A, A) -> A, B) -> B, B) -> B, " +
    "found [A, B]((A, B) -> B, B) -> B",
  ]);
});
