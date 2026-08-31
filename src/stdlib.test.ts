/**
 * The stdlib corpus, checked as the CLI would check it.
 *
 * `stdlib/` is written twice over -- once as datatypes and once as Church
 * encodings -- so that the same library exercises the inference from two
 * directions, and once more over `Ref`, which is the control: `MList[A]` and
 * `List[A]` differ by one `Ref` and come out invariant and covariant, so every
 * type argument `uses-ref.ga` has to write is one the covariant list does not.
 * What it is for is the *usages*: a type asserted here is a type nothing in the
 * source wrote, so a regression in local type inference shows up as a changed
 * answer rather than as an error nobody sees.
 *
 * A written type argument under `stdlib/` is therefore a claim that inference
 * could not have found it, and there are three reasons any of them are there.
 * `Nil[A]()` in `uses-both.ga` is a fold's initial value, which staging makes
 * the argument that fixes `B` -- and an empty list has nothing to fix it with.
 * `MNil[Nat]()` in the `Ref` library is invariance: `MList[never]` widens to
 * nothing. `diverge[A, B]()` is a cell's seed, unconstrained in the argument
 * list it is solved in, the cell learning what it holds one line later. Every
 * other one is found -- from a sibling argument, from an annotation on a
 * lambda, or from the expected type -- so any of these answers changing is the
 * inference having got weaker.
 *
 * Read off the disk rather than embedded, so these are programs a reader can
 * run and so the require walk is exercised on a real tree. The entries at the
 * root run bare -- `deno task run stdlib/uses-data.ga` -- and the ones under
 * `rec/` need `-I stdlib`, requires resolving against the search path rather
 * than against the requiring file. This filesystem is rooted at `stdlib/`, so
 * it *is* that configuration and no entry here has to say which it needs.
 */

import { expect } from "@std/expect";
import {
  checkFiles,
  type FileSystem,
  isPlainPath,
  runFiles,
  showDiagnostic,
  valueToString,
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

/** A `[value, ...located messages]` tuple, `check`'s counterpart one phase on. */
function evaluated(
  entry: string,
  extra: Record<string, string> = {},
): [string, ...string[]] {
  const result = runFiles(stdlibFiles(extra), entry);
  return [
    result.value === undefined ? "<stuck>" : valueToString(result.value),
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
      "    | Nil -> z\n" +
      "    | Cons(h, t) -> op(h, self(t)))(xs)\n" +
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

Deno.test("stdlib: a Ref makes its datatype invariant, and that costs", () => {
  expect(check("uses-ref.ga")).toEqual(["Pair[Nat, List[Nat]]"]);

  // The two refusals `uses-ref.ga` documents, which are the same fact twice.
  // A `never` tail cannot widen, so the argument list has no solution --
  const inMList = '#require "ref/list.ga"\n';
  expect(check("m.ga", { "m.ga": inMList + "MCons(Z, ref!(MNil()))\n" })[1])
    .toBe(
      "m.ga:2:6: error: cannot infer the type argument A: it is bounded " +
        "below by Nat and above by never, and no type is both",
    );

  // -- and an expected type does not rescue it, because joining two `MList`s
  // that disagree gives `unknown`: invariance leaves nothing between them.
  expect(
    check("m.ga", {
      "m.ga": inMList + "let r : Ref[MList[Nat]] = ref!(MNil())\nr\n",
    })[1],
  ).toBe(
    "m.ga:2:31: error: cannot infer the type argument T: it is bounded " +
      "below by unknown and above by MList[Nat], and no type is both",
  );

  // The covariant list, written the same way, needs neither.
  expect(check("l.ga", {
    "l.ga": '#require "data/list.ga"\n' + "Cons(Z, Nil())\n",
  })).toEqual(["List[Nat]"]);
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

Deno.test("stdlib: mutual recursion, once as a feature and five times encoded", () => {
  // The same pair -- `(Nat) -> List[Nat]` beside `(Nat) -> Nat`, so nothing
  // here can lean on a shared result type -- written once as a `def` run and
  // five times as an encoding: Bekic's decomposition, a fixed point at a
  // product, a tag, continuations, and backpatched cells. One answer from all
  // six is the point: `def` is a scoping rule and not a new way to recurse.
  for (
    const entry of [
      "rec/mutual-def.ga",
      "rec/mutual-bekic.ga",
      "rec/mutual-pair.ga",
      "rec/mutual-tag.ga",
      "rec/mutual-cps.ga",
      "rec/mutual-ref.ga",
    ]
  ) {
    expect([entry, ...check(entry)]).toEqual([entry, "Pair[List[Nat], Nat]"]);
  }
});

Deno.test("stdlib: bottom is a value at an arrow and nowhere else", () => {
  // What makes a backpatched knot a closed term at all. `fix` over a body that
  // only calls itself inhabits every arrow type, and it is a *lambda*, so a
  // cell can hold one -- which is the synthesis problem `fixFrom` ducks by
  // taking its seed as a parameter.
  expect(check("d.ga", {
    "d.ga": '#require "rec/fix.ga"\n' + "diverge\n",
  })).toEqual(["[A, B]() -> A -> B"]);

  // And why `rec/mutual-ref.ga` writes the seed's type arguments. Nothing in
  // `ref!`'s list constrains them, so they solve at the extremes and the
  // backpatch is what finds out.
  expect(
    check("k.ga", {
      "k.ga": '#require "ref/cell.ga"\n' +
        "let f = fn [A, B](f: ((A) -> B) -> (A) -> B) ->\n" +
        "  let r = ref!(diverge())\n" +
        "  let g = fn (v: A) -> get!(r)(v)\n" +
        "  let _ = set!(r, f(g))\n" +
        "  g\n" +
        "f\n",
    })[1],
  ).toBe(
    "k.ga:5:15: error: cannot infer the type argument T: it is bounded below " +
      "by A -> B and above by unknown -> never, and no type is both",
  );
});

/**
 * The same corpus, run.
 *
 * The types above say what the checker made of these programs; this says what
 * they compute, which is the other half of a claim that they mean anything. It
 * is also the widest evaluation test there is -- the entries reach every term
 * form, both encodings, staged folds, and cells -- and nothing else exercises
 * the evaluator against programs a reader can run.
 *
 * The six under `rec/` are the sharpest of them. They are the same pair of
 * mutually recursive functions six ways over -- Bekic's decomposition, a fixed
 * point at a product, a tag, continuation passing, backpatched cells, and a
 * `def` run -- so they must agree on a value, and an encoding that has drifted
 * from what it encodes shows up here and nowhere in the types.
 */
Deno.test("stdlib: the corpus runs, and the encodings agree on a value", () => {
  expect(evaluated("uses-data.ga")).toEqual(["MkPair(S(S(Z)), True)"]);
  expect(evaluated("uses-both.ga")).toEqual(["MkPair(S(S(S(Z))), Z)"]);
  expect(evaluated("uses-ref.ga")).toEqual(["MkPair(S(Z), Nil())"]);
  // A Church value is a function, so running one says only that it did not get
  // stuck. What it computes is read by converting it, which `uses-both.ga` is.
  expect(evaluated("uses-church.ga")).toEqual(["<function>"]);

  const mutual = "MkPair(Cons(Z, Cons(Z, Nil())), S(S(Z)))";
  for (const encoding of ["bekic", "pair", "tag", "cps", "ref", "def"]) {
    expect(evaluated(`rec/mutual-${encoding}.ga`)).toEqual([mutual]);
  }
});
