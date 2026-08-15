import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { checkSource } from "../mod.ts";
import { typeToString } from "./types.ts";

/** Check a program, as a `[type, ...messages]` tuple the tests can read. */
function run(...lines: readonly string[]): [string, ...string[]] {
  const result = checkSource(mkSource(lines.join("\n"), "test.tg"));
  return [
    result.value === undefined ? "<none>" : typeToString(result.value),
    ...result.diagnostics.map((d) => d.message),
  ];
}

/** The type alone, asserting nothing was reported. */
function typeOf(...lines: readonly string[]): string {
  const [type, ...messages] = run(...lines);
  expect(messages).toEqual([]);
  return type;
}

const BOOL = ["datatype Bool where", "  | True", "  | False"];
const LIST = ["datatype List[A] where", "  | Nil", "  | Cons(A, List[A])"];

Deno.test("a constructor is a function of its fields", () => {
  expect(typeOf(...BOOL, "True")).toBe("Bool");
  expect(typeOf(...LIST, ...BOOL, "Cons(True, Nil[Bool]())"))
    .toBe("List[Bool]");
});

Deno.test("an annotated lambda infers its own type", () => {
  expect(typeOf(...BOOL, "fn (x: Bool) -> x")).toBe("Bool -> Bool");
  expect(typeOf(...BOOL, "fn [A](x: A) -> x")).toBe("[A](A) -> A");
});

Deno.test("an unannotated parameter is an error in inference position", () => {
  const [type, ...messages] = run("fn (x) -> x");
  expect(messages).toEqual([
    "cannot infer a type for x: annotate it, or use this function where its " +
    "parameter types are known",
  ]);
  expect(type).toBe("<bad> -> <bad>");
});

Deno.test("an unannotated parameter takes its type from the expected one", () => {
  expect(typeOf(...BOOL, "let f : (Bool) -> Bool = fn (x) -> x; f")).toBe(
    "Bool -> Bool",
  );
});

Deno.test("application instantiates a polymorphic callee", () => {
  expect(typeOf(...BOOL, "let id = fn [A](x: A) -> x; id(True)")).toBe(
    "Bool",
  );
});

Deno.test("a solution may name an EVar of an enclosing argument list", () => {
  // The inner list solves while `?A` is still open, and the bare lambda's `x`
  // has exactly `?A` for its type -- so `?B := ?A` is stored unsolved, and only
  // the outer `?A := Bool` finishes it. This is what `Context.apply` recurses
  // for; resolving one level deep would leave `?B` standing here.
  expect(
    typeOf(
      ...BOOL,
      "let id = fn [B](y: B) -> y",
      "let f = fn [A](g: (A) -> A, a: A) -> g(a)",
      "f(fn (x) -> id(x), True)",
    ),
  ).toBe("Bool");
});

Deno.test("a type argument is inferred from an invariant position", () => {
  // `List[?A] <: List[Bool]` only constrains ?A because invariance relates
  // arguments both ways rather than testing them for equality.
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let head = fn [A](xs: List[A]) -> xs;",
      "let bools : List[Bool] = Nil[Bool]();",
      "head(bools)",
    ),
  ).toBe("List[Bool]");
});

Deno.test("several arguments join rather than the first one winning", () => {
  const [type] = run(
    ...BOOL,
    "datatype Int where",
    "  | Zero",
    "let pick = fn [A](x: A, y: A) -> x;",
    "pick(True, Zero)",
  );
  // Nothing relates Bool and Int and there is no union, so the join is top.
  expect(type).toBe("unknown");
});

Deno.test("a bare lambda works in a later parameter list", () => {
  // The Scala staging: by the second application `A` is solved, so the
  // parameter type is ground and `x` needs no annotation.
  expect(
    typeOf(
      ...BOOL,
      "let apply = fn [A](x: A) -> fn (f: (A) -> A) -> f(x);",
      "apply(True)(fn (y) -> y)",
    ),
  ).toBe("Bool");
});

Deno.test("a bare lambda in the same list binds to the EVar itself", () => {
  // Better than the Scala rule requires: the parameter is bound to `?A`
  // directly, so as long as the body never needs its *structure*, the
  // constraint from the other argument settles it afterwards. Argument order
  // does not matter either, since nothing is solved until the list is done.
  expect(
    typeOf(
      ...BOOL,
      "let both = fn [A](x: A, f: (A) -> A) -> f(x);",
      "both(True, fn (y) -> y)",
    ),
  ).toBe("Bool");
  expect(
    typeOf(
      ...BOOL,
      "let both = fn [A](f: (A) -> A, x: A) -> f(x);",
      "both(fn (y) -> y, True)",
    ),
  ).toBe("Bool");
});

Deno.test("a bare lambda that destructures needs a later list", () => {
  // The boundary: `match` has to know the scrutinee's datatype, and `?A` is
  // not one yet. This is where an earlier parameter list is required.
  const [, ...messages] = run(
    ...BOOL,
    "let both = fn [A](x: A, f: (A) -> A) -> f(x);",
    "both(True, fn (y) -> match y with | True -> False | False -> True)",
  );
  expect(messages).toEqual(["cannot match on ?A: it is not a datatype"]);

  // Staged over two lists, the same body is fine.
  expect(
    typeOf(
      ...BOOL,
      "let staged = fn [A](x: A) -> fn (f: (A) -> A) -> f(x);",
      "staged(True)(fn (y) -> match y with | True -> False | False -> True)",
    ),
  ).toBe("Bool");
});

Deno.test("an explicit type application discharges the quantifier", () => {
  expect(typeOf(...BOOL, "let id = fn [A](x: A) -> x; id[Bool]")).toBe(
    "Bool -> Bool",
  );
  expect(typeOf(...BOOL, "let id = fn [A](x: A) -> x; id[Bool](True)"))
    .toBe("Bool");
});

Deno.test("a type argument is checked against its declared bound", () => {
  const [, ...messages] = run(
    ...BOOL,
    "datatype Int where",
    "  | Zero",
    "let f = fn [A <: Bool](x: A) -> x;",
    "f[Int]",
  );
  expect(messages).toEqual(["expected Bool, found Int"]);
});

Deno.test("a declared bound constrains what inference may pick", () => {
  const [, ...messages] = run(
    ...BOOL,
    "datatype Int where",
    "  | Zero",
    "let f = fn [A <: Bool](x: A) -> x;",
    "f(Zero)",
  );
  expect(messages).toEqual(["expected Bool, found Int"]);
});

Deno.test("an argument of the wrong type is reported once", () => {
  const [, ...messages] = run(
    ...BOOL,
    "datatype Int where",
    "  | Zero",
    "let f = fn (x: Bool) -> x;",
    "f(Zero)",
  );
  expect(messages).toEqual(["expected Bool, found Int"]);
});

Deno.test("arity is checked for arguments and for type arguments", () => {
  expect(run(...BOOL, "let f = fn (x: Bool) -> x; f()")[1])
    .toBe("expected 1 argument, found 0");
  expect(run(...BOOL, "let id = fn [A](x: A) -> x; id[Bool, Bool]")[1])
    .toBe("expected 1 type argument, found 2");
});

Deno.test("calling a non-function is reported without cascading", () => {
  const [type, ...messages] = run(...BOOL, "True(True)");
  expect(messages).toEqual(["Bool is not a function"]);
  expect(type).toBe("<bad>");
});

Deno.test("an unknown name is reported once, not at every later use", () => {
  const [, ...messages] = run("let f = nope; f(f)");
  expect(messages).toEqual(["unknown name nope"]);
});

Deno.test("a bad argument does not also fail to infer a type argument", () => {
  // `TBad` has to reach the EVar's bounds so it solves to `TBad` as well.
  // Short-circuiting the relation would leave it unconstrained and produce a
  // second complaint about the same mistake.
  const [type, ...messages] = run(
    ...BOOL,
    "let id = fn [A](x: A) -> x;",
    "id(nope)",
  );
  expect(messages).toEqual(["unknown name nope"]);
  expect(type).toBe("<bad>");
});

Deno.test("a let ascription is checked, and is what the name gets", () => {
  expect(typeOf(...BOOL, "let x : unknown = True; x")).toBe("unknown");
  expect(run(...BOOL, "let x : Bool = fn (y: Bool) -> y; x")[1])
    .toBe("expected Bool, found Bool -> Bool");
});

Deno.test("match binds a constructor's fields at the scrutinee's arguments", () => {
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let xs : List[Bool] = Cons(True, Nil[Bool]());",
      "match xs with",
      "  | Nil -> False",
      "  | Cons(head, rest) -> head",
    ),
  ).toBe("Bool");
});

Deno.test("a match that misses a constructor is reported", () => {
  const [, ...messages] = run(
    ...LIST,
    ...BOOL,
    "let xs : List[Bool] = Nil[Bool]();",
    "match xs with",
    "  | Nil -> True",
  );
  expect(messages).toEqual(["match is not exhaustive: Cons not covered"]);
});

Deno.test("a wildcard makes a match exhaustive", () => {
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let xs : List[Bool] = Nil[Bool]();",
      "match xs with",
      "  | Nil -> True",
      "  | _ -> False",
    ),
  ).toBe("Bool");
});

Deno.test("a constructor from another datatype is rejected", () => {
  const [, ...messages] = run(
    ...LIST,
    ...BOOL,
    "let xs : List[Bool] = Nil[Bool]();",
    "match xs with",
    "  | True -> True",
    "  | _ -> False",
  );
  expect(messages).toEqual(["True is not a constructor of List"]);
});

Deno.test("a pattern binding the wrong number of fields is reported", () => {
  const [, ...messages] = run(
    ...LIST,
    ...BOOL,
    "let xs : List[Bool] = Nil[Bool]();",
    "match xs with",
    "  | Nil -> True",
    "  | Cons(head) -> head",
  );
  expect(messages).toEqual(["Cons takes 2 fields, bound 1"]);
});

Deno.test("matching a non-datatype is reported", () => {
  const [, ...messages] = run(
    ...BOOL,
    "let f = fn (x: Bool) -> x;",
    "match f with",
    "  | _ -> True",
  );
  expect(messages).toEqual([
    "cannot match on Bool -> Bool: it is not a datatype",
  ]);
});

Deno.test("inferring a match joins its arms, privileging none by position", () => {
  // Nothing relates Bool and List[Bool], so the join is top -- and it is the
  // same answer whichever order the arms are written in.
  const forward = run(
    ...LIST,
    ...BOOL,
    "let xs : List[Bool] = Nil[Bool]();",
    "match xs with",
    "  | Nil -> True",
    "  | Cons(head, rest) -> rest",
  );
  const backward = run(
    ...LIST,
    ...BOOL,
    "let xs : List[Bool] = Nil[Bool]();",
    "match xs with",
    "  | Cons(head, rest) -> rest",
    "  | Nil -> True",
  );
  expect(forward).toEqual(["unknown"]);
  expect(backward).toEqual(["unknown"]);
});

Deno.test("a match joins to the more general arm where one relates", () => {
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let xs : List[Bool] = Nil[Bool]();",
      "let top : unknown = True;",
      "match xs with",
      "  | Nil -> True",
      "  | Cons(head, rest) -> top",
    ),
  ).toBe("unknown");
});

Deno.test("a match still checks every arm against an expected type", () => {
  const [, ...messages] = run(
    ...LIST,
    ...BOOL,
    "let xs : List[Bool] = Nil[Bool]();",
    "let f : (List[Bool]) -> Bool =",
    "  fn (ys) -> match ys with",
    "    | Nil -> True",
    "    | Cons(head, rest) -> rest",
    "f",
  );
  expect(messages).toEqual(["expected Bool, found List[Bool]"]);
});

Deno.test("a subtype is accepted where a supertype is expected", () => {
  expect(typeOf(...BOOL, "let f = fn (x: unknown) -> x; f(True)"))
    .toBe("unknown");
});

Deno.test("checking runs to the end, so one program reports every error", () => {
  const [, ...messages] = run("let f = nope; let g = alsoNope; g");
  expect(messages).toEqual(["unknown name nope", "unknown name alsoNope"]);
});

Deno.test("a require directive is skipped by the lexer, not lexed", () => {
  // The walker reads directives off the raw source; the lexer must step over
  // them without meeting `#` or `"`, which it has no tokens for. A single-source
  // run has nowhere to resolve one, so it says so rather than dropping it.
  const [type, ...messages] = run('#require "other.tg"', ...BOOL, "True");
  expect(type).toBe("Bool");
  expect(messages).toEqual([
    'cannot require "other.tg": this run has a single source',
  ]);
});

Deno.test("a term binding shadows a type variable of the same name", () => {
  // One namespace, so the parameter `A` takes the name and the inner
  // annotation has nothing left to resolve to.
  const [, ...messages] = run("fn [A](A: A) -> fn (y: A) -> y");
  expect(messages).toEqual(["unknown type A"]);

  // Not within one parameter list, though: annotations are all elaborated
  // before any parameter is pushed, so a list binds simultaneously.
  expect(typeOf("fn [A](A: A, y: A) -> y")).toBe("[A](A, A) -> A");
});

Deno.test("a constructor is shadowed by a later binding of its name", () => {
  // Constructors are seeded as ordinary terms at the outermost position, so
  // this is shadowing rather than a redeclaration.
  expect(typeOf(...BOOL, "let True = False", "True")).toBe("Bool");
});

Deno.test("a wildcard binds a position but no name", () => {
  const [, ...messages] = run(...BOOL, "fn (_: Bool) -> _");
  expect(messages).toEqual(["unknown name _"]);
});

Deno.test("a name bound twice in one parameter list is reported", () => {
  const [, ...messages] = run(...BOOL, "fn (x: Bool, x: Bool) -> x");
  expect(messages).toEqual(["x is bound twice in one parameter list"]);

  // The wildcard binds no name, so any number of them collide with nothing.
  expect(typeOf(...BOOL, "fn (_: Bool, _: Bool) -> True"))
    .toBe("(Bool, Bool) -> Bool");
});

Deno.test("a type parameter may not take a declared type's name", () => {
  // Declarations are the other namespace and nothing shadows them, so this
  // parameter would be unreachable rather than merely surprising.
  const [, ...messages] = run(...BOOL, "fn [Bool](x: Bool) -> x");
  expect(messages).toEqual(["type Bool is already declared"]);
});

Deno.test("a constructor may not be the wildcard", () => {
  // A binder may decline to name itself; a constructor is what a pattern
  // matches on, so an unnameable one could be neither built nor matched.
  const [, ...messages] = run(
    "datatype Weird where",
    "  | _",
    "  | Ok",
    "Ok",
  );
  // The parser refuses it, so nothing downstream has to check.
  expect(messages).toEqual(["a constructor name"]);
});

Deno.test("a declaration may not be named with the wildcard", () => {
  expect(run("datatype _ where", "  | Ok", "Ok")[1]).toBe("a type name");
  expect(run("typedef _ = unknown", "Ok")[1]).toBe("a type name");
});

Deno.test("a nullary constructor of a monomorphic datatype is a value", () => {
  expect(typeOf(...BOOL, "True")).toBe("Bool");
  // So applying it is applying a non-function, like any other value.
  expect(run(...BOOL, "True()")[1]).toBe("Bool is not a function");

  // Both conditions are needed: `Nil` still has a type argument to fix, and
  // `[A]List[A]` would be a quantifier over a non-function.
  expect(typeOf(...LIST, ...BOOL, "Nil[Bool]()")).toBe("List[Bool]");
});
