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

Deno.test("a nested application is solved before the outer one begins", () => {
  // `id(x)` is checked while `f`'s type parameters do not yet exist: an
  // argument's pattern hides them behind missing parts, and the batch is
  // pushed only for the relating that follows. So `?B` is solved and gone
  // before `?A` is created, and no solution ever names an EVar.
  expect(
    typeOf(
      ...BOOL,
      "let id = fn [B](y: B) -> y",
      "let f = fn [A](g: (A) -> A, a: A) -> g(a)",
      "f(fn (x: Bool) -> id(x), True)",
    ),
  ).toBe("Bool");
});

Deno.test("an expected type constrains the type arguments", () => {
  // Nothing in the argument list mentions `A` -- there is no argument list --
  // so the expected type is the only thing that can say what `Nil` is empty
  // of. Inferring first and comparing after would have given up before it saw
  // it.
  expect(
    typeOf(...LIST, ...BOOL, "let xs : List[Bool] = Nil();", "xs"),
  ).toBe("List[Bool]");
});

Deno.test("the expected type reaches the call but not its arguments", () => {
  // `Cons` takes its `A` from the annotation. The `Nil()` in its second field
  // does not: an argument is checked against a pattern that hides the type
  // parameters behind missing parts, so nothing there says what it is empty
  // of, and it has to say so itself.
  //
  // Only a datatype's invariant arguments make that necessary -- `List[never]`
  // would do otherwise -- so this is the variance limitation showing through,
  // not a limit of what checking propagates.
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let xs : List[Bool] = Cons(True, Nil[Bool]());",
      "xs",
    ),
  ).toBe("List[Bool]");
});

Deno.test("an application checked against the wrong type says so once", () => {
  // The expected type is a constraint, not a demand: `?A` picks up `Bool` from
  // the argument and `List[Bool]` from the context, they do not agree, and the
  // conflict is reported where the call is. The result is then `TBad`, so the
  // subsumption that follows adds nothing.
  const [, ...messages] = run(
    ...LIST,
    ...BOOL,
    "let id = fn [A](x: A) -> x;",
    "let bad : List[Bool] = id(True);",
    "bad",
  );
  expect(messages).toEqual([
    "cannot infer the type argument A: it is bounded below by Bool and " +
    "above by List[Bool], and no type is both",
  ]);
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
  // The Scala staging: by the second application `A` is fixed, so the
  // parameter type is ground and `y` needs no annotation.
  //
  // `A` is given explicitly because the first list cannot settle it: it occurs
  // invariantly in what that list hands back, `((A) -> A) -> A`.
  expect(
    typeOf(
      ...BOOL,
      "let apply = fn [A](x: A) -> fn (f: (A) -> A) -> f(x);",
      "apply[Bool](True)(fn (y) -> y)",
    ),
  ).toBe("Bool");
});

Deno.test("an invariant occurrence is settled by a bound from one side", () => {
  // `True` says `Bool <: A` and nothing says anything from above, so `Bool` is
  // the only type any argument asked for -- a demand weighed against a default
  // is not a choice, and a staged call settles on it without an annotation.
  expect(
    typeOf(
      ...BOOL,
      "let apply = fn [A](x: A) -> fn (f: (A) -> A) -> f(x);",
      "apply(True)(fn (y) -> y)",
    ),
  ).toBe("Bool");
});

Deno.test("a bare lambda in the same list has no type to take", () => {
  // What an argument is checked against hides the type parameters behind
  // missing parts, so `(A) -> A` arrives as `(?) -> ?` and `y` is told
  // nothing. The constraint from the other argument cannot help: it is
  // collected after this argument has already had to be checked.
  for (
    const call of [
      "both(True, fn (y) -> y)",
      "both(fn (y) -> y, True)",
    ]
  ) {
    const decl = call.startsWith("both(True")
      ? "let both = fn [A](x: A, f: (A) -> A) -> f(x);"
      : "let both = fn [A](f: (A) -> A, x: A) -> f(x);";
    const [, ...messages] = run(...BOOL, decl, call);
    expect(messages.length).toBe(1);
    expect(messages[0]).toContain("cannot infer a type for y");
  }

  // Annotated, in either order, and nothing else has changed.
  expect(
    typeOf(
      ...BOOL,
      "let both = fn [A](x: A, f: (A) -> A) -> f(x);",
      "both(True, fn (y: Bool) -> y)",
    ),
  ).toBe("Bool");
  expect(
    typeOf(
      ...BOOL,
      "let both = fn [A](f: (A) -> A, x: A) -> f(x);",
      "both(fn (y: Bool) -> y, True)",
    ),
  ).toBe("Bool");
});

Deno.test("a bare lambda that destructures needs a later list", () => {
  // Reported at the parameter now rather than at the `match`: there is no
  // type to destructure because there was none to begin with. One message
  // either way, and it names the thing the author can fix.
  const [, ...messages] = run(
    ...BOOL,
    "let both = fn [A](x: A, f: (A) -> A) -> f(x);",
    "both(True, fn (y) -> match y with | True -> False | False -> True)",
  );
  expect(messages.length).toBe(1);
  expect(messages[0]).toContain("cannot infer a type for y");

  // Staged over two lists, the same body is fine: the first list settles `A`
  // from `True` alone, so by the second one `y` has a type to match on.
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
  expect(messages).toEqual([
    "cannot infer the type argument A: it is bounded below by Int and above " +
    "by Bool, and no type is both",
  ]);
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
  // them without meeting `#` or `"`, which it has no tokens for. A lone source
  // is a filesystem holding just itself, so the directive resolves to nothing
  // and is reported in the walker's words -- the same ones a real run gives a
  // path that is not there.
  const [type, ...messages] = run('#require "other.tg"', ...BOOL, "True");
  expect(type).toBe("Bool");
  expect(messages).toEqual(['cannot resolve "other.tg"']);
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

Deno.test("a declared bound is checked against what the arguments demand", () => {
  // The bound is an upper constraint, the argument a lower one, so this is the
  // `lower <: upper` step failing rather than a rule of its own.
  const [type, ...messages] = run(
    ...BOOL,
    "datatype Int where | Zero",
    "let f = fn [A <: Bool](x: A) -> x;",
    "f(Zero)",
  );
  expect(type).toBe("<bad>");
  expect(messages.length).toBe(1);
  expect(messages[0]).toContain("Int");
});

Deno.test("a type argument nothing constrained is a warning, and checks", () => {
  // `A` reaches neither the parameters nor the result, so nothing downstream
  // can tell which type it took -- sound, and still worth saying, since the
  // `never` it settles on is a type the author never wrote.
  const [type, ...messages] = run(
    ...BOOL,
    "let f = fn [A](x: Bool) -> x;",
    "f(True)",
  );
  expect(type).toBe("Bool");
  expect(messages).toEqual([
    "nothing constrains the type argument A, so it was taken to be never; " +
    "give it explicitly if that is not what was meant",
  ]);
});

Deno.test("two type parameters of one call no longer depend on each other", () => {
  // This used to be refused as `?A <: ?B`, a dependency within one batch that
  // the selection cannot see. Constraints are now collected between the *complete*
  // type an argument came back with and the parameter type, so `?B := Bool`
  // arrives ground and there is no dependency to refuse.
  expect(
    typeOf(
      ...BOOL,
      "let both = fn [A, B](x: A, f: (A) -> B) -> f(x);",
      "both(True, fn (y: Bool) -> y)",
    ),
  ).toBe("Bool");
});

Deno.test("staging the same call in two lists is inferred", () => {
  // The annotation the batch rule asks for is not the only way out: a second
  // parameter list puts `B` in a batch of its own, with `A` already solved.
  expect(
    typeOf(
      ...BOOL,
      "let both = fn [A](x: A) -> fn [B](f: (A) -> B) -> f(x);",
      "both(True)(fn (y) -> y)",
    ),
  ).toBe("Bool");
});

Deno.test("a lambda is not pushed into a variable that merely bounds one", () => {
  // `X <: (Bool) -> Bool` says every X is that arrow, never the reverse, so a
  // written arrow is not an X. Promoting the *expected* type would accept one.
  const [, ...messages] = run(
    ...BOOL,
    "let h = fn [X <: (Bool) -> Bool](k: (X) -> Bool) -> k(fn (b: Bool) -> b);",
    "h",
  );
  expect(messages).toEqual(["expected X, found Bool -> Bool"]);
});

Deno.test("the same value is judged the same written inline or bound", () => {
  // The checking rule and the inference rule have to agree: a lambda argument
  // must not pass where the identical `let` fails.
  const inline = run(
    ...BOOL,
    "let h = fn [X <: (Bool) -> Bool](k: (X) -> Bool) -> k(fn (b: Bool) -> b);",
    "h",
  );
  const bound = run(
    ...BOOL,
    "let id = fn (b: Bool) -> b;",
    "let h = fn [X <: (Bool) -> Bool](k: (X) -> Bool) -> k(id);",
    "h",
  );
  expect(inline.slice(1)).toEqual(bound.slice(1));
});

Deno.test("an unannotated lambda argument is reported once, not per variable", () => {
  // `(A) -> B` arrives as `(?) -> ?`, so `y` has nothing -- one message, at
  // the parameter. Neither `A` nor `B` goes on to complain separately that
  // nothing constrained it: that is this same mistake under another name.
  const [, ...messages] = run(
    ...BOOL,
    "let both = fn [A, B](f: (A) -> B) -> f;",
    "both(fn (y) -> y)",
  );
  expect(messages.length).toBe(1);
  expect(messages[0]).toContain("cannot infer a type for y");
});

Deno.test("an arity error settles the call, and nothing is inferred after it", () => {
  // No type arguments are asked for at all: the missing argument is what would
  // have constrained `B`, so there is nothing left to ask. Saying so again
  // under another name would be one mistake told twice.
  const [, ...messages] = run(
    ...BOOL,
    "let f = fn [A, B](x: A, y: B) -> x;",
    "f(True)",
  );
  expect(messages).toEqual(["expected 2 arguments, found 1"]);
});

Deno.test("a lambda of the wrong arity is still checked inward", () => {
  // The parameters that line up still take their types from the expected
  // type: inferring instead would ask the author to annotate every one of
  // them. What is left over is `<bad>`, so nothing is reported at the extra
  // parameter's uses -- the count is said once, on its own.
  const [, ...tooMany] = run(
    ...BOOL,
    "let f : (Bool) -> Bool = fn (x, y) -> x;",
    "f",
  );
  expect(tooMany).toEqual([
    "cannot infer a type for y: annotate it, or use this function where " +
    "its parameter types are known",
    "expected 1 parameter, found 2",
  ]);

  // Annotated, the extra parameter has a type and only the count is left --
  // which is why the pattern says *nothing* about a position it does not
  // reach rather than saying `<bad>`. Standing `<bad>` there would claim the
  // parameter had been supplied when nothing supplied it.
  const [, ...annotated] = run(
    ...BOOL,
    "let f : (Bool) -> Bool = fn (x, y: Bool) -> x;",
    "f",
  );
  expect(annotated).toEqual(["expected 1 parameter, found 2"]);

  // A parameter the term never wrote is filled from the expected type, so the
  // count is again the whole of what differs.
  const [, ...tooFew] = run(
    ...BOOL,
    "let f : (Bool, Bool) -> Bool = fn (x) -> x;",
    "f",
  );
  expect(tooFew).toEqual(["expected 2 parameters, found 1"]);
});

Deno.test("a lambda checked against a non-function is inferred instead", () => {
  // Nothing to push inward there, so the unannotated parameter is a real
  // second complaint rather than a consequence of the first.
  const [, ...messages] = run(...BOOL, "let f : Bool = fn (x) -> x;", "f");
  expect(messages.length).toBe(2);
  expect(messages[1]).toContain("expected Bool, found");
});

Deno.test("an annotation is what the body is typed against, not the pattern", () => {
  // The written type wins outright: the pattern is consulted only for whether
  // the annotation accepts what a caller may pass, and `unknown` does. So `x`
  // is an `unknown` inside the body, and the one thing wrong with this lambda
  // is its result -- said once, where it happens.
  const [, ...wider] = run(
    ...BOOL,
    "let f : (Bool) -> Bool = fn (x: unknown) -> x;",
    "f",
  );
  expect(wider).toEqual(["expected Bool, found unknown"]);

  // Narrower is not the parameter's own error either. The annotation stands,
  // the body is typed against it, and what is wrong is the type the lambda
  // ends up with -- said once, by the coercion at the lambda, which names the
  // part that could not be reached rather than the whole arrow around it.
  const [, ...narrower] = run(
    ...LIST,
    ...BOOL,
    "let g : (List[Bool]) -> unknown = fn (x: Bool) -> x;",
    "g",
  );
  expect(narrower).toEqual(["expected List[Bool], found Bool"]);
});
