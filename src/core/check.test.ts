import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { checkSource } from "../mod.ts";
import { typeToString } from "./types.ts";

/** Check a program, as a `[type, ...messages]` tuple the tests can read. */
function run(...lines: readonly string[]): [string, ...string[]] {
  const result = checkSource(mkSource(lines.join("\n"), "test.ga"));
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
const LIST = ["datatype List[A] where", "  | Nil()", "  | Cons(A, List[A])"];
/** Invariant, `A` standing both ways in the one field. */
const CELL = ["datatype Cell[A] where", "  | MkCell((A) -> A)"];
/** Contravariant, and the only shape that gets there. */
const SINK = ["datatype Sink[A] where", "  | MkSink((A) -> Bool)"];
/** A `List` that is never empty, and so presents as one. */
const NONEMPTY = [
  "datatype NonEmpty[A] <: List[A] where",
  "  | One(x: A)              -> Cons(x, Nil())",
  "  | More(x: A, r: List[A]) -> Cons(x, r)",
];

Deno.test("a constructor is a function of its fields", () => {
  expect(typeOf(...BOOL, "True")).toBe("Bool");
  expect(typeOf(...LIST, ...BOOL, "Cons(True, Nil[Bool]())"))
    .toBe("List[Bool]");
});

Deno.test("the term form follows the declaration form", () => {
  // A bare declaration is a value, so applying it applies a non-function.
  expect(run(...BOOL, "True()")[1]).toBe("Bool is not a function");
  // And a declared `()` is a function, so the bare name is one -- which is a
  // type error only where something wanted the datatype.
  const WITH = ["datatype Flag where", "  | Off()"];
  expect(typeOf(...WITH, "Off")).toBe("() -> Flag");
  expect(typeOf(...WITH, "Off()")).toBe("Flag");
});

Deno.test("a pattern is spelled the same whichever form declared it", () => {
  // Patterns take apart *fields*, and a nullary constructor has none either
  // way, so the distinction is invisible here -- which is what makes it
  // presentational.
  expect(typeOf(
    ...LIST,
    ...BOOL,
    "fn (xs: List[Bool]) -> match xs with",
    "  | Nil -> True",
    "  | Cons(h, t) -> h",
  )).toBe("List[Bool] -> Bool");
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

Deno.test("never is callable, at any arity and with type arguments", () => {
  // `never` sits under `unknown -> never` at every arity, and under every
  // polymorphic function type, so calling one is not a mistake and there is
  // nothing to say about how many arguments it was written with either.
  expect(typeOf(...BOOL, "fn (loop: never) -> loop(True, False)"))
    .toBe("never -> never");
  expect(typeOf(...BOOL, "fn (loop: never) -> loop[Bool](True)"))
    .toBe("never -> never");
});

Deno.test("never in an invariant argument is a choice, not a mismatch", () => {
  // `never` is a `Cell` of anything and nothing picks which. The call goes
  // through on `Cell[never]` -- a type comes back at all, so this was no
  // error -- and the report is what says a choice was made here.
  const [type, ...messages] = run(
    ...CELL,
    ...BOOL,
    "let use = fn [A](c: Cell[A]) -> True;",
    "fn (loop: never) -> use(loop)",
  );
  expect(messages).toEqual([
    "no least Cell[?] to cast never to: Cell's argument A is invariant, so " +
    "it was taken to be never",
  ]);
  expect(type).toBe("never -> Bool");
});

Deno.test("a covariant argument has an extreme, so nothing is chosen", () => {
  // The same call against a `List`, where `List[never]` *is* the least one:
  // there is nothing arbitrary left to report.
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let len = fn [A](xs: List[A]) -> True;",
      "fn (loop: never) -> len(loop)",
    ),
  ).toBe("never -> Bool");
});

Deno.test("a datatype's arguments move the way its parameters say", () => {
  // Three declarations, three answers, and the only difference between them
  // is where the parameter stood in the field that used it.
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let widen = fn (xs: List[unknown]) -> True;",
      "fn (bs: List[Bool]) -> widen(bs)",
    ),
  ).toBe("List[Bool] -> Bool");
  expect(
    typeOf(
      ...SINK,
      ...BOOL,
      "let narrow = fn (s: Sink[Bool]) -> True;",
      "fn (s: Sink[unknown]) -> narrow(s)",
    ),
  ).toBe("Sink[unknown] -> Bool");
  const [type, ...messages] = run(
    ...CELL,
    ...BOOL,
    "let hold = fn (c: Cell[unknown]) -> True;",
    "fn (c: Cell[Bool]) -> hold(c)",
  );
  // The mismatch is the argument's, and is reported there.
  expect(messages).toEqual(["expected unknown, found Bool"]);
  expect(type).toBe("Cell[Bool] -> Bool");
});

Deno.test("an empty list takes its element type from its neighbours", () => {
  // `Nil()` is a `List[never]`, and a covariant argument lets that sit under
  // the `List[?A]` the outer call is collecting -- so `?A` takes `Bool` from
  // the first argument and nothing has to be written. Invariance had no such
  // reading: `?A` would have had to be `never` *and* `Bool`.
  expect(typeOf(...LIST, ...BOOL, "Cons(True, Nil())")).toBe("List[Bool]");
});

Deno.test("arms join at the argument, not only at the datatype", () => {
  // Two `List`s that are not the same type still have a `List` above them,
  // which is `#latticeData` going argumentwise where it used to ask for
  // equivalence and give up on top.
  expect(
    typeOf(
      ...LIST,
      ...BOOL,
      "let bs : List[Bool] = Cons(True, Nil());",
      "fn (b: Bool) -> match b with",
      "  | True -> bs",
      "  | False -> Nil[unknown]()",
    ),
  ).toBe("Bool -> List[unknown]");
});

Deno.test("a name in a domain is documentation and reaches no type", () => {
  // Dropped at elaboration, so a named arrow and a bare one are one type --
  // which is what keeps a name from ever deciding a cast, an equality, or what
  // gets printed.
  expect(typeOf(...BOOL, "fn (f: (x: Bool) -> Bool) -> f"))
    .toBe("(Bool -> Bool) -> Bool -> Bool");
  expect(typeOf(...BOOL, "let f : (x: Bool) -> Bool = fn (y: Bool) -> y;", "f"))
    .toBe("Bool -> Bool");
  expect(typeOf(...BOOL, "let f : (Bool) -> Bool = fn (y: Bool) -> y;", "f"))
    .toBe("Bool -> Bool");

  // A constructor's fields are the same domain, so they take names on the same
  // terms and lose them on the same terms.
  expect(
    typeOf(
      "datatype Box where",
      "  | MkBox(flag: Bool, Bool)",
      ...BOOL,
      "MkBox",
    ),
  ).toBe("(Bool, Bool) -> Box");

  // And it binds nothing: `x` scopes over nothing until a dependent arrow has
  // something to bind it to.
  expect(run(...BOOL, "fn (f: (x: Bool) -> x) -> f")[1]).toBe("unknown type x");
});

Deno.test("the reference builtins are seeded, and Ref is a type", () => {
  expect(typeOf(...BOOL, "let c = ref!(True);", "set!(c, False)")).toBe("Bool");
  expect(typeOf(...BOOL, "fn (c: Ref[Bool]) -> get!(c)"))
    .toBe("Ref[Bool] -> Bool");
  // `set!` answers the value written, so a write is an expression.
  expect(typeOf(...BOOL, "fn (c: Ref[Bool]) -> set!(c, True)"))
    .toBe("Ref[Bool] -> Bool");
});

Deno.test("a cell is invariant, and so is anything holding one", () => {
  // Stipulated, not inferred -- and the stipulation is what every datatype
  // holding a `Ref` reads, so `Holder` comes out invariant without anything
  // in it standing both ways on its own.
  const [type, ...messages] = run(
    ...BOOL,
    "datatype Holder[A] where",
    "  | H(Ref[A])",
    "let widen = fn (h: Holder[unknown]) -> True;",
    "fn (h: Holder[Bool]) -> widen(h)",
  );
  expect(messages).toEqual(["expected unknown, found Bool"]);
  expect(type).toBe("Holder[Bool] -> Bool");
});

Deno.test("a cell is not a datatype, so it is not matchable", () => {
  // Refused with the other unmatchable heads rather than analysed. A `Ref` is
  // inhabited and still has nothing to take apart, which is why it is not a
  // datatype with no constructors: the exhaustiveness set would read that as
  // an empty *type*, call the arm unreachable and answer `never`.
  const [type, ...messages] = run(
    ...BOOL,
    "fn (c: Ref[Bool]) -> match c with",
    "  | _ -> True",
  );
  expect(messages).toEqual(["cannot match on Ref[Bool]: it is not a datatype"]);
  expect(type).toBe("Ref[Bool] -> <bad>");
});

Deno.test("Ref is a name, so it obeys the rules every type name obeys", () => {
  // Seeded as a transparent alias for the former rather than spelled in the
  // grammar, so none of these is a rule of its own -- each is the message the
  // machinery already had for a `Pair` or a `List`.
  expect(run(...BOOL, "datatype Ref[A] where", "  | MkRef(A)", "True")[1])
    .toBe("type Ref is already declared");
  expect(run(...BOOL, "typedef Ref = Bool", "True")[1])
    .toBe("type Ref is already declared");
  expect(run(...BOOL, "fn [Ref](x: Bool) -> x")[1])
    .toBe("type Ref is already declared");
  expect(run(...BOOL, "fn (c: Ref) -> True")[1])
    .toBe("type alias Ref takes 1 type argument, given 0");
});

Deno.test("only the checker declares a bang name, so none can be shadowed", () => {
  // The lexer takes a trailing `!` on any identifier and knows no list of
  // builtins; what makes the three of them the only ones is that no *binding*
  // position admits the spelling.
  expect(run(...BOOL, "let set! = fn (x: Bool) -> x;", "set!(True)")[1])
    .toBe("set! may not be bound: a trailing `!` marks a builtin");
  // A use that resolves to nothing is an unknown name like any other, which
  // is what a misspelt builtin should be told.
  expect(run(...BOOL, "st!(True)")[1]).toBe("unknown name st!");
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

Deno.test("an arm no value reaches is reported, and does not join", () => {
  // The type is the reachable arm's alone: joining a dead arm in would widen
  // the answer to `unknown` for an arm that never runs.
  expect(
    run(
      ...BOOL,
      "datatype Nat where",
      "  | Zero",
      "match True with",
      "  | _ -> True",
      "  | True -> Zero",
    ),
  ).toEqual(["Bool", "this arm is unreachable: True is matched above"]);
});

Deno.test("a dead arm's body is still checked", () => {
  const [, ...messages] = run(
    ...BOOL,
    "match True with",
    "  | _ -> True",
    "  | True -> nosuchname",
  );
  expect(messages).toEqual([
    "this arm is unreachable: True is matched above",
    "unknown name nosuchname",
  ]);
});

Deno.test("a dead arm says what is left, which is what covered it", () => {
  const dead = (...arms: readonly string[]) =>
    run(...BOOL, "match True with", ...arms).slice(1);

  // A constructor arm names the constructor, whether an arm of its own or a
  // wildcard took it; a wildcard has no name to give and says so of values.
  expect(dead("  | True -> True", "  | True -> False", "  | False -> True"))
    .toEqual(["this arm is unreachable: True is matched above"]);
  expect(dead("  | _ -> True", "  | True -> False"))
    .toEqual(["this arm is unreachable: True is matched above"]);
  expect(dead("  | True -> True", "  | False -> False", "  | _ -> True"))
    .toEqual(["this arm is unreachable: every value is matched above"]);
  expect(dead("  | _ -> True", "  | _ -> False"))
    .toEqual(["this arm is unreachable: every value is matched above"]);
});

Deno.test("a name that is no constructor is not also matched above", () => {
  // It was never in the set, so it cannot have been taken out of it: asking
  // coverage about it would blame the author twice for one mistake.
  const [, ...messages] = run(
    ...BOOL,
    "match True with",
    "  | Bogus -> False",
    "  | Bogus -> True",
    "  | True -> True",
    "  | False -> True",
  );
  expect(messages).toEqual([
    "Bogus is not a constructor of Bool",
    "Bogus is not a constructor of Bool",
  ]);
});

Deno.test("a wildcard that still has a constructor to catch is silent", () => {
  expect(
    typeOf(...BOOL, "match True with", "  | True -> True", "  | _ -> False"),
  )
    .toBe("Bool");
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

Deno.test("matching on never is not a mistake, and answers never", () => {
  // Nothing reaches a `never` scrutinee, so there is no datatype to resolve
  // names against, nothing to leave uncovered, and no arm whose type the
  // match could answer with -- every one of them is unreachable, and the
  // rule for those is that the type is dropped and the body checked anyway.
  expect(typeOf(
    ...BOOL,
    "fn (x: never) ->",
    "  match x with",
    "  | True -> True",
    "  | Cons(y) -> y(True)",
  )).toBe("never -> never");

  const [type, ...messages] = run(
    ...BOOL,
    "fn (x: never) ->",
    "  match x with",
    "  | True -> nosuchname",
  );
  expect(messages).toEqual(["unknown name nosuchname"]);
  expect(type).toBe("never -> never");
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
  const [type, ...messages] = run('#require "other.ga"', ...BOOL, "True");
  expect(type).toBe("Bool");
  expect(messages).toEqual(['cannot resolve "other.ga"']);
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

Deno.test("a type argument nothing constrained is silent", () => {
  // `A` reaches neither the parameters nor the result, so nothing downstream
  // can tell which type it took. Nor could an author: there is no position to
  // write a better one at, and saying so would report every use of a type
  // parameter the callee happens not to need.
  expect(
    run(...BOOL, "let f = fn [A](x: Bool) -> x;", "f(True)"),
  ).toEqual(["Bool"]);
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

const NAT = ["datatype Nat where", "  | Z", "  | S(Nat)"];

Deno.test("an annotated def is visible to its whole group", () => {
  // What `let` cannot do: `even` names a binding written below it. Signatures
  // are pushed before any body is checked, so the reference resolves to a level
  // that is already there rather than to a forward pointer.
  expect(typeOf(
    ...BOOL,
    ...NAT,
    "def even(n: Nat): Bool = match n with",
    "  | Z -> True",
    "  | S(k) -> odd(k)",
    "def odd(n: Nat): Bool = match n with",
    "  | Z -> False",
    "  | S(k) -> even(k)",
    "even(S(Z))",
  )).toBe("Bool");
});

Deno.test("an unannotated def is a let, and unknown inside its own body", () => {
  // No signature to push, so it is checked where it stands and its siblings see
  // the type it turned out to have. This is the case an SCC pass would have
  // ordered; here it works because `foo` needs no annotation to be inferred and
  // the annotated two need no inference to be visible.
  expect(typeOf(
    ...NAT,
    "def rec1(n: Nat): Nat = rec2(foo(n))",
    "def foo(n: Nat) = S(n)",
    "def rec2(n: Nat): Nat = rec1(n)",
    "rec1(Z)",
  )).toBe("Nat");

  // Recursion without a signature is refused at the call, where the recursion
  // is. `unknown` and not `<bad>`: nothing is known of the binding yet, which
  // is a fact and not a failure, so no report is filed until one is used.
  expect(run(...NAT, "def loop(n: Nat) = loop(n)", "loop(Z)")[1])
    .toBe("unknown is not a function");

  // And it really is only the *call* that is refused -- passing it on is fine,
  // which is what `unknown` says and what a bad type could not.
  expect(typeOf(
    ...NAT,
    ...LIST,
    "def opaque(n: Nat) = Cons(opaque, Nil())",
    "opaque(Z)",
  )).toBe("List[unknown]");
});

Deno.test("a def group is the run of adjacent defs, nothing wider", () => {
  // A `let` between them is sequential, so `a` would have to see a binding that
  // is not yet bound. The run is the largest scope where that cannot happen.
  expect(
    run(
      ...NAT,
      "def a(n: Nat): Nat = b(n)",
      "let sep = Z",
      "def b(n: Nat): Nat = a(n)",
      "b(Z)",
    )[1],
  ).toBe("unknown name b");
});

Deno.test("several parameter lists stage a def's type arguments", () => {
  // The same rule `foldr(xs)(z)(op)` is written for, now sayable in one binder:
  // `A` is settled by the first list, so the second reaches a bare lambda that
  // already knows its parameter.
  expect(typeOf(
    ...NAT,
    ...LIST,
    "def foldr[A](xs: List[A])[B](z: B)(op: (A, B) -> B): B =",
    "  match xs with",
    "  | Nil -> z",
    "  | Cons(h, t) -> op(h, z)",
    "foldr(Cons(Z, Nil()))(Z)(fn (h, acc) -> h)",
  )).toBe("Nat");

  // Fused into one list, `B` is solved before `op` is looked at -- the same
  // failure the `fn` form has, since the sugar is only the `fn` form.
  expect(
    run(
      ...NAT,
      ...LIST,
      "def foldr[A, B](xs: List[A])(z: B)(op: (A, B) -> B): B = z",
      "foldr(Cons(Z, Nil()))(Z)(fn (h, acc) -> h)",
    )[1],
  ).toBe("expected never, found Nat");
});

Deno.test("a def's parameters must be annotated, and stand bad if not", () => {
  // Nothing can supply them: a `def`'s body is inferred, or checked against its
  // own signature, and never sits where a context would know them. So the
  // report is due at the binder, not deferred to a use the way `unknown` is.
  const [, first] = run(...NAT, "def f(n) = n", "Z");
  expect(first).toBe(
    "cannot infer a type for n: a def's parameters must be annotated, " +
      "nothing else can supply them",
  );

  // The def keeps the signature it wrote, so the group still sees it and the
  // omission is not reported again as an unknown name at every call.
  const [, ...both] = run(
    ...NAT,
    "def even(n): Nat = odd(n)",
    "def odd(m): Nat = even(m)",
    "Z",
  );
  expect(both.length).toBe(2);
  expect(both.every((message) => message.startsWith("cannot infer a type")))
    .toBe(true);

  // And the body is still checked, the parameter standing `bad` rather than
  // hiding what else is written there.
  expect(run(...NAT, "def f(n): Nat = nope(n)", "Z").slice(1))
    .toEqual([
      "cannot infer a type for n: a def's parameters must be annotated, " +
      "nothing else can supply them",
      "unknown name nope",
    ]);
});

Deno.test("a def's parameter types are elaborated once, not twice", () => {
  // The signature is the one place they are written: left on the `Abs` as well
  // they would be read again for the body, doubling every diagnostic they
  // raise. Two occurrences in the source, two reports.
  const [, ...messages] = run(...NAT, "def f(x: Nope): Nope = x", "Z");
  expect(messages).toEqual(["unknown type Nope", "unknown type Nope"]);
});

Deno.test("a def bound twice in one group is reported once", () => {
  expect(
    run(...NAT, "def f(n: Nat): Nat = n", "def f(n: Nat): Nat = n", "Z")[1],
  )
    .toBe("f is bound twice in one def group");
});

Deno.test("a datatype may be used as the one it presents as", () => {
  // Every `List` function takes a `NonEmpty` and needs no word about it.
  expect(typeOf(
    ...LIST,
    ...BOOL,
    ...NONEMPTY,
    "def length(xs: List[Bool]): Bool = True;",
    "length(One(True))",
  )).toBe("Bool");

  // Covariantly, and no further: a `List` is not a `NonEmpty`.
  expect(
    run(
      ...LIST,
      ...BOOL,
      ...NONEMPTY,
      "def head(xs: NonEmpty[Bool]): Bool = True;",
      "head(Nil[Bool]())",
    )[1],
  ).toBe("expected NonEmpty[Bool], found List[Bool]");
});

Deno.test("arms of two datatypes join at the one they present as", () => {
  // A head-level join, where `#latticeData` used to have nothing above two
  // names and answer top.
  expect(typeOf(
    ...LIST,
    ...BOOL,
    ...NONEMPTY,
    "fn (b: Bool) -> match b with",
    "  | True -> One(True)",
    "  | False -> Nil[Bool]()",
  )).toBe("Bool -> List[Bool]");

  // Two children of one super type rise past both, and no further than they must.
  expect(typeOf(
    ...LIST,
    ...BOOL,
    ...NONEMPTY,
    "fn (b: Bool) -> match b with",
    "  | True -> One(True)",
    "  | False -> More(True, Nil[Bool]())",
  )).toBe("Bool -> NonEmpty[Bool]");
});

Deno.test("a constructor is reachable through the datatype that declared it", () => {
  expect(typeOf(...LIST, ...BOOL, "List.Cons(True, List.Nil[Bool]())"))
    .toBe("List[Bool]");

  // Which is what the plain name cannot promise. `Cons` is whatever was
  // declared last, and the qualified one reaches past it either way.
  const SNOC = ["datatype Snoc where", "  | Cons(Bool)"];
  expect(typeOf(...LIST, ...BOOL, ...SNOC, "Cons(True)")).toBe("Snoc");
  expect(typeOf(...LIST, ...BOOL, ...SNOC, "List.Cons(True, Nil[Bool]())"))
    .toBe("List[Bool]");
  expect(typeOf(...LIST, ...BOOL, ...SNOC, "Snoc.Cons(True)")).toBe("Snoc");

  // A `let` may take the plain name and never the qualified one.
  expect(typeOf(
    ...LIST,
    ...BOOL,
    "let Cons = True;",
    "List.Cons(Cons, Nil[Bool]())",
  )).toBe("List[Bool]");
});

Deno.test("a qualified name may be used, never bound", () => {
  expect(run(...LIST, ...BOOL, "let List.Cons = True; True")[1])
    .toBe(
      "List.Cons may not be bound: a `.` names a constructor of a datatype",
    );
  expect(run(...BOOL, "Bool.Nope")[1]).toBe("unknown name Bool.Nope");
});

Deno.test("a super constructor is checked as a term against the super type", () => {
  const bad = (...arms: readonly string[]) =>
    run(...LIST, ...BOOL, "datatype One[A] <: List[A] where", ...arms, "True")
      .slice(1);

  expect(bad("  | Mk(x: A) -> Cons(x, Nil())")).toEqual([]);
  // The field's type comes from the super type instantiated at *this* datatype's
  // arguments, so the tail's second field wants a `List[A]`.
  expect(bad("  | Mk(x: A) -> Cons(x, x)"))
    .toEqual(["expected List[?], found A"]);
  expect(bad("  | Mk(x: A) -> Cons(x)"))
    .toEqual(["expected 2 arguments, found 1"]);

  // A field with no name cannot be reached, the name being the only way in.
  expect(bad("  | Mk(A) -> Cons(x, Nil())")).toEqual(["unknown name x"]);
});

Deno.test("every tail is a constructor of the super type, on the tree", () => {
  const bad = (...arms: readonly string[]) =>
    run(...LIST, ...BOOL, "datatype One[A] <: List[A] where", ...arms, "True")
      .slice(1);

  // Named against the super type and not the term scope, so neither a shadowing
  // `let` nor a constructor of some other datatype can stand in a tail.
  expect(bad("  | Mk(x: A) -> Snoc(x)"))
    .toEqual(["unknown name List.Snoc"]);
  // A `let` may shadow `Cons` for the arguments and never for the tail: the
  // tail was rewritten to `List.Cons` before any scope existed.
  expect(bad(
    "  | Mk(x: A) ->",
    "      let Cons = True;",
    "      Cons(x, Nil())",
  )).toEqual([]);
  expect(bad("  | Mk(x: A) -> x")).toEqual(["unknown name List.x"]);
  // A tail that is no application of a name at all.
  expect(bad("  | Mk(x: A) -> fn (y: A) -> Cons(y, Nil())")).toEqual([
    "a super constructor ends in a constructor of List, applied to its fields",
    "expected List[A], found A -> List[A]",
  ]);
});

Deno.test("a super constructor may compute, and may name any constructor", () => {
  expect(typeOf(
    ...LIST,
    ...BOOL,
    "datatype Pair[A] <: List[A] where",
    "  | Two(x: A, y: A) -> Cons(x, Cons(y, Nil()))",
    "def swap(p: Pair[Bool]): List[Bool] = p;",
    "swap(Two(True, False))",
  )).toBe("List[Bool]");
});

Deno.test("a super constructor body may write the datatype's own parameters", () => {
  expect(typeOf(
    ...LIST,
    ...BOOL,
    "datatype One[A] <: List[A] where",
    "  | Mk(x: A) -> Cons(x, Nil[A]())",
    "Mk(True)",
  )).toBe("One[Bool]");
});
