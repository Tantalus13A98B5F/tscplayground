import { expect } from "@std/expect";
import { mkSource } from "../diagnostics/diagnostic.ts";
import { runSource } from "../mod.ts";
import { parseProgram } from "../syntax/parser.ts";
import { tokenize } from "../syntax/lexer.ts";
import { layout } from "../syntax/layout.ts";
import { evaluate, valueToString } from "./evaluate.ts";

/**
 * Run a program, as a `[value, ...messages]` tuple. Deliberately not checked
 * first: the messages a test asserts are whatever the whole pipeline said, and
 * several of these programs are ill-typed on purpose.
 */
function run(...lines: readonly string[]): [string, ...string[]] {
  const result = runSource(mkSource(lines.join("\n"), "test.ga"));
  return [
    result.value === undefined ? "<stuck>" : valueToString(result.value),
    ...result.diagnostics.map((d) => d.message),
  ];
}

/** The value alone, asserting nothing was reported by any phase. */
function valueOf(...lines: readonly string[]): string {
  const [value, ...messages] = run(...lines);
  expect(messages).toEqual([]);
  return value;
}

const BOOL = ["datatype Bool where", "  | True", "  | False"];
const NAT = ["datatype Nat where", "  | Z", "  | S(Nat)"];
const LIST = [
  "datatype List[A] where",
  "  | Nil()",
  "  | Cons(A, List[A])",
];

Deno.test("values are constructors, closures and cells", () => {
  expect(valueOf(...BOOL, "True")).toBe("True");
  expect(valueOf(...NAT, "S(S(Z))")).toBe("S(S(Z))");
  expect(valueOf(...BOOL, "fn (x: Bool) -> x")).toBe("<function>");
  // A cell prints as its address: one may hold a function that reads it.
  expect(valueOf(...BOOL, "ref!(True)")).toBe("<cell 0>");
  // A constructor is a function of its fields, so an unsaturated one is one.
  expect(valueOf(...NAT, "S")).toBe("<function S>");
});

Deno.test("application, let, and a def run that sees itself", () => {
  expect(valueOf(...BOOL, "let f = fn (x: Bool) -> x;", "f(False)"))
    .toBe("False");
  expect(
    valueOf(
      ...NAT,
      ...BOOL,
      "def even(n: Nat): Bool =",
      "  match n with",
      "  | Z -> True",
      "  | S(m) -> odd(m)",
      "def odd(n: Nat): Bool =",
      "  match n with",
      "  | Z -> False",
      "  | S(m) -> even(m)",
      "even(S(S(S(Z))))",
    ),
  ).toBe("False");
});

Deno.test("a def run is scoped as the checker scopes it", () => {
  // Annotated members are bound before any body runs, so they see the whole
  // run whatever the order. `even` is written above the `odd` it calls.
  expect(
    valueOf(
      ...NAT,
      ...BOOL,
      "def even(n: Nat): Bool = match n with",
      "| Z -> True",
      "| S(m) -> odd(m)",
      "def odd(n: Nat): Bool = match n with",
      "| Z -> False",
      "| S(m) -> even(m)",
      "even(S(Z))",
    ),
  ).toBe("False");

  // An unannotated member falls back to being a `let`, so a *later*
  // unannotated sibling is a name outside the run -- the outer `k` here, and
  // not the one below. Binding the whole run at once would resolve it to the
  // group and quietly mean something else than the checker means.
  expect(
    valueOf(
      ...BOOL,
      "let k = fn (x: Bool) -> True;",
      "def f(x: Bool) = k(x)",
      "def k(x: Bool) = False",
      "f(False)",
    ),
  ).toBe("True");

  // And it sees itself, which is what makes a recursive use resolve at all: to
  // a hole, filled before anything can call it. The checker types that hole
  // `unknown` and refuses the call, so this is a program that runs and does not
  // check -- which is the whole reason the run is not gated on the check.
  expect(
    run(
      ...NAT,
      "def down(n: Nat) = match n with",
      "| Z -> Z",
      "| S(m) -> down(m)",
      "down(S(S(Z)))",
    ),
  ).toEqual(["Z", "unknown is not a function"]);
});

Deno.test("type application erases, so a type it names need not exist", () => {
  // Nothing about a type reaches here. The check still reports the name; the
  // run is untroubled by it, which is the property being pinned.
  const [value, ...messages] = run(...LIST, "Nil[Nope]()");
  expect(value).toBe("Nil()");
  expect(messages).toEqual(["unknown type Nope"]);
});

Deno.test("a def's parameter needs no type at runtime", () => {
  // `MissingParamType` is a type, and no type is read here, so the omission
  // that the checker reports costs the run nothing.
  const [value, ...messages] = run(...BOOL, "def f(x): Bool = x", "f(True)");
  expect(value).toBe("True");
  expect(messages.length).toBe(1);
});

Deno.test("an ill-typed program runs until it is stuck, and says where", () => {
  // Each of these is a shape the checker would have guaranteed. With no such
  // guarantee they are the whole error vocabulary: a value arrived where a
  // different shape was needed.
  const stuck = (...lines: readonly string[]) => {
    const [value, ...messages] = run(...lines);
    expect(value).toBe("<stuck>");
    return messages.at(-1);
  };

  expect(stuck(...BOOL, "True(False)")).toBe(
    "expected a function, found a Bool",
  );
  expect(stuck(...BOOL, "let f = fn (x: Bool) -> x;", "f(True, False)"))
    .toBe("expected 1 arguments, found 2");
  expect(
    stuck(
      ...BOOL,
      "let f = fn (x: Bool) -> x;",
      "match f with",
      "| True -> True",
    ),
  ).toBe("expected something to match on, found a function");
  expect(stuck(...BOOL, ...NAT, "match True with", "| Z -> True"))
    .toBe("Z is not a constructor of Bool");
  expect(stuck(...NAT, "match S(Z) with", "| Z -> Z"))
    .toBe("no arm matches S");
  expect(stuck(...NAT, "match S(Z) with", "| Z -> Z", "| S(m, k) -> m"))
    .toBe("S has 1 fields, bound 2");
  expect(stuck(...BOOL, "get!(True)")).toBe("expected a cell, found a Bool");
  expect(stuck(...BOOL, "ref!(True)(True)"))
    .toBe("expected a function, found a cell");
  // A constructor is a function of its fields, so its arity is checked where
  // every other function's is -- and it names itself, having a name to give.
  expect(stuck(...NAT, "S(Z, Z)")).toBe("S expected 1 arguments, found 2");
  expect(stuck("nope")).toBe("unknown name nope");
});

Deno.test("only the first stuck term is reported, evaluation being a trace", () => {
  // The second application is as wrong as the first and is never reached, so
  // reporting it would be reporting an order rather than a mistake.
  const [value, ...messages] = run(
    ...BOOL,
    "let f = fn (x: Bool) -> True(x);",
    "f(f(True))",
  );
  expect(value).toBe("<stuck>");
  expect(messages.filter((m) => m.startsWith("expected a function")).length)
    .toBe(1);
});

Deno.test("divergence is answered by fuel, not by hanging", () => {
  // Landin's knot: a cell holding a function that reads the cell is general
  // recursion, and this program checks.
  const [value, ...messages] = run(
    ...BOOL,
    "let r = ref!(fn (x: Bool) -> x);",
    "let f = fn (x: Bool) -> get!(r)(x);",
    "let tie = set!(r, f);",
    "f(True)",
  );
  expect(value).toBe("<stuck>");
  expect(messages.at(-1)).toMatch(
    /^evaluation did not finish within \d+ steps$/,
  );
});

Deno.test("the forms a type declaration leaves at runtime", () => {
  // An alias declares no constructor, so it contributes nothing here and is
  // skipped rather than handled.
  expect(valueOf("typedef Also[A] = (A) -> A", ...BOOL, "True")).toBe("True");

  // `| Off()` is a function of no arguments where `| On` is a value, which is
  // the distinction `CtorDecl` carries, and printing is where it shows.
  const FLAG = ["datatype Flag where", "  | On", "  | Off()"];
  expect(valueOf(...FLAG, "On")).toBe("On");
  expect(valueOf(...FLAG, "Off()")).toBe("Off()");
  expect(valueOf(...FLAG, "Off")).toBe("<function Off>");
  // Neither form is a distinction a pattern can see, both having no fields.
  expect(valueOf(...FLAG, "match Off() with", "| On -> On", "| Off -> On"))
    .toBe("On");
});

Deno.test("a wildcard pattern matches, and a nearer binding shadows", () => {
  expect(valueOf(...NAT, "match S(Z) with", "| Z -> Z", "| _ -> S(S(Z))"))
    .toBe("S(S(Z))");
  // `_` binds a scope like any other name, and nothing can look one up.
  expect(valueOf(...BOOL, "let f = fn (_: Bool) -> True;", "f(False)"))
    .toBe("True");
  expect(
    valueOf(...BOOL, "let x = True;", "let x = False;", "x"),
  ).toBe("False");
});

Deno.test("set! answers the value written, so a write is an expression", () => {
  expect(
    valueOf(
      ...BOOL,
      "let c = ref!(True);",
      "let written = set!(c, False);",
      "get!(c)",
    ),
  ).toBe("False");
  // Two cells are two addresses, which is what a heap of them buys.
  expect(valueOf(...BOOL, "let a = ref!(True);", "ref!(False)"))
    .toBe("<cell 1>");
});

Deno.test("a stack the host cannot grow is not reported as fuel", () => {
  // Reachable only above the budget, which is set below the ceiling on
  // purpose. The two have different fixes, so they have different words.
  const source = mkSource(
    [
      ...BOOL,
      "let r = ref!(fn (x: Bool) -> x);",
      "let f = fn (x: Bool) -> get!(r)(x);",
      "let tie = set!(r, f);",
      "f(True)",
    ].join("\n"),
    "deep.ga",
  );
  const tokens = layout(tokenize(source).value!).value!;
  const result = evaluate(parseProgram(tokens).value!, 1_000_000);
  expect(result.value).toBeUndefined();
  expect(result.diagnostics.map((d) => d.message))
    .toEqual(["evaluation nested too deeply"]);
});

Deno.test("a qualified constructor runs to the one it names", () => {
  const LIST = ["datatype List where", "  | Nil", "  | Cons(Bool, List)"];
  const SNOC = ["datatype Snoc where", "  | Cons(Bool)"];

  // The plain name is the last declaration of it, in both phases; the
  // qualified one reaches the constructor a later `Cons` shadowed.
  expect(valueOf(...BOOL, ...LIST, ...SNOC, "Cons(True)")).toBe("Cons(True)");
  expect(valueOf(...BOOL, ...LIST, ...SNOC, "List.Cons(True, Nil)"))
    .toBe("Cons(True, Nil)");

  // And the value it built is the one its own datatype takes apart, which is
  // what a bare name could not have promised.
  expect(valueOf(
    ...BOOL,
    ...LIST,
    ...SNOC,
    "match List.Cons(True, Nil) with",
    "  | Nil -> False",
    "  | Cons(h, t) -> h",
  )).toBe("True");
});

/** Monomorphic, so a pattern and a super constructor read without type arguments. */
const BOOLS = ["datatype Bools where", "  | Nil", "  | Cons(Bool, Bools)"];
/** Every value of it is a `Bools`, and says which one. */
const NONEMPTY = [
  "datatype NonEmpty <: Bools where",
  "  | One(x: Bool)            -> Cons(x, Nil)",
  "  | More(x: Bool, r: Bools) -> Cons(x, r)",
];

Deno.test("a value carries what it presents as, matched through", () => {
  // The value is its own constructor; the image is beside it, not instead.
  expect(valueOf(...BOOL, ...BOOLS, ...NONEMPTY, "One(True)")).toBe(
    "One(True)",
  );
  expect(valueOf(
    ...BOOL,
    ...BOOLS,
    ...NONEMPTY,
    "match One(True) with | One(x) -> x | More(x, r) -> x",
  )).toBe("True");

  // Which datatype a match takes apart is the scrutinee's own, so viewing one
  // as its super type is said and not guessed -- there is no downcast, and an
  // annotation is the whole of what saying it costs.
  expect(valueOf(
    ...BOOL,
    ...BOOLS,
    ...NONEMPTY,
    "let xs : Bools = One(True);",
    "match xs with | Nil -> False | Cons(h, t) -> h",
  )).toBe("True");

  // And the tail the super constructor built is the one it named.
  expect(valueOf(
    ...BOOL,
    ...BOOLS,
    ...NONEMPTY,
    "let xs : Bools = More(False, Cons(True, Nil));",
    "match xs with | Nil -> Nil | Cons(h, t) -> t",
  )).toBe("Cons(True, Nil)");
});

Deno.test("the super constructor runs once, at construction", () => {
  // A `ref!` in a super constructor allocates when the value is made and never again,
  // so two views of one value read one cell. Lazily it would be two.
  expect(valueOf(
    ...BOOL,
    "datatype Box where",
    "  | MkBox(Ref[Bool])",
    "datatype Flag <: Box where",
    "  | On() -> MkBox(ref!(True))",
    "let f : Box = On();",
    "let written = (match f with | MkBox(c) -> set!(c, False));",
    "match f with | MkBox(c) -> get!(c)",
  )).toBe("False");
});

Deno.test("a chain is built whole, and walked whole", () => {
  expect(valueOf(
    ...BOOL,
    ...BOOLS,
    ...NONEMPTY,
    "datatype Single <: NonEmpty where",
    "  | Just(x: Bool) -> One(x)",
    "let xs : Bools = Just(True);",
    "match xs with | Cons(h, t) -> h | Nil -> False",
  )).toBe("True");
});

Deno.test("a pattern no view admits is stuck, naming the value's own", () => {
  expect(
    run(...BOOL, ...BOOLS, ...NONEMPTY, "match One(True) with | Z -> True")[1],
  ).toBe("Z is not a constructor of NonEmpty");
});

Deno.test("a super constructor may branch, and each tail is pinned on its own", () => {
  const run = (...lines: readonly string[]) =>
    valueOf(
      ...BOOL,
      ...BOOLS,
      "datatype Maybe <: Bools where",
      "  | Keep(b: Bool) ->",
      "      match b with",
      "      | True -> Cons(b, Nil)",
      "      | False -> Nil",
      ...lines,
    );
  // The value stays a `Keep` -- an annotation is a view and not a conversion
  // -- so which tail ran is read through a match on the super type.
  const kept = (b: string) =>
    run(
      `let xs : Bools = Keep(${b});`,
      "match xs with | Nil -> False | Cons(h, t) -> h",
    );
  expect(kept("True")).toBe("True");
  expect(kept("False")).toBe("False");
});

Deno.test("a tail is not reached by a shadowing let", () => {
  // `Cons` in a tail was rewritten to its qualified form before any scope
  // existed, so the `let` reaches the arguments and never the head.
  expect(valueOf(
    ...BOOL,
    ...BOOLS,
    "datatype One <: Bools where",
    "  | Mk(x: Bool) ->",
    "      let Cons = True;",
    "      Cons(x, Nil)",
    "let xs : Bools = Mk(True);",
    "match xs with | Nil -> False | Cons(h, t) -> h",
  )).toBe("True");
});

Deno.test("two datatypes in one chain may spell a constructor the same", () => {
  // `Top.Same` and `Mid.Same` differ in arity, and a `Leaf` presents as both.
  // Nothing untyped tells them apart; the datatype the checker recorded does.
  const CHAIN = [
    "datatype Top where",
    "  | Same(Bool, Bool)",
    "datatype Mid <: Top where",
    "  | Same(b: Bool) -> Same(b, False)",
    "datatype Leaf <: Mid where",
    "  | L(b: Bool) -> Same(b)",
  ];
  expect(valueOf(
    ...BOOL,
    ...CHAIN,
    "let x : Top = L(True);",
    "match x with | Same(p, q) -> q",
  )).toBe("False");
  expect(valueOf(
    ...BOOL,
    ...CHAIN,
    "let x : Mid = L(True);",
    "match x with | Same(p) -> p",
  )).toBe("True");

  // Written `as`, and it must agree with what the scrutinee is.
  expect(valueOf(
    ...BOOL,
    ...CHAIN,
    "let x : Top = L(True);",
    "match x as Top with | Same(p, q) -> p",
  )).toBe("True");
  expect(
    run(
      ...BOOL,
      ...CHAIN,
      "let x : Top = L(True);",
      "match x as Mid with | Same(p, q) -> p",
    )[1],
  ).toBe("these patterns are matched against Top, not Mid");
});
