# Before the first release

GaML runs end to end today -- lex, lay out, parse, elaborate, check, print a
type. What follows is the work between here and a version anyone else should
use. Three items, in a rough order, each with the reason it is on the list
rather than merely desirable -- then what has landed, and then the things
deliberately left off, which are limitations the design chose rather than
corners left unfinished.

The order is not a dependency chain, and necessity is not the same axis as cost.
(1) is the one the language is _for_, so it outranks the two below it even
though neither needs it.

## 1. Dependent arrows

The largest item, and the one that changes the calculus rather than extending
it. It sits above evaluation and recursion because it is what the rest is
scaffolding for: nothing above depends on it, and that is what makes it the
point rather than what makes it optional. An earlier draft of this list read
that backwards and put it last.

It reopens part of the variance work rather than building on it. Variance is a
property of arrow positions, and every walk over an arrow -- `#castFun`,
`#relateFun`, `#latticeFun`, and `noteField` -- assumes the result cannot
mention the parameter. A result that can is a case each of them has to grow.

The phantom warning is the other thing to revisit here. A type parameter no
constructor observes is warned about today as almost certainly a mistake, there
being no way to use one; dependent arrows are the feature that would give
phantoms a use.

## 2. Evaluation

Six term forms -- `Var`, `Abs`, `App`, `TypeApp`, `Let`, `Match` -- over values
that are closures and tagged constructor applications. Type application erases:
nothing about a type reaches runtime. `mod.ts` already hands back a `Result`, so
a value joins the type it currently returns alone.

**It needs a fuel counter from the start.** An earlier draft of this entry
argued the opposite -- `#checkLet` pushes the binder after checking the bound
term, so nothing is in its own scope, so no program can diverge and the
evaluator is total. The premise holds and the conclusion does not. Divergence is
reachable today, twice over:

    let r = ref!(fn (x: Bool) -> x)
    let f = fn (x: Bool) -> get!(r)(x)
    let tie = set!(r, f)
    f(True)

A cell holding a function that reads the cell is general recursion -- Landin's
knot -- and it needs no recursive datatype at all. Independently, a _negative_
recursive datatype gives the same thing: `| MkBad((Bad) -> Bad)` is a legal
field, so self-application types through it and `Ω` is writable. Both check
today. So the interpreter is an interpreter plus a fuel counter plus a story
about what a diverging playground tab does, whenever it is written, and (3) does
not change that.

Independent of (1), so it could come earlier still. The bundle targets a browser
playground, and a playground that prints a type and runs nothing is half a demo.

## 3. Recursive functions, and how far to infer them

Two halves, and they are not equally hard.

**Self-recursion with an annotation is small and locatable.** `#checkLet`'s
annotated branch already elaborates the annotation _before_ checking the bound
term, which is exactly the shape recursion needs -- so the change is pushing the
binder above that check rather than below it. It wants a `rec` marker to go with
it (there is no such keyword today), since making every annotated `let`
recursive would let `let f : T = ... f ...` silently capture its own name where
an author meant an outer one.

**Mutual recursion needs a group.** `LetItem`s fold right into nested `Let`s in
`parser.ts`, so each binding sees only the ones before it. A mutually recursive
group needs all of them in scope for all of the bodies, which is a different
node rather than a different fold.

**There is no open half, which an earlier draft got wrong.** It argued that a
recursive binding wants an EVar created at the binding, constrained by the whole
body and solved at the end -- a lifecycle `withEVars` does not have, and one
that would break the invariant the relation leans on when it records a bound
without asking whether it is allowed to. That would be true of `rec` as a
_binder_. It is not a fact about recursion, because recursion needs no binder:

    fix : [A, B](((A) -> B) -> (A) -> B) -> (A) -> B

`stdlib/rec/fix.ga` defines it -- the Z combinator over a negative recursive
datatype, which is legal here for the reasons under §2 -- and the whole datatype
half of the stdlib is written through it. `fix` is an ordinary polymorphic
callee at an ordinary application, so its type arguments are found by the
`withEVars` that already exists: `fix(fn (self: (Nat) -> (Nat) -> Nat) -> ...)`
infers `A` and `B` with neither written. Polymorphic recursion still needs an
annotation, being undecidable anywhere, and that annotation is the one on
`self`, which is the same one a `rec` binding would have wanted.

So `rec` is **sugar, not expressiveness**, and the case for it is ergonomics
alone: `self` is a worse name than the function's own, and spelling the whole
type in its annotation is a tax on the commonest thing anyone writes. Two things
follow. Its cost is the roadmap's original estimate -- move the `pushTermVar`
above the `check`, add a keyword -- and not a desugaring, which would need `Rec`
and `fix` seeded as builtins. And leaving it out makes (2) _simpler_: recursion
through `fix` is ordinary closures and ordinary tagged applications, where a
`rec` binding needs a closure whose environment contains itself.

## Landed

**Proper variance for datatypes.** Arguments are no longer invariant by fiat:
each datatype's parameters are inferred from its constructor fields, by a fixed
point over the whole declaration table, and every walk over a `TData` reads the
answer. Four limitations were the same one seen from four sides, and all four
are gone --

- `Cons(True, Nil())` infers `List[Bool]`, where `Nil()` used to need an
  annotation because nothing related `List[never]` to `List[Bool]`.
- Lifting `never` into a demanded `List[?]` has a least solution, so the cast
  neither chooses nor warns; the warning survives for an argument that really is
  invariant, and names the parameter it is about.
- Avoidance widens inside a covariant argument instead of taking the whole type
  down with it.
- An EVar occurring in a datatype argument is recorded at that argument's
  variance, so a call that would otherwise infer principally does.

The design is [variance.md](./variance.md); the round-by-round behaviour is
pinned by the inference tests at the foot of `elaborate.test.ts`.

**A separate invariant `Ref[]`.** Mutability is a builtin rather than something
declarable, and that was a consequence of the variance pass rather than an
independent wish: the walk enters each constructor field at `+1` because a field
is _projected_ by `match` and never assigned, and it reads field types rather
than operations, so it cannot see a write. Either mutability is a builtin, or
the inference is wrong about every datatype with a mutable field.

    ref! : [T](T) -> Ref[T]
    get! : [T](Ref[T]) -> T
    set! : [T](Ref[T], T) -> T

A cell is a type _former_, `TRef`, rather than a datatype the checker declares
for itself -- which is where this landed after trying it the other way, and the
attempt is what showed why. Almost nothing a datatype is would be true of it: it
has no constructors, nothing takes one apart, and its invariance comes from
`get!` and `set!`, which are terms rather than fields. Every one of those had to
be a flag or an exception on a `TData`; as its own kind they are all structural.
The invariance is a literal `0` in each walk, and `match` refuses it along with
everything else that is no datatype.

The _name_ is ordinary: a transparent alias for the former, seeded before the
program's own declarations -- which is exactly what an alias is, its body simply
being one this language has no syntax for. A keyword would have worked and was
tried; a name is better because it obeys whatever rule every other type name
obeys, so "already declared" and the arity message come from machinery that was
already there, and a later decision to make type names shadowable reaches this
one for free.

That last one found a latent bug on the way through. As a constructorless
datatype, the exhaustiveness analysis read an empty constructor set as an empty
_type_, so a wildcard arm over a cell was called unreachable and the match
answered `never` -- a false unreachability and an unsound type, on a value that
plainly exists.

The lexer takes a trailing `!` on any identifier and knows no list of builtins.
What reserves the spelling is that the parser refuses one at every position
where a name is _bound_, so a bang name can only ever be used -- and a use that
resolves to nothing is an ordinary unknown name, which is what a misspelt `st!`
should be told. The rule sits beside the one about `_`, both being ordinary
identifiers whose admitting positions the parser decides once.

## Non-goals for now

Recorded so that "not on the list" stays a decision rather than an oversight.
Each is a limitation the design chose, not a corner left unfinished.

- **Type aliases cannot be recursive.** They are transparent, so expansion would
  not terminate. Structural, not a bug -- datatypes are the recursive ones.
- **Pattern matching is one-level.** This is what keeps exhaustiveness a
  set-membership test rather than a coverage analysis.
- **Subtyping runs on fuel** and can answer "gave up" as well as yes or no. Full
  Fsub subtyping is undecidable, so some such limit is not optional; the size of
  it is a tuning question.
