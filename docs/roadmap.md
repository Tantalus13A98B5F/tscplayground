# Before the first release

GaML runs end to end today -- lex, lay out, parse, elaborate, check, print a
type. What follows is the work between here and a version anyone else should
use. Two items, in a rough order, each with the reason it is on the list rather
than merely desirable -- then what has landed, and then the things deliberately
left off, which are limitations the design chose rather than corners left
unfinished.

The order is not a dependency chain, and necessity is not the same axis as cost.
(1) is the one the language is _for_, so it outranks the one below it even
though that does not need it.

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

### What a self-referential signature costs

The wanted case is a `def` whose result type mentions the `def` -- a measure, or
a specification that reads its own argument. Three things follow, and the last
is a boundary rather than a task.

**The self-reference must be a level, never an embedded node.** A `Type` that
reached back into itself would not be a finite value, which is the same reason a
`TData` carries its declaration's parameters by reference and never its
constructors. So `def`'s push has to be two steps rather than one -- allocate
the binder, _then_ elaborate the signature in a scope that already holds it --
and it is worth building that way before this lands, since retrofitting it means
touching every `def` path. `typeToString` stops at the name for the same reason
a `TData` prints its name.

**Nothing may be reordered afterwards.** `Level` is an index into the context
and `lookup` reads `#entries[level]` directly, so popping a group and pushing it
back in a different order silently _mispoints_ every `FVar` already elaborated:
the size is unchanged, so `assertClosed` sees nothing wrong. This is what makes
the existing order load-bearing rather than incidental. Signatures are pushed in
source order and an unannotated `def` replaces its own entry at its own level,
so nothing ever moves.

**Two rules fall out of that order, and both are the standard ones.** A
signature may mention only an annotated `def` written earlier in the run --
Agda's forward-declaration rule, signatures being a sequence where bodies are a
group. And an unannotated `def` can appear in no signature at all, which is not
a restriction to lift: its type is inferred from a body that may mention the
very `def` whose signature is asking, so the dependency is circular at the level
of type _formation_.

Genuinely mutual signatures -- each mentioning the other -- are **induction-
recursion**, and out of scope. A first phase that pushes all the _names_ before
any signature (what `Declarations` already does for datatypes, which is why
`List` and `Tree` may name each other) does not reach it: elaborating
`Vec(foo(n))` needs `foo`'s result type to type the application, and a name is
not one. That phase is still worth having on its own -- it turns a forward
reference into "`foo` is declared below; its signature is not available here"
rather than `unknown name foo` -- and it is additive, so it can land whenever.

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
about what a diverging playground tab does, whenever it is written, and `def`
does not change that.

Independent of (1), so it could come earlier still. The bundle targets a browser
playground, and a playground that prints a type and runs nothing is half a demo.

## Landed

**Recursive and mutually recursive functions, as `def`.** A run of adjacent
`def`s is one scope: every member may name every other, so `even` and `odd` are
written the way anyone would write them and nothing is encoded. What `def` adds
to `let` is that scope and nothing else -- the parser folds its parameter lists
into the `Abs` and its result type into the `FunType` that becomes its
annotation, so a member reaching the checker is a `LetItem`.

Annotations are what buy the visibility, and the reason is the constraint solver
rather than taste. A signature the author wrote can be pushed before any body is
checked; a result type to be _inferred_ would need an EVar created at the
binding, constrained by the whole body and solved at the end, which is a
lifecycle `withEVars` does not have. So an annotated `def` is visible to its
whole group and an unannotated one falls back to being a `let`, visible once it
is checked and `unknown` inside its own body -- which is the honest statement
that nothing is known of it yet, so it may be passed on, may not be called, and
a recursive use is refused at the call. `unknown` and not `<bad>`: `badUnder`
takes the diagnostic that licenses it, and the report belongs at each use.

An earlier draft of this entry wanted a `rec` marker and a dependency graph.
Neither is here. `def` needs no marker, being a keyword already; and the graph
would only additionally order a non-recursive unannotated `def` ahead of a
sibling that calls it, which is a change that accepts strictly more and so can
land later without rewriting any of this.

`fix` is untouched and stays a library. `stdlib/rec/` now holds the same pair of
mutually recursive functions seven times: once as a `def` run, and six times
encoded -- Bekic's decomposition, a fixed point at a product, a tag,
continuation passing, and backpatched cells.

**Several parameter lists on one binder.** `fn [A](xs: List[A])[B](z: B)(op) ->`
is surface sugar the parser folds into nested `fn`s, so staging -- one batch of
type arguments per list, which is what lets `foldr(xs)(z)(op)` take a bare
lambda -- is sayable in one binder. There is still no multi-list function type,
and the type it gives is the curried one.

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
