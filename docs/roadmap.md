# Before the first release

GaML runs end to end today -- lex, lay out, parse, elaborate, check, print a
type. What follows is the work between here and a version anyone else should
use. Six items, in a rough order, each with the reason it is on the list rather
than merely desirable -- then the things deliberately left off, which are
limitations the design chose rather than corners left unfinished.

The order is not a dependency chain, and necessity is not the same axis as cost.
(1) is first because four separate limitations turn out to be it. (4) is the one
the language is _for_, so it outranks the two below it even though neither needs
it. (5) sits above (6) only because it gets measurably harder once (6) lands.

## 1. Proper variance for datatypes

A datatype's arguments are invariant: `#cast` passes a literal `0` per argument,
and `#subtype`, `#eqtype`, `#join` and `#meet` all reach for `#eqtypeArgs`. This
is first because four separate limitations are the same limitation seen from
different sides:

- `Nil()` needs an annotation where `Cons(True, Nil())` should do, because
  nothing relates `List[never]` to `List[Bool]`.
- Lifting `never` into a demanded `List[?]` has no least solution, so the cast
  chooses an argument and warns about having chosen.
- Avoidance cannot widen inside a datatype argument, so a whole type collapses
  where one part could not be avoided.
- `solveEVar` marks an occurrence inside a datatype argument as both covariant
  and contravariant, which is what forces the invariance warning on calls that
  would otherwise infer principally.

Inferred, not declared, and the design is written up in
[variance.md](./variance.md): the lattice, the walk, the fixed point and its
stopping criterion, worked examples with round counts, and what gets reported.

## 2. A separate invariant `Ref[]`

Mutability arrives as a builtin type constructor rather than as something
declarable, and this is a consequence of (1) rather than an independent wish.
The variance walk enters each constructor field at `+1` because a field is
_projected_ by `match` and never assigned. A mutable field would break that, and
the walk cannot see assignment -- it reads field types, not operations. So
either mutability is a builtin whose invariance is stipulated, or the variance
inference is wrong about every datatype that has a mutable field.

Stipulating it is the smaller thing: `Ref` is invariant by fiat, which is
already what the checker does for every datatype today, so nothing in the
relation has to learn a new case.

## 3. Nullary constructors in the surface syntax

The checker already draws the line -- a nullary constructor of a _monomorphic_
datatype is a value, so `True` is a `Bool` and `True()` is applying a
non-function, while `Nil` still has a type argument to fix and is written
`Nil[Bool]()`. What is missing is that a _declaration_ does not show which one
it is producing. The proposal is to make the declaration syntax say so: a
monomorphic paramless constructor declared as a name, a polymorphic one as a
method.

Presentational rather than semantic, which is why it is third. It is on the list
because the current rule is discoverable only by trying both.

## 4. Dependent arrows

The largest item, and the one that changes the calculus rather than extending
it. It sits above evaluation and recursion because it is what the rest is
scaffolding for: nothing above depends on it, and that is what makes it the
point rather than what makes it optional. An earlier draft of this list read
that backwards and put it last.

It also interacts with (1) rather than following it. Variance is a property of
arrow positions, and every walk over an arrow -- `#castFun`, `#relateFun`,
`#latticeFun` -- assumes the result cannot mention the parameter. A result that
can is a case each of them has to grow, so some of (1) will be revisited here.
That is an argument for knowing the shape of this item early, not for deferring
variance: the four limitations (1) removes are what make the language usable
enough to experiment in.

Worth noting against (1) in the other direction: a phantom type parameter -- one
no constructor field mentions -- is warned about as almost certainly a mistake,
since there is no way to use one. Dependent arrows are the feature that would
give phantoms a use, so that warning is the first thing this item revisits.

## 5. Evaluation

Six term forms -- `Var`, `Abs`, `App`, `TypeApp`, `Let`, `Match` -- over values
that are closures and tagged constructor applications. Type application erases:
nothing about a type reaches runtime. `mod.ts` already hands back a `Result`, so
a value joins the type it currently returns alone.

It is small _because_ of what is not here yet. `#checkLet` pushes the binder
after checking the bound term, so nothing is in its own scope and no program can
diverge -- the evaluator is total, needs no step limit, and cannot be wrong
about a case that never arises. That stops being true the moment (6) lands,
which is the argument for doing this one first: written now it is an
interpreter, written later it is an interpreter plus a fuel counter plus a story
about what a diverging playground tab does.

Independent of (1) through (4), so it could come earlier still. The bundle
targets a browser playground, and a playground that prints a type and runs
nothing is half a demo.

## 6. Recursive functions, and how far to infer them

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

**Inferring the type is the open half**, and the fuzziness has a location worth
naming: this checker has no global unification, on purpose. EVars arise from one
place only -- instantiating a polymorphic callee at an application -- and are
created, constrained and solved inside a single `withEVars`, with nothing
outside ever holding a type that names one. A recursive binding wants an EVar
created at the binding, constrained by the whole body, and solved at the end: a
different lifecycle, and one that breaks the invariant the relation leans on
when it records a bound without asking whether it is allowed to. Polymorphic
recursion is undecidable even in Hindley-Milner, so some annotation is required
regardless.

So the scoping is: annotation-required recursion is a real feature and can land
on its own. Inferring it is a separate question, and "not in the first release"
is an acceptable answer to it.

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
