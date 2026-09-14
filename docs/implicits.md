# Implicits, and the solver they need

A neighbours note, split out of `docs/clti.md` because it outgrew a subsection.
Nothing here is implemented or planned; it is what typeclass-style resolution
would cost, and which of our invariants it would spend.

The short of it: three things `subtype.ts` relies on -- an append-only
constraint store, batches that never overlap, and a compatibility test that
knows no scope -- are all affordable only because nothing here resolves an
argument by search. Scala pays for all three. Haskell pays for none, by
declining a case Scala accepts. The last section is why our type language makes
that decline nearly free.

## What search costs

**Search is a constraint source, not a lookup.** The obvious discipline -- solve
the batch, then resolve the implicits against the solutions -- is not available,
because a given can determine a type argument that nothing else mentions:

    trait Factory[A]:  def make: A
    given intFactory: Factory[Int]
    def create[A](using f: Factory[A]): A = f.make

    val n = create              -- A = Int, from the search and nothing else

There is no explicit list here and no expected type; `?A` is fixed by which
given was found. Solving first would infer `never` and then fail to find a
`Factory[never]`. So the batch is _live_ during the search, and everything below
follows from that.

**A candidate writes before it fails, so the store needs rollback.**

    given listOrd[A](using Ordering[A]): Ordering[List[A]]

Searching `Ordering[?X]` with `?X` open, `listOrd` matches at the head and
records `?X := List[?A']` -- then its own nested search for `Ordering[?A']`
finds nothing. The candidate is dead and has already written to a variable the
next candidate will be tried against. So most of what a Scala constraint store
sees is speculative and discarded.

Dotty pays for it by making the store a forkable value rather than a mutation:
`TyperState` owns a `Constraint`, `ctx.test` runs a typing against a child
state, and only a winner is committed upward. Overload resolution, SAM
conversion and `viewExists` are all spent out of that one mechanism. Our
`#constrain` appends and never retracts, and `withEVars` solves once the last
constraint is in -- which is why the file header can say no operation ever has
to be undone. Speculation was already ruled out once, in `docs/clti.md`'s
recursion note; this is the same absence, and it is deliberate both times.

**Instantiation timing stops being free.** Search wants a variable as determined
as it can get -- `Ordering[?A]` with `?A` wholly unconstrained matches every
`Ordering` in scope, and the answer is ambiguity rather than a type -- while the
explicit arguments want it still open:

    def f[A](x: A, y: A)(using Show[A]): String
    f(1, "s")

Solve `?A` after `x` and it is `Int`, and `y` fails against a variable already
decided; the join of both arguments is the only honest answer. So the search
must run after the whole explicit list and before the result is used -- as late
as possible while the batch is still open, which is a narrower window than
either end of it. That is why `using` is a _trailing clause_: it is a later
parameter list, and it is later for our reason -- a list is solved before the
next one is checked, the way `foldLeft(z)(op)` stages its own. Dotty
additionally needs `interpolateTypeVars` to say when a variable dies, `IfBottom`
to say what an unconstrained one reads as at that moment, and
`necessaryConstraintsOnly` for eligibility tests, so that a candidate is neither
admitted nor rejected on the strength of a constraint only one speculative
branch would have justified. Our answer to all three is structural: batches
never overlap, so "when to solve" is "at the end of this argument list" and no
consumer exists that could read a variable early.

**Compatibility stops being a relation on types.** With conversions in scope,
`A` acceptable where `B` is wanted is no longer `isSubtype(A, B)`:

    given intToStr: Conversion[Int, String]
    def g(s: String): Unit
    g(1)                        -- compiles here, not in the file next door

So the test is scope-dependent, and non-transitive on purpose (chained
conversions are refused, or the closure would swallow everything). Our `Verdict`
has a third answer, but it is "the tank ran dry" -- still a fact about the pair
and the budget. That is what lets `subtype.ts` know no scope beyond levels.

**Two undecidabilities, not one.** Given

    given loop[A](using Ordering[List[A]]): Ordering[A]

a search for `Ordering[Int]` asks for `Ordering[List[Int]]`, then
`Ordering[List[List[Int]]]`, forever. Implicit search plus type members is a
small logic programming language, so it needs a termination criterion of its own
-- dotty's divergence checker, on the covering-set/stable-prefix condition
inherited from Haskell's instance rules. That is a _second_ guard, unrelated to
the subtyping fuel counter, which dotty also has and for our reason. We have one
because we have one source of non-termination.

**What it buys, and what we buy instead.** The requirement `Ordering[A]` sits
beside the type, so it can be satisfied retroactively: a `given Ordering[Foo]`
declared anywhere makes an old `Foo` sortable without touching it. A bound puts
the requirement _in_ the type -- `[A <: Ord]` -- which loses that entirely and
gains that there is nothing new to solve: a declared bound is an upper
constraint like any other, and `solveEVar` already checks `lower <: upper`
against it. Same expressive job, one of them free to the machinery we have.

Which names the invariant that would break first if typeclasses ever landed.
`withEVars` says nothing outside it holds a type naming an EVar, and an implicit
argument is resolved from inside a search against a batch that is still open.
The disciplined form -- solve, then resolve against the solutions -- is the same
one offered to the TS rounds idea in `docs/clti.md`, and it keeps the invariant
in both cases by being strictly weaker: there, a lambda that needs its
parameter's structure; here, `create`. Scala can decline it and we cannot, which
is the whole of the difference.

## Selection without subtyping

Where matching and subtype-search come apart -- and why, for us, they barely do.

    given animalShow: Show[Animal]      -- Show contravariant in A
    summon[Show[Dog]]

Haskell cannot ask the question: no subtyping, so selection is matching on the
head and `showAnimal` is simply not a candidate. Scala answers yes --
`Show[Animal] <: Show[Dog]`, so it is not merely a candidate but the only one --
and that is the whole reason `isAsSpecific` reduces specificity to applicability
rather than to the substitution-instance order. Both of the classic rankings,
concrete over generic and `F[A, A]` over `F[A, B]`, are that substitution order;
Scala reaches them through subtyping, which agrees there and diverges here.

**We cannot write the pair.** Datatypes are nominal with no declaration form
relating two of them: `#relateData` demands `s.name === t.name`, and there is
nothing to unfold and no third datatype to appeal to. So between two ground
closed types the relation is nontrivial _only_ through the extremes -- distinct
heads relate only if one is `never`, `unknown` or `<bad>` -- and nobody writes a
given head at an extreme. Matching and subtype-search coincide on a ground goal,
which means the design decision the section above said had to be stated up front
is not a decision: the type language already made it.

**The one place it would want a hierarchy is already spent elsewhere.**
Constructor refinement -- what a value can still be, having reached this arm --
is the natural home for `Dog <: Animal`, and Scala spells it that way, a sealed
trait with case classes under it. We keep it out of `Type` entirely: patterns
are one level, so the question is set membership over the remaining
constructors, decided in `#checkMatch` and never reaching `subtype.ts`. Right
behaviour, other machinery.

**What survives is the bound.** A declared bound is the one leaf that relates
two things spelled differently, so it is the one case where a subtype-aware
selection would still beat matching:

    fn [X <: Bool](x: X) -> ...     -- goal `Show[X]`, candidate `Show[Bool]`

Contravariantly, `Show[Bool] <: Show[X]` because `X <: Bool`, so Scala
discharges this and matching does not. Which closes the circle: the only place
selection would want subtyping is the place where the bound is already the
answer, and a bound costs the solver nothing -- it is an upper constraint like
any other.

## Modes, and what they do not fix

Lean's `outParam` and Rocq's `Hint Mode` are the other way to make search
tractable: annotate each class parameter as input or output, and refuse to
commit to a candidate until every input is known. `Hint Mode Ord +` says a goal
`Ord ?x` with `?x` still open is not attempted at all -- it is postponed, or it
fails -- so the ambiguity that forced dotty's `necessaryConstraintsOnly` never
arises, and `Factory[?A]` above is simply rejected rather than resolved by
whichever given happened to match.

This is a real discipline and it is cheaper than speculation, but it does not
reach the case this file ends on. A mode constrains a _metavariable_: what it
regulates is whether the elaborator may instantiate an as-yet-unknown argument
during search. In

    fn [X <: Bool](x: X) -> ...     -- goal `Show[X]`, candidate `Show[Bool]`

`X` is not a metavariable. It is rigid -- a bound `FVar` at a level, as fixed as
`Bool` is -- so the goal `Show[X]` is fully input-mode already and every mode
discipline admits it. The question is then what a mode discipline never asks:
whether `Show[Bool]` is _acceptable_ at `Show[X]`, which is the subtyping fact
`X <: Bool` under contravariance, and neither Lean nor Rocq has a relation to
appeal to there. They match up to unification, so they answer no.

Which is the same conclusion from the other side. Modes settle _when_ to search
and leave selection to matching; the bound settles selection and costs the
solver nothing. They are orthogonal, and only one of them is a question we have.
