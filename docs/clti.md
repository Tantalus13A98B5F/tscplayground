# Colored Local Type Inference

Both LTI and CLTI require that EVars do not depend on each other in constraints.
In fact, LTI does not even have EVars in the original paper: constraint
generation relates two _complete_ types, which is what keeps the problem
dependency-free and decidable.

We broke that. Arguments are checked against `openMany(param, evars)` -- a
parameter type holding EVars -- so an argument's own checking writes
constraints, and a nested application can produce one naming a sibling.
`#constrain`'s refusal is the scar tissue, not the disease.

So how does CLTI push a partial type inward? Not with inference variables. With
missing parts.

## What this buys

If constraints are only ever generated between a complete synthesized type and a
parameter type over abstract variables, then an EVar appears in no type that
flows anywhere -- only in the two the checker relates on purpose. These all go:

- the `EVar` case of `Type`. A variable is an `FVar` naming a level, and the
  entry there says whether it is rigid or still being inferred
- `EVarMode`, and the whole `probe`/`collect` split -- `probe` exists only
  because `#join`/`#meet` walk types that might hold an EVar and must not
  record; the lattice is never handed one, so there is nothing to stop
- every `Context.apply` but the one that carries a batch's answers out

What survives, and should: `#assertUnsolved`, `expose`'s refusal to promote an
EVar, the refusal of a sibling and `noteReported`. Constraint collection is
where an EVar is still real, and those are what it needs.

That deletion is the point. The rest is how to get there.

## 1. `TMissing`, and a type that says whether one is possible

Add `TMissing` to `Type` (not `TypeNode` -- this is not something anyone
writes). Then parameterize: `TypeMaybe<M>`, where `TMissing` carries a field of
type `M`, so `TypeMaybe<never>` cannot construct one.

    type Type = TypeMaybe<never>          // complete
    type TypePattern = TypeMaybe<number>  // may have missing parts

`readonly` arrays are covariant, so a complete type flows into a pattern
position with no coercion -- which is the direction that matters, since
subtyping and constraint solving take complete types only.

The reverse does not narrow. Excluding `kind === "TMissing"` does not change the
type argument, so "walked it, found none, treat it as complete" is a walk that
has to fill what it finds -- and filling a missing part is what a cast does. So
there is no separate `assertComplete`: `castComplete` is the one hole-
elimination walk, and a second one cannot exist without the two disagreeing
about what was invented.

## 2. Matching, and the two casts

Everything below depends on one predicate, so it is written down first: opening,
`isClosed`, and avoidance already have to agree about what a position is, and
these will too.

**A complete `S` matches a pattern `P`** when

- `P` is `TMissing`: always
- `P` is a leaf -- `unknown`, `never`, `<bad>`, `BVar`, `FVar`: `alphaEq(S, P)`
- `P` is `TFun`: `S` is one, arities agree, and parameters, result, and bounds
  match pointwise
- `P` is `TData`: `S` is one, same name and arity, arguments match pointwise

Matching is a shape test and knows nothing of variance. Note that a complete
pattern matches only what is alpha-equal to it, so `check(e, P)` on a complete
`P` returns `P` -- exactly what `check` does today -- and `TMissing` constrains
nothing, so `infer(e)` is `check(e, TMissing)`. The two modes are one procedure,
parameterized by how much is known.

Variance lives in the casts, which find the nearest matching type in a
direction. They are total -- like subtyping, which reports rather than fails --
and answer with a verdict beside the type. They collect constraints like the
relation does -- a cast is something a checking rule _asks_, and what it learns
on the way is exactly what the relation it replaces used to record.

    downcast(T, P)  the greatest S <: T matching P
    upcast(T, P)    the least    S :> T matching P

- `P` missing: `T`. Nothing is demanded, so nothing moves.
- `T` is `<bad>`: `<bad>`. A report already stands.
- `T` is `unknown` going down, or `never` going up: build from `P` alone,
  filling each missing part with the extreme for its variance. This is the
  operation the note wanted separately for result patterns -- it is not
  separate, it is this one against top.
- both `TFun`: recurse, flipping direction at the parameters and at the bounds.
  Same flip as `#avoid`.
- both `TData`, same name: each argument recurses at its own parameter's
  variance composed with the direction. (Written before variance was inferred,
  when the rule was that every argument is invariant -- a missing one takes
  `T`'s and a written one must be `#equiv` to it.)
- `T` is an `FVar`: going up it stands aside for its bound and the cast goes on
  there, since the bound is a supertype. Going down it may not -- nothing says
  the bound sits under it -- so unless `P` is missing or names that same
  variable, fail. This is the asymmetry `#join`/`#meet` already document.
- otherwise: fail.

So these are `#join`/`#meet` generalized to a partial second argument, and
belong beside them. They cannot simply _be_ them: join and meet are total and
fall back to `unknown`/`never`, while a cast must be able to fail.

## 3. Abstraction

A parameter's type is complete before the body is checked -- no missing part, no
EVar. This is the invariant the whole design rests on.

It comes from the pattern, from the annotation, or from their merge, which is
filling the pattern's missing parts from the annotation and then checking the
annotation is wide enough, as `#bindParam` already does for the complete case. A
part still missing after that is the error, reported at the parameter.

**This costs us something, and we are taking the cost.** Today a bare lambda in
an argument list binds to the callee's EVar directly and works as long as the
body never needs the parameter's _structure_. That was never a rule an author
could predict -- the same program one `match` away stops working -- so what goes
is a coincidence, not a capability. Staging over two parameter lists, the Scala
`foldLeft(z)(op)` shape, is the idiom that survives, and the tests confirm it:
everything staged or annotated is unaffected.

Order-independence survives intact, and gets cleaner: one pass, nothing decided
until the whole list is in.

## 4. Application

1. Infer the callee, expose it to a function type.
2. Replace its type variables with `TMissing`, giving a parameter pattern per
   argument.
3. Check each argument against its pattern. Each comes back complete.
4. Relate those complete types against the parameter types over the abstract
   variables, which is where constraints are collected -- both sides ground,
   which is the whole point.
5. The result type against the expected pattern, likewise, using the cast of top
   against the pattern. This is what lets `Nil()` know what it is empty of, and
   it is why an application must accept a pattern rather than a type.
6. Select by where the variable occurs, unchanged.

Step 3 walks terms and step 4 walks types, so there is no re-checking.

## 5. `match`

Check each arm against the pattern, join the complete results, then
`upcast(join, P)`. No prefilling: filling a missing part in an invariant
position needs a witness, and only the arms have one.

Sound because the join is above every arm and the cast only goes further up;
least because the cast is; and its partiality is the error -- the arms agree on
nothing that matches -- reported where it happens instead of the silent
`unknown` we give today.

It degrades along the axis we already know about. Arms `List[Bool]` and
`List[Int]` against `List[?]` joined to `unknown` under invariance, and nothing
above `unknown` is a `List`, so it failed. Datatype arguments carry variance
now, so the join is `List[Bool ⊔ Int]` -- top, for want of a union, but a `List`
of it -- and the cast is a no-op. `match` needs no special case for a missing
part; it inherits whatever the join can do.

## Plan

- **0. Size the damage.** Done. Two genuine regressions across three tests --
  `f(fn (x) -> id(x), True)` and `both(True, fn (y) -> y)` in both orders.
  Everything else is unchanged, is a better message on an already-failing
  program, or tests the sibling refusal and disappears with it.
- **1. Write down matching.** Done, above.
- **2. The type parameter, as a no-op.** Introduce `TypeMaybe<M>` and both
  aliases, thread them through every signature, and do _not_ add `TMissing` yet.
  Pure retype: suite unchanged, differential harness identical. Landing the
  mechanical churn on its own is what keeps the next diffs readable.
- **3. The casts.** Done. `TMissing`, and `upcast`/`downcast`/`exactcast` beside
  `#join`/`#meet`, unit-tested directly.
- **4. Merge `check` and `infer`.** Done. One procedure over a pattern, with
  `infer(e) = check(e, TMissing)` and the answer being the type the term has
  rather than the pattern it was asked for. Abstraction is one rule,
  `#abstract`, taking each part from the pattern where it has one; a parameter
  with neither annotation nor supplied type is the error. `match` joins its arms
  and coerces after, which is §5 falling out rather than being written. The
  suite is unchanged -- the two regressions step 0 measured belong to step 5,
  since an argument's pattern is still an EVar-bearing complete type. What did
  change is that an annotation wider than the pattern is now merged rather than
  refused, the merge being a downcast: `fn (x: unknown) -> x` checks at
  `(Bool) -> Bool`, which it has.
- **5. Application on missing parts.** Done. Each parameter type is opened
  twice: once with `TMissing` for its type parameters, which is what the
  argument is checked against, and once with the EVars, which is what the
  complete type coming back is then related to. Constraints are collected
  between two ground types, which is the property §1 says LTI rests on and we
  had broken. The relation's verdict is reported: a plain `no` is unreachable
  there, the pattern having already answered for every complete part, but
  `exhausted` is the relation declining to record, and the EVar it gave up on is
  marked as reported, so nothing downstream would. The cost step 0 measured is
  paid here and nowhere else: a bare lambda in the same argument list now asks
  for an annotation, in three tests. What it bought is the sibling refusal
  becoming unreachable in practice -- `both[A, B](True, fn (y: Bool) -> y)` was
  refused and now infers, since `?B := Bool` arrives already solved rather than
  as `?A <: ?B`.
- **6. `EVar` out of `Type`.** Done, but not as written above. "Constraints live
  in the context, indexed by binder position" was the wrong shape: an index is
  relative, so the relation would have had to carry a binder and a depth. A
  level is absolute, and type variables and EVars already share the level space
  -- so an EVar is simply an `FVar`, and the entry at that level says which kind
  it is. The node's `kind` was a second copy of an answer the context already
  held.

  What that costs: `FVar` no longer licenses promotion on sight. Exposure,
  `#join`'s standing-aside, `#meet`'s dual, `#avoid`'s widening, and `#cast`'s
  covariant promotion all ask `#rigid` first, because an EVar has constraints
  where a rigid variable has a declared bound. Six places, all adjacent to a
  rule that already had to distinguish them.

  What carries the rest of the deletion is not the node but an invariant about
  the _entry_: **an EVar entry is short-lived, and inside its window only two
  types name one.** A batch is pushed in `#applyCall`, the two
  constraint-collecting relations record against it -- an argument against its
  parameter, the result against the expected type -- it is solved, and it is
  gone. Everything else in that window is EVar-free by construction: patterns
  hide the type parameters behind missing parts, arguments come back complete, a
  recorded bound has been avoided already.

  So:

  - **`EVarMode` and `probe` go.** They existed to stop `#join`/`#meet`
    recording on an operand. The lattice joins a `match`'s arms and the bounds a
    batch collected, and neither can name an EVar -- so there is nothing to
    stop. Recording is now unconditional, gated by reaching an EVar at all.
  - **`Context.apply` has one caller**, the end of `#applyCall`. The other seven
    -- closing a lambda, a `let` body, a `match` arm, the program's result, both
    sides of a printed verdict -- were substituting into types that cannot hold
    an EVar. Verified by removing them: the suite does not move. It takes a
    `Type` rather than a pattern now, for the same reason.
  - **The refusal of a sibling stays**, and earns it: constraint collection is
    exactly where a sibling or an escaping variable can still turn up.

  Then the invariant was made structural rather than argued. **Arguments are
  checked before the batch is pushed**, so there is a stretch of `#applyCall`
  where no EVar exists at all, and the EVars are created only for the relating
  that follows. That has a consequence worth naming: **batches never overlap**.
  A nested application opens and closes its own entirely inside the argument
  loop, so a constraint mentioning an EVar can only mean a sibling, and there is
  no "enclosing batch" case left anywhere.

  **`Subtyper.withEVars` owns the batch and nothing else** -- the scope, one
  EVar per hint, solving, and the substitution that carries the answers out. Not
  even the declared bounds: a bound is a constraint like any other, and
  `#applyCall` records it by asking `?A <: bound` the way it asks everything
  else, which also makes the unbounded case fall out rather than be excluded --
  `?A <: unknown` is vacuous and the relation says so before it reaches the
  variable. What the call _does_ with its variables stays in `#applyCall` too:
  which types to open, where each variable occurs, what to relate. `#solveEVars`
  moved in, leaving `#reportTypeArg` behind, since the three failures differ
  only in what to _say_.

  Arity stopped being part of this. An argument list of the wrong length now
  settles the call on its own -- report, and `<bad>` -- rather than
  instantiating a batch and then suppressing everything it concluded. The
  suppression was `abandon`, and it was really the admission that a wrong arity
  and an uninferable type argument had been made one thing when they are two.

  With that, the assertions guarding what can no longer happen go too:
  `#assertUnsolved` at the relation's head and the cast's, and
  `#unsolvedEVarsFrom`'s throw on a solved EVar. Solving happens after the last
  constraint and the scope drops immediately after, so a solved EVar is never
  standing where anything looks. `Context.apply` stopped recursing for the same
  reason -- a solution is built from bounds that cannot name an EVar, and there
  is no second batch to name -- and then went entirely; see below.

  The escape check stays: it is about _scope_, which is avoidance's business and
  still subtle. It moved with the solving, and its bar is the batch.
- **7. `#subsume`.** What is left of it relates two written types -- a bound
  against a bound, a type argument against its bound -- and those are casts
  against a complete pattern, once nothing else is left to break.

Steps 2 and 3 were additive and safe. Step 4 was the commitment point, and it
came through without moving the suite -- the behavior it commits to is not paid
for until step 5 puts patterns where the EVars are.

## Where EVars live

`EVarEntry` is a class, and the operations on it -- recording a bound, noting a
occurrences, noting that a diagnostic already accounts for it -- sit there
rather than on `Context`. Nothing they do consults the ordering: the bar for a
bound is the entry's own `batch`. `Context` keeps the push that allocates a
batch and the lookup that finds one, and its level-keyed reads answer
`undefined` for the wrong kind rather than throwing, because which kind a level
holds is a genuine question -- an `FVar` does not say, rigid variables and EVars
sharing the space. A level naming nothing at all is still a bug and still
throws.

An entry carries its own level and the `FVarRef` naming it, so a batch is pushed
as entries and hands out its variables rather than a caller rebuilding them from
levels. Everything reached by level is reached from one of those variables, so
that is what the context's reads take: a level on its own says which entry but
not that anything pointed at it.

There is no solution field. `withEVars` decides a batch all at once and collects
the answers in order, so nothing has to represent "not solved yet" -- a state
only that loop was ever in a position to observe, and the source of a
three-way-ambiguous `undefined`. The caller still holds the unopened result the
batch was instantiated from, so it opens _that_ with the solutions: one ordinary
substitution, and `Context.apply` -- a second mechanism that walked a type to do
the same job -- deletes.

### A lower bound is taken as it is

A solution from below is the join of the lower constraints and nothing else. It
is not widened, and the case for widening it is worth recording, because it came
close.

Once a constructor has a type of its own, a batch's timing has a price:
`foldr(xs)(Z)(op)` solves `B` at the end of the list `Z` stands in, before `op`
is checked at all, so `B` fixed at `Z` refuses the `S` the operator answers
with. Taking the solution at its _family_ fixes exactly that, costs nothing
where an upper bound demands the constructor, and was implemented and measured:
it saves three ascriptions across the corpus.

It was dropped because of what it does everywhere else. `id(Cons(x, xs))` would
answer `List`, so the principal type would survive a `let` and not a call, and
the one thing _Constructors as types_ promised -- that a constructor's own type
is what inference returns -- would hold only until a polymorphic function was in
the way. The precision is worth more than the three ascriptions, and the
ascriptions are ordinary: this is `foldLeft(Nil)` in Scala, which has always
needed `List.empty[Int]` and for the same reason.

Scala's own widenings are a narrower thing, and the difference is instructive.
`widenInferred` widens _singleton_ and _union_ types when a variable is
instantiated -- types an author mostly cannot write and rarely means -- and
leaves nominal precision alone: `val x = Some(1)` is a `Some[Int]`, never an
`Option[Int]`. The rule is keyed on which types are too precise to be meant, not
on where the solution stands. Our own version of it is the value form: `|
True`
is a member of `Bool`, and that is decided at the declaration.

And `foldLeft(Nil)` fails there for our reason, not for a different one. Scala's
constraint set does outlive a parameter list -- the variables are made once, at
the polymorphic method, and every list records into the same set -- but
instantiation is demand-driven, and typing a lambda is the demand: its parameter
types come from the expected type, so a `B` still standing in `(B, A) => B` is
forced to a value before the lambda's body is looked at, and what it is forced
to is what `z` said. Constraints from the later list are not weighed, because
the later list cannot be typed until the variable is gone.

So a bare lambda is what closes a batch early in both designs. We close one per
list, which is a coarser cut at the same place and for the same reason, and the
list boundary is where an author can see it. Widening the answer was a way of
paying for that cut with imprecision everywhere; the cut described in the
roadmap's _Batching one parameter list_ is the way of making it later and
narrower, and it is where this pressure should go.

## Who says what went wrong

`Subtyper` shares the checker's `diagnostics` array, the way `Elaborator` does,
and files its own. The line is not severity or wording but this:

> A fact about what was **recorded** -- a bound widened, a constraint refused,
> an EVar settled -- happened whatever the ask was for, so it is said where it
> happened. A fact about the **answer** is only a failure relative to the
> asker's intent, so it goes back as a `Verdict`.

Most of `Subtyper`'s own asks are questions rather than assertions -- `#join`
ordering two variables, `#equiv` running one direction of two -- so a `no` there
is an ordinary answer and nothing to report. Only the caller knows which it
made.

Severity follows soundness, and only the recording site knows it: a bound
_widened_ is a one-directional loss, so any later failure is still explainable
by it -- a **warning**. A constraint _discarded_, or a choice between two
_incomparable_ candidates at an invariant occurrence, settles the program's
meaning arbitrarily -- an **error**. That is why `disagrees` is not warnable
while `unconstrained` is: nothing was demanded there, so the selection is sound
and even principal, it is only unactionable.

`interdependent` left `Verdict` with this. It was never an answer about two
types -- it was a report that the relation had been asked to record something it
could not write down -- so `#constrain` now files it and returns.
`TypeArgFailure`/`EVarSolution`, whose only purpose was carrying a reason out to
be phrased elsewhere, are gone with it.

What is left is `boolean | undefined`: it holds, it does not, or the fuel ran
out. The third case is not folded into `true` the way `TBad` folds an
already-reported mistake into the relation, and the difference is where the
marker can live. `TBad` rides in the _type_, so everything downstream still sees
that a report stands; a relation has no such carrier, and its caller would
proceed as though the comparison had held. `solveEVar` is what proves it -- it
answers `TBad` on exhaustion, which it can only do because the verdict reached
it. So the third value buys the ability to plant a marker at the one site with
somewhere to plant one, not merely a choice of wording.

Positions come from the checker, which has them. `withEVars` takes the
application's, and an optional `at` on `isSubtype` or on a cast narrows it to
one argument's for the length of that ask -- so a widened bound names the
argument that caused it, where a solve-time error names the call. There is no
separate `relate`: a top-level ask installs a position the same way it resets
the fuel, both being facts about what one query covers, so `#query` does it.

The cast family reports the same way, and has to. A cast never fails on the
surface -- it always answers with the shape that was asked for, filling what it
could not reach with `TBad` -- and `TBad` is the checker's word for _a report
already stands_. Letting the verdict carry the report out put it at whatever
granularity the outermost caller had, so a result that disagreed came back as
the whole arrow disagreeing; and a caller with no use for the verdict dropped
it, leaving a `TBad` speaking for a report nobody had filed. Now `#castFailed`
files where the shape gives out, and the messages name the part:
`expected Int, found Bool` rather than
`expected Bool -> Int, found Bool -> Bool`, and a lambda of the wrong arity gets
`expected 1 parameter, found 2` back.

So a cast has no verdict at all, and `Cast` is gone -- `upcast`, `downcast` and
`exactcast` answer with a `Type`. Nothing ever read the verdict before merging
it into another with `bothVerdicts`, which is what a value that says nothing
looks like: every way a cast could decline is a fact about a part, said where
that part is, and the combination at the top named no part and no reason.
`Verdict` is now the relation's alone -- asking whether one type is under
another is a question with an answer, where a cast is a rewriting. The one
decline about the whole ask rather than a part is exhaustion, which is why
`#castQuery` is the only entry point that still files anything itself.

An ask that passes no position is a _query_, and stays silent. That is not a
loophole but the distinction itself: `downcast(unknown, expected)` asks what a
pattern admits at its widest, reads no program that could be wrong, and passes
no position for exactly that reason.

## Exhaustion unwinds

Fuel is a property of the whole query, so a spent tank is not an answer any
local caller could use -- and the old code proved it by not using it: `#join`
and `#meet` both read `exhausted` as "unrelated" and settled for an extreme, a
definite answer manufactured from a limit. It is an exception now, caught only
in `#query`, which takes the caller's own way of saying it does not know -- a
verdict, an extreme, the demanded shape. Interior relations return `boolean`;
three-valued logic exists only at the boundary.

## What the neighbours do

Scala 3 is the same design under other names. `ProtoTypes` is our patterns --
`WildcardType` is `TMissing`, `deepenProto` is pushing one inward -- and
`Inferencing.interpolateTypeVars` is `solveEVar`: a variance map over the
occurrences in the result type, minimising covariant ones, maximising
contravariant ones, and taking the lower bound for a variable that does not
occur. The one difference worth naming is that it picks silently where we warn.
Unsurprising ancestry: colored local type inference is Odersky, Zenger and
Zenger, and dotty is its descendant.

What follows is the places we refuse something they do. Each refusal is a
property of the _type language_, not of the solver, and it is the same property
every time -- recorded below. Then one difference that runs the other way: a
feature they have whose whole cost lands on the solver instead.

### A bound that names another variable

    ?x <: ?y -> Int
    ?x <: Bool -> ?z

Three answers exist. Dotty **stores the meet**: bounds are arbitrary types, so
the upper bound is literally `(?y -> Int) & (Bool -> ?z)`, inert until something
is compared against it and the subtype checker's distribution laws take it
apart. That needs intersections in the language.

MLsub **decomposes** instead -- a variable under an arrow bound takes a function
shape, splitting into `?x1 -> ?x2` with `?x1 :> ?y` and `?x2 <: Int` -- and gets
principal solutions for it. That needs unions and intersections to state the
results in.

We have the decomposition already: `downcast(T, P)` is that walk, at the same
variance flips. What we lack is anywhere to put its results, which is why `T` is
ground. A pattern hides what is unknown behind a missing part rather than behind
a variable, and a missing part is not something one can constrain and come back
to.

### The ordering graph, and the levels that come with it

Dotty keeps ordering separate from bounds: `lowerMap`/`upperMap` hold, for each
variable, the variables known to be below and above it, closed transitively on
insert, while `boundsMap` holds the concrete part. Joins and meets are applied
to concrete bounds and never to variables. An edge discharges when its source is
instantiated -- substitute, and `?y <: ?x` becomes an ordinary join against a
ground type. Equality is not primitive but a _cycle_: two variables ordered both
ways are merged, keeping the outer one.

Two reasons we do not.

The join it defers to is ours, and ours is lossy -- `List[Bool] ⊔ List[Int]` is
`List[unknown]` for want of a union (§5). So recording `?A <: ?B` would convert
the refusal `#constrain` files today into a silent `unknown` one step later,
which is the trade the exhaustion rule already declines: say so, rather than
fall back to an extreme.

And a graph needs levels. Dotty carries a nesting level on every variable, with
level checks and a level-avoidance map, because an edge crossing scopes must
discharge before its inner end dies -- the outer variable cannot be left naming
one that is gone. Step 6 bought us out of all of it: batches never overlap, so
there is no elimination order to get right, and the escape check's bar is simply
the batch.

### Context-sensitive arguments in rounds

TypeScript skips context-sensitive arguments -- lambdas with unannotated
parameters -- in a first pass, fixes what the other arguments determine, then
contextually types the skipped ones. It skips them _wherever they sit_; the
left-to-right restriction applies only between two context-sensitive arguments.
So it recovers one of the two regressions step 0 measured and not the other:

    f(fn (x) -> id(x), True)    -- `True` fixes ?A, and the lambda then checks
                                   at Bool -> Bool
    both(True, fn (y) -> y)     -- nothing determines ?B anywhere in the list;
                                   TS "succeeds" only by giving `y` implicit any

The price is not the ordering, which is cheap. It is that a deferred argument is
checked while the call's batch is live, so batches overlap again and "a
constraint mentioning an EVar can only mean a sibling" goes with them. The form
that keeps the invariant is to solve the batch _before_ any context-sensitive
argument is checked, and check those against what came out -- best effort, no
second solve, no live batch during an argument. Which is a cut in the list
rather than a deferral within it: one list, several batches, `withEVars` still
owning each alone. `docs/roadmap.md`'s _Batching one parameter list_ is what
that would take, and where the cut would fall.

### Recursion, and a rule that was rejected

The split here is unification against subtyping, not local against global.
Hindley-Milner infers a recursive function's result by unifying against a fresh
monomorphic variable, and gets a principal answer free. With subtyping the same
question is a least fixed point on a lattice, and each round widens -- so Scala
refuses outright ("recursive method needs result type"), TypeScript reports a
circularity and falls back to `any`, and Crystal does infer, by iterating over
unions, at the cost of whole-program compilation. Ours is Scala's answer with
better diagnostics: an unannotated `def` falls back to `let`, is `unknown` in
its own body, and is reported at each use.

The same split settles the other two. Inferring a fold's accumulator is not a
recursion problem at all -- `foldr` is staged so `z` fixes `B`, and where `z`
says nothing the answer everywhere is an annotation, `Nil[A]()` here exactly as
`foldLeft(List.empty[Int])` there. And a dependency graph over a mutually
recursive group buys nothing for a real cycle: SCC analysis is load-bearing in
HM because it enables generalisation, which we do not do.

**Rejected: inferring the result from the non-recursive arms.** Push the join of
the arms that do not mention the def, then check the ones that do against it --
one pass over each arm, no fixpoint, no speculation. It fails on `let`. A body
is a nested chain whose result is the innermost expression, so the bindings are
not branches at all -- they are on every path:

    def len(xs: List[A]) ->
      let n = match xs with | Nil -> Z | Cons(h, t) -> S(len(t));
      match xs with | Nil -> Z | Cons(h, t) -> n

Here no arm of the final match mentions `len`, and every one of them depends on
it through `n`. So the check must be transitive over the binding structure, and
for accumulator- and helper-shaped recursion -- the recursive call in a `let`,
the final match assembling -- every arm is tainted and the rule yields nothing.
What is left is a conjunctive syntactic trigger served by a taint pass, which is
new machinery for a case the annotation already covers.

### The common cause

Every refusal above is the same one. There is no union, so there is no join to
state a variable's bounds in, no lattice for a fixpoint to converge in, and no
principal answer for two arms of different instantiations. Unions are therefore
the single change that would move all of them at once, and the only one worth
costing; anything narrower is approximating what the type language cannot say.

**Costed, and declined.** What pays for a union is _elimination_ -- TypeScript's
unions are worth their weight because narrowing takes them apart again, by
discriminant, by `typeof`, by control flow. We have one eliminator, `match`, and
it is one level and nominal: a scrutinee whose type named several datatypes
could not be matched at all, since `#checkMatch` reads a single `TData` head and
`#remaining` is a set of _one_ declaration's constructors. So the join would be
formed everywhere and taken apart nowhere.

Restricting unions to constructor sets of one datatype -- the narrow form that
would fit `#remaining` -- does not rescue it, because a union over cases is
still a union over their _arguments_:

    datatype Foo[A] where | Pos(A) | Neg((A) -> Unit)

`A` is bivariant here and neither occurrence can be widened independently of the
other, so joining a `Pos` at one `A` with a `Neg` at another is not a set
operation on cases; it is constraint solving, and the answer depends on a
variance the case set does not carry.

And `#joinMany` is a _left fold_ over pairwise `#join`. At an invariant slot a
pairwise join has no answer and must choose arbitrarily -- but a later candidate
in the same list may have made one choice the right one, which the fold has
already thrown away. So the result depends on arm order, which is exactly what
"no arm is privileged by position" was supposed to rule out. A full-fidelity
answer needs a _primitive n-ary_ `joinMany` that sees every candidate before
committing an invariant slot. That is the thing to build if this is ever
reopened, and it is worth noting that it is useful without unions: it is the
same machinery `match` wants for rising several constructor heads at once.

Not now, and probably not soon. The baseline stands: `join` falls back to
`unknown`.

### Implicits

Split out to `docs/implicits.md`: what resolution-by-search would cost, why it
forces speculation, and why a matching-based fragment fits `withEVars` unchanged
where Scala's cannot.

## Open

- Does avoidance survive? Probably, but for a narrower reason than today: the
  escaping variables it exists for are still introduced by binders, but the
  types that could carry them out are now all complete.
- Whether the casts can share one traversal with `#join`/`#meet` or only a
  skeleton. Settle it by writing them, not by deciding now.
