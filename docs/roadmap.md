# Before the first release

GaLa runs end to end today -- lex, lay out, parse, elaborate, check, evaluate,
print a value and its type. What follows is the work between here and a version
anyone else should use. What is left, with the reason each is on the list rather
than merely desirable -- then what has landed, and then the things deliberately
left off, which are limitations the design chose rather than corners left
unfinished.

## 1. Dependent arrows

The largest item, and the one that changes the calculus rather than extending
it. It is what the rest is scaffolding for: nothing else depends on it, and that
is what makes it the point rather than what makes it optional. An earlier draft
of this list read that backwards and put it last.

It reopens part of the variance work rather than building on it. Variance is a
property of arrow positions, and every walk over an arrow -- `#castFun`,
`#relateFun`, `#latticeFun`, and `noteField` -- assumes the result cannot
mention the parameter. A result that can is a case each of them has to grow.

The phantom warning is the other thing to revisit here. A type parameter no
constructor observes is warned about today as almost certainly a mistake, there
being no way to use one; dependent arrows are the feature that would give
phantoms a use.

The surface is not the cost. Domain names parse today and are dropped, so the
binder has somewhere to be written; what is missing is anywhere for it to be
_read_. A `Type` has no way to mention a term -- there is no kind for one, and
`Context` keeps term and type variables apart -- so the wall is in the core and
not in the parser.

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

## 2. Constructors as types

Each constructor of a datatype becomes a type of its own, below the datatype:
`Cons[A] <: List[A]`, `Nil <: List[A]`. Derived, not declared -- there is no new
syntax and nothing to write -- depth exactly one, and the coercion is the
identity, since a `Cons` value already _is_ the `List` value. One new leaf in
`#relateData`, and no new runtime representation.

This is the successor to `docs/subtyping.md`, which designed a declared
hierarchy with super constructors, implemented most of it, and lost. It delivers
the case that design was really for -- a subgrammar that embeds into a full one,
`NonEmpty[A]` out of `List[A]`, `Type` out of `TypePattern` -- at a fraction of
the cost, and it populates Fsub's bounds, which is the other thing that file
wanted and the reason `FUEL` and the three-valued `Verdict` exist at all.

Four things it needs, in order.

**Constructor names become globally unique.** They are type names now, so they
share a namespace with datatypes and with each other; two datatypes may no
longer both declare a `Same`. The alternative -- qualified names, `List.Cons` --
was tried on the closed branch and is what forced a `match ... as` there. A flat
rule is cheaper and is what the evaluator already half-assumes.

**Elaboration's first phase admits constructor names.** `Declarations` already
seeds every datatype name before any signature is elaborated, which is what lets
`List` and `Tree` name each other; constructor names now join that seeding, so a
field may mention `Cons[A]` in the same declaration run.

**The scrutinee's type supplies the case set.** `#checkMatch` seeds `#remaining`
from `datatypeOf(scrutinee.name)` today. It should seed from the scrutinee's
type, which is behaviour-preserving while a `TData`'s identity is its name and
becomes the whole feature the moment it is not: `match xs with | Cons(h, t) ->`
on an `xs : Cons[Bool]` is exhaustive with one arm. That refactor is worth
landing on its own, precisely because nothing about the suite changes.

It does surface one diagnostic decision. A pattern name can then fail two ways
-- not a constructor of the datatype at all, or a constructor the _scrutinee's
type_ excludes -- and the second is unreachability rather than a name error. It
wants its own wording and must not double-blame.

**Inference returns the principal type.** `Cons(True, Nil())` infers
`Cons[Bool]` rather than `List[Bool]`, which is what makes the feature reachable
without annotations everywhere. Two consequences are already known. Arm joins
now rise two constructor heads to their datatype, so `#latticeData` is on the
critical path from day one. And an arm excluded by the scrutinee's type must be
a _warning_ rather than the error `#report` files today -- an ordinary `match`
with a `Nil` arm over a known `Cons` is not a mistake worth refusing a program
for, whereas an arm shadowed by the arms above it still is.

The known cost is the usual one for inference under subtyping: `ref!(Cons(...))`
infers `Ref[Cons[Bool]]`, a cell nothing can `set!` a `Nil` into, and the fix is
an annotation.

## 3. Sugar for single-case datatypes

`let Pair(x, y) = e` as a one-arm match, which is one token of lookahead in
`letBinding` handing off to `matchPat`. It works for any constructor, not only a
sole one -- `let Cons(hd, tl) = xs` is legal and partial, and the totality
report is the one `#remaining` already produces, which under item 2 is silent
exactly when the scrutinee's type says it is total.

## 4. Batching one parameter list

Today a parameter list is one batch, and the staging that a bare lambda needs is
the author's to write: `foldLeft(z)(op)`, a second list so that `z` is solved
before `op` is checked. TypeScript reaches the same effect without the syntax --
it defers the context-sensitive arguments of a single list, fixes what the rest
determines, and checks the deferred ones against that. So the benefit is
available to a language that never asks the author to split the list, and the
question is what it costs us.

The cost is the one `docs/clti.md` names in "Context-sensitive arguments in
rounds": TS checks a deferred argument while the call's batch is still live,
which overlaps batches and takes "a constraint mentioning an EVar can only mean
a sibling" with them. The form that keeps the invariant is to _cut_ the list
rather than defer within it -- solve the batch at the cut, and check what is
after it against the solutions, exactly as a second written list behaves. One
list, several batches, and `withEVars` still owns each one alone.

What is left to decide is where the cut falls. "Before the first
context-sensitive argument" is one batch boundary and recovers
`f(fn (x) -> id(x), True)` only if the lambda is not first, which is the
left-to-right restriction TS lifts; a cut before _each_ context-sensitive
argument recovers it wherever it sits, at one solve per lambda. Neither reaches
`both(True, fn (y) -> y)`, where nothing in the list determines the parameter --
that answer is an annotation here as it is in Scala, and TS only appears to have
one because it has implicit `any`.

Which is why this is an item and not a dependency: the syntax stays, since a
written list is still the only way to stage what no argument determines. This
would make the common case stop needing it.

## Landed

**The extreme lift, dropped.** `upcast(never, Ref[?])` was `Ref[never]`, lifted
one level into the pattern's shape and warning about the argument it had to
choose. It is `never` now, and says nothing.

Standing aside is the easy half: an extreme moving the way the cast moves is
under -- or over -- every type of every shape, so the pattern asks nothing of it
that is not already true. That is the same vacuous case `#subtype` answers on
its first line, so the cast now agrees with the relation by construction instead
of merely not contradicting it. A bad head stands aside for the stronger version
of the same reason, `<bad>` being below and above everything and so answering
invariantly too, where an extreme needs a direction.

The harder half is whether the demanded shape is still _built_ around the head,
and there the two part company. The answer is not what the head means but what a
reader of the answer would otherwise supply. A cast's answer is related against
a type naming EVars in exactly one place -- `#applyCall`'s argument loop -- and
a relation reads parts; an argument's pattern carries a missing part exactly
where a type argument stands, so the parts a relation walks into are the EVar
positions and the shape is how it reaches one. That makes `#castFailed` and
`#avoid` two fillings of the same holes: `TBad`, so an EVar solves bad rather
than being blamed twice, or the extreme the position asks for.

The same question answers differently for `widestMatching`, and the reason is
provenance. An argument's pattern is the call's own parameter type holed at each
type argument, and it is related against that same parameter type opened with
EVars -- so its written parts are compared with themselves and its holes are the
EVar positions. The pattern `widestMatching` reads came from one level up and is
related against something else, the callee's result, so its written parts are
news. Made observable by an invariant argument: `outer(NoPair())` against
`[B](Pair[Bool, B]) -> ...` stops checking if the shape is dropped, `NoPair`'s
own first type argument never hearing `Bool`.

An extreme may therefore be dropped and a `<bad>` may not. The `Cell[never]` a
lift used to build planted at each position the very extreme an unconstrained
EVar reaches by itself, so the constraint it recorded was redundant -- bought
with an arbitrary choice at every invariant argument and a report about the
choice. Nothing else in the solver produces a `<bad>`, so dropping that one
leaves the EVar unconstrained: `use(oops)` against `[A](List[A]) -> List[A]`
comes back `List[never]`, an ordinary type for a program already blamed.

Checked rather than argued. Six programs against the old behaviour -- `never`
and `<bad>` each into a covariant `List`, a contravariant `Sink`, an invariant
`Cell`, a nested `List[Cell[?]]`, and an arrow pattern -- agree everywhere
except for the warning that is gone. Two of them are now tests.

Both decisions are made between `#cast`'s two switches: the first settles the
demands that may not move `type` -- a missing part answers with what stood in
the position, a leaf goes to the relation whole -- and only then is the head
read, once, for the three that do. Getting that order wrong loses the variable
in `up(X, ?)` and `up(X, X)` for an `X` bounded by `never`, which is the shape
the walk had briefly and the regression test it now carries.

Two switches on one `kind` is the trade. The alternative repeated the promotion
and the standing-aside in each of the three shape arms, where nothing forced a
new arm to include them -- and one was in fact written without, during this
change, and caught by a test rather than by the compiler.

An assertion that the lattice operations never see a live EVar was written and
then removed. `#lattice` at an invariant position does reach `#eqtype`, which
records before it tests -- but `#applyCall` checks every argument before a
single EVar exists, and nothing inside a batch's body calls a lattice operation,
so the case is unreachable by construction rather than by luck. The invariant is
`withEVars`'s to state and `#applyCall`'s to keep.

**Optional names in a domain.** `(x: A, B) -> C` and `| MkBox(flag: Bool, Bool)`
parse, an arrow's parameters and a constructor's fields being one syntax and so
one rule. The name is documentation: dropped at elaboration, so a named arrow
and a bare one are the same type and a name can never decide an equality, a cast
or a printed form. It reserves the spelling a dependent arrow's binder will
want, and nothing more -- `(x: A) -> x` is still `unknown type x`, there being
nothing yet that could bind it.

Cheap because the slot was already marked: `domainType` read the `:` and refused
it in so many words. It now reads the domain as a type and reinterprets it
there, which needs no second token of lookahead -- only a bare name can be a
binder -- and routes the name through the same `toBinder` every other binding
position uses, so `_` and the refused trailing `!` reach it without being
restated.

**An evaluator, and a CLI that is the whole pipeline.** Closures, constructed
values and cells, over six term forms. Type application erases. `runFiles`
parses, checks and runs, each phase contributing what it reported, and the CLI
prints `value : type`.

Untyped, and told nothing about whether the program checked -- so it runs on
anything that _parsed_, and an ill-typed program is one the tests run on
purpose. That is where the interesting decision was. With no guarantee from the
checker, every shape it would have supplied is tested here instead, and all of
them are one rule: a value arrived where a different shape was needed. The
alternative design was a bad _value_ mirroring `TBad`, absorbing a failure so
the run could go on and collect more; it is wrong, and the reason is what the
two walks are. Checking is structural recursion over the tree, so every subterm
is visited whatever its siblings did and absorbing genuinely buys the rest of
the reports. Evaluation walks a trace. Past the first stuck term there is no
rest that was going to be visited anyway -- only sibling arguments, and
everything downstream, which is either a consequence of the first failure or an
artifact of the order arguments happen to evaluate in. A test pinning that would
be pinning an implementation detail. So the diagnostics are zero or one, and
terminal.

Scope is the one thing that is _not_ a type question, and the one thing the two
must agree on: where a name resolves decides what a program means. So `#tie`
follows `#checkLetRec` phase for phase -- annotated members bound before any
body runs, unannotated ones as they are reached -- and a later unannotated
sibling is a name outside the run there and here. Binding the whole run at once
is the obvious thing and is wrong: it resolves that name to the group, and the
run quietly means something the check never agreed to.

Cells live in a `Heap` the evaluator owns, a value carrying an address rather
than the cell. Shallow-embedding them in the host heap would work and would put
allocation somewhere nothing here can see it; a budget on cells, a count of
them, or anything that walks them needs somewhere to be, and there is nowhere if
the host heap is the heap.

`LetRec` needs no black hole, and for a parser reason rather than a checker one:
a `DefItem`'s bound is an `Abs` by construction, so the frames can be allocated
before any body is evaluated and no member is ever read while it is still a
hole. Haskell's `<<loop>>` has no analogue here.

The fuel counts applications, every loop passing through one, and is set _below_
what the host stack takes. That ordering is the point: an application recurses,
so a runaway program would otherwise always exhaust the stack first and be told
something about the interpreter rather than about itself. The stack is still a
backstop, with its own message, since a shape whose frames are deeper than
assumed can reach it -- and an explicit-stack machine is the way out from under
the ceiling, when one is wanted.

**Recursive and mutually recursive functions, as `def`.** A run of adjacent
`def`s is one scope: every member may name every other, so `even` and `odd` are
written the way anyone would write them and nothing is encoded. What `def` adds
to `let` is that scope and nothing else -- the parser folds its parameter lists
into the `Abs` and its result type into the `FunType` that becomes its
annotation, so a member reaching the checker is a `DefItem`.

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
- **No union or intersection types.** Costed in `docs/clti.md` and declined. A
  union pays for itself in its eliminator, and ours is nominal and one level, so
  the join would be formed everywhere and taken apart nowhere; restricting
  unions to constructor sets does not help, because a union over cases is a
  union over their arguments. A full-fidelity answer also needs a primitive
  n-ary `joinMany` -- pairwise folding is order-dependent at an invariant slot
  -- and that is the piece worth building first if this is ever reopened.
- **No declared subtyping between datatypes.** `docs/subtyping.md` is the design
  and the epitaph. Constructors-as-types above is what replaces it.
