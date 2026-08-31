This is a prototype checker for a Fsub-like language, written in TypeScript. We
follow an ML-like, indent-based syntax, but use local type inference. Ignore
`legacy/`. Keep comments brief. Don't have to document every error case we've
been through. Be care of naming: avoid generic names; "operation + target" is
often better.

Pipeline: require walk (`#require "path"`, textual and flat) -> lexer -> layout
(insert scope markers, semicolons) -> parser -> elaborate -> check.

Elaboration is not a pass of its own. Declarations are elaborated once up front;
a type written inside a term is elaborated when checking reaches it, because
binders scope over what follows and the context _is_ the scope.

Checker structure:

- Infer to a _bad type_ if anything wrong
- Checking to a bad type always success
- So, never fail checking a tree halfway

A bad type means _a report already stands_, and that is constructive: `TBad` is
private to `types.ts` and the only way to one is `badUnder`, which takes the
diagnostic that licenses it. So a rule either files and passes the diagnostic it
got back, or hands on a bad type it already holds. `completePattern` takes the
report lazily -- it is asked for only where a part was missing, and at most once
however many were, which is the question callers used to ask as `already`.

`never` is not a bad type and does not merge with one. `bad` is below and above
everything -- it takes whatever shape is demanded, in whatever arity, so filling
from it invents nothing. `never` is only below, so it lifts into a shape whose
holes have a variance and no further: `unknown -> never` is the least function
type at every arity, which is why a `never` is callable, takes type arguments,
and answers `never`; the least `List[?]` is a `List` of the least thing and the
least `Sink[?]` a `Sink` of the greatest, the argument's own variance saying
which; an invariant argument has no extreme of its own, so a demanded `Cell[?]`
has no least solution. Where a rule needs a shape and there is none to read at
all -- a `match` demands a datatype without knowing which -- `never` answers for
the whole form: nothing arrives, so no name resolves, nothing is left uncovered,
and no arm is reachable to be joined.

A cast out of an extreme in its own direction can always be made, so it never
errors. Choosing an invariant argument _warns_, the way a `joinMany` that runs
dry does: the answer is sound and only arbitrary, blaming the program for what
the checker could not name principally would be wrong, and there is no `TBad` to
hand back anyway, `badUnder` taking errors alone.

A constructor is a function of its fields, so there is no constructor term form
and saturation follows from arity. The exception is a _value_ constructor, and
which one a declaration produces is something the declaration says rather than
something the arity implies: `| True` declares a value of type `Bool`, `| Off()`
a function `() -> Flag`, and both are legal on a monomorphic datatype. Only
there, though -- a value of `List[A]` would need `[A]List[A]`, a quantifier over
a non-function, so `| Nil` is refused and told to write `Nil()`. So `CtorDecl`
carries the domain as _absent_ rather than empty for a bare name, which is what
keeps the two forms distinguishable at all, and `DataCtorInfo.isValue` is what
every later reading asks. Patterns are untouched by the distinction: they take
apart fields, a nullary constructor has none either way, and `| Nil ->` is the
spelling whichever form declared it.

A datatype's variance is inferred, not declared -- read off its constructor
fields by a fixed point over the whole declaration table, since two datatypes
may name each other. `Variance` and _position_ stay the two things they were:
variance is a direction of travel, three-state, composed by multiplication, and
the inference carries it; a position is an accumulated record, four-state,
merged and never composed, and the inference writes it down. Bivariance -- a
parameter nothing observes -- has no direction, so it collapses to covariant on
the way out and is warned about at the declaration instead. `docs/variance.md`
has the walk, the stopping criterion and the worked examples. Everything after
reads that number off the `TData` in front of it: a node carries its
declaration's parameters by reference, so where an argument stands is a property
of the type rather than a lookup, and a walk in `types.ts` can ask without
knowing declarations exist. The parameters alone, not the whole declaration --
that reaches its constructors' field types, and a `Type` that reached back into
itself would not be a finite value.

A mutable cell is a type _former_, `TRef`, and not a datatype the checker
declares for itself. Almost nothing a datatype is would be true of it: it has no
constructors, nothing takes one apart, and its argument is invariant for a
reason no walk over constructor fields could find -- `get!` reads a `T` out
where `set!` puts one in, and neither of those is a field. So the invariance is
a literal `0` in every walk rather than a stipulation in a table, and a `Ref`
carries no name, two cells being the same type when their arguments are.

`match` refuses it along with the other heads that are no datatype, which is the
right answer for a type that is inhabited and still has nothing to take apart.
It is worth seeing why the alternative fails: as a constructorless datatype, the
exhaustiveness set reads "no constructors" as "no values", calls every arm
unreachable and answers `never`.

The _name_ `Ref` is nothing special, though -- a transparent alias for the
former, seeded before the program's own declarations, which is what an alias
already is. So it obeys whatever rule every other type name obeys rather than a
rule of its own: a program declaring one is told the name is taken, a type
parameter spelling it is told the same, a wrong arity is reported the way
`Pair[Bool]`'s is, and if type names are ever made shadowable this one follows
without being revisited.

`ref!`, `get!` and `set!` are ordinary term bindings, seeded outermost like the
constructors. A trailing `!` is part of an identifier to the lexer, which knows
no list of builtins; what reserves the spelling is that the parser refuses it at
every position where a name is _bound_, so a bang name can only ever be used.
That rule lives beside the one about `_`, both being ordinary identifiers whose
admitting positions the parser decides once.

Walk types structurally. A function over types dispatches on the kind of each
node and recurses on what that kind contains; a whole-type equality test like
`alphaEq` is not a case, and standing one in front of the switch as a fast path
hides which cases it is answering for. Reach for it only where the structure
runs out -- at a leaf, or on one invariant argument, where there is nothing to
recurse into and nothing else to ask.

Local type inference. EVars arise from one place only: instantiating a
polymorphic callee at an application. Collect constraints on them and solve at
the end of each argument list: both bounds always, LUB of the lower constraints
and GLB of the upper ones, defaulting to bottom and to top. A declared bound is
an upper constraint like any other, and so is the expected type when an
application is checked rather than inferred -- it says nothing about the
arguments, but it does say something about the type arguments, which is what
lets `Nil()` know what it is empty of. Then check the lower bound sits under the
upper, and pick between them by how the EVar occurs in the application's result
type -- covariant takes the lower, contravariant the upper, which is what makes
the answer principal. Occurring both ways, which is what an invariant `TData`
argument makes of a single occurrence, neither bound is the answer by position,
since widening either way breaks the other. Bounded from one side only, there is
still nothing to choose: the other bound is the default extreme, which nobody
recorded, and a demand weighed against a default settles it silently -- this is
what lets a staged `apply(True)(fn (y) -> y)` infer its type argument. Bounded
both ways by equivalent types, likewise. Bounded both ways by types that differ,
take the lower for being the demand and _warn_: either bound would check, so
nothing is unsound, but neither is above the other and settling silently would
hide that a choice was made. A variable occurring nowhere in the result is not
this case at all: the solution goes into the result type, which has no place for
it, so nothing can tell the bounds apart and no choice is one. It takes the
lower. Bounded from neither side is not a case either: both bounds are then the
extreme, and the occurrence reads them as it reads any pair -- `Nil()` is
`List[never]` because that is what the program says, not because something was
left out.

Exhaustion is per solve, not per bound: joining the lower constraints, meeting
the upper ones and comparing the two are one ask, and running dry in any of them
is the checker's limit rather than the program's mistake. Say so and answer
`TBad`, which cannot go on to be wrong somewhere else; falling back to an
extreme would manufacture a bound the author never wrote and then blame them for
it.

A constraint picked up under a binder may mention variables that binder
introduced, which an EVar's solution must not. Avoidance removes them, widening
a lower bound and narrowing an upper one, swapping direction at every
contravariant position: a rigid variable goes to its declared bound or to
top/bottom, and a `TData` argument goes at its parameter's variance -- an
invariant one cannot be touched at all, so the whole type collapses. An unsolved
EVar of the same batch is _interdependent_ and is rejected rather than
approximated -- there is no bound to widen to, and collapsing it would silently
drop the constraint. Say so and ask for an annotation. In either direction, not
only rightward: selection reads the result type alone, so a sibling standing in
a pending bound is a dependency it cannot see. An EVar of an _enclosing_ batch
is ordinary, and is how a bare lambda's parameter gets its type.

Unannotated lambda parameters are never EVars -- a parameter's type comes from
annotations or from the checking context. In an argument list the parameter
binds to the callee's EVar directly, so a bare lambda works there as long as its
body does not need the parameter's _structure_; `match` on it does, and that is
where a _later_ parameter list is required, the way Scala's `foldLeft(z)(op)`
stages it. Currying gives this for free; there is no multi-list function type.
`fn [A](xs)[B](z)(op) -> e` writes the lists on one binder, and that is surface
sugar the parser folds into nested `fn`s -- so several lists cost the checker
nothing, and the type they give is the curried one.

Recursion is `def`, and what it adds to `let` is a scope rather than a shape: a
run of _adjacent_ `def`s is one group whose members may name each other, and
anything between two of them closes the run. The parser has folded a `def`'s
parameter lists into its `Abs` and its result type into a `FunType` by the time
the checker sees it, so a member is a `DefItem` -- a `LetItem` whose bound is an
`Abs` by construction -- and the only question left is whether it has an
annotation. That question is the rule. A signature is something the author
supplied, so it can be pushed before any body is checked and its `def` is
visible to the whole group; without one there is nothing to push, and the
binding falls back to being a `let` -- visible once checked, and `unknown`
inside its own body. Not a placeholder for the type it will turn out to have:
nothing is known of it yet, so it may be passed on and may not be called, and a
recursive use is refused at the call where the recursion is. `unknown` rather
than `bad` because `badUnder` takes the diagnostic that licenses it, and the
report belongs at each use rather than once at the push.

A `def`'s _parameters_, though, must always be annotated. Nothing else can
supply them: the body is inferred or checked against the def's own signature,
and never sits where a context would know them, so the advice a lambda gets --
use it where its parameter types are known -- names nothing an author could do.
An omission is therefore settled in the tree rather than asked about by every
reader of it: the parser stands a `MissingParamType` where the annotation would
be, and elaboration reports it, once, at the binder, and answers `bad`. That is
the only node standing for something unwritten, and it is what keeps the rest
ordinary -- a `def` missing a parameter type still has whatever signature it
wrote, so the group still sees it, and its body is still checked, against a
parameter that absorbs what is done with it. `unknown` would not do here the way
it does for a missing signature: nothing is merely unknown, a report stands, and
`bad` is what says so. A signature is also the one place the parameter types are
_written_ -- the parser strips them from the `Abs` it folds, since elaborating
them there as well would read every one twice and double whatever it reports.

The order follows: signatures, then the unannotated bodies -- each replacing its
own entry at its own level, so no `FVar` already elaborated goes stale -- then
the annotated bodies. What is _not_ there is a dependency graph. An SCC pass
would additionally order a non-recursive unannotated `def` before a sibling that
calls it, and adding one later only accepts more, so nothing here would be
rewritten for it.

Inferring a `match` joins its arms with LUB, so no arm is privileged by position
-- but only the arms a value can reach. One-level patterns keep the whole
analysis one set: what a value could still be on reaching the arm being checked.
An arm is unreachable when nothing it matches is left in that set, and the arms
are exhaustive when it is empty at the end. A name that is no constructor of the
scrutinee's datatype is asked nothing of the set -- it was never in it, so it
cannot have been taken out, and reporting it as matched above would blame the
author twice for one thing. An unreachable arm is reported and its body still
checked, since what is written there is as wrong as it would be anywhere else;
only its type is dropped, joining it in having widened the answer for an arm
that never runs.

Some limitations:

- Type aliases cannot be recursive: they are transparent, so expansion would not
  terminate. Datatypes may be recursive, being nominal -- nothing unfolds a
  `TData`, so `List` and `Tree` cost the checker nothing.
- Pattern matching is only one-level, which keeps exhaustiveness a
  set-membership test
- Full Fsub subtyping is undecidable, so it runs on a fuel counter and can
  answer "gave up" as well as yes or no
