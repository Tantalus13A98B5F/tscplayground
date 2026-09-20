This is a prototype checker for a Fsub-like language, written in TypeScript. We
follow an ML-like, indent-based syntax, but use local type inference. Ignore
`legacy/`. Keep comments brief. Don't have to document every error case we've
been through. Be care of naming: avoid generic names; "operation + target" is
often better. A constructor is named for what it builds, not `MkFoo`; where it
is a datatype's only one, that is the datatype's own name.

This is for teaching and for research, so a coarser diagnostic is a fair price
for simpler code. Where a distinction would buy a better message and cost a
branch, a flag or a second path through a rule, the message loses -- say the one
thing, in the one place, and let the reader of the code see why. What a report
may _claim_ is a separate matter and is not negotiable: a coarse report is fine,
a wrong one is not.

Pipeline: require walk (`#require "path"`, textual and flat) -> lexer -> layout
(insert scope markers, semicolons) -> parser -> elaborate -> check -> evaluate.

Evaluation is untyped and is not gated on the check: it runs on anything that
_parsed_, which is what lets an ill-typed program be run on purpose. So it reads
no types, and every shape the checker would have guaranteed is tested there
instead. Scope is the exception, and is not a type question -- where a name
resolves must have one answer, so `#tie` follows `#checkLetRec` phase for phase,
and reading an annotation's _presence_ is reading the tree rather than the type.
One diagnostic, at the first stuck term, and then nothing; there is no bad
_value_. Cells live in a `Heap` the evaluator owns, so allocation is a step this
project takes rather than one the host takes behind it. `evaluate.ts`'s header
has the reasoning, and the trace-not-tree argument that rules out recovery.

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

`never` is not a bad type and does not merge with one, but where a _shape_ is
demanded they stand aside the same way. `bad` is below and above everything, so
it answers every demand in every direction; `never` is only below and `unknown`
only above, so each answers the demands a cast moving that way makes, and an
invariant ask has no direction and so no extreme. The extreme case is the same
vacuous one `#subtype` answers on its first line, so the cast and the relation
agree by construction rather than by coincidence. Where a rule needs a shape and
there is none to read at all, `never` answers for the whole form.

Standing aside is decided where a head is _read_, which is after `#cast` has
settled which demand it is answering and before it takes the shape apart. A
missing part answers with whatever stood in the position, and a leaf goes to the
relation whole, which promotes on its own and knows `X <: X` -- so promoting in
front of the demand would answer for a variable bounded by an extreme with the
extreme, and throw the variable away.

Whether the demanded shape is still _built_ around the head that stood aside is
a different question, and the answer is not what the head means but what a
reader of the answer would otherwise supply. A cast's answer is related against
a type naming EVars in one place, `#applyCall`'s argument loop, and an
argument's pattern carries a missing part exactly where a type argument stands
-- so the parts a relation walks into are the EVar positions, and a shape is how
it reaches one. `#castFailed` and `#avoid` are two fillings of those same holes,
`TBad` and the extreme the position asks for.

So `upcast(bad, Cell[?])` is `Cell[<bad>]`: nothing else in the solver produces
a `<bad>`, so dropping it leaves the EVar unconstrained and a program already
blamed comes back with an ordinary type. `upcast(never, Cell[?])` is `never`,
because the `Cell[never]` it used to build planted at each position the very
extreme an unconstrained EVar reaches by itself -- a redundant constraint, paid
for with an arbitrary choice at every invariant argument and a report about it.
Checked rather than argued, across covariant, contravariant, invariant and
nested-invariant arguments.

`joinMany` still warns where it cannot name one answer principally: blaming the
program for what the checker could not name would be wrong, and `badUnder` takes
errors alone, so there is no `TBad` to hand back anyway.

A constructor is a function of its fields, so there is no constructor term form
and saturation follows from arity. The exception is a _value_ constructor:
`|
True` declares a value and `| True()` a function of no arguments, which the
declaration says rather than the arity implying it. `CtorDecl` therefore carries
the domain as _absent_ rather than empty for a bare name, and `isValue` is what
every later reading asks. See `CtorDecl`, and `constructorType` for why the
value form is refused on a parameterised datatype.

A constructor's name is also a _type_, claimed in the phase that claims datatype
names, so a field may mention `Cons[A]` in the same run it may mention
`List[A]`. Its entry is a datatype in every respect but declaring one: the
owner's _own_ parameter array, so arity and variance are the family's and
nothing is kept in step, and one case. So constructor names share the type
namespace, and two datatypes may no longer each declare a `Nil`.

First come, first served, and the case goes with the name: a constructor whose
name is held elsewhere is dropped, and so is a declaration that lost its own.
Nothing of a loser is elaborated, its fields having no names of its own to be
read against. `#settleCtorNames` decides all of it and has the reasons.

Two claim no type and lose nothing by it. A constructor of its datatype's own
name, where it is the only one: `datatype Box where | Box(Bool)` has one family
and one case either way, so the two names are the same type. And a _bare_ name,
which declares a value and so builds nothing, leaving no term that could have
the type. Which is why a declaration may not repeat a name is its own rule and
not a consequence of the namespace: half a declaration's names reach the type
table and half do not, so `| On` beside `| On()` would collide nowhere.

Every head carries its _family_, the datatype whose constructors its values are
among, and a datatype is its own -- reflexive rather than optional, so "the same
family" is one comparison rather than a case for whether there is one. It is
carried for the reason `params` is: a walk in `types.ts` can ask without knowing
declarations exist. `datatypes()` answers the declared ones alone, the entries
that are their own family, or variance would be inferred twice over the same
fields and every constructor term seeded twice.

A constructor type is _below_ its family: `Cons[A] <: List[A]`, derived rather
than declared, with no new runtime representation and the identity for a
coercion, a `Cons` value already being the `List` value. Depth is exactly one: a
family is a name and not a chain, so this is a comparison and never a search.

`headsLattice` is the one home for that hierarchy -- the head above two heads,
or below them. Upward, one family's constructors rise to it; downward there is
nothing to build, the constructors partitioning the family's values, so all that
can be answered is the one already below the other. `#latticeData` asks it, and
so does `headConforms`, the same question with its answer pinned. The relation
and the cast both go through `headConforms` -- two homes for that question is
how a coercion the relation allows becomes one the cast refuses.

Nothing rises at an invariant position. `Cell[Cons[A]]` is not `Cell[List[A]]`,
or a `Ref[List[A]]` could be `set!` a value the read side was promised could not
arrive -- which is the whole of why `headsLattice` answers nothing at `0`.

A constructor _application_ answers with the constructor's own type, so
`Cons(h, t)` is a `Cons` and rises only where something asks it to. A
constructor declared as a _value_ is outside that rule rather than excepted from
it: `| True` builds nothing and is a member of `Bool`, where `| Nil()` is a
function whose result is what it built -- so the declaration is where a
monomorphic datatype says whether its nullary cases are members or singletons. A
_sole_ constructor is no exception and answers with itself like any other:
collapsing it into its family would leave nothing inhabiting it, and a
one-constructor datatype is how a nominal subtype of one thing gets written. A
type argument solved from below is _not_ widened to match: a solution that
survived a `let` and not a call would be most of the precision gone, and the
ascription a staged argument then wants is `foldLeft(Nil)`'s. `docs/clti.md` has
that argument.

A pattern therefore names a constructor of the scrutinee's _own_ type, not of
its family: `#checkMatch` seeds `#remaining` from that type and resolves each
arm's name against it, so the two agree by construction. A `Nil` arm over a
`Cons[A]` is then the same mistake as a name nothing declares -- `Cons` is a
datatype with one case, and `Nil` is not it -- which leaves unreachability
saying one thing, that the arms above cover this one.

A domain position -- an arrow's parameter, or a constructor's field -- may carry
a name: `(x: A, B) -> C`, `| Box(flag: Bool, Bool)`. One syntax, so one rule,
and the rule is that the name is documentation: dropped at elaboration, scoping
over nothing until a dependent arrow gives it something to bind. See
`DomainType`.

A datatype's variance is inferred, not declared -- read off its constructor
fields by a fixed point over the whole declaration table, since two datatypes
may name each other. `docs/variance.md` has the walk, the lattice and the worked
examples. What matters everywhere else: a `TData` carries its declaration's
parameters by reference, so where an argument stands is a property of the type
rather than a lookup, and a walk in `types.ts` can ask without knowing
declarations exist. The parameters alone, never the whole declaration -- that
reaches constructor field types, and a `Type` that reached back into itself
would not be a finite value.

A mutable cell is a type _former_, `TRef`, not a datatype the checker declares
for itself: it has no constructors, nothing takes one apart, and its argument is
invariant for a reason no walk over constructor fields could find -- `get!`
reads where `set!` writes, and neither is a field. So the invariance is a
literal `0` in every walk, and `match` refuses a `Ref` along with every other
head that is no datatype. The _name_ `Ref` is ordinary, a transparent alias
seeded before the program's declarations, so "already declared" and the arity
message come from machinery that was already there. `docs/roadmap.md` has why
each of those beats the alternative that was tried.

`ref!`, `get!` and `set!` are ordinary term bindings, seeded outermost like the
constructors. A trailing `!` is part of an identifier to the lexer, which knows
no list of builtins; what reserves the spelling is that the parser refuses it
wherever a name is _bound_, so a bang name can only ever be used. That rule sits
beside the one about `_`, in `toBinder`, which is the one place a binding
position's rules are decided.

Walk types structurally. A function over types dispatches on the kind of each
node and recurses on what that kind contains; a whole-type equality test like
`alphaEq` is not a case, and standing one in front of the switch as a fast path
hides which cases it is answering for. Reach for it only where the structure
runs out -- at a leaf, or on one invariant argument, where there is nothing to
recurse into and nothing else to ask.

Local type inference. EVars arise from one place only: instantiating a
polymorphic callee at an application -- nothing else invents one. Constraints
are collected on both bounds and the whole batch is solved at the end of each
argument list, so no bound is read while its siblings are still moving. A
declared bound is an upper constraint like any other, and so is the expected
type when an application is checked rather than inferred, which is what lets
`Nil()` know what it is empty of. Which bound wins is decided by how the EVar
occurs in the result type, and where nothing can tell them apart the answer is
arbitrary rather than wrong, so it warns. `solveEVar`'s docblock has the case
analysis, with the staged `apply(True)(fn (y) -> y)` worked through; `#avoid`
has the avoidance rules, including why an interdependent sibling is refused
rather than approximated.

Exhaustion is the checker's limit, not the program's mistake: say so and answer
`TBad`, rather than falling back to an extreme, which would manufacture a bound
the author never wrote and then blame them for it.

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
anything between two of them closes the run. The parser folds a `def`'s
parameter lists into its `Abs` and its result type into a `FunType`, so a member
reaching the checker is a `DefItem` and the only question left is whether it has
an annotation. That question is the rule. A signature can be pushed before any
body is checked, so an annotated `def` is visible to its whole group; without
one there is nothing to push and the binding falls back to being a `let` --
visible once checked, and `unknown` inside its own body. `unknown` and not
`bad`: nothing is known of it yet, so it may be passed on and may not be called,
and the report belongs at each use rather than once at the push.

A `def`'s _parameters_, though, must always be annotated. Nothing else can
supply them: the body is inferred or checked against the def's own signature,
and never sits where a context would know them, so the advice a lambda gets --
use it where its parameter types are known -- names nothing an author could do.
An omission is therefore settled in the tree rather than asked about by every
reader of it: the parser stands a `MissingParamType` where the annotation would
be, and elaboration reports it once, at the binder, and answers `bad`. That is
the only node standing for something unwritten, and it is what keeps the rest
ordinary -- the group still sees the signature that was written, and the body is
still checked against a parameter that absorbs what is done with it. A signature
is also the one place parameter types are _written_: the parser strips them from
the `Abs` it folds, since elaborating them twice would double what they report.

The order follows: signatures, then the unannotated bodies -- each replacing its
own entry at its own level, so no `FVar` already elaborated goes stale -- then
the annotated bodies. What is _not_ there is a dependency graph. An SCC pass
would additionally order a non-recursive unannotated `def` before a sibling that
calls it, and adding one later only accepts more, so nothing here would be
rewritten for it.

Inferring a `match` joins its arms with LUB, so no arm is privileged by position
-- but only the arms a value can reach. One-level patterns keep the whole
analysis one set: what a value could still be on reaching the arm being checked,
which makes both unreachability and exhaustiveness questions about that set. An
unreachable arm is still checked and only its type dropped. See `#remaining`.

Some limitations:

- Type aliases cannot be recursive: they are transparent, so expansion would not
  terminate. Datatypes may be recursive, being nominal -- nothing unfolds a
  `TData`, so `List` and `Tree` cost the checker nothing.
- Pattern matching is only one-level, which keeps exhaustiveness a
  set-membership test
- Full Fsub subtyping is undecidable, so it runs on a fuel counter and can
  answer "gave up" as well as yes or no
