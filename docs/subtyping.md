# Coercive subtyping between datatypes

A design, not an implementation. Datatypes are nominal and today no two of them
relate: `#relateData` demands name equality and there is no declaration form
that says otherwise. This is what it would take to add one.

    datatype List[A] where
    | Nil
    | Cons(A, List[A])

    datatype NonEmpty[A] <: List[A] where
    | One(x: A)              -> Cons(x, Nil)
    | More(x: A, r: List[A]) -> Cons(x, r)

Every `NonEmpty` presents as a `List`, so `head : NonEmpty[A] -> A` is total and
every existing `List` function accepts a `NonEmpty` unchanged.

## Why

**Refinement.** A subgrammar that embeds into a full one is the case ML users
lack and reach for GADTs to get. The sharpest instance is in this repo:
`TypePattern` and `Type` are one grammar where the second has no `TMissing`, and
`subtype.ts` is organised around keeping them apart by hand --
`completePattern`, `completeLeafPattern`, the `Extract<TypePattern, ...>`
parameter types. In a self-hosted checker that is
`datatype Type <: TypePattern`.

**It makes Fsub's bounds inhabited.** What can a bound say today? `Bool` is a
datatype and no datatype relates to another, so the subtypes of `Bool` are
`Bool`, `never`, `<bad>` and variables bounded by those; `[A <: Bool]` is very
nearly an equation, and every non-vacuous bound in the language is `unknown`.
Meanwhile the file carries full Fsub -- `#relateFun` comparing bounds
contravariantly, the undecidability that follows, `FUEL`, `FuelExhausted`, the
three-valued `Verdict`, and every docblock explaining why exhaustion is not a
mismatch. That is the most expensive apparatus here, built for a quantifier
whose bounds have almost nothing to range over. This is what would populate it.

**Not** unions. The join `clti.md` complains about is `List[Bool] ⊔ List[Int]`,
an _argument_-level loss; a hierarchy gives those no common ancestor. Head-level
joins do improve -- two arms of different datatypes join to their least common
ancestor rather than `unknown` -- but that is a small win and not the one the
common-cause section asks for.

## Shape of the feature

- **Single inheritance.** With several bases the least common ancestor for a
  join is not unique, and the choice would be arbitrary or need intersections.
- **No downcast.** Passing a `Foo` where a `Bar` is wanted is one-way. This is
  what keeps exhaustiveness a set-membership test: a value of type `Bar` is
  matched over `Bar`'s constructors and nothing else, where Scala's `Animal`
  match must consider every case class under it. Give downcasting up and
  `#checkMatch` and `#remaining` do not change at all.
- **Narrowing, not extension.** Every `Foo` presents as some `Bar`, so this
  cannot add cases to a datatype. No expression problem.

## Semantics: eager, with the chain in the value

Constructing `One(v)` also evaluates its super constructor and stores the
resulting `Cons` value alongside, recursively up the chain. A match on an
ancestor walks the stored chain; nothing is recomputed.

The alternative -- coerce lazily at each match -- was rejected. It runs the body
once per inspection, so a `ref!` in a super constructor allocates a fresh cell
every time a value is looked at as a `List`, and no part of the program text
says that a match allocates.

Eager is safe here for a reason specific to this language: **datatype fields are
immutable.** The only mutation is through `Ref`, and a super constructor that
passes a cell through passes the same cell, so a `MutList[A] <: List[Ref[Int]]`
sees writes through both views. A materialised parent image can never go stale,
because the fields it was computed from never change. This is why the same
layout is wrong in an OO language and right here.

Costs: every construction pays for its ancestor chain whether or not anything
ever views it as a `Bar`, and every value carries it. Right side of the trade
for hierarchies of depth one or two.

Super constructor bodies may diverge, and that is ordinary -- the language has
`def`, and the divergence happens at a construction the author wrote, exactly as
Scala permits `class Foo extends Bar(new Foo)`. What must _not_ be able to
diverge is the part the author did not write, which is what the tail rule below
is for.

## The tail rule

A super constructor body is an ordinary term with one restriction: **every tail
position is a constructor of the declared super type**, named. Tails distribute
through `let` and `match`, so

    | Two(x: A)  -> let y = f x; Cons(x, y)
    | Some(x: A) -> match p x with
                    | True  -> Cons(x, Nil())
                    | False -> Nil()

are both well-formed and each branch is pinned on its own. Arguments are
arbitrary terms and may diverge like any expression.

Unqualified, a tail name resolves against **the declared super type**, not the
term scope, and is _rewritten to its qualified form_ by `resolveSuperCtorTails`,
between parsing and everything else. That resolution needs no types, so it can
happen before either consumer and both read the rewritten tree -- which is the
point of doing it rather than stating the rule twice. Left unrewritten, the
checker would resolve `Cons` against the super type while the evaluator resolved
it through a shadowable flat namespace, and the two would disagree exactly when
a `let` or a later datatype reused the name. A tail already written `List.Cons`
is left alone; one written `Other.mk` is refused.

Why the rule exists: without it a tail can hand back a value of a _sibling_
subtype, whose own super constructor then runs, and two such declarations loop
at construction with a perfectly acyclic `<:`. Scala cannot write this because
`extends Bar(args)` names `Bar` structurally; the tail rule is that, recovered
without giving up computation or branching.

Four earlier formulations were wrong and are recorded so they are not retried: a
body merely _typed_ at the super type (subsumption unpins the head -- a `Baz`
value has type `Bar`), a tail _position_ over arbitrary terms with no rewrite
(an application in tail position has no static head), a tail _name_ left to
resolve in the term scope (a `let` shadows it), and no body at all but a
constructor name and an argument list, which pins the head by giving up the
`let` and the `match` above.

## What the evaluator reads

Evaluation reads no types. It may read **name resolution** recorded in the tree
by an earlier phase, and it does so in two places -- one that costs nothing and
one that is the exception this feature had to buy.

The super constructor tail costs nothing: elaboration rewrites it, needs no
types to do so, and hands both consumers one tree. Nothing about the invariant
changes.

`Match.datatype` is the exception. **The checker writes it.** A pattern name
alone does not say which datatype it belongs to once a value presents as
another, and two datatypes along one chain may spell a constructor the same --
`Leaf <: Mid <: Top`, all three with a `Same`, is a program where an untyped
guess is wrong rather than arbitrary. Either the author says which, or the
checker records what it already worked out; demanding it of the author would be
demanding bookkeeping, which is the thing `def`'s annotation rule exists to
avoid.

The half worth protecting is untouched: an ill-typed program still runs, and
runs meaningfully. Where the field is absent -- unchecked, or checking failed
here -- evaluation falls back to the nearest datatype in the value's own chain
admitting the pattern name: exact wherever a chain spells no constructor twice,
and a tiebreak where it does. Syntactic rewriting as a resolution device is
ordinary; Koka uses it for overload resolution.

## Names

Two problems, and only one of them turned out to need a mechanism. This follows
F#'s default: case names go into the enclosing scope, collisions are permitted,
later shadows earlier, and a qualified form always reaches past it.

**Term position.** The evaluator holds only a name and a table of constructors
keyed by it. So a name in term position must determine a constructor with no
types. Plain `bar` stays last-wins, and `Foo.bar` is added -- resolvable from
scope and declarations alone, and never shadowed, because the parser refuses the
spelling at every position that _binds_. That also retires the wart at
`seedConstructors`, where an earlier same-named constructor was unreachable.

`Foo.bar` is one identifier to the lexer, the way `set!` is, and the two are
refused together by one rule: each names something only seeding produces, so
writing either at a binder would redeclare a name its owner already holds. Both
phases build the string with `qualifiedCtor`, which is why they agree on what it
names where they agree on a plain name only by coincidence of order.

_Not_ an omittable prefix. Lean's `.bar` resolves against the expected type, and
the expected type is exactly what the evaluator does not have.

**Pattern position.** A pattern head stays a plain constructor name, resolved
against the scrutinee's datatype -- statically, and at runtime against the
value's own or the nearest thing it presents as. The two agree because there is
no downcast: a scrutinee has exactly one static datatype, so viewing a value as
its super type is written down, and the runtime walk finds that same datatype.

Where a chain spells one constructor twice, the walk has no way to tell which
was meant and takes the nearer. That is the case a `match inst as Foo with`
would settle, and the only thing here still waiting for one.

## Declaration processing

Three stages, the third of which is checking rather than elaboration:

1. **Names.** Datatype names and their parameters, as now. Additionally: resolve
   each `<: Base` and refuse a super type that is not a datatype after alias
   expansion (`Ref` is a transparent alias to a former and has no constructors).

   Resolved _here_, in source order, so **a super type names a datatype declared
   earlier** -- and that is where the cycle refusal comes from, there being no
   separate check to write. The alias rule at a different table: ordering rules
   recursion out by construction.

   An **alias is accepted**, expanding to the datatype it names. Nothing
   downstream reads the spelling: the tails are rewritten here, against the
   elaborated super type, and the subtyper walks the table. So `<: Alias` and
   `<: Box` reach the same entry.

   The cost is that a super type cannot mention a datatype declared below it, in
   its head or in its arguments, so `datatype Rose <: Tree[Rose]` is out. Fields
   are unaffected: they are elaborated in stage 2 against the complete table.
2. **Constructors**, as now, plus each super constructor: is one written exactly
   where there is a super type, and, if so, which datatype does each of its
   tails name? The rewrite lives here because it takes the super type's
   _identity_, which stage 1 resolved; whether the name it produces exists, at
   what arity, is stage 3's.
3. **Super constructor bodies**, checked as terms against the super type
   instantiated at this datatype's parameters, after every constructor is
   seeded. The scope is those parameters, by name, and this constructor's fields
   under the names the declaration gave them -- the first thing a `DomainType`'s
   name has ever bound. Seeding first is what lets two datatypes' super
   constructors name each other's constructors with no order to arrange.

## Variance

The super type is one more occurrence in the existing fixed point,
**covariant**. Necessary because transitivity requires `Foo[A] <: Foo[A']` to
imply the bases relate; sufficient because a parameter occurring contravariantly
in the super type is driven to invariant by the meet, and an invariant parameter
makes the obligation vacuous. Mutual recursion through bases is the same fixed
point that already handles two datatypes naming each other. `docs/variance.md`
gains one occurrence source and no new rule.

## The ordinal beside the super type

`DatatypeInfo` carries an `ordinal`, stamped by `addDatatype` from the table's
own size. It is `Level` at a different table: a declaration's identity is its
position, so the next one is the size and no allocator is needed, and the one
fact read off it is the one `Level` gives -- **a super type may name only a
datatype declared before it**, so an ordinal strictly decreases along a chain.

_Not_ a depth in the chain, which was tried first and is worse for a reason
worth keeping: two chains have nothing to say to each other about depth, so
every comparison across them reads as meaning something it does not. An ordinal
is total. It is also assigned at registration and never recomputed, where a
depth had to be written together with the super type it counted and could go
stale behind it.

There is no cycle check, and no method that records a super type after the fact.
A super type is elaborated in pass 1 against the table as it stands, so it names
an entry already in it, so its ordinal is below the one stamped a moment later.
The alias rule, at a different table: a datatype naming itself is an
`unknown type` rather than an infinite chain, exactly as `#elaborateAlias`
already arranged for aliases.

Three readers:

- `#riseTo` terminates by the ordinal alone rather than by trusting that cycles
  were refused, and refuses in **O(1)** where the target is declared no earlier
  than where the walk stands -- the common case of two unrelated datatypes, and
  the one `#relateData` hits most.
- `#leastCommonData` merges the two chains: whichever side stands later is the
  one that climbs. Their common ancestors are declared before both, so nothing
  it steps past could have been one, which is what makes the first agreement the
  least. Without an index the only way to the least is to try each of one chain
  against all of the other, instantiating a super type at every try.
- `#latticeData`'s meet asks the relation once instead of twice: only the
  later-declared of two can be the one presenting as the other.

## Where the super type is read from

`DatatypeInfo` gains `superType?: Type`, closed over the declaration's
parameters exactly as `DataCtorInfo.fields` are, with `baseAt(datatype, args)`
beside `ctorFieldsAt` to instantiate it. `DataHead` does not change and neither
does `TData`; `Subtyper` reads the super type through `context.declarations`,
which it holds already.

The alternative was to carry the super type on the head, where a type walk would
reach it. Four reasons against, the first decisive:

- **A super type's `BVar`s belong to the declaration's binder, not the ambient
  one.** Every structural walk threads a `depth` -- `openWith`, `closeAt`,
  `isClosed`, `noteField` -- and one that descended into a super type sitting in
  a node would read those indices against a binder it never entered. A
  constructor's fields are closed the same way and are deliberately unreachable
  from a `Type` for exactly this reason. types.ts's opening line names the
  invariant: only `open*` and `close*` touch index arithmetic.
- **A field every walk must skip is not part of the node's meaning.** `params`
  is on the node because every walk reads it -- variance is a property of a
  position, and every walk descends into positions. A super type would be read
  at three sites in one file and skipped everywhere else.
- **It is the question `#promote` already asks.** A rigid variable's bound is
  not on the `FVar` either; it is in the context, and reading it is the step
  where structure runs out and one type stands aside for another. A datatype's
  super type is that same step at a different head, so the rule about reaching
  past structure only where it runs out is satisfied rather than bent.
- **No plumbing.** `Context.declarations` is public and `Subtyper` holds a
  `Context`.

The cost is one sentence in `#latticeData`'s docblock, which says today that
heads not orderable by looking at them settle for top or bottom. After this a
lookup can order them. That sentence was about structure, and will say so.

## Checker changes, by site

Landed. Two primitives, `#superTypeOf` and `#riseTo`, and three sites using
them:

- `#relateData` -- name equality still, but the left may climb to a name that
  agrees. Climbing only where the position moves upward, and that one test
  covers equivalence too: at `0` the left stays put, so two datatypes are the
  same only when they are the same one.
- `#castHead` -- a fourth way to stand aside, beside promoting a variable,
  taking a bad type's shape, and lifting an extreme. After the extreme tests,
  which a risen head never triggers, so the two never contend.
- `#latticeData` -- joining rises both sides to their least common ancestor and
  goes on argumentwise, which is the existing walk split out as
  `#latticeDataArgs`. Meeting cannot do the same, a child's parameters not being
  recoverable from its super type, so it asks the relation which side already
  sits under the other -- what `#meet` already says of a variable.
- `#eqtype`, `#checkMatch`, `#remaining`, avoidance -- unchanged.

`Extract<Type, { kind: "TData" }>` became `DataType` on the way: the climb goes
datatype to datatype and never leaves the kind, and a pair of them is a return
type that had to be spelled.

## Evaluator changes

- `VData` carries `superType`, what the value presents as, built by `#construct`
  at the moment the value is made and never again.
- `#coerce` evaluates the super constructor body over a scope binding this
  constructor's fields by name -- the first consumer of a domain name, a
  position `DomainType` describes as "scoping over nothing until a dependent
  arrow gives it something to bind". It reads no types and needs none: which
  constructor each tail names was settled on the tree. The two recur through
  each other, so a chain is built whole; it terminates because a super type is
  declared before the datatype presenting as it.
- `#viewAs` walks that chain to the datatype the match names, and binds against
  what it finds -- falling back to the nearest one admitting the pattern's name
  where the match names none.
- `#ctors` became a list rather than a map keyed by name, a name having stopped
  being an identity once `Foo.bar` can reach past a shadowing `bar`.
- Duplicate datatype names are now first-wins here as they are in the checker's
  table -- reading the parse tree instead of that table is what makes an
  ill-typed program runnable, and is no reason to answer differently.

Most of the budget for this feature was here, not in `subtype.ts`, where the
relation is a few sites. The evaluator is untyped by design, so every name the
checker resolves with types in hand has to be resolvable here from scope and
declarations alone -- and that constraint is what decided eager construction,
the chain in the value, the tail rule and its rewrite, and the refusal of an
omittable prefix.

## Order of work

Four landings, each green on its own. The feature is unreachable from source
until the third.

**1. The relation, and the declaration form's head.** _Landed._
`DatatypeInfo.superType`, the three sites in `subtype.ts`, and one more
occurrence in the variance fixed point. No syntax, so no program can declare a
super type and nothing can reach a value whose ancestor image does not exist;
tests fill a `Declarations` table directly, which is what made it separable at
all.

Two things came out differently. There is no `baseAt` beside `ctorFieldsAt`:
only `#superTypeOf` instantiates a super type, and one caller is not a helper.
And `noteField` became `noteOccurrencesIn`, the old name having started to lie
at the call site that hands it a super type.

**2. Names.** _Landed._ `List.Cons` is one identifier to the lexer, the way
`set!` is, and `requirePlainName` refuses both at every position that binds --
one rule, since each names something only seeding produces. Both phases seed
plainly and qualified, sharing `qualifiedCtor` so they build the same string,
which is what makes them agree.

`match xs as List with` landed too, and is not optional in the way it first
looked. Viewing a value as its super type is indeed an annotation the author
writes on the _scrutinee_ -- `let xs : List = One(x)` -- but that is a type, and
the evaluator has none. Without the datatype on the tree, a `Leaf <: Mid <: Top`
whose three datatypes all declare a `Same` binds the wrong fields in a
well-typed program.

**3. The super constructors.** _Landed._ `-> <term>` in the parser,
`resolveSuperCtorTails` called from elaboration, presence checked at the
declaration, bodies checked by `#checkSuperCtors`, and the evaluator building
the image at construction and walking it at a match.

`<: Base` landed earlier, with stage 1, because writing the table's side first
had `Declarations` grow a `presentAs` that existed only for want of a frontend.

**4. What is left.** Nothing named. The claims that nothing else changed:
`#eqtype`, `#checkMatch`, `#remaining` and avoidance are listed above as
untouched, and stayed so -- a scrutinee still has exactly one datatype because
there is no downcast, which is what the evaluator tests lean on when they
annotate.
