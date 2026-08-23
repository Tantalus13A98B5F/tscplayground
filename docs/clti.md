# Colored Local Type Inference

Both LTI and CLTI require that EVars do not depend on each other in constraints.
In fact, LTI does not even have EVars in the original paper: constraint
generation relates two _complete_ types, which is what keeps the problem
dependency-free and decidable.

We broke that. Arguments are checked against `openMany(param, evars)` -- a
parameter type holding EVars -- so an argument's own checking writes
constraints, and a nested application can produce one naming a sibling.
`#constrain`'s refusal and the `interdependent` verdict are the scar tissue, not
the disease.

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
EVar, `interdependent` and `noteReported`. Constraint collection is where an
EVar is still real, and those are what it needs.

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
  filling each missing part with the extreme for its polarity. This is the
  operation the note wanted separately for result patterns -- it is not
  separate, it is this one against top.
- both `TFun`: recurse, flipping direction at the parameters and at the bounds.
  Same flip as `#avoid`.
- both `TData`, same name: arguments are invariant, so a missing one takes `T`'s
  and a written one must be `#equiv` to it. Otherwise fail.
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
6. Select by polarity, unchanged.

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
`List[Int]` against `List[?]` join to `unknown` under invariance, and nothing
above `unknown` is a `List`, so it fails. Once datatype arguments carry variance
the join is `List[Bool ⊔ Int]` -- top, for want of a union, but a `List` of it
-- and the cast is a no-op. `match` needs no special case for a missing part; it
inherits whatever the join can do.

## Plan

- **0. Size the damage.** Done. Two genuine regressions across three tests --
  `f(fn (x) -> id(x), True)` and `both(True, fn (y) -> y)` in both orders.
  Everything else is unchanged, is a better message on an already-failing
  program, or tests `interdependent` and disappears with it.
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
  `interdependent` and `exhausted` are the relation declining to record, and the
  EVar it gave up on is marked as reported, so nothing downstream would. The
  cost step 0 measured is paid here and nowhere else: a bare lambda in the same
  argument list now asks for an annotation, in three tests. What it bought is
  `interdependent` becoming unreachable in practice --
  `both[A, B](True, fn (y: Bool) -> y)` was refused and now infers, since
  `?B := Bool` arrives already solved rather than as `?A <: ?B`.
- **6. `EVar` out of `Type`.** Done, but not as written above. "Constraints live
  in the context, indexed by binder position" was the wrong shape: an index is
  relative, so the relation would have had to carry a binder and a depth. A
  level is absolute, and type variables and EVars already share the level space
  -- so an EVar is simply an `FVar`, and the entry at that level says which kind
  it is. The node's `kind` was a second copy of an answer the context already
  held.

  What that costs: `FVar` no longer licenses promotion on sight. Exposure,
  `#join`'s standing-aside, `#meet`'s dual, `#avoid`'s widening, and
  `#castHead`'s covariant promotion all ask `#rigid` first, because an EVar has
  constraints where a rigid variable has a declared bound. Six places, all
  adjacent to a rule that already had to distinguish them.

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
  - **`interdependent` stays**, and earns it: constraint collection is exactly
    where a sibling or an escaping variable can still turn up.

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
  which types to open, where the polarity lies, what to relate. `#solveEVars`
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
  standing where anything looks. `Context.apply` stops recursing for the same
  reason -- a solution is built from bounds that cannot name an EVar, and there
  is no second batch to name.

  `setSolution`'s checks stay: those are about _scope_, which is avoidance's
  business and still subtle.
- **7. `#subsume`.** What is left of it relates two written types -- a bound
  against a bound, a type argument against its bound -- and those are casts
  against a complete pattern, once nothing else is left to break.

Steps 2 and 3 were additive and safe. Step 4 was the commitment point, and it
came through without moving the suite -- the behavior it commits to is not paid
for until step 5 puts patterns where the EVars are.

## Open

- Does avoidance survive? Probably, but for a narrower reason than today: the
  escaping variables it exists for are still introduced by binders, but the
  types that could carry them out are now all complete.
- Whether the casts can share one traversal with `#join`/`#meet` or only a
  skeleton. Settle it by writing them, not by deciding now.
