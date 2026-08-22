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
parameter type over abstract variables, then no EVar appears in any type that
flows anywhere. These all go:

- the `EVar` case of `Type`, and with it `#assertUnsolved`, `Context.apply`, and
  `expose`'s EVar handling
- `EVarMode`, and the whole `probe`/`collect` split -- `probe` exists only
  because `#join`/`#meet` walk types that might hold an EVar and must not
  record; with none in `Type` there is nothing to record
- the `interdependent` verdict and `noteReported`

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
type argument, so "walked it, found none, treat it as complete" needs one
validated cast at a chokepoint, the way `assertClosed` already works. Budget
exactly one.

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

Variance lives in the two casts, which find the nearest matching type in a
direction. Both are partial, and failing _is_ the error:

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
- **3. The casts.** Add `TMissing`, implement `upcast`/`downcast` beside
  `#join`/`#meet`, unit-tested directly. Nothing calls them.
- **4. Merge `check` and `infer`.** One procedure over a pattern. Abstraction
  gets its invariant and its error. Behavior changes here.
- **5. Application on missing parts.** Patterns replace EVars in parameter
  types; constraints move to step 4 above.
- **6. Delete.** `EVar` out of `Type`, and with it `EVarMode`, `probe`, `apply`,
  `#assertUnsolved`, `interdependent`. Constraints live in the context, indexed
  by binder position. Separate commit, so the deletion reads as one.

Steps 2 and 3 are additive and safe. Step 4 is the commitment point.

## Open

- Does avoidance survive? Probably, but for a narrower reason than today: the
  escaping variables it exists for are still introduced by binders, but the
  types that could carry them out are now all complete.
- Whether the casts can share one traversal with `#join`/`#meet` or only a
  skeleton. Settle it by writing them, not by deciding now.
