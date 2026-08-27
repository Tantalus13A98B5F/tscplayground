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
the answer principal. Occurring both ways, or inside an invariant `TData`
argument, neither bound is the answer by position, since widening either way
breaks the other. Bounded from one side only, there is still nothing to choose:
the other bound is the default extreme, which nobody recorded, and a demand
weighed against a default settles it silently -- this is what lets a staged
`apply(True)(fn (y) -> y)` infer its type argument. Bounded both ways by
equivalent types, likewise. Bounded both ways by types that differ, take the
lower for being the demand and _warn_: either bound would check, so nothing is
unsound, but neither is above the other and settling silently would hide that a
choice was made. A variable occurring nowhere in the result is not this case at
all: the solution goes into the result type, which has no place for it, so
nothing can tell the bounds apart and no choice is one. It takes the lower.

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
top/bottom, and an invariant `TData` argument cannot be touched at all, so the
whole type collapses. An unsolved EVar of the same batch is _interdependent_ and
is rejected rather than approximated -- there is no bound to widen to, and
collapsing it would silently drop the constraint. Say so and ask for an
annotation. In either direction, not only rightward: selection reads the result
type alone, so a sibling standing in a pending bound is a dependency it cannot
see. An EVar of an _enclosing_ batch is ordinary, and is how a bare lambda's
parameter gets its type.

Unannotated lambda parameters are never EVars -- a parameter's type comes from
annotations or from the checking context. In an argument list the parameter
binds to the callee's EVar directly, so a bare lambda works there as long as its
body does not need the parameter's _structure_; `match` on it does, and that is
where a _later_ parameter list is required, the way Scala's `foldLeft(z)(op)`
stages it. Currying gives this for free; there is no multi-list function type.

Inferring a `match` joins its arms with LUB, so no arm is privileged by
position.

Some limitations:

- Type aliases cannot be recursive: they are transparent, so expansion would not
  terminate. Datatypes may be recursive, being nominal -- nothing unfolds a
  `TData`, so `List` and `Tree` cost the checker nothing.
- Pattern matching is only one-level, which keeps exhaustiveness a
  set-membership test
- Full Fsub subtyping is undecidable, so it runs on a fuel counter and can
  answer "gave up" as well as yes or no
