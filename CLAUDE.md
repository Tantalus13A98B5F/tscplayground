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

Local type inference. EVars arise from one place only: instantiating a
polymorphic callee at an application. Collect constraints on them and solve with
GLB/LUB at the end of each argument list.

A constraint picked up under a binder may mention variables that binder
introduced, which an EVar's solution must not. Avoidance removes them, widening
a lower bound and narrowing an upper one, swapping direction at every
contravariant position: a rigid variable goes to its declared bound or to
top/bottom, and an invariant `TData` argument cannot be touched at all, so the
whole type collapses. An unsolved EVar standing to the right is _interdependent_
and is rejected rather than approximated -- there is no bound to widen to, and
collapsing it would silently drop the constraint. Say so and ask for an
annotation.

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
