# Staging one parameter list

A design model, for review before it is built. PR #13 on `stage-parameter-list`
is an earlier and coarser version; where it differs it is wrong, not merely
older.

## The problem

`#applyCall` checks every argument against a pattern built from
`callee.typeParams.map(() => TMissing)`, so an unannotated lambda parameter in
an argument list has nothing to read and always reports:

```
apply(fn (y) -> y, True)
      ^ cannot infer a type for y
```

A _second_ parameter list works, the first list's type parameters being solved
by then. That is why `foldr` is `(xs)(z)(op)`. This computes that staging from
the types instead of asking the author to write it.

## 1. What the planner reads

Walk the argument term and its parameter type **in parallel**, descending
through matched arrow/lambda pairs, stopping at any quantifier on either side.
Per argument:

|               |                                                                 |
| ------------- | --------------------------------------------------------------- |
| `requires(i)` | type parameters standing where the lambda left a parameter bare |
| `mentions(i)` | type parameters occurring anywhere in its parameter type        |
| `supplies(i)` | `mentions(i) \ requires(i)`                                     |
| `harvest(i)`  | `(position, annotation)` per parameter it did annotate          |

`supplies` is what the argument can say that it was not _told_. A bare lambda's
parameter type **is** the solution of what it required, so relating it back says
only `?A <: solution(A)`, which is vacuous. `requires` and `supplies` are
disjoint by construction, so no argument has an edge to itself.

Stopping at quantifiers keeps everything flat: no depth field, no scope push in
the planner. Anything reached sits at the callee's binder depth, so an
annotation there mentions only ambient scope. An annotation mentioning the
lambda's _own_ type parameter would constrain a variable about to leave scope,
which `#avoid` would discard anyway, so nothing is lost. `[C](C, A) -> A`
requires nothing and reports as it does today.

**Harvesting is out of scope for v1, and may stay out.** It means elaborating
the annotation in `#applyCall` and again in `#checkAbs`, doubling what it
reports, so `#checkAbs` would have to take the already-elaborated types -- what
the parser already does for a `def`, but only straightforward for the outermost
list.

Dropping it costs less than it sounds, and the distinction is worth keeping
straight: that an annotated parameter does not **block** is a fact about
`requires`, which excludes it, and that holds with or without harvesting. So
`fn (a: Bool, b) -> e` still waits on one type parameter rather than two. What
is given up is only the annotation _contributing a constraint_ before the lambda
is checked.

**Collecting `requires` correctly is the fiddly part**, and the effort is in the
co-walk rather than the idea. It descends wherever the term and the type agree
-- an `Abs` against a `TFun`, parameter by parameter, through curried arrows and
through quantifiers -- and stops only at a genuine disagreement: a body that is
not literally a lambda (a `Let` or a `Match` wrapping one), an arity mismatch, a
type that is no arrow at all. `mentions` and `supplies` need no co-walk, being
read off the type alone.

Every stop is **safe but imprecise**: recording no requirement means the
argument is not waited for, is checked with that position still missing, and
reports exactly as it does today. So the walk can be extended case by case
without any extension being load-bearing.

The hazard is the opposite one -- descending where the shapes do _not_
correspond, which records a requirement nothing will ever satisfy and stalls the
peel into a rejection. Agreement is the precondition; a quantifier is not a
disagreement.

## 2. Checking entities

No parameter is a checking entity. An annotation the walk reaches needs no scope
push; an unannotated parameter needs no elaboration. Parameters are _planning
data_. The entities are:

- a non-lambda argument,
- a whole lambda, processed atomically as `#checkAbs` does today,
- the call's **result type**, which checks nothing and only synthesizes.

Nothing interleaves, so `Context`'s stack discipline and `closeFrom(_, mark)`
are untouched. The result entity requires nothing, so it contributes in round
one -- which is what lets `Nil()` at `List[Bool]` know what it is empty of
whatever round its type parameter is solved in.

## 3. The graph

Nodes are arguments. One edge:

```
a → b   iff   supplies(a) ∩ (requires(b) \ solved) ≠ ∅
```

**The edge set is built once.** `\ solved` never fires: if `A ∈ supplies(a)` and
`A ∈ requires(b)` with `a` still waiting, `A` cannot have been solved, because
it is solved only when some ready `r` requires it -- and `r` ready means nothing
waiting supplies what `r` requires, which `a` does. So the graph is static and
the loop below is Kahn peeling, not a rebuild per round.

An argument of **in-degree zero** is one that nothing still waiting can tell
anything more. Its parameters are as constrained as they will ever be, so
solving them now gives up nothing. That is the entire ordering criterion.

It is deliberately not a measure of how constrained a parameter is, nor of
whether it has anything to solve from:

```
bar(f: (A) -> B, g: (B) -> C, w: A, x: B, y: B, z: B)
```

`B` carries three constraints and `A` one before either lambda is looked at, so
any rule that counts -- or that asks merely whether a parameter is constrainable
-- solves `B` first and checks `g`. Wrong: `f` supplies `B` too. `f → g`, `f`
has in-degree zero and `g` does not, so the order is solve `A`, check `f`, then
solve `B` with `f`'s body in hand.

## 4. The loop

```
state       solved ⊆ type parameters      (each solved once, never revised)
            checked ⊆ arguments           (each checked once)

build the graph once, then peel it

repeat
  ready = waiting arguments of in-degree 0
  if ready is empty and waiting is not:  give up ordering -- see 5
  solve   ⋃ requires(i) \ solved   over i ∈ ready
  check   each i ∈ ready against openMany(params[i], solved ?? TMissing)
  relate  each i ∈ ready against openMany(params[i], solved ?? evar)
until waiting is empty
solve   every type parameter still unsolved
```

Needs are solved **before** the arguments that demanded them are checked. An
argument requiring nothing has in-degree zero from the start, so every
non-lambda goes in round one and solves nothing. Nothing is solved for any other
reason: a type parameter no argument requires collects from the whole list and
is solved by the last line.

Well-founded, each quantity using only settled ones -- and with a static graph
the in-degrees come from removing the previous round's nodes rather than from
recomputing:

```
graph ─→ in-degree_k ─→ ready_k ─→ solve_k ─→ solved_k
                                └─→ checked_k ─→ in-degree_{k+1}
```

`fold[A,B](op: (A,B) -> B, z: B, l: List[A])` applied to `(λ, Z, xs)`:

```
requires   op {A,B}   z ∅     l ∅
supplies   op ∅       z {B}   l {A}

round 1    ready {z,l}   solve nothing, check, relate
round 2    ready {op}    solve {A,B}, check, relate
```

`op` is checked after `B` is solved, so its body has no vote on `B`. That is the
give-up, and it is the one a second written list makes.

## 5. Cycles are rejected, not broken

No argument of in-degree zero means every waiting argument is on or downstream
of a cycle. Then:

```
solve  every unsolved type parameter that has any constraint
check  every remaining argument
```

and stop ordering. "Any constraint" is the same test as above. Whatever still
has no type reports where it always did -- `cannot infer a type for x` -- so
this needs no diagnostic of its own and no cycle-finding: the absence of an
in-degree-zero node _is_ the detection.

The alternative is to break the cycle by seeding one argument. Rejected. Picking
which argument is a heuristic -- the leftmost, the leftmost on a cycle -- and
none of them is guaranteed to pick a cycle that is not itself downstream of
another. Breaking the wrong one solves its needs from fewer constraints than
were available, so the answer comes out too narrow and the _next_ argument fails
to conform: a report blaming the program for the checker's arbitrary choice. A
coarse report is fine and a wrong one is not, so the honest move is to say the
ordering ran out. Tarjan would make the choice sound; it is not worth a
condensation, stamping and postorder collection for the shapes it buys.

What this costs is real and small:

```
three[A, B](g: (A) -> B, h: (B) -> A, a: A)
```

`g` and `h` are a cycle. Round one takes `a`; round two stalls. `A` has `a`'s
constraint and is solved, `B` has none and stays missing, so `g` checks and `h`
reports. Breaking the cycle would have taken `B` from `g`'s body and checked
both. One report on a program that could have checked, fixed by one annotation.

`foo[A,B,C,D](x: A, y: B, e: (C) -> D, h: (A,B) -> C, f: (A) -> B, g: (B) -> A)`
stalls for the same reason, and `x` and `y` do not prevent it: `supplies(f)`
meets `requires(g)` and `supplies(g)` meets `requires(f)` however much else
supplies them.

## 6. EVars

**One batch, pushed once, before the first round, and popped after the last.**
An argument is related as soon as it is checked, recording constraints on every
parameter it names; those already solved are checked against, those still open
are constrained. So a parameter nobody requires keeps collecting from the whole
list, and no checked argument ever loses its vote on one solved later.

```
once      push one EVar per type parameter, in reverse of the solve order
          evar <: binder.bound                      (bounds are parallel)
          the result type, noting occurrences
per round as section 4, then pop what that round solved
once      solve the rest, pop
```

**The push order is not needed for soundness, and is worth having anyway.**
Bounds must be EVar-free whatever the order (below), so nothing depends on it.
What it buys is the property `withEVars` has today: it pops the scope _before_
solving, so a solution naming an entry is structurally impossible rather than
refused by a check. Keep every EVar pushed for the whole call and that becomes a
promise; push them so the first solved sits highest and each round can pop
exactly what it solved, and it stays a fact. The solve order is known upfront,
the planner being static.

**No bound may mention an EVar**, in any order. Solving `?A` whose bound names
an unsolved `?B` cannot answer closed, and `?A`'s choice comes from where it
occurs in the result type alone, blind to what is pending in `?B`. The rule is
independence, not ordering, and `addConstraint` already enforces it with
`isClosed(type, this.batch)` against the level the group begins at. With
EVar-free bounds any subset may be solved at any time, so staged solving needs
nothing new -- no push order, no second group, no zonking, no rejection in the
relation.

What keeps bounds EVar-free is that arguments are **checked** against
`solved ?? TMissing` and never against an EVar, so every actual is closed. The
result-type relation is the one place an EVar stands on the left, and `#avoid`
already answers for it. That same fact makes a nested application harmless: its
batch sits above ours, but nothing it relates can mention ours, because nothing
it checked could have seen one. `CLAUDE.md`'s "batches never nest" therefore
wants restating -- what it protects is now bought by where EVars are _visible_
rather than by when they exist.

**To verify when building this**: that no bound is ever recorded mentioning an
EVar once they live across argument checking (`addConstraint` throws rather than
letting one pass, which is the property to lean on); that `assertClosed` on the
call's result still holds; and that `#avoid` is asked where it is today.

## What is given up

An argument that has not been **checked** cannot constrain anything, so a
parameter solved before it is checked is settled without its vote. That is
`op`'s vote on `B`, and the price of answering `fold(op, z, l)` at all.

Plus, at a cycle, the ordering itself -- section 5.

Nothing else. An argument already checked keeps its say on every parameter it
names, whenever that parameter is solved.

The syntax stays. A written list is still the only way to stage what no argument
determines, and still where a type parameter's scope is decided. `foldr` keeps
its three lists; it no longer needs them.
