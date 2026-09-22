# Staging one parameter list

A reading guide to how a call's type arguments are ordered and answered. It
assumes no familiarity with the code; `src/core/batching.ts` and `#applyCall` in
`src/core/check.ts` are what it describes, and section 8 maps the two.

## 1. The problem

A lambda's unannotated parameter has no type of its own. It reads one from the
_pattern_ the lambda is checked against -- the expected type, with the parts
nobody has settled yet standing as `TMissing`, a hole meaning "nothing is known
here".

At a polymorphic call the callee's type parameters start out as exactly such
holes, because they are what the argument list is about to determine. So an
argument that is a bare lambda used to find nothing where its parameter's type
should be:

```
def apply[A, B](f: (A) -> B, x: A): B = f(x)

apply(fn (y) -> y, True)
          ^ cannot infer a type for y
```

even though the sibling `True` says perfectly well that `A` is `Bool`. A
_second_ parameter list worked, because by the time it is reached the first
list's type parameters have answers. That is why the list library used to write
`foldr(xs)(z)(op)` rather than `foldr(xs, z, op)`.

Staging computes that split from the types instead of asking the author to write
it.

## 2. The idea

Cut the argument list into **rounds**. Each round begins by answering the type
parameters that round's arguments are waiting on, and then checks those
arguments against the answers. `fold(op, z, l)` then works in one list: `z` and
`l` go first, `A` and `B` are answered from them, and `op` is checked against
real types.

Everything below is about one question -- _when is it safe to answer a type
parameter?_ -- and the answer is: when nothing that has yet to be checked could
still say anything about it.

## 3. Three sets per argument

All three are read off the tree before anything is checked, by walking each
argument term against its parameter type in parallel. Nothing is elaborated or
compared here; they are bookkeeping about which type parameters sit where.

**`requires(i)`** -- the type parameters standing where argument `i` left a
lambda parameter bare. These are what it must be _told_ before it can be checked
at all. An annotated parameter requires nothing, its type being written down;
`fn (a: Bool, b) -> e` waits on one position rather than two.

Where the walk reaches a lambda and the type has stopped short of it -- a lambda
at a bare `T` rather than at an arrow -- the lambda will be checked against
whatever `T` becomes. So if it leaves any parameter bare, it requires everything
that type names. That is what lets `set!(r, fn (n) -> S(n))` wait for `r`.

**`mentions(i)`** -- every type parameter occurring anywhere in its parameter
type.

**`supplies(i)` = `mentions(i) \ requires(i)`** -- what it can say that it was
not told.

That subtraction is the crux. A bare lambda's parameter type _is_ the answer it
was handed, so comparing it back against `A` afterwards only re-states the
answer and constrains nothing. A requirer contributes its **result** and nothing
else. Since `requires` and `supplies` are disjoint by construction, no argument
can supply what it is itself waiting for.

## 4. The order

Draw an edge `a → b` when `supplies(a)` meets `requires(b)`: "`a`, once checked,
could still say something `b` is waiting on."

> An argument of **in-degree zero** is one that nothing still waiting can tell
> anything more. Its type parameters are as constrained as they will ever be, so
> answering them now gives up nothing.

That is the entire criterion. It is deliberately **not** a measure of how
constrained a type parameter already is:

```
bar(f: (A) -> B, g: (B) -> C, w: A, x: B, y: B, z: B)
```

Before either lambda is looked at, `B` carries three constraints and `A` one.
Any rule that counted them -- or that merely asked whether a parameter has
_anything_ to answer from -- would answer `B` first and check `g`. That is
wrong, because `f` supplies `B` too. Here `supplies(f) = {B}` meets
`requires(g)`, so `f → g`: `f` has in-degree zero and `g` does not, and the
order is answer `A`, check `f`, then answer `B` with `f`'s body in hand.

**The edge set is built once.** It never needs recomputing against what has been
answered, because a type parameter is answered only when some in-degree- zero
argument requires it -- and an in-degree-zero argument has no waiting supplier
for anything it requires. So no edge can go stale while its source is still
waiting. What the loop does is peel in-degree-zero nodes off a fixed graph.

## 5. The loop

```
repeat
  ready = waiting arguments of in-degree 0
  if ready is empty and waiting is not:  the order has run out -- see 6
  answer  ⋃ requires(i)   over i ∈ ready        -- before checking them
  check   each i ∈ ready against the answers so far
  relate  each i ∈ ready against its parameter type
until nothing is waiting
answer  every type parameter still unanswered
```

Answering comes **before** checking, which is the point of the exercise: a bare
lambda cannot be checked until the positions it left bare have types.

An argument requiring nothing has in-degree zero from the start, so every
non-lambda argument goes in round one and causes no answers. A type parameter
that no argument requires is answered by none of them -- nothing is waiting on
it, so it collects constraints from the whole list and is answered by the last
line, which the plan writes as a final round that checks nothing.

_Relating_ is comparing the type an argument came back with against the
parameter type it was supposed to have. That comparison is where constraints on
type parameters are recorded: an argument of type `Bool` arriving at a position
written `A` is what says `A` is at least `Bool`.

It happens immediately after checking, so what an argument says reaches every
type parameter it names: those already answered as a check against the answer,
those still open as a constraint on it. Nothing an argument knows is lost
because of when it was checked.

Take `fold[A, B](op: (A, B) -> B, z: B, l: List[A])`, applied as
`fold(fn (a, b) -> S(b), Z, xs)` -- `op` bare, so it is waiting on both:

```
requires   op {A,B}   z ∅     l ∅
supplies   op ∅       z {B}   l {A}

round 1    ready {z,l}  -- nothing waiting supplies what they need, which is
                           nothing.  Answer nothing; check and relate them.
round 2    ready {op}   -- nothing waiting supplies A or B any more.
                           Answer {A,B}; check and relate op.
```

`op` is checked after `B` is answered, so its body has no vote on `B`. That is
the one thing staging gives up, and it is exactly what a second written list
gives up.

## 6. When the order runs out

No argument of in-degree zero means every argument left is on or downstream of a
cycle -- each waiting on something another waiting argument could still supply,
all the way round. The ordering has run out, and the response is to say so
rather than to force one:

```
answer  every unanswered type parameter that an argument already checked
        mentions -- those are the ones something has been said about
check   every remaining argument
```

Whatever still has no type reports where it always did --
`cannot infer a type
for x` -- so this needs no diagnostic of its own, and no
cycle-finding either: the absence of an in-degree-zero node _is_ the detection.

The alternative is to break the cycle by picking one argument to check first.
That is rejected. Every cheap way of picking is a heuristic, and none is
guaranteed to pick a cycle that is not itself downstream of another. Breaking
the wrong one answers its type parameters from fewer constraints than were
available, so the answer comes out too narrow and the _next_ argument fails to
conform -- a report blaming the program for a choice the checker made. A coarse
report is fine; a wrong one is not.

What it costs is small and real:

```
three[A, B](g: (A) -> B, h: (B) -> A, a: A)
```

`g` and `h` are a cycle. Round one takes `a`. Round two has no in-degree-zero
argument, so: `A` has `a`'s constraint and is answered, `B` has none and stays
open, `g` checks and `h` reports. Breaking the cycle would have taken `B` from
`g`'s body and checked both.

## 7. An answer nobody asked for is not an answer

A type parameter that **nothing** constrained is answered -- something has to
fill the call's result type -- but that answer is not handed to the arguments as
what their positions _are_. Those stay `TMissing`, and the parameter that could
not be typed says so:

```
one[A, B](f: (A) -> B)   applied to   fn (y) -> y
                                          ^ cannot infer a type for y
```

`A` stands only where the lambda left a parameter bare, so nothing determines
it. Answering `y` from a choice the checker made would be inventing a type;
reporting "nothing constrained `A`" instead would be the same mistake under a
name the author never wrote. The report goes where an annotation would go.

Handing the choice over would not make the argument fail instead. The choice at
a parameter position is `unknown`, and a lambda that only passes `y` along
checks at it: `one(fn (y) -> y)` would be accepted, silently, as
`unknown -> unknown`. One that does use `y` is refused, but by a report about
the invented type -- `cannot match on unknown` for a `match` on `y` -- where the
fix is an annotation the report does not mention.

This holds in every round, and it is also the backstop for section 6: the
planner picks what to answer there by what an already-checked argument
_mentions_, which is a guess that something was said; where nothing actually
was, this rule keeps that answer from reaching any argument.

## 8. Where the code is

|                                                             |                                                                                                                                                                                                                                             |
| ----------------------------------------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| `src/core/batching.ts`                                      | the planner: everything in sections 3 to 6, and nothing else. Pure, reads only the tree and the callee's type.                                                                                                                              |
| `planStages(params, args, typeParamCount)`                  | the whole plan: the rounds in order, the last answering what no argument required and checking nothing.                                                                                                                                     |
| `Round = { solve, check }`                                  | solve these type parameters, **then** check these arguments. `solve` is indices into the callee's binders; `check` is the arguments themselves.                                                                                             |
| `StagedArg = { arg, param, mentions, requires, supplies }`  | one argument, the parameter type it is checked at, and its three sets from section 3.                                                                                                                                                       |
| `collectVars(type, depth, into)`                            | the type parameters a type names, counted from `depth` binders in.                                                                                                                                                                          |
| `collectRequired(arg, param, depth, into)`                  | the co-walk of section 3. It mirrors `#checkAbs` -- the rule that checks a lambda against an expected type -- so that it waits for exactly what that rule would otherwise fail to find.                                                     |
| `src/core/subtype.ts`                                       |                                                                                                                                                                                                                                             |
| `Subtyper.withStagedEVars(hints, orderedIndices, at, body)` | owns the EVars' lifetime -- section 9. Takes the binders' hints and the order they will be solved in; `body` receives the variables in binder order and a `solveNext(count)`. The one place solve order is translated back to binder order. |
| `SolvedTypeArg = { index, type, constrained }`              | one answer, the binder it answers, and whether anything said so. Section 7 is this flag.                                                                                                                                                    |
| `src/core/check.ts`                                         |                                                                                                                                                                                                                                             |
| `#applyCall`                                                | the rule for an application. Runs the plan.                                                                                                                                                                                                 |

`#applyCall` reads, in order: infer the callee; settle an arity mismatch on its
own; plan the rounds; then inside `withStagedEVars`, handed the rounds' `solve`
lists end to end as the order, record the declared bounds and the call's
expected type, and run the rounds. Everything it holds is in binder order. It
keeps two arrays. `solved` starts as the EVars and takes each answer as it
comes, so it is what a _relation_ opens a parameter type with, and by the end it
is the answers alone, which fill the result type. `told` starts as all
`TMissing` and takes only the answers that were constrained, so it is what
arguments are checked against.

## 9. The type variables, and how long they live

A type parameter being solved for is an **EVar**: a placeholder that collects
lower and upper bounds while arguments are related to their parameter types, and
is then resolved to one type.

EVars live in the same scope stack as ordinary variables, so pushing one makes
it visible and popping it makes it gone. All of a call's EVars are pushed
**once**, before the first round, and live for the whole argument list. Not one
batch per round -- a round answers only what the next arguments demand, and an
argument checked in round one must keep its say on a type parameter answered in
round three.

They are pushed in **reverse** of the order they will be answered in, so the
next to be answered is always on top and is popped the moment it is. The
property that buys: no type outside `withStagedEVars` ever names an EVar, and
that stays _structural_ -- an answer is computed with its own variable already
out of scope -- rather than becoming a promise some later check has to keep.

Three invariants hold this together:

- **No bound ever mentions an EVar.** `EVarEntry.addConstraint` throws if one
  does. It is what lets any subset be answered at any time: an answer can never
  be waiting on another answer. It is also why the call's EVars are one batch
  and not one per round: the check counts from where the batch was pushed, so
  nested per-round batches would let an early round's bound name a later round's
  variable, and carry it out when answered.
- **Arguments are checked against answers or `TMissing`, never against an
  EVar.** So every type an argument comes back with is EVar-free, and every
  bound recorded from one is too. It is also why a nested call is harmless: its
  own variables sit above ours on the stack, but nothing it relates can mention
  ours, because nothing it checked could have seen one.
- **Every type parameter is answered exactly once.** Where its lower and upper
  bounds cannot be told apart, resolving one is an arbitrary pick and warns;
  answering once means that warning cannot be repeated for the same parameter.
  It is also what lets the call's result type be built by substitution at the
  end.

The call's **result type** is a contributor belonging to no round: it demands
nothing and says whatever the call's context says, so it is related once at the
start. That is what lets `Nil()` checked against `List[Bool]` know what it is
empty of, whichever round settles the type parameter.

## 10. Not in this implementation

**Parameter annotations as early constraints.** An annotated lambda parameter
stops the argument _waiting_ on that position -- that is `requires`, and it
works today. What it does not do is _contribute_ its type before the lambda is
checked. Doing so means elaborating the annotation once in `#applyCall` and
again in `#checkAbs`, so everything it reports would be reported twice; the fix
is for `#checkAbs` to accept already-elaborated parameter types, which the
parser already arranges for a `def`. It is straightforward only for the
outermost parameter list.

**A sound choice of where to break a cycle.** Section 6 rejects instead. A
condensation into strongly connected components would make the choice sound and
recover programs like `three` above; it was judged not worth the machinery for
the shapes it buys.

**The co-walk stops at anything but a lambda.** `collectRequired` descends
through curried arrows and through quantifiers, but a body that is not literally
a lambda -- one wrapped in a `let` or a `match` -- ends the walk, so a lambda
nested inside those is not waited for.

That last one degrades gently, and so would any further gap in the walk: no
requirement is recorded, the argument is not waited for, it is checked with the
position still missing, and it reports exactly as it did before staging existed.
**Stopping the walk early is always safe**, which is what makes it extensible a
case at a time. The unsafe direction is the opposite -- descending where the
term and the type do _not_ correspond, which records a requirement nothing will
ever satisfy and turns an ordinary call into a rejected one. Requiring what a
lambda stands at when the type stops short is not that: without it, the lambda
is checked against a missing part and its bare parameter reports, so only a call
that already reported is changed.

The first two are different in kind. A missing annotation constraint costs
precision that nothing reports; rejecting a cycle costs a program that a sound
choice would have accepted. Both are visible as reports rather than as silently
wrong answers.

## 11. What is given up for good

An argument that has not been **checked** cannot constrain anything, so a type
parameter answered before it is checked is settled without its vote. That is
`op`'s vote on `B` in section 5 -- the price of answering `fold(op, z, l)` at
all, and the same price a second written list pays.

Nothing else. An argument already checked keeps its say on every type parameter
it names, whenever that parameter is answered.

The syntax stays: a written parameter list is still the only way to stage what
no argument in the list determines, and still where a type parameter's scope is
decided. The list library no longer writes them for folding: `foldr` is one
list.
