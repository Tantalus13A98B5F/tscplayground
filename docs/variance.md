# Inferring datatype variance

Datatype arguments used to be invariant by fiat: `#cast` passed a literal `0`
per argument, and `#subtype`, `#eqtype`, `#join` and `#meet` all reached for an
`#eqtypeArgs`. This is the pass that replaced that literal with something read
off the declaration -- the last pass of `elaborateDeclarations`, run once every
datatype's constructors are in, writing into `ParamInfo.variance` and read back
through `Declarations.argVariance`.

Written as a design note before any of it existed, and kept as the description
of what was built; where the two would differ, the note has been brought to the
code.

Inferred, not declared. Checking a written `+A` needs the same walk over the
constructor fields that inferring it does, so the inference is the part we need
either way and an annotation would be a thin layer on top. The usual reason to
demand the annotation is separate compilation -- a library's variance is part of
its published interface -- and the require walk is textual and flat, so we have
no library boundary to protect.

## 1. The lattice is the one we already have

Four points, ordered by permissiveness:

            bivariant
           /         \
    covariant     contravariant
           \         /
            invariant

This is `EVarEntry`'s pair of flags, read as a lattice: both false is bivariant
(occurs nowhere), both true is invariant (occurs both ways), and merging is `||`
componentwise. Its docblock in `context.ts` already names the two properties
that make it right -- "occurring covariantly _and_ contravariantly is what
leaves neither bound free to widen, and there is no variance for occurring
nowhere."

So the existing variance/position separation stays exactly as it is. **Variance
is a direction of travel**, three-state, composed by `flip`, never merged --
what a walk carries. **Position is an accumulated record**, four-state, merged
and never composed -- what the walk writes down. The inference accumulates
positions; the checker reads variances.

Reading a position back as a `Variance` has to answer for bivariance, which has
no direction. It collapses to covariant: sound, incomplete only for a parameter
no program can observe, and it keeps `Variance = -1 | 0 | 1` and `flip` as
negation. See §7 for what is said about it instead.

## 2. The walk

One walk per constructor field, entered at variance `+1` -- a field is projected
by `match` and never assigned, which is why there is no contravariant entry and
why mutability arrives as a builtin `Ref` rather than as a declared datatype the
walk would have to model. `Ref` is a type former of its own -- `TRef`, not a
`TData` -- so this pass has nothing to compute for it and nothing to leave out:
the walk has a `TRef` case that recurses at `0`, and a datatype holding a cell
comes out invariant with no table entry involved. Had it been a datatype
instead, optimism would have been exactly the unsound kind: no constructor field
of it mentions a `T`, so the walk would find nothing and conclude that nothing
observes one.

Carrying a `Variance` end to end:

- a parameter `BVar j` at direction `d`: merge `d` into position `j` -- the same
  two-line rule `EVarEntry.noteOccurrence` applies, over the same pair of flags.
- `S -> T` at `d`: recurse into `S` at `flip(d)`, into `T` at `d`, and into each
  type parameter's bound at `flip(d)`.
- `TData(Foo, args)` at `d`: for each argument, branch on `Foo`'s current
  position for that parameter --

      covariant     -> recurse at d
      contravariant -> recurse at flip(d)
      invariant     -> recurse at 0
      bivariant     -> do not recurse

- a leaf -- `unknown`, `never`, `<bad>`, `FVar`: nothing to record.

The `TData` branch is why no operation composes two positions and why positions
never need `flip`. The fourth arm prunes rather than composing: a parameter
nothing observes contributes nothing, so the sub-walk is dropped. Checked
against the general position-composition on the cases that could disagree
(contravariant into contravariant, anything into invariant, invariant into
bivariant); they agree everywhere, so the branch is exact and not an
approximation.

Aliases are not a case. They are transparent and expanded during elaboration, so
by the time `ctors` is walked no field holds one.

The **checker** side of this is not the same walk and does not want the
four-point branch. It carries a `Variance` into a `TData` and composes with what
the table says, which is multiplication -- `composeVariance`, of which `flip` is
the case that composes with `-1`, and `0` absorbs. Bivariance never reaches it,
having collapsed at the read-back. See §8 for where it is read.

## 3. Two recursions, one criterion

They are easy to confuse and only one needs a stopping rule.

**The walk over a field type terminates structurally.** Reaching `Foo[X]` reads
the table and recurses into `X`, a proper subterm -- it does _not_ unfold `Foo`.
That is the same property the whole checker rests on ("nothing unfolds a
`TData`, so `List` and `Tree` cost the checker nothing"), and it survives here.
No fuel, no cycle check, nothing to say.

**The fixed point over the table is the one that iterates**, because a field
walk reads positions that the same round is computing.

## 4. Stopping criterion

Seed every parameter of every datatype at bivariant. Then repeat:

1. Snapshot the table.
2. For every datatype, for every constructor, for every field, walk it at `+1`
   against the snapshot, merging what it finds into a fresh table.
3. Stop when the fresh table equals the snapshot.

Concretely, and easier to assert in a test than a deep comparison: positions
only ever descend, and a merge only ever flips a flag from false to true. So the
**total number of set flags across the whole table is a non-decreasing integer
bounded by `2n`**, where `n` is the total parameter count over every datatype.
The criterion is that a round did not increase it.

That is also the termination argument. Every round that changes anything sets at
least one flag, flags never clear, and there are `2n` of them -- so at most `2n`
changing rounds and one more to notice, `2n + 1` in all. It cannot diverge, so
unlike subtyping it takes no fuel.

The fixed point is **global over the table, not per datatype**: two declarations
may name each other, so it is one worklist over every parameter of every
datatype.

Snapshot (Jacobi) and not update-in-place (Gauss-Seidel). In-place reaches the
same fixed point and often in fewer rounds, but the round _counts_ below are
then implementation-defined, and those counts are the thing a test can use to
catch a one-pass bug.

## 5. Why the seed is optimistic

Bivariant is the _most permissive_ point, so seeding there and only ever
descending computes the best sound answer rather than a merely safe one.
Starting at invariant instead would be sound and useless -- everything would
stay invariant, which is where the checker was before this pass.

The obvious worry is whether optimism can be _wrong_ about a recursive datatype.
It cannot, and the case that shows why is worth keeping:

    datatype Opaque[A] where
      | Mk(Opaque[A] -> Bool)

`A` occurs only inside the recursive occurrence, so every round prunes and the
answer is bivariant: `Opaque[X]` and `Opaque[Y]` are interchangeable for any `X`
and `Y`. That is correct, not optimistic. Nothing in `Opaque` ever produces an
`A`, so no program can observe the difference -- the soundness of a nominal
recursive type is a coinductive property, and the greatest permissive fixed
point is what states it.

## 6. Worked examples

Notation: `T` bivariant, `+` covariant, `-` contravariant, `X` invariant. (The
tests print the settled answer, where bivariance has already collapsed, and
spell invariance `=`.)

**Covariance, the base case.**

    datatype List[A] where
      | Nil
      | Cons(A, List[A])

| round | vA               |
| ----- | ---------------- |
| 0     | T                |
| 1     | +                |
| 2     | + -- fixed point |

Round 1 prunes the recursive occurrence, since `vA` is still bivariant; round 2
reads `+` and merges `+` into `+`. Two rounds, `n = 1`, bound 3.

**A rotation.**

    datatype Foo[A, B, C] where
      | Arrow(A -> B)
      | Data(C)
      | Shift(Foo[B, C, A])

Non-recursive fields give `A <- -`, `B <- +`, `C <- +`. The recursive field
gives `B <- read(vA)`, `C <- read(vB)`, `A <- read(vC)`.

| round | vA    | vB    | vC               |
| ----- | ----- | ----- | ---------------- |
| 0     | T     | T     | T                |
| 1     | -     | +     | +                |
| 2     | **X** | **X** | +                |
| 3     | X     | X     | **X**            |
| 4     | X     | X     | X -- fixed point |

All three invariant. Confirmable by hand: `Shift` is a permutation, three shifts
return to the start, slot 0 is contravariant and slot 1 covariant, so every
parameter visits both.

**A rotation that grows.**

    datatype Foo[A, B, C] where
      | Arrow(A -> B)
      | Data(C)
      | Shift(Foo[B, C, A -> B])

Slot 2 now holds a compound, so the walk descends an arrow while inside a
datatype argument. The recursive field gives `B <- read(vA)`, `C <- read(vB)`,
`A <- flip(read(vC))` and `B <- read(vC)`.

| round | vA    | vB    | vC               |
| ----- | ----- | ----- | ---------------- |
| 0     | T     | T     | T                |
| 1     | -     | +     | +                |
| 2     | -     | **X** | +                |
| 3     | -     | X     | **X**            |
| 4     | **X** | X     | X                |
| 5     | X     | X     | X -- fixed point |

Same answer, reached as a staircase -- one parameter per round, `vB` then `vC`
then `vA` -- against a bound of `2n + 1 = 7`. This is the example to keep: the
rotation above can be checked by a human argument about permutations that does
not generalize, whereas here the unfolding never returns to its start
(`Foo[A,B,C] ⊃ Foo[B,C,A→B] ⊃ Foo[C, A→B, B→C]`) and the fixed point is the only
way to the answer.

**The one-pass trap.** Round 1 of either rotation is a complete, plausible,
_unsound_ answer: `Foo[-A, +B, +C]`. Taking `+B` on faith licenses
`Foo[A,B,C] <: Foo[A,B',C]` for `B <: B'`, but projecting `Shift` from the
supertype then demands `Foo[B,C,A] <: Foo[B',C,A]`, which puts `B` in the
contravariant slot and needs `B' <: B`. Any implementation that walks the fields
once and stops produces exactly this.

## 7. What gets reported

A parameter that ends **bivariant is observed by nothing, transitively** -- a
phantom, and worth a warning at the declaration, which is the site that knows.
Reported once there rather than at every use, which also keeps `#castHead`
silent when it lifts an extreme into such an argument.

    nothing observes the type parameter A of Opaque, so it makes no
    difference to the type; write it `_` if that is meant

"Observed" and not "used": `Opaque[A]` in §5 mentions `A` in a field and is
still a phantom, so a message about the parameter being unused would be false
there. It needs the fixed point and not a pass, for the same reason -- `Data(C)`
alone never looks unused, and only the closure shows that nothing observes it.

**Not reported for a wildcard.** `datatype Tag[_]` is how an author says a
parameter is deliberately unobserved, which is what the message asks for; saying
it again would be noise.

**Not reported when a field is bad.** An unresolved field type elaborates to
`<bad>` with a report already standing, and a parameter that occurred only there
then looks unused -- blaming the author twice for one mistake. A datatype with a
bad field is excluded from this warning, not from the inference.

`DatatypeInfo.params` grew from `readonly string[]` to a `ParamInfo` record for
this: the variance has to live somewhere, and a parameter's own position is what
this message points at.

## 8. What reads it

Six places, and each of them had a hard-coded invariance before:

| site                   | what changed                                     |
| ---------------------- | ------------------------------------------------ |
| `#relateData`          | one walk for `#subtype` and `#eqtype`, composing |
| `#cast`'s `TData` case | the argument's variance, not `0`                 |
| `#liftExtreme`         | an extreme per position, and the warning         |
| `#avoidPart`'s `TData` | a directed argument widens; invariant collapses  |
| `#latticeData`         | join and meet go argumentwise                    |
| `openAt`'s `TData`     | where an EVar occurs, so `solveEVar` can choose  |

The last is the one that is easy to miss. `types.ts` is the representation and
must not know about declarations, so `openWith` takes an `ArgVariance` callback
and defaults it to `invariantArgs`; only `#applyCall`, which is recording where
each EVar stands in the result type, passes the real one.

`Subtyper` reads the table through `Context`, which now holds a `Declarations`.
Declarations sit _beneath_ the typing context -- unscoped, fixed before the
first binder is pushed -- so that is where a thing holding a context can find
them.

## 9. Deliberately not here

- **No annotations.** Adding `+A`/`-A` later means checking the written variance
  against the inferred one and reporting at the declaration; nothing above
  changes.
- **No fuel.** §4 bounds the work; a fixed point that cannot diverge should not
  pretend it might.
- **No variance on aliases.** They do not survive elaboration.
