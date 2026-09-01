---
name: read-through
description: Read a body of code linearly, in the order it is meant to be understood, and judge whether it makes sense as English with the comments covered — names that predict what happens at their use sites, honest decomposition and reuse, and no question answered twice — in the code or in a repeated traversal. Use when asked for a read-through, a design read, or whether code "reads well". Not a bug hunt; use /code-review for that.
---

# Read-through

Target: `$ARGUMENTS` — a file, a directory, a subsystem, or a diff. A diff is
the weakest target and is never the whole one: whether a name is good is a
question about its **use sites**, so reading only the changed lines cannot
answer it. Given a diff, read the changed code and every place that calls it.

## What this pass is for

The code is assumed correct. Something else already looks for bugs; this looks
for the thing a correct program can still get wrong, which is that its structure
does not say what it means.

One test, applied six ways:

**Cover the comments and read it.** Good comments hide bad structure — a
docblock explaining what a badly named function does will read fine and leave
the call site unreadable. Judge the code as if the comments were not there, then
uncover them and ask whether any of them exists to apologize for the code under
it. A comment that would be unnecessary after a rename is a finding about the
name, not about the comment.

Follow this one literally. Comments drift, and in a file that has been through
many passes -- or through a model -- they are the least reliable thing present:
they overclaim, they describe a version that no longer exists, and they are
verbose in a way that reads as authority. So a comment is never *evidence* for a
judgment about the code. If a note only holds because a docblock says so, it is
a note about the docblock, and it belongs to `/trim-comments` rather than here.

**Read names where they are used, not where they are defined.** Almost every
name is defensible at its definition; a name earns its place by predicting what
happens at the call. `paramType(param)` reads as parsing a type in a file whose
every other verb parses. Ask of each call: if I did not know this function,
would I guess wrong? A proposed replacement must describe the operation rather
than restate a metaphor for it, and must never be harvested from the docblock's
own figurative language -- a phrase that carries prose can be opaque as an
identifier, and idiom travels worst across a reader's first language. Where the
existing name and the type signature together predict the call, there is no
finding.

**Ask what each unit is for, in one sentence, before reading it.** If the
sentence needs an "and", the unit does two things.

**Duplication is a finding only when the general thing can be named.** Folding
two occurrences into one is a guess about which half is the general part, made
from two samples -- usually too few to tell, and a fold that guesses wrong buys
a helper with a parameter for every way the two differed. So: several
occurrences, and a component nameable without hedging, or leave them. Two short
ones may stand side by side and often should, symmetry being easier to read than
an abstraction over it -- but then the names have to carry the *difference*,
`ensureParamTypes` beside `dropWrittenTypes` rather than two spellings of one
word. For a two-way duplication the finding is nearly always about the names.

The exception needs no distilling: a component that already exists, is already
named, and is bypassed anyway. That is reuse that was available and not taken.

**Find the question answered twice.** Repeated branching on the same fact, or on
facts that are the same fact in different clothes: three `if`s on whether an
annotation is present, a flag threaded in to say what the caller already knew, a
`kind` re-tested downstream of the switch that already dispatched on it. The
finding is not "there is duplication" — it is *what the question is*, and where
its one home should be.

**Count the walks over the same structure.** Three passes over one tree, each
re-deriving what the last already knew; a lookup inside a loop over the thing
that was looked up; a shape tested in a function and tested again by its caller.
The finding is not that it is slow -- at most sizes it will not be. It is that
the structure is being asked the same question over and over, which is the test
above in time rather than in code, and repeated traversal is the loudest signal
a design gives that something one pass could have carried is instead being
recovered by the next. Ask what that something is; if it is easy to say, the
design is missing it.

## How to read

1. **Get the architecture first**, from the project's own description — the
   README, the module docblocks, `CLAUDE.md`. Read to the point of being able to
   say what each unit is for before opening it. A read-through with no model of
   the whole is proofreading.
2. **Read in the order the code is meant to be understood**, which is almost
   never alphabetical and often not the order of the file: follow the pipeline,
   the dataflow, the call graph down from the entry point. Note where that order
   and the file's own order disagree, which is itself worth reporting.
3. **Read whole units.** Skimming for patterns finds nits and misses shape.
4. Do not edit. This pass produces judgments; applying them is a separate act
   with separate risks.

## What earns a note

The bar, since naming is the easiest thing in the world to have an opinion
about. A note must carry one of three things:

- **the better name**, actually proposed — not "this name is unclear"
- **the use site that misleads**, quoted
- **the question being answered twice**, named, and where its one home should be

If none of the three can be produced, the note is a preference and does not go
in. Prefer the note that dissolves several smaller ones: three awkward names
that share a cause are one finding about the cause.

Say what read well, too, and why — particularly a structure that looks
gratuitous and turns out to be load-bearing. A pass that only accuses is one
the author cannot calibrate against.

## What to report

Prose, in reading order, not a ranked defect list — the order is part of the
argument, since a note often only makes sense after the one before it.

For each: where, what the code says, what it means to say, and the change that
would close the gap. Then a short close on the shape of the whole — the question
that turned out to have several homes, the boundary that is doing more work than
its name admits.

Where a judgment depends on something not read, say so rather than guessing.
