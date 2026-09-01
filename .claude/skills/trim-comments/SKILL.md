---
name: trim-comments
description: Debloat comments in a file or directory — strip line-by-line narration and the record of how the code got here, keep the high-level pitch of what a chunk is for and the invariants it enforces. Use when asked to trim, debloat, prune, or clean up comments, or when comments have accumulated from many editing passes.
---

# Trim comments

Target: `$ARGUMENTS` (a file, a glob, or a directory). If empty, ask what to
trim rather than guessing; if the user said "the changed files", use the working
diff.

## What a comment is for

A reader arriving at a chunk of code has two questions the code itself answers
badly:

- **What is this chunk aiming at?** The pitch, one or two sentences, at the
  altitude of the whole function or block — not its steps.
- **What must stay true?** The invariants, preconditions, and the reason a
  non-obvious choice is the right one.

Everything else the code already says, and says more reliably, because the code
cannot drift from itself.

## Cut

- **Narration.** `// increment i`, `// loop over the args`,
  `// return the
  result`. Restating the next line in English.
- **Iteration history.** The back-and-forth of how this arrived: "previously we
  did X but that broke Y", "originally this used a map", "changed to handle the
  case from last week". Distill what survived into the invariant it protects,
  then delete the story. One line stating the rule beats five reconstructing the
  path to it.
- **The claim wider than the code.** A local choice defended with a statement
  about the whole file -- "every rule that asks wants it", "the only thing it
  does not already carry" -- where a counterexample sits a few dozen lines away.
  The cure is not to repair the claim into a true one, which only trades a wrong
  sentence for a longer sentence. Cut the clause; what is left says what the
  code does and stops. Usually this is a third-kind sentence written in a
  first-kind register; see below.
- **Per-case error commentary.** A comment on every error branch explaining that
  particular failure. Say the rule once at the top of the function.
- **Restated signatures.** Param and return lists that repeat the types.
- **Dead scaffolding.** Commented-out code, TODOs already done, section banners
  that only announce the next declaration's name.

## Which kind of claim

Before keeping a sentence, ask which of three it is -- the split the JDK marks
with `@apiNote`, `@implSpec` and `@implNote`:

- **binding on callers**: what they must guarantee, what they may rely on
- **binding on the implementation**: what this must keep true however it is
  rewritten
- **true today**: how it currently happens to work, which callers and rewrites
  are both free to ignore

The first two are the invariants, and they earn whatever length they need --
stated against what a function takes and what it hands back, which is the only
part of a comment anything mechanical can check against the signature, and so
the part that survives. The third is what rots, and it rots invisibly, because
nothing on it says it was only ever an observation. Keep one only where a reader
would otherwise be misled, and write it so it reads as an observation rather
than a rule -- "today every caller wants the bound" rather than "every rule that
asks wants it". A third-kind sentence in the register of the first two is how a
claim gets wider than its code.

## Keep

- The chunk-level pitch, if the chunk's aim is not obvious from its name.
- Invariants, preconditions, and what callers must guarantee.
- Why a surprising choice is correct — the non-obvious tradeoff, the reason the
  simple version fails. This is the most valuable comment in a file; do not cut
  it just because it is long.
- Genuine future-proof notes: known limitations, a case deliberately unhandled,
  a place that will need work when a feature lands.
- Pointers to external context a reader cannot derive: a paper, an RFC, a spec
  section.

## Method

1. Read the whole file before editing. Altitude judgments need the surrounding
   code — you cannot tell narration from invariant one line at a time.
2. Per chunk, ask: does this comment answer "what is this for" or "what must
   stay true"? If neither, cut it. If it answers one badly, rewrite it to answer
   it well — trimming is allowed to produce _better_ comments, not only fewer.
3. Where several scattered comments circle one rule, collapse them into a single
   statement of the rule at the top of the chunk.
4. Match the file's existing comment idiom — its density, its voice, `//` vs
   docblock. A trimmed file should read as if written that way, not as one that
   was pruned.
5. Touch comments only. No renames, no reordering, no logic changes. If you spot
   a real bug, report it; do not fix it here.
6. When a comment and the code disagree, the comment is stale: fix it to match
   the code, and flag the discrepancy — a stale comment is often a real bug's
   only witness.

## Verify

Run the project's typecheck and tests after editing. Comment-only edits must not
change behavior, so any failure means something was cut that wasn't a comment —
find it rather than re-running.

Then report per file: what was cut, in one clause each, and anything you kept
that looked cuttable but earns its place.
