# Fuzzy alignment in the selector

Status: step 1 verified; step 2 publication and cleanup in progress
Updated: 2026-09-30

## Intent

Keep the selector's case-insensitive subsequence filter and existing listing
order. Choose a scored alignment within each displayed existing target,
favoring consecutive characters, word starts and smaller gaps, and underline
the matching characters. Selection reverse and the terminal's status palette
remain independent. Creation stays an explicit labelled choice.

Use pure Lean on v4.34.1 with no dependency, C change or new CLI option.
Compute alignments only for displayed rows. A dynamic program must keep the
work proportional to query length times target length; do not enumerate all
matching subsequences in production.

## Steps

1. Add the alignment algorithm, semantic proofs, unit checks and presentation.
   Exercise the visible change against the preceding executable first.
   Preserve the shared listing row text, exact attachment targets and order.
   Protect the executor's consumption with source gates. Independently review
   the change and break-verify its semantic guarantees.
2. Run both required builds and the complete foreground Linux verifier.
   Capture lessons in SCRATCHPAD.md, commit and push main, inspect hosted
   checks, remove integrated worker worktrees and archive this record.

## Contracts

An alignment exists exactly when the folded query is a subsequence of the
folded target. Its mask covers the original Unicode scalar positions, and
selecting those characters spells the folded query in order. The chosen
alignment maximizes the documented additive score; equal scores choose the
lexicographically earliest matching positions.
The score affects emphasis only, never row order or attachment identity.
Annotations preserve every plain row character and its existing status style.

## Verification

Pure checks cover competing alignments, repeats, boundaries, gaps, empty and
impossible queries, and non-ASCII characters. An independent exhaustive small
oracle checks optimality. Live pty checks inspect the terminal's parsed cells
and attributes, including selection, NO_COLOR and wide/combining characters.
Every added pure definition has exact-constant theorem coverage.

Record actual failures, fixes and verification outcomes here before closure.

## Step 1 checkpoint — 2026-09-30

Implemented an 81-line pure alignment module, with four-point word bonuses,
eight-point adjacency bonuses and a one-point gap penalty before the last
match. Matching still folds ASCII capitals; non-ASCII scalars match exactly.
The dynamic program visits each query/target cell, sharing mask suffixes.
It runs only for rows being displayed and adds no dependency, C code, public
executable or CLI option.

An independent weighted-walk specification gives one certificate for
completeness, exact mask length and spelling, maximum score and globally
earliest equal-score choice. The public presentation iff connects the actual
query and original target to displayed marks; projection theorems preserve
the shared listing text and status data. All added pure definitions pass the
exact-constant census. Existing order and attachment contracts remain intact.

Independent review caught an accent-only query whose scalar mask was correct
but whose base terminal cell was not underlined. A separate linear cell pass
now propagates emphasis backward through the following zero-width run.
Its indexed theorem states the exact rule against the original input, and
its projection theorem preserves characters and status. A contiguous source
gate ties the runtime to the proved stages and ANSI underline.

The exhaustive small oracle compares complete answers, including scores and
ties, over 341 targets and 40 queries. A repeated-character case exercises the
maximum query length. Compiling mutations have kernel counterexamples and
semantic rejections for scoring, folding, masks, global ties, presentation
offsets, actual query consumption and zero-width propagation. Runtime
mutations are caught by the display gates and the actual renderer regression.
All mutated sources are restored. Failed initial diagnostic setups are
preserved separately and do not count as semantic witnesses.

The predecessor runs all 111 selector assertions with five expected failures
for missing emphasis. The initial implementation then runs 110 passing
assertions with one accent-only failure; the corrected implementation passes
111/111. Permanent live checks cover optimal emphasis, retained listing order,
exact attachment, status/selection styles, NO_COLOR, wide and combining cells,
query clearing and clipping.

Both required builds and the complete foreground Linux verifier pass.
The assembled run, 05:15:00Z–05:22:30Z, includes the clean 166-job build,
generated Lean/C ABI, source gates, standalone formatting, theorem/emitter
coverage, CI runner checks, POSIX smoke and all fourteen live suites.
All 437 live assertions ran and passed; the unrelated-session sentinel
survived. All 163 source identities stayed fixed throughout verification.
The final independent review accepts the implementation with no remaining
source changes.

Evidence is preserved outside the worker trees:

- `/tmp/linger-fuzzy-proof-evidence-20260930/HANDOFF.md`
- `/tmp/linger-fuzzy-ui-evidence-20260930/HANDOFF.md`
- `/tmp/linger-fuzzy-cell-evidence-20260930/HANDOFF.md`
- `/tmp/linger-fuzzy-e2e-evidence-20260930/combining-regression/GREEN.md`
- `/tmp/linger-fuzzy-cell-review-20260930/FINAL.md`
- `/tmp/linger-fuzzy-final-verifier-20260930/counts.json`

All agents are closed. Both worker trees have zero unique commits and only
accepted source changes, byte-identical to main, plus generated caches.
Complete uncolored patches, baseline/final sources, hashes and inventories
are sealed in `/tmp/linger-fuzzy-cleanup-20260930/`. Publication, a fresh
cleanup preflight and hosted outcomes are recorded at closure.
