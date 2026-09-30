# Reusable fuzzy matching policies

Status: complete — local Linux verification green; hosted checks could not start
Updated: 2026-09-30

## Intent

The user permits the internal fuzzy library to support features that linger
does not consume. Start with case policy and scoring: sensitive matching,
ASCII-insensitive matching, and smart case (ASCII capitals in the query
select sensitive matching); configurable word, adjacency and gap scores.
The existing `align` function keeps its current defaults and every selector
call site stays unchanged. Broader library features need no CLI options.

Keep one dynamic program and one configuration-quantified proof. Scores are
arbitrary integers; no sign restriction is needed for a finite alignment.
Scoring cannot change which queries match, and equal-score ties remain
globally earliest. Character normalization never changes scalar positions.

## Steps

1. State the generalized contracts, add failing extension checks, expose a
   small `Config` / `Scoring` / `CaseMode` API and `alignWith`, and generalize
   the existing optimality certificate. Keep the default API and its semantic
   theorems. Independently check configurations with an exhaustive oracle.
2. Review and break-verify the new contracts; run both required builds and
   the full foreground verifier. Record the usable library API, lessons,
   verification and hosted results, commit and push main, clean up integrated
   workers, and archive this record.

## Contracts

- `alignWith` succeeds exactly for subsequences under the selected case policy.
- Every successful mask has one entry per original scalar and spells the
  normalized query in order.
- Every configuration returns maximum score and globally earliest ties.
- Changing only scoring preserves acceptance.
- Smart case equals sensitive matching for queries containing an ASCII
  capital, and insensitive matching otherwise.
- The legacy default still has its existing completeness, spelling, optimality
  and tie contracts. Linger retains its current case behavior and row order.
- The fuzzy module's import closure remains independent of session and
  terminal code.

## Verification

The independent whole-mask oracle checks 46,358 combinations across twenty-one
configurations, including zero, negative and gap-rewarding weights. It also
checks 13,640 default-wrapper equalities and 23,205 scoring-independent
acceptance equalities. Thirteen ordinary-import checks exercise the public API.
The predecessor adapter produces eight directed wrong values and fails
twenty-eight permanent semantic guards. Missing declarations and setup errors
remain separate diagnostic evidence.

Independent review accepts the eleven-file snapshot. Eight compiling
production mutations have kernel-confirmed wrong results and fail their
intended public contracts and unchanged complete proofs; every exact
restoration passes. They cover both smart-case branches, all score fields,
ignored configuration, rejection of negative answers and drift in the default
adjacency weight. A separate compiling wrong-library-root mutation fails its
source gate and restores to green.

Both required builds, the independent `LingerFuzzy` target and the full
foreground Linux verifier pass. The assembled run at 13:08:05Z–13:15:41Z
checks the clean build, generated Lean/C ABI, source gates, standalone
formatter, exact-constant and emitter coverage, CI runner, POSIX smoke checks
and all fourteen live suites. All 437 live assertions pass, including the
unchanged selector checks and unrelated-session sentinel. All 165 source
identities remain fixed.

Evidence:

- Tests and predecessor checks:
  `/tmp/linger-fuzzy-library-test-evidence-20260930/HANDOFF.md`.
- Independent review, accepted hashes and semantic mutations:
  `/tmp/linger-fuzzy-library-review-evidence-20260930/HANDOFF.md`.
- Named-root gate:
  `/tmp/linger-fuzzy-library-evidence-20260930/target-gate-mutation/result.json`.
- Frozen assembled verifier, original outputs and independently counted checks:
  `/tmp/linger-fuzzy-library-full-20260930-3XECV9/receipt.json`.

## Completion

Implementation checkpoint `14f213d` is committed and pushed to main. Both
required builds and every commit hook pass. The frozen assembled verifier
above remains the implementation verification; closure changes documentation.

Both agents are closed. Fresh cleanup preflight confirms zero unique commits
on both worker branches and byte-identical integration of every changed file
in committed, published main. Complete uncolored patches, baseline/final
sources and status/index/ignored inventories are preserved in
`/tmp/linger-fuzzy-library-cleanup-20260930-8HDKwG/`. Both worker trees and
branches are removed; only main remains. The reviewer's original accepted
documentation snapshot remains in its review evidence, separately from the
refreshed checkpoint-status copies recorded in
`/tmp/linger-fuzzy-library-review-doc-refresh-20260930-LOYcCr/`.

Hosted run `36720594609` failed before any steps ran. The GitHub annotation
names failed recent account payments or a spending limit requiring an
increase; the full-gate job was skipped. Actual run/job/annotation responses
are preserved in
`/tmp/linger-fuzzy-library-hosted-checkpoint-20260930-Fr5g3m/`.
No hosted or macOS pass is claimed.

The reusable API can evolve independently of linger's CLI. Its compatibility
contract pins concrete defaults, while its general laws quantify over every
configuration. Keep that separation when extending the library again.
