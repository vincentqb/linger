# Four-area CI refinement

## Status

Active, 2026-10-01. Steps 1 and 2 complete; Step 3's full foreground
verification passes, with commit checks and publication pending.
Baseline: `b837d56`, clean and published. The preceding
audit's final hosted run passed: Linux job 173 seconds, full verifier 99.198,
live suites 65.807, cached build 2.252. These are observed warm timings, not
cold-build promises.

## Intent and constraints

The user requests an agent for each of the four delivered improvements:
isolated concurrent tests and teardown, narrower coverage scans and simpler
VT proofs, proved linear repainting, and installation of missing dependencies.
Audit each for correctness, minimal code and remaining cost, and implement
supported refinements. Integrate accepted work into main, commit and push.

Retain every existing proof statement and assertion unless a stronger,
reviewable replacement is justified. Preserve signal behavior, bounded
concurrency, process isolation, exact assertion counts, output fidelity,
coverage of exact constants, cache invalidation and clean-run CI policy.
Keep negative observation windows and cleanup deadlines. No C additions,
new dependencies, compiler upgrade, benchmark thresholds tied to one host,
or speculative general-purpose frameworks.

## Ownership and reads

Every worker reads AGENTS.md, SCRATCHPAD.md, the preceding archived audit,
this spec, and its implementation and callers. Each writes only in its own
worktree. Workers leave shared records and integration edits to the
coordinator; they provide evidence and a concise handoff outside the tree.

1. **Test execution:** `E2E/Runner.lean`, `E2E/Harness.lean`,
   `E2E/Manager.lean`, and runner-specific checks in `E2E/Ci.lean`.
2. **Coverage and proofs:** `Theorems/Coverage.lean`,
   `E2E/Coverage.lean`, and `Theorems/Vt.lean`.
3. **Repainting:** `Linger/Core/Render.lean`, `Theorems/Render.lean`,
   `Theorems/Render/*.lean`, `Tests/Render.lean`, and `E2E/Delivery.lean`.
4. **Dependency setup:** `.github/workflows/ci.yml` and, only if a
   regression needs a separate module, `E2E/CiDependencies.lean`.

The coordinator owns `tests/e2e.sh`, `tests/gates.sh`, `E2ETest.lean`,
`THEOREMS.md`, AGENTS.md, this spec and append-only SCRATCHPAD.md.
Dependency-specific edits to `E2E/Ci.lean` are integrated by the coordinator
after the test-execution worker stops writing. Any additional write scope
must be recorded here first.

## Steps

1. **Audit and refine.** Each worker identifies a concrete gap or measures
   a remaining cost, applies the smallest supported correction, and verifies
   its own scope. Exit: four handoffs with fixed source identities, commands,
   results, failed candidates, and meaningful regression or mutation evidence.
   A substantiated no-change finding is acceptable.
2. **Review and integrate.** Read the patches against their callers and
   the invariants, integrate accepted changes and shared checks, and obtain
   independent review of the assembly. Exit: no correctness or requirement
   blocker; at most two review/revise rounds before replanning.
3. **Verify and publish.** Run the required builds, full foreground verifier
   and hooks against fixed sources. Compare timings with their cache and host
   context. Exit: all checks pass, accepted work is committed and pushed,
   and hosted CI has been checked.
4. **Close.** Record results, archive the spec and retire worker branches
   only after accepted changes are published and unique work is preserved.
   Exit: clean main matches the remote; the completion record distinguishes
   measured improvements from unchanged or inconclusive areas.

## Evidence

Worker reports, mutation logs, profiles and verifier receipts live in a fresh
task directory under `/tmp`. The coordinator records its exact path in the
worklog. Timed experiments serialize through a shared lock; correctness
checks may run concurrently, with host contention noted when relevant.

All four implementation workers are closed. Accepted changes reject an
explicit failure hidden behind a passing runner summary, add seven dependency
assertions to the existing function, simplify two VT proof bodies with all
1,148 theorem statements preserved, and replace whole-grid row append with
prepend plus one reversal under the unchanged exact-output theorem.
The narrowed coverage scans and actual dependency-install workflow remain
unchanged after audit. A further tab-proof experiment is rejected as
inconclusive. Independent review's argument-boundary finding is reproduced
and fixed within the dependency function; its new mutation and the previous
seven all fail as intended, with controls passing. No new assertion is needed
for that strengthening. The assembled CI inventory is 29; the existing
fifteen live suites retain all 470 assertions. Both independent reviewers
accept the final source identities without blockers and are closed.

The full foreground verifier passes in 208.057 seconds against unchanged
sources: the build stage takes 82.392 seconds and the live batch plus final
checks 66.593 seconds. All 470 live assertions, 29 CI assertions, 63 shim
checks, both semantic censuses, generated C ABI, formatting and fuzz pass.
This source-changing local run includes recompilation and is not comparable
to the preceding hosted warm-cache total as a speedup. Commit checks,
publication, hosted checks and worktree retirement remain pending.
