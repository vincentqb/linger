# CI redesign

## Status

Active, 2026-10-02. Steps 1–2 pass independent review and the complete
foreground verifier (103.822 s). Shared-path publication and hosted checks
are pending. Step 3 remains isolated: review requires serializing PTY
acquisition before accepting concurrent Manager fixture groups.
Baseline is published, clean `de310f4`.
The previous warm hosted run, 36954511812, takes 168 seconds for Linux:
101.511 in the verifier, including 66.682 in live suites; the build is
1.393 seconds. Source gates execute in the preliminary job, full verifier,
and final pre-commit invocation. Python exists only for hook orchestration.

## Intent and constraints

Give each verification obligation one execution per CI run. Remove the
Python hook dependency, keep local and CI checks on the same implementation,
and make logs distinguish compilation, product checks and verifier regression
checks. Reuse a successful verification only when every relevant input is
identical; an artifact cache or a documentation-only diff is not evidence
that a previous verification succeeded. Scheduled, manual and release runs
retain clean verification and macOS coverage.

Keep all product theorem contracts and live assertions. Reduce waiting only
where an observed condition replaces it; negative observation windows retain
their meaning. New regression tests must reject deliberately broken behavior.
Shell remains the build/CI boundary; tests of that boundary are Lean. No
Python, new C, generic workflow framework, or product feature changes.

## Ownership

One writer per worktree. Shared records, workflow, verifier orchestration,
entry points, gates, README and publication belong to the coordinator.
Workers read this spec, AGENTS.md, SCRATCHPAD.md and their implementation.
Evidence and temporary scripts live under
`/tmp/linger-ci-redesign-20261002-nuJuA0/`. Controlled timing runs take its
exclusive `measure.lock`; ordinary correctness runs must not be described
as isolated timing measurements.

- Hygiene worker: `tests/hygiene.sh` and `E2E/Hygiene.lean`. Replace generic
  hook checks with small native boundary checks and exercise their failures.
  The coordinator owns hook installation, workflow lint, and integration.
- Coverage worker: `Theorems/Coverage.lean` and `E2E/Coverage.lean`. Consolidate
  source census and semantic checking without losing fresh-source detection
  or the existing parser/reference regression fixtures.
- Selector-test worker: `E2E/Manager.lean` only. Reduce its measured latency
  while preserving every assertion and isolation/signal/timeout contract.

## Steps

1. **Design and measure.** Read the actual workflow and hosted phase receipts,
   inventory the obligations, and make regression fixtures for the proposed
   boundaries. Reads: workflow, verifier, hooks, coverage, selector tests and
   prior records. Writes: this spec, append-only SCRATCHPAD, worker evidence.
   Exit: duplicate work and remaining costs have measured owners, and the
   execution/reuse design fails closed.
2. **Implement the shared path.** Integrate native hygiene, consolidated
   coverage, successful-verification reuse and the simplified workflow.
   Reads: Step 1 evidence and actual callers. Writes: workflow, verifier
   scripts, hooks, E2E entry point/CI checks, gates, README and owned worker
   files. Exit: each obligation has one owner, no Python hook setup remains,
   and focused controls catch stale reuse, skipped checks and real failures.
   Run required builds and the full verifier; commit and push the checkpoint.
3. **Reduce live-test latency and verify the assembly.** Integrate justified
   selector-test changes after a separate review; measure fixed inputs and
   keep exact check counts. Writes: selector test, any required integration
   and records. Exit: every live assertion still runs, the assembled foreground
   verifier passes, and hosted CI confirms the new execution path. Review is
   bounded to two review/revise rounds; unresolved correctness issues require
   revisiting the design.
4. **Close and publish.** Record actual warm/source-changing/records-only
   timings without conflating them, preserve worker evidence, retire owned
   branches/worktrees after containment checks, archive this spec and update
   AGENTS.md. Exit: verified main is committed and pushed, remote matches,
   and the completion record states any remaining costs or limitations.
