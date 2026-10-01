# Lean release and faster CI

Status: active
Updated: 2026-10-01

## Intent

Use the most recent stable Lean release and make verification substantially
faster without losing a proof, warning, ABI check, formatter check or live test.
The official Lean release API currently identifies v4.34.1 as the latest stable
release, matching this repository; v4.35.0-rc3 is explicitly a prerelease.
Recheck before publication rather than inventing a version bump.

Out of scope: runtime behavior, new public CLI options, new Lean dependencies,
changes to the established macOS cadence, or rewriting historical records.

## Decisions to verify

- Reuse Lake's dependency-tracked artifacts if source changes and diagnostics
  are still checked reliably. Verify content invalidation and cached diagnostic
  behavior against the actual pinned Lake executable.
- Preserve a clean verification path for release/compiler validation and
  periodic runs. Caches may save deterministic compilation; no cache hit may
  skip the runtime verifier checks or live suites. All proof and unit-test
  targets remain validated through Lake's dependency graph.
- Remove duplicated workflow setup and validation where the same checks can run
  once. Keep the runner decision executable and covered by `E2E.Ci`.
- Keep mathematical guarantees in the existing theorem targets. CI orchestration
  is IO: test real scripts and use source gates for their workflow call sites.

## Step 1 — implementation and assembled verification

Reads: `AGENTS.md`, `SCRATCHPAD.md`, `.github/workflows/ci.yml`,
`tests/e2e.sh`, `tests/ci-runners.sh`, `tests/gates.sh`, `E2E/Ci.lean`,
`lake`, `lakefile.lean`, `.pre-commit-config.yaml`, Lean release metadata.

Writes: the workflow, verifier and CI regression checks above; CI setup
configuration if extraction removes duplication; `lean-toolchain` and compiler
compatibility fixes only if a newer stable release exists; `README.md`,
`AGENTS.md`, this spec and append-only `SCRATCHPAD.md`.

Ownership: one worker owns `tests/e2e.sh` and `E2E/Ci.lean` in a separate
worktree. The coordinator owns the workflow, source gates and documentation,
and performs final integration. A separate reviewer checks the assembled diff.

Exit: both required builds pass; the complete foreground Linux verifier passes
from a clean build and with reused artifacts; changed sources and diagnostics
are rejected by focused regression checks; all prior live assertions execute;
workflow syntax and source gates pass. Record cold/warm times, exact toolchain
and actual hosted outcomes. At most two review/revision rounds before revisiting
any unresolved implementation choice.

## Step 2 — publication and closure

Publish the verified checkpoint to main, inspect hosted results, preserve and
remove accepted worker worktrees/branches, append the final verification record
and archive this spec. A hosted check that did not run is recorded as unexecuted.

Exit: all intended changes are committed and pushed, the checkout is clean,
no worker work remains, and the final report distinguishes measurements from
expectations.

## Verification status

Step 1 implementation and independent review are complete. The official release
API still identifies v4.34.1 as the latest stable release at 11:49:50Z on
2026-10-01, so no compiler change is warranted.

Both complete foreground Linux runs pass on the same 172 source identities:
clean 11:34:24Z–11:42:02Z (458 seconds), cached 11:44:08Z–11:49:58Z
(350 seconds). The same post-build commit hooks pass in five and six seconds.
Every run includes the theorem/test targets, generated ABI, standalone layout,
both coverage checks, twelve CI checks, all shim checks, all 437 live assertions
and the unrelated-session sentinel.

Actual Lake and formatter probes reject changed sources and dependencies.
Compiling mutations show that removing rehashing or warning rejection makes
the intended permanent check fail. Separate workflow mutations fail the real
matrix-output and build-before-lint gates; restoration passes.

The previous hosted run now executes, but failed in lint before reaching its
full gate: dynamically imported Main was not yet built. The new ordering fixes
that failure locally. Source hashes, timings, original logs and independent
review are sealed in `/tmp/linger-ci-full-20261001-Z4QaxC/`; worker and mutation
evidence paths are recorded in SCRATCHPAD.md.

Both required builds, actionlint, shell syntax and source gates also pass.
Publication, hosted validation and worker cleanup remain.
