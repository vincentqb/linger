# Lean release and faster CI

Status: active
Updated: 2026-10-01

## Intent

Use the most recent stable Lean release and make verification substantially
faster without losing a proof, warning, ABI check, formatter check or live test.
The official Lean release API currently identifies v4.34.1 as the latest stable
release, matching this repository; v4.35.0-rc3 is explicitly a prerelease.
Recheck before publication rather than inventing a version bump.

Out of scope: new public CLI options, new Lean dependencies, changes to the
established macOS cadence, or rewriting historical records. Runtime changes
are limited to fixing concrete failures exposed by hosted verification.

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

## Step 2 — hosted portability checks

Implementation checkpoint `f0e3a14` is published. Hosted run `36858109059`
passes source gates, compilation, ABI, layout, coverage and all twelve CI
checks, then fails the existing deep-directory POSIX fixture before the live
suites run. Reproduce the runner's shell behavior and fix the fixture without
weakening its long-path or usable-directory assertions. Also replace the
deprecated action versions identified by that run after checking current
upstream compatibility.

Writes: `LingerTest.lean`, action versions in `.github/workflows/ci.yml`,
this spec and append-only `SCRATCHPAD.md`. The action-version worker owns
only the workflow in its separate worktree.

Exit: the original failure is reproduced, the fixed fixture passes on both
shell implementations, all required builds and the full foreground verifier
pass, and the hosted result is inspected before closure.

## Step 3 — portable account-home lookup

Checkpoint `fff4c58` is published. Hosted run `36861077691` passes the shim
and the first ten live suites, then fails the two existing import assertions
for missing and empty HOME. Its `/bin/sh` is Dash, which leaves bare `~`
unexpanded in an empty environment. The importer must use the standard
library's account-information API instead of relying on shell expansion.

Writes: `Manager/Resurrect.lean`, its import boundary in `tests/gates.sh`,
`E2E/Delivery.lean`, this spec and append-only `SCRATCHPAD.md`. A separate
reviewer checks the native API choice and the remaining live suites in its
own worktree. That review also exposes delivery fixture socket paths that
overflow in long checkouts; move their temporary root outside the checkout
without changing assertions or cleanup.

Exit: retain explicit HOME resolution and the absolute-path guard, remove the
fallback subprocess without adding C or dependencies, pass the existing
account-home assertions, reproduce and repair the long-worktree fixture,
pass the full foreground verifier, and inspect the next hosted result.

## Step 4 — publication and closure

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
Checkpoint `f0e3a14` is committed and pushed, and its original worker branch
and worktree are removed with exact accepted-source recovery copies.
The hosted fixture failure and action deprecations above extend verification
through step 2 before final publication and closure.

Step 2 local verification is complete. The original deep-directory fixture
fails exactly one of 63 shim checks under Dash v0.5.12. Physical `cd -P`
preserves both assertions and passes all 63 checks under Dash and Bash.
An independent review accepts the fixture and the seven action-version updates.

The full foreground Linux verifier passes with Dash used for child `sh`
commands, 12:12:18Z–12:17:59Z (341 seconds), followed by passing hooks in
five seconds. All 172 source identities remain unchanged, and all 437 live
assertions, twelve CI checks and 63 shim checks execute. The first attempt
stopped at a formatter layout correction; its original failure is preserved
separately from the successful run.

Evidence is sealed in `/tmp/linger-ci-portability-full-20261001-ourcZX/`.
Checkpoint `fff4c58` is published and the action worker is removed after a
fresh guarded preflight. Hosted run `36861077691` reaches the recipes suite
and exposes the account-home failure described in step 3; it is not green.

Step 3 local verification and independent review are complete. The native
account API preserves explicit HOME resolution and absolute-path validation.
A compiled substitution of the environment-aware `getHomeDir` fails exactly
the existing HOME-empty assertion; exact restoration passes all 55 import
checks. The delivery fixture's original path overflow is reproduced in a
long worktree, and its corrected temporary root passes the same case and
all 34 existing delivery assertions.

The final assembled foreground verifier passes at 12:47:39Z–12:53:17Z
(338 seconds), followed by passing hooks in five seconds. All 172 source
identities remain fixed, and all 437 live assertions, twelve CI checks,
63 shim checks, proofs, ABI, layout, coverage and fuzz checks pass.
The complete receipt is `/tmp/linger-ci-assembled-20261001-SQphwv/`;
the independent review is
`/tmp/linger-ci-home-review-20261001-w5aoIT/evidence/HANDOFF.md`.
The reviewer is closed and its source is integrated. Publication, fresh
worker cleanup and the next hosted run remain. The latest stable Lean
release is still v4.34.1 at the 12:48:49Z recheck.
