# Compilation and CI latency

## Status

In progress, 2026-10-01. Baseline is `f6a5583` on main; its hosted run
`36908212054` passed. The bounded suite runner passes a full foreground Linux
run with every existing live assertion. Initial independent review's logging
fixture gap is fixed and mutation-checked. Coverage and wait changes are
integrated with exact source identities; the assembled verifier passes in
118.4 seconds. Clean compilation is measured separately at 88.5 seconds,
with an identical warm rerun at 0.6 seconds. Final independent review accepts
the assembled checkpoint without blockers. Step 1 is committed and pushed as
`8427d80`; hosted run `36913950661` passes in 237 seconds for the full Linux
job, including a 157.1-second verifier. Step 2 integrates the measured row
painter optimization and three simpler VT proof bodies. Independent review
accepts the renderer; its theorem/unit build also passes in main. The proof
worker's builds, fresh censuses and formatting pass with identical declaration
types. Independent source review also accepts the VT proof changes. The
assembled foreground verifier passes in 210.6 seconds, including 84.4 seconds
of affected recompilation and 66.6 seconds of live suites. All 470 live
assertions and the complete verifier stack pass with fixed source identities.
Final independent review accepts the assembled checkpoint without blockers.
Step 2 is ready for commit, push and its hosted verification.

## Request and constraints

Compilation and CI feel too slow. Audit their actual costs, fix waste, and
refine the resulting design. Existing authorization includes independent
agents in worktrees, frequent verified commits, integration into main and push.

Retain all proofs, semantic coverage, source gates, generated C ABI checks,
live terminal assertions, signal behavior and unrelated-session isolation.
Keep Lean v4.34.1, the standalone formatter, the `./lake` wrapper and clean
scheduled/manual/release verification. Do not speed up tests by shortening
negative observation windows or claiming cached work was executed anew.

## Reads and writes

Read: AGENTS.md, SCRATCHPAD.md, the closed CI refresh record, hosted logs,
Lake configuration and build artifacts, coverage elaborators, E2E harness
and suites, verifier scripts and workflow.

Write: measured changes to the coverage elaborators, E2E harness/suites,
E2ETest.lean, CI workflow and verifier scripts; build configuration only
with a measured need. Update this spec, current instructions and append-only
worklog. Production code and proof statements change only if a measured
compiler or verifier CPU bottleneck justifies a semantics-preserving refactor.

Worker A owns E2E/Harness.lean, E2E/Manager.lean and E2E/Delivery.lean in
an isolated worktree. Worker B owns Theorems/Coverage.lean and
E2E/Coverage.lean in another. The coordinator owns orchestration, workflow,
records and integration. A fresh reviewer assesses the assembled change.

After the wait audit measured roughly 48 CPU seconds in Delivery's large
replay fixtures, worker A also investigates a bounded rendering optimization
in `Linger/Core/Render.lean` and its proofs. Acceptance requires exact emitted
bytes and final-pen equivalence, unchanged fixture sizes, and a measured gain.
Worker B follows the clean compiler profile into `Theorems/Vt.lean`; any
proposed proof simplification must retain the exact theorem statements and
show a measured elaboration saving before acceptance.

## Steps

1. Measure stage costs and identify waste. Implement the smallest supported
   improvements, with failing checks or deliberate mutations for behavior.
   Compare the same live assertions, record negative findings, independently
   review, and run the full foreground Linux verifier before committing.
2. Push the verified CI implementation and measure its actual hosted run.
   Investigate the measured rendering hotspot separately; accept a production
   change only with exact-output proofs, unchanged fixtures, independent review
   and full verification. Commit an accepted optimization separately.
3. Resolve hosted failures and close with truthful timing and verification
   records. Retire worker branches/worktrees only after integration is verified.

## Acceptance

- Record compiler, coverage, live-test and CI setup costs separately.
- Prove unchanged pure guarantees through the existing theorem census.
- Exercise each changed test-driver contract with a meaningful failure.
- Execute every existing live assertion and the unrelated-session sentinel.
- Report observed before/after costs, including cache state and limitations.
- End with all accepted work on main, committed and pushed.

## Evidence

Local receipts and worker outputs:
`/tmp/linger-ci-latency-20261001-Ah7wOc/`.
The latest baseline hosted run is `36908212054`: 535 seconds for the full
job, 412.5 seconds for its verifier, and 315.9 seconds for live suites.
The first runner-only local verifier takes 121.6 seconds with unchanged
source identities and all 470 live assertions. The preceding full local
run took 383.2 seconds. With the coverage and wait changes integrated, the full
local verifier takes 118.4 seconds, still executing all 470 live assertions.
A separate clean full-target build takes 88.5 seconds and its identical warm
rerun takes 0.6 seconds; the longest jobs are proof/test checking. The clean
measurement uses the isolated coverage worktree and retains the installed
compiler and OS page cache. The new hosted full job takes 237 seconds, its
verifier 157.1 seconds, and its concurrent live batch 83.9 seconds. It restores
the preceding commit's build cache; that compiler interval includes the CI,
coverage and harness changes. Source gates and final hygiene also pass.
The separate VT proof experiment checks the same module three times per
variant with warm imports: median wall time falls from 32.403 to 29.138 seconds
and total CPU from 213.581 to 152.020. Original runs precede optimized runs
on the shared host; this is not an interleaved or whole-build comparison.
All 1,148 serialized declaration types match exactly.
The assembled optimized tree retains all fixtures and assertions. Delivery
takes 14.7 seconds in its full run. The 210.6-second total includes affected
proof/test recompilation, unlike the earlier 118.4-second warm run; comparing
those totals would not measure an optimization regression.
