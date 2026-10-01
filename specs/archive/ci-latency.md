# Compilation and CI latency

## Status

Complete, 2026-10-01. Both independently reviewed implementation checkpoints
are committed and pushed to main: `8427d80` and `81e1cc0`. Their full foreground
local verifiers and hosted Linux runs pass with every existing assertion.
The latest run executes all 470 live, 21 CI and 63 shim assertions, both
semantic inventories, proofs, unit tests, generated C ABI, formatting, fuzz
checks and unrelated-session isolation.

The hosted live batch falls from 315.9 to 65.3 seconds. Step 1's whole job
falls from 535 to 237 seconds. Step 2's whole job takes 487 seconds, including
142.2 seconds of affected recompilation, 74.6 seconds of source/layout checks
and 150 seconds restoring caches. This source-changing run is not a warm-build
comparison. The recorded clean local full-target build takes 88.5 seconds;
an identical warm rerun takes 0.6 seconds. These are measurements on different
hosts and cache states, not a promise that every future run takes one time.

Both worker trees and branches are retired after checking accepted files
against the published commit and complete source recovery copies. Main is
the only remaining local branch/worktree. This final record closes the round;
its publication changes no compiled source.

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

Hosted Step 2, run `36917279911`, passes at 19:59:06Z. Its verifier takes
302.016 seconds; the live batch takes 65.341 seconds and Delivery 15.554
seconds, retaining all 34 Delivery assertions. Fresh semantic coverage takes
6.518 seconds. The toolchain cache is the identical 759,014,725-byte artifact
used by Step 1: download time changes from 4.028 to 96.654 seconds, extraction
from 13.145 to 22.134. Build and formatter downloads also stall. This explains
the setup variation without attributing it to compiler work or a cache miss.
The original logs and arithmetic live in `evidence/hosted-36917279911/` and
`evidence/hosted-cache-comparison.json`.

## Completion record

Bounded process isolation replaces serialized live execution. Early child
exit ends cleanup polling while preserving the full grace period. Coverage
looks up relevant declarations instead of scanning the entire environment.
Three VT proof bodies use their existing preservation lemmas; all 1,148
serialized declaration types remain byte-identical. A kernel-checked
`@[csimp]` equality substitutes a linear row painter with exactly the same
bytes and final pen. No C code, dependency or resource-limit increase is added.

Meaningful mutations exercise the runner, coverage checks, cleanup grace and
renderer equality. Independent final reviews accept both assembled checkpoints.
No fixture, negative observation window, assertion or proof contract is removed.
The full verifier and normal commit hooks pass before publication. Worker
source recovery copies remain outside the retired trees; no unique work is lost.

Source-changing proof/layout checks and remote cache transfer still have real
costs. Their measured intervals remain separate from live-test improvements.
Further changes should start from fresh phase measurements, not shorten test
observation windows or weaken the preserved contracts. No macOS result is
claimed for this round; neither the shim nor build wrapper changes.
