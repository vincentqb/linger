# Minimal code and compound engineering audit

## Status

In progress, 2026-09-26. The starting point is `49f48c0` on `main`.
Step 1 fixes a confirmed CI history error; the three parallel source audits
and the local runtime/verifier audit continue. The previous complete Linux
verifier passed; hosted verification of that checkpoint did not start because
of the repository owner's GitHub billing/spending limit.

## Purpose

Audit the entire maintained tree for unnecessary code, repeated policy,
avoidable proof complexity, and checks that would miss a recurrence. Apply
confirmed improvements while preserving the public behavior and the stated
theorems. Count production, proof, and verification code together when pricing
a refactor.

Use the code-minimalism, compound-engineering, design-for-provability,
verifier-in-the-loop, subagent-orchestration, and git-workflow skills.
Read the worklog and relevant closed records before reopening a decision.

## Scope and invariants

- Preserve the single `linger` entry point and native terminal configuration.
- Keep pure session/VT policies, manager policies, IO executors, and the raw
  POSIX interface within their existing import boundaries.
- Keep the C shim limited to OS/ABI work; remove an export only with evidence
  that Lean core or an existing boundary can perform the same operation.
- Preserve theorem strength and exact-constant coverage. A behavioral fix
  starts with a failing check; a new guard or policy consumer is tied to its
  executor and checked with a compiling mutation.
- Keep the recorded non-goals, toolchain pin, dependency set, and proof limits.
  Do not manufacture a refactor or a new abstraction to fill an audit quota.

## Work and ownership

Independent writers use fresh worktrees. They own only their assigned source,
proof, and test files; the main worktree owns shared ledgers, gates, and this
record. Findings include affected code, the actual failure or measured saving,
verification receipts, and any rejected experiment.

- Audit VT, renderer, and terminal code with the corresponding proofs/tests.
   Integrate justified reductions or fixes without weakening receiver laws.
- Audit remaining pure session policies, framing, checkpoints, names, replay,
   listing, and remote/status policies with their proofs/tests.
- Audit `Tools/`, `Manager/`, entry-point composition, and recipes. Integrate
   fixes for unnecessary policy or observable manager failures.
- Audit runtime, POSIX/C, build/configuration, proof census, and verifier
   orchestration. Capture confirmed recurring failure modes with the smallest
   useful deterministic check.

Commit verified steps as they become concrete. A step with no justified code
change records its findings with the next verified checkpoint.

## Checkpoints

### Step 1 — propagate CI history errors

Complete locally. A scheduled runner decision must distinguish empty history
from failure to read history. The failing check removes a throwaway repository's
Git metadata and requires a nonzero exit with no runner matrix; the old script
instead reported success and selected Ubuntu alone. Moving the history command
to a standalone assignment propagates its failure through `set -e`.

All seven actual runner checks pass, including recent and stale histories.
Both required builds, source gates, shellcheck and standalone formatting pass.
This is an IO/script contract tested against the real command, not a theorem
about an unconnected model. No session runtime, proof, C or dependency changed.

## Completion

Review the assembled diff independently, resolve actionable findings, and
run both required builds and the complete foreground verifier after deletions
and runtime edits. Record mutation results separately from compiler failures.
Recheck standalone formatting and repository hooks. Archive this spec with
an explicit completion record, restore the no-live-spec pointer, commit and
push the verified changes to `main`. Report hosted and platform limitations
without treating unexecuted checks as passes.
