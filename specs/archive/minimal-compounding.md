# Minimal code and compound engineering audit

## Status

Complete locally, 2026-09-27. The starting point is `49f48c0` on `main`;
Step 1 is `041e7c5`. The three parallel source audits and local runtime/verifier
audit are integrated. Independent review's census and child-output findings
are fixed, regression-checked and reviewed. The complete foreground Linux
verifier and both required final builds pass. Hosted checks are pending for
the final checkpoint; the preceding checkpoint's hosted verification did not
start because of the repository owner's GitHub billing/spending limit.

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

### Step 2 — remove duplication and make the verifier harder to fool

Complete and verified in the assembled tree.

The CSI collector loses a redundant empty-prefix branch. Renderer proofs share
the existing projection-preservation lemmas from the earlier `Keeps` module,
removing the duplicate grid/mode walks previously blocked by file order.
Exact collector equations and all receiver-law statements remain unchanged.
Remote host validation uses its duplicate-reporting walk once; a kernel-checked
certificate establishes equality to the predecessor expression for every input.
A private batch-preservation lemma replaces five Session inductions; Wire reuses
its existing unknown-tag and leftover facts.

The two client drain loops return directly on their distinct terminal conditions.
They retain separate timeout/completion policies, decoder-error precedence and
exit-status propagation. The selector inlines a single-use attach wrapper while
retaining its blocking child wait and terminal cleanup.

The importer has a proved diagnostic transformation that removes C0, DEL and C1
while preserving printable text. Actual executor regressions cover rejected
names, missing saved directories and missing save paths. Both creation-child
streams are captured and routed through that boundary on failure; checks
preserve the error cause, silent success and immediate stop after a failed
creation. The original path and argument values are retained.

The definition census uses Lean's parser, standard private-name resolution and
one environment/theorem index. Scope tracking ignores quotations and handles
compound namespaces and section names. Renderer/replay classification reads
resolved constants from the built program, checks the target's module provenance
and excludes references within that module. Compiled fixtures cover escaped and
multiline declarations, nested comments, quoted scopes, opened/renamed/relative
references and private names shadowing a renderer. The standalone execution after
the program build avoids cached source-census results and separates the census
from the native live-test executable.

Retained decisions have no new evidence to reopen them: the isolated POSIX
boundary, all C exports, fixed wire widths, VT representation, receiver domains,
distinct buffer/replay contracts, native terminal settings and portable entry
point. No dependency, production abstraction or proof-limit raise was added.
The worklog records the code price, compiling mutations, rejected experiments
and final verification receipts.

## Completion

The assembled diff has independent review with all findings resolved. Against
`49f48c0`, production shrinks by 25 lines and proofs/census by 197; verification
grows by 147. The complete source change is 75 fewer lines, including comments
and formatting, excluding work records and documentation.

The foreground Linux verifier passes from an empty build directory: clean
program/proof/test compilation, generated C ABI, source gates, standalone
formatting, parser/environment census, seven CI runner checks, fuzz fixtures,
POSIX smoke tests, all thirteen live suites with exact counts, and the
unrelated-session sentinel. Both required final builds pass separately.
The importer suite runs 47 checks and the selector suite 58.

Final assembled receipts are
`/tmp/linger-minimal-20260926/assembled-full-verifier-final.log`,
`final-verifier/`, `final-build.log`, `final-proofs-tests.log`,
`final-lint.log` and `final-shellcheck-warning.log`. The worklog indexes
worker audits, compiling mutations, equivalence certificates and rejected
experiments. Informational shellcheck suggestions for the existing literal
backticks and C filename inventory also occur at the baseline; warning-level
shellcheck passes. Repository hooks run with the final commit.

Archived with local verification complete. Hosted checks remain pending at
this checkpoint; no macOS, live GUI-terminal or real remote-host result is
claimed.
