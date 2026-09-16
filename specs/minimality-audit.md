# 2026-09-14 minimality-audit — smaller code, stronger boundaries

Status: active
Updated: 2026-09-14
Next: Step 2 — make coverage semantic
Predecessor: `specs/archive/scrollback-fidelity.md` (complete)

## Goal

Audit and tighten linger without adding features: delete code that has no consumer,
use current Lean 4 idioms where they reduce code, harden the raw POSIX boundary,
close runtime/test gaps the proofs cannot see, and leave the user and contributor
documentation shorter and true. Every behavioral fix starts with a failing check;
every deletion survives the complete verifier stack.

## Requirements

- **R1 — Test safety.** While a verification suite runs, it SHALL terminate only
  processes created by that suite; it SHALL NOT signal unrelated `linger` sessions.
- **R2 — Terminal restoration.** If attach output fails after raw mode is acquired,
  the client SHALL still restore termios and close its daemon connection.
- **R3 — Honest outcomes.** When a daemon refuses, disappears, or sends malformed
  frames, one-shot, wait, attach, and watch commands SHALL return a nonzero status;
  only an observed completion or requested detach SHALL return success.
- **R4 — Bounded runtime.** During sustained connects or replies, each poll round and
  each client request SHALL remain bounded, and a failed connect SHALL NOT unlink a
  socket while that session's ownership lock is held.
- **R5 — Durable recovery.** Checkpoint I/O failures SHALL be visible and SHALL NOT
  terminate the daemon or silently replace unread recovery state with a fresh session.
- **R6 — Safe POSIX inputs.** Before process syscalls, linger SHALL reject values that
  POSIX interprets as process groups; wait status SHALL be read only after a requested
  child is reported complete. Process-spawn setup/exec failures SHALL reach the parent.
- **R7 — Exact coverage.** The coverage gate SHALL associate every pure-core definition
  with theorem statements by fully qualified constant, not by a colliding basename.
  Suite check counts SHALL be exact, and a skipped required regression SHALL not count
  as a pass.
- **R8 — Minimal Lean.** A definition, field, parameter, branch, proof, or parsed field
  with no executable or downstream proof consumer SHALL be deleted unless an explicit
  contract preserves it. Retained duplication SHALL have distinct semantics.
- **R9 — Current compatible Lean.** The tree SHALL use modern v4.34 APIs when they are a
  net simplification. The toolchain SHALL move from rc2 to stable only when the matching
  standalone `lean-fmt` tag exists; the exact-tag CI guard SHALL not be weakened.
- **R10 — Minimal truthful docs.** README SHALL contain only installation, command
  surface, and user-visible semantics/caveats. AGENTS SHALL contain only active state
  and rules. THEOREMS SHALL contain only anchors, rungs, conformance assumptions, and
  open proof boundaries. All claims and names SHALL match code/theorem types.
- **R11 — Verification.** Every step SHALL pass its targeted checks, `./lake build`,
  `./lake build Theorems Tests`, source/coverage gates, and any affected pty suites.
  The final step SHALL pass foreground `./tests/e2e.sh` warning-free.

## Acceptance criteria

**Unrelated-session safety**
- Given a live sentinel in another `LINGER_DIR`
- When a suite runs
- Then the sentinel remains alive and a source gate rejects unscoped process killing

**Cleanup under failure**
- Given PTY stdin and closed stdout
- When attach enters raw mode and its hand-back write fails
- Then the tty settings after exit equal those before attach

**Failure status**
- Given a rejected label, malformed connection, or daemon loss
- When the relevant CLI command exits
- Then its status is nonzero and its diagnostic names the failure

**Bounded daemon**
- Given sustained connection/reply traffic
- When poll rounds continue
- Then pty/client progress continues, transport state stays capped, and ownership
  prevents a live socket from being removed

**Recovery I/O**
- Given deterministic save, read, or delete failure
- When the checkpoint path is exercised
- Then the failure is reported and no recovery state is silently lost

**POSIX boundary**
- Given pid zero/out-of-range, child setup failure, or exec failure
- When the wrapper runs
- Then it fails without signaling/reaping another process or claiming spawn success

**Semantic coverage**
- Given two definitions with the same basename
- When one definition loses every theorem reference
- Then the coverage gate fails on that fully qualified definition

**Minimality**
- Given each deletion candidate
- When references, proof dependencies, builds, and affected tests are checked
- Then only candidates with no contract-bearing consumer are removed

**Documentation**
- Given the shipped CLI and theorem declarations
- When docs are audited mechanically and by a fresh reviewer
- Then all names/claims resolve, known caveats remain, and no duplicated history or
  rationale remains outside the worklog/archive

## Design constraints

- Preserve `Linger/Core` purity and the private `Vt`/`State`/`Buf` boundaries.
- Keep C to syscall, ABI conversion, input validation, and child-side process setup;
  policy stays in Lean. A correctness check may add boundary code even when LOC rises.
- Do not merge similar loops whose EOF/backpressure/timeout policies differ.
- Do not weaken a theorem, ratchet, exact-tag check, or fixture to buy green.
- `SCRATCHPAD.md` stays append-only; archived specs stay closed.
- One writer uses this tree. Independent reviewers remain read-only.

## Steps

### Step 1 — make the test gate safe — done ✓ (2026-09-14)

Removed every unscoped process-name kill. The full gate now keeps a real session in
another `LINGER_DIR` alive through all suites, and `tests/gates.sh` rejects future
`pkill`/`killall` regressions. Suite and shim checks require exact counts; fish is a
required CI prerequisite rather than a counted skip. The resume winsize probe is a
child mode of the existing Lean e2e binary, so no embedded Python executes.

RED: the new source gate found all three `pkill` sites; the resume suite failed its
geometry assertion when `--winsize-probe` had no dispatcher. GREEN: source gates,
resume (9), terminal (12), shim smoke (12), and foreground `./tests/e2e.sh` all passed;
the sentinel survived all ten suites.

### Step 2 — make coverage semantic

Replace the basename/text theorem census with fully qualified core constants and exact
occurrences in elaborated theorem types (or the smallest equivalent Lean-environment
check). Break-verify with a colliding-name claim removal. Retain cap zero.

### Step 3 — make client cleanup and outcomes honest

Write failure-first pty cases, nest attach finalizers so termios and fd cleanup always
run, and replace Boolean/`Option` reply results with the smallest sum that distinguishes
completion, exit, refusal, loss, and silence. Map CLI statuses accordingly; include
rejected labels, daemon loss during attach/wait, and idle-stdin daemon loss for `send -`.

### Step 4 — bound daemon and listing work

Bound accepts per poll round and total pending connections using an existing policy cap
or one named runtime cap. Give `queryInfo` an absolute deadline and decoder-error exit.
On failed connect, use the ownership lock to distinguish stale from owned before unlink;
construct listing liveness from confirmed outcomes, not the directory snapshot. Add live
oracles for slow-client cut and connect flood.

### Step 5 — make checkpoint failures explicit

Keep save errors from unwinding the daemon; distinguish no file/corrupt bytes/read I/O;
report failed deletion; put established daemon resources under cleanup finalization. Make
the HOME-less fallback state directory per-user. Add deterministic E2E failures.

### Step 6 — harden and re-audit the C boundary

Reject pid selectors/range overflow, fix `waitpid(..., WNOHANG)` result handling, preserve
errno, reject zero-byte reads, detect cwd truncation, and accurately document sentinels.
Make detached and PTY spawn setup/exec failure observable to the parent with one shared,
close-on-exec error mechanism; keep child-after-fork work minimal and checked. Re-run the
exact export/caller/core-replacement audit; do not raise the shim ratchet.

### Step 7 — delete and modernize

Apply only break-verified simplifications: redundant `Nat` zero guards in `printMark`;
confirmed orphan definitions/proofs/fields; direct delegation for duplicate one-line
semantics; unused defaults; discarded remote fields; modern `String.split`/`contains`;
`Checkpoint.R` as `abbrev` if the complete proof build accepts it. Re-measure all
ratchets. Keep proof seams and distinct-policy loops rejected by the audit.

### Step 8 — minimize and align documentation

Correct theorem hypotheses/names, status glyph/remote/watch/command semantics, raw-boundary
scope, ratchet wording, and stale comments. Reduce README/AGENTS/THEOREMS/recipes README to
the minimum load-bearing content; preserve the gated prior-art shape, §Reading promise,
A5 projection names, Graphics/scrollback caveats, conformance entry 11, and open paint
budget. Update code comments in the same change as the behavior they describe.

### Step 9 — verify, review, compound

Run all builds and foreground E2E. Run a fresh read-only aspect review against this spec;
fix verified findings only. Record each durable lesson as the narrowest automatic artifact:
regression test for bugs, source gate for syntactic ties, theorem for pure properties,
and concise standing rule only where no checker can decide it. Update this status, append
the worklog, archive this spec with completion record, commit, and push.
