# 2026-09-14 minimality-audit — smaller code, stronger boundaries

Status: complete (2026-09-15) — all nine steps done, archived
Updated: 2026-09-15
Next: nothing; open a new specs/<slug>.md for the next item
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
  with theorem types by fully qualified constant, not by a colliding basename.
  Suite check counts SHALL be exact, and a skipped required regression SHALL not count
  as a pass.
- **R8 — Minimal Lean.** A definition, field, parameter, branch, proof, or parsed field
  with no executable or downstream proof consumer SHALL be deleted unless an explicit
  contract preserves it. Retained duplication SHALL have distinct semantics.
- **R9 — Current compatible Lean.** The tree SHALL use modern v4.34 APIs when they are a
  net simplification. The toolchain SHALL move from rc2 to stable only when the matching
  standalone `lean-fmt` tag exists; the exact-tag CI guard SHALL not be weakened.
- **R10 — Minimal truthful docs.** README SHALL contain only installation, command
  surface, user-visible semantics/caveats, and a tree-orientation table — the last
  kept deliberately: it is the one place the pure/impure split is visible to someone
  browsing the repo, and seven lines is cheaper than the question. AGENTS SHALL
  contain only active state and rules. THEOREMS SHALL contain only anchors, rungs,
  conformance assumptions, and open proof boundaries. All claims and names SHALL
  match code/theorem types, and a claim that can be checked mechanically SHALL be
  gated rather than reviewed.
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

### Step 2 — make coverage semantic — done ✓ (2026-09-14)

`Theorems/Coverage.lean` now discovers every explicit pure-core `def`, resolves its
actual environment constant (including private declarations), unions exact constants
from elaborated theorem types, and fails the build on any miss or ambiguous source name.
The checker lives in the sanctioned theorem friend region; E2E imports only its public
source scanner and therefore gains no Vt forge access. The three remaining legacy leaf
proof files moved to the current module form so their declarations enter that environment.

Break: adding unclaimed `Linger.Core.Buf.Probe.feed` left the old gate green (`271`,
zero misses) because other `feed` theorems satisfied its basename. The new gate failed
with that exact fully qualified name. The semantic census has 276 definitions: the old
dedup hid five declarations across `step`, `feed`, and `mendAt`. Builds, source gates,
coverage runtime classification, and `lean-fmt check` pass with the zero-miss invariant.

### Step 3 — make client cleanup and outcomes honest — done ✓ (2026-09-14)

`Client.Drained` now distinguishes completion, child exit, refusal, transport/protocol
loss, and bounded silence; callers map only observed completion to success. Attach has
a separate lost outcome, nested finalizers guarantee termios restoration and socket
close even when hand-back output fails, and `send -` polls the daemon while stdin is
idle. All daemon text is scrubbed before stderr.

RED: Agent failed rejected-label, malformed-response, and idle-sender-loss checks;
Attach failed daemon-loss, wait-loss, and broken-stdout termios checks; Watch failed
daemon-loss — seven independent failures. GREEN: Agent 28/28, Attach 38/38, Watch
18/18. Existing drain loops remain separate because blocking, silence-bounded, and
interactive conversations have different termination policy; only their outcome type
and text scrubber are shared.

### Step 4 — bound daemon and listing work — done ✓ (2026-09-14)

Each listener round accepts at most `Session.maxClients`; the pure `.connected`
handler admits or refuses that batch before the next poll. Connected info reads use one
absolute two-second window, stop on decoder error, close in `finally`, and degrade I/O
failure to a live/unknown row. A failed initial connect removes its path only while
holding that name's nonblocking ownership lock; the listing's live set now comes from
confirmed outcomes, so a stale socket cannot hide a same-name checkpoint on the first
listing.

RED: Resume failed first-list recovery; Robust failed lock-held preservation, continuous
info deadline, and bounded accept count. GREEN: Resume 9/9 and Robust 18/18. A new direct
runtime oracle also covers the existing `outbufCap` cut; disabling the cut fails that
check. No parallel buffer, connection state, or policy layer was added.

### Step 5 — make checkpoint failures explicit — done ✓ (2026-09-14)

Save/delete hook errors are caught and logged at the daemon effect boundary, so state
serialization failure cannot unwind the service and cleanup failure cannot disappear.
`loadCkpt` returns `none` only for absence or successfully-read corrupt/foreign bytes;
an existing unreadable path throws a contextual error before any fresh daemon starts.
The established daemon loop now owns listener, clients, pty, child, socket path, and name
lock under one `finally`, removing the socket before releasing ownership. HOME-less state
falls back under `/tmp/linger-$UID/state/<host>`.

RED: Overview failed the per-user path check; Resume failed save containment, unreadable
state refusal, and delete reporting. GREEN: Overview 8/8, Resume 12/12. The existing corrupt
checkpoint case still starts fresh, preserving the cache-not-contract policy.

### Step 6 — harden and re-audit the C boundary — done ✓ (2026-09-15)

Reject pid selectors/range overflow, fix `waitpid(..., WNOHANG)` result handling, preserve
errno, reject zero-byte reads, and accurately document sentinels. Make detached and PTY
spawn setup/exec failure observable to the parent with one shared, close-on-exec error
mechanism; keep child-after-fork work minimal and checked. Re-run the exact
export/caller/core-replacement audit; do not raise the shim ratchet.

`Linger.Posix.checkPid` rejects `0` and values that cast to a negative `pid_t` before
`kill`/`alive`/`waitpidNohang`; `read` refuses `max = 0`, which `read(2)` answers `0` for
without testing for end of file — the one value that would forge this wrapper's EOF.
`linger_spawn_pty` and `linger_spawn_detached` report child-side failure over a shared
close-on-exec pipe, so a missing program is an error rather than a live pid and a dead
session. `waitpid` now branches on `r == 0` explicitly and answers a non-`ECHILD` failure
`-2` (ask liveness) rather than `-1` (still running), which cannot hang a caller.
`bind`/`listen`/`execvp` capture errno before `close`/`free`, matching `connect`'s existing
shape. Exports unchanged at 22; every wrapper's 2026-09-14 audit conclusion holds.

Two audit items resolved as no-change, measured rather than assumed. `linger_getcwd_of`
needs no truncation branch: the kernel builds `/proc/<pid>/cwd` in a `PATH_MAX` buffer, so
an over-long cwd fails `readlink` with `ENAMETOOLONG` — checked at exactly 4096 bytes and
at ~4500 — and the existing `n < 0 -> ""` already covers the class. And there is no fourth
`waitpid` outcome to report: with a constant `WNOHANG` and selectors rejected in Lean, the
reachable errno set is `{EINTR, ECHILD}`.

RED: `lingertest` self-terminated, because `kill 0 15` reached its own process group — the
defect, demonstrated. GREEN: 24/24, including a child that walks past `PATH_MAX` and a
`getcwdOf` that answers with a usable directory or nothing (break-verified: returning any
unusable non-empty path fails it).

Two findings outside the C boundary, both from the same root cause — a gate that only ran
in CI. `E2E/Resume.lean`'s save-failure check was flaky 1-in-5: the last-detach save fires
only when the session is dirty, and the daemon's first tick is eligible immediately
(`lastCkptMs` starts at 0), so it could checkpoint the shell's prompt before the test
planted the bad tmp path. The test now produces output *after* planting it and asserts that
precondition (Resume 14, after the daemon-exit check below). And eight files had drifted past `lean-fmt format --check`, which
ran nowhere but CI, so a locally-passing `lean-fmt check` (the linter) looked like the
formatter passing too: the tree is reformatted and `tests/e2e.sh` now runs the layout gate
next to the source-tree gates.

### Step 7 — delete and modernize — done ✓ (2026-09-15)

Apply only break-verified simplifications; re-measure all ratchets; keep proof seams
and distinct-policy loops rejected by the audit.

`Vt.printMark`'s `if v.cursor.x == 0 then 0 else v.cursor.x - 1` is `v.cursor.x - 1`
on `Nat`, so the guard is gone — and with it `hx0 : v.cursor.x ≠ 0`, which was then
unused in `print_mark_eq` and not needed for its truth (at `x = 0` both sides read
column `0`). Dropped from `print_mark_eq`, `cursor_print_mark` and
`Render/Pen.print_mark`, with three call sites losing a `(by omega)` (`Grid` once, `Row` twice). The second
guard, `&& cx0 != 0`, stays: also behaviourally inert, but it is what makes the
step-left total without reading the pair invariant.

`RemoteRow.clients` and `.labels` were parsed, scrubbed and unit-tested with no
consumer: the one caller builds a fresh four-field row. Deleted, along with the
comment claiming the peer "does not forward them" — it does, and a false label on a
known gap is the failure mode SCRATCHPAD 2026-08-12 already recorded. `Checkpoint.wU8`
/`rU8` and their `rt_u8` formed a closed island — no writer or reader composes them,
and nothing uses the theorem. `Checkpoint.R` is an `abbrev`, which retires `@[expose]`
and its justification. Pure-core defs: 276 → 273, all still in theorem types.

Ratchets re-measured, not assumed. `SHIM_CAP` 22, `RUNTIME_PARTIAL_CAP` 2 and
`RECDEPTH_CAP` 1 are exact — the surviving `maxRecDepth 4096` on `stepGround` was
re-tested by deletion and still fails at depth. `E2E_PARTIAL_CAP` drops 5 → 3: two of
its slots belonged to the text-based coverage scanner deleted in step 2, so the cap
had stopped biting (break-verified at 4).

Modern Lean, with two negative results so they are not re-attempted: `String.contains`
replaces `entry.any (· == '=')`, but v4.34.0-rc2 has **no** `String.containsSubstr`, so
`has`/`contains` keep their `splitOn` bodies; and `String.split` returns a
`Std.Iter String.Slice`, so routing `lines` through it costs a `.toList` and a
`.map (·.toString)` — more code, not less.

### Step 8 — minimize and align documentation — done ✓ (2026-09-15)

Correct theorem hypotheses/names, status glyph/remote/watch/command semantics,
raw-boundary scope, ratchet wording, and stale comments. Reduce the four documents to
the minimum load-bearing content; preserve the gated prior-art shape, §Reading promise,
A5 projection names, Graphics/scrollback caveats, conformance entry 11, and open paint
budget. Update code comments in the same change as the behavior they describe.

Four claims were false, not merely stale. **The idle glyph**: `Status.icon` emits `⣀`
and README printed `⡀` — one dot, not four — which no test could see, because the
suites compare against `Status.icon` itself. That is now a gate in both directions
(every emitted glyph appears in README; README shows none the code cannot emit; the
count is seven), break-verified from each side. **The raw-boundary scope**: AGENTS
said only `Linger/Posix.lean` and `c/shim.c` "touch the OS", which is not what is
gated or true — the runtime reaches the OS through Lean core's `IO` throughout; what
is gated is that every `@[extern]` lives in `Linger/Posix.lean`. **A theorem that does
not exist**: `Theorems/Render/Scrollback.lean` called the whole-stream byte bound "a
Step-5 theorem", but `scrollbackAnsi_le` was the optional last step of
`specs/archive/scrollback-fidelity.md` and the spec was archived without it; THEOREMS
already said fixture-carried. **Check-count floors**: two comments still described the
per-suite counts as floors after step 1 made them exact.

Verified rather than reviewed where possible: every recipe file the recipes README
lists exists, every command in the README table appears in the CLI dispatch, and
`watch`'s "marks output seen" holds through `lookSeq := s.outSeq` on attach. Aliases
stay undocumented in README on purpose — `linger --help` carries them in `[a]ttach`
form, and the fourteen in `usage` would cost more than they inform. Note `l`/`list` are
accepted by the dispatch and appear in neither, which is a real if minor gap.

**This paragraph also recorded a false clean, and step 9 caught it.** It claimed every
theorem name cited in THEOREMS resolved to a declaration, "0 missing of the extracted
set". The check behind that claim was `git grep -w <name>`, which matches prose and
comments — so `scrollbackAnsi_le`, named by THEOREMS.md and two code comments and
declared nowhere, satisfied it. That is the same shape as the vacuous glyph loop below:
a verification that cannot fail. The name is now absent from all three sites, and
resolution is a gate that looks for `theorem|lemma|def|abbrev` over 85 citations,
break-verified.

Also retired three dangling "Step-N" references to archived spec numbering, now that a
different step 7 exists, and `Cli.Hooks`' docstring says what the seam is for instead.
R10 amended in place rather than obeyed silently: the README's layout table is not
installation, command surface, or semantics, and it stays anyway — the requirement was
too tight, and the reason is recorded with it.

### Step 9 — verify, review, compound — done ✓ (2026-09-15)

Full stack green: `./lake build`, `./lake build Theorems Tests`, `sh tests/gates.sh`,
`lean-fmt check`, `lean-fmt format --check`, and foreground `./tests/e2e.sh`
warning-free, with zero leaked state directories or daemons after a complete run.

**Three changes landed during this spec without being recorded in it**, which a
reviewer scoped to this file would not have reviewed. Named here rather than left to
the worklog:

* `e3c857c` — the process-group signal gate, and two leak fixes. `verdict` takes the
  `Env` and removes the suite's state directory on a green run (538 had accumulated,
  ten suites × one per run); `E2E/Resume.lean` gained the check that a *reported*
  delete failure still lets the daemon exit, after an orphaned `drop-fail` daemon was
  found alive for 1h48m. So step 6's "two findings outside the C boundary" was an
  undercount: these are two more.
* `f1df868` — macOS off the per-push CI path, the `gates` job stopped compiling (the
  `e2e` job already rebuilds from empty, so one signal was billed twice), and
  `push: branches: [main]` closed the PR double-billing trap. Measured: 66-97 billed
  minutes per push, 50-70 of them macOS at 10x; 36 commits exhausted a 2,000-minute
  quota. A `paths:` filter was measured and rejected.
* `02c53a3` — `tests/ci-runners.sh` (the third sanctioned non-Lean file, justified by
  the `gates` job compiling nothing) and `E2E/Ci.lean`, which drives it rather than
  copying it, against real temporary git repositories.

**A fresh read-only reviewer found 24 items; the load-bearing ones were four checks
that could not fail.** Every one is now fixed and break-verified:

1. **The reverse status-glyph gate never executed.** Its README-side filter,
   `grep -vE '^[[:alnum:][:punct:][:space:]]$'`, was meant to drop non-glyph noise, but
   glibc classifies `⣀ ⣷ ⣿ ✓` as `[[:punct:]]`, so it deleted all seven and the loop
   body ran zero times. The gate advertised "both directions" while one existed, and
   both break-verifications recorded for it had landed on the forward half. Fixing it
   surfaced a second defect in the *forward* half: `for g in $icon_glyphs` unquoted
   undergoes pathname expansion, and `?` matched the `c/` directory — so the `?` glyph
   was never checked either. Both loops now run under `set -f`, both extractions assert
   a count of seven, and four break directions bite (README loses a glyph; code drops a
   state; and `?` specifically, from each side).
2. **`E2E/Ci.lean`'s 7th check could not exercise the script.** It ran `git` from Lean
   with an argv array, where `--since=8 days ago` is one argument by construction, so it
   could not exhibit the *shell* quoting bug it claimed to guard — and its stated
   premise was false, since the "recent commit" check already catches that. Deleted; the
   suite is 6.
3. **`testZeroLengthRead` was satisfied before touching an fd.** `read` throws on
   `max == 0` as its first statement, so eight lines of socket setup proved nothing.
   Reduced to what it pins.
4. **`testDeepCwd` judged `isDir` after `rm -r`** had removed the tree, so any
   non-empty answer failed and the check had degraded to "the answer was empty" — which
   matters on macOS, where the libproc branch NUL-terminates rather than refusing.

Two claims were false and are corrected: `scrollbackAnsi_le` (above), and
`linger_getcwd_of`'s comment, which credited `readlink` with refusing a short buffer —
readlink truncates silently; the protection is the kernel's `d_path` failing the call,
which is why `buf` must stay `PATH_MAX`.

**One real behavioural regression, found by review rather than by test.** Rewriting
`linger_spawn_pty` from `execvp` to `execve` in step 6 silently dropped `execvp`'s
`ENOEXEC` fallback, so a shebang-less executable — legal input to
`linger attach <name> <cmd>` — stopped running. Restored (pre-allocated `shargv`, since
the child may only call async-signal-safe operations), with a `lingertest` check that
break-verifies, and made crash-safe so a future regression reports FAIL rather than
aborting the binary and losing the count. `lingertest` is 26, having also gained the
waitpidNohang overflow case the review found missing.

Also from the review: `waitpidNohang`'s and `spawnDetached`'s docstrings were behind
their step-6 behaviour; `E2E/Ci.lean` leaked two fixture repositories on failure (now
`try`/`finally`); `verdict`'s docstring called itself "the single exit point every suite
goes through" while two non-pty suites print their own verdict; the process-group gate's
pathspec is narrower than AGENTS claimed; `testProcessSelectors` omitted the overflow
case for `waitpidNohang`; and the macOS cost measurement had been copied into seven
files. Copies cut to pointers, keeping the evidence in SCRATCHPAD and the decision in
the workflow header — the numbers had *already* started to rot, which is where three of
the four stale figures above came from.

R10's "a claim that can be checked mechanically SHALL be gated" now holds for two
claims rather than one: the glyph set and THEOREMS declaration resolution.

Run all builds and foreground E2E. Run a fresh read-only aspect review against this spec;
fix verified findings only. Record each durable lesson as the narrowest automatic artifact:
regression test for bugs, source gate for syntactic ties, theorem for pure properties,
and concise standing rule only where no checker can decide it. Update this status, append
the worklog, archive this spec with completion record, commit, and push.
