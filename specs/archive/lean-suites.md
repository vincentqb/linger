# lean-suites — the pty suites become Lean; the tree carries no Python

Status: **complete (2026-08-29)** — archived record, do not edit
Predecessor: `specs/archive/pin-the-gaps.md` (which added the tenth suite,
`watch`, and the per-suite check-count floors that made this port safe).

## Completion record

Ten pty suites and the coverage gate ported from Python to Lean. **Zero `.py`
files remain in the repo.** `./lake build`, `./lake build Theorems Tests` and
`./tests/e2e.sh` green and warning-free (`E2E OK — 10 live suites green`), every
floor exact, `SHIM_CAP` unmoved at 27/27, coverage at `259 defs, 16 unclaimed,
cap 16`.

| suite | checks | from |
|---|---|---|
| `attach` | 35 | `tests/attach_test.py` |
| `agent` | 24 | `tests/agent_test.py` |
| `watch` | 17 | `tests/watch_test.py` |
| `robust` | 14 | `tests/robust_test.py` |
| `terminal` | 12 | `tests/terminal_query_test.py` |
| `remote` | 11 | `tests/remote_test.py` |
| `resume` | 9 | `tests/resume_test.py` |
| `graphics` | 9 | `tests/graphics_test.py` |
| `overview` | 7 | `tests/overview_test.py` |
| `status` | 5 | `tests/status_test.py` |
| `remote-live` | 5 | `tests/remote_live_test.py` (opt-in, not in the gate) |
| `coverage` | — | `tests/coverage.py` (the source-tree ratchets) |

## The question this spec had to answer first

"The tests would be stronger as Lean theorems." **They cannot be theorems.** A pty
suite drives the real binary through real syscalls, so it is `IO`; a theorem needs a
pure function, and the pure core already carries 1467. `LingerTest.lean` was already
the in-repo precedent for a Lean `IO` test exe with the same `PASS`/`FAIL` contract.

So the claim the port actually makes is narrower and still worth it: **a suite in
the implementation's own language cannot drift from it.** The Python held copies of
what the implementation emits; the Lean suites name the emitter —
`Render.leaveAnsi`, `Status.wantsYou`, `Listing.humanListing []`,
`Render.escSeq`/`Terminal.STFinal`, `Remote.parse`. A rename is a compile error
where it used to be a passing assertion.

## The precondition, and why the port was allowed

It was worth doing **only if it did not grow the C trust boundary for a test's
benefit**, because that boundary is the audited attack surface and `SHIM_CAP`
ratchets it deliberately. It did not: `Linger.Posix` already exposed `spawnPty`
(forkpty *with the winsize set before exec* — strictly better than the
`pty.fork()`-then-`ioctl` race every Python copy had), `winsizeSet`, `kill`,
`alive`, `waitpidNohang`, `chmod`, `flock`, and the poll/read/write trio. `SHIM_CAP`
is still 27/27.

## What got better, not just relocated

1. **A platform split deleted rather than ported.** `tests/procs.py` filtered
   candidate daemon pids by `LINGER_DIR` via `/proc/<pid>/environ` on Linux with an
   `lsof` fallback on macOS — one of the repo's only two platform splits. Asking
   `linger info` over `<LINGER_DIR>/<name>.sock` makes that isolation *structural*,
   so the filter is gone. `Env.daemonPid` is one `info` plus one `ps -o ppid=`, the
   same command on both platforms.
2. **A non-vacuity closed.** The Python's `assert dpids` proved a daemon pid was
   *found*, never that the SIGKILL landed. `Env.crashDaemon` returns `true` only if
   the daemon was found, was alive first, and is gone after.
3. **Two bugs found by porting.** `Child.tryWait` reaps, so a second call is ECHILD
   — that aborted `E2E.Terminal` before its first check, and the fix is to ask
   `Posix.alive`, which does not reap. And the coverage port initially measured
   *less* (193 defs against 259) because `takeWhile identChar` stops at the
   namespace dot; caught only by diffing the two gates, which now produce
   byte-identical output.

## What is deliberately still not Lean

`tests/e2e.sh`, the orchestrator. It sequences the builds, runs the `git grep`
purity gates and the ratchets. A Lean program shelling out to `git grep` and
`./lake` would be a worse shell script. **A deliberate stop, not an oversight.**

## The follow-up, scoped and not done here

`E2E/Coverage.lean` is a *textual* port on purpose — identical scan, identical
numbers, caps keep their meaning, and that identity is what made deleting the Python
safe. The stronger design is to stop scanning text: import the `Theorems`
environment and ask whether each `Linger.Core` constant appears in any theorem's
**type**. Semantic, no comment-stripping, immune to formatting. It changes the
measure and therefore the cap, which needs re-justifying — so it is its own commit.
