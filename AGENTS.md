# lean-zmx → linger

Session attach/detach + a CLI session overview in pure-function Lean 4.
The binary is `linger` (renamed from `lzmx`; the repo keeps its
historical name, and the checkpoint magic stays "LZMX" — a frozen
format identifier, not branding).
`README.md` is the user-facing overview. `PLAN.md` is the original
requirements (goal-level, not current state); `specs/archive/` holds the
closed build plans with their completion records (`lean-zmx.md`,
`bigger-theorems.md`, `terminal-contract.md`, `grid-fidelity.md`,
`restore-conformance.md`, `ledger-cleanup.md`).

## Where things stand — read this first after any compaction

1. **Two specs are live in `specs/`, and both are started.**
   * **`specs/scrollback-fidelity.md` — Step 1 done (2026-08-19), Step 2 next.**
     `restore` now paints the session's ring into the *receiver's own* scrollback
     (`scrollbackAnsi`), and the three flagship screen statements are
     byte-identical to what they were — the hard exit criterion held. Read its
     "Where this stands" before anything else: it names Step 2 (the positive
     scroll specification, zero emitter change) and the two things not to
     re-derive — `replayEq`'s `sb` conjunct is blind to bugs *inside* `sbRows`
     (the literal-anchored fixtures are the oracle for the fit and the order),
     and the twelve mode bytes ending `scrollbackAnsi` are behaviourally inert
     but proof-load-bearing. The obvious emitter shape — painting
     `sbRows v ++ v.grid` as one tall array — *deletes* `paint_rows`' no-scroll
     argument; the staged push is why it did not.
   * **`specs/runtime-invariants.md` — Steps 1–2 done, 3–4 optional.** The
     daemon's two byte queues are now `Zmx.Core.Buf`, proved, with a grep gate
     in `tests/e2e.sh` that makes the theorems bite an `IO` caller no theorem
     can see. Its poll-plan half was **killed on purpose** (the
     `revents[i]`↔`fds[i]` premise lives in `c/shim.c`, not in Lean, so proving
     it would be decoration) — that negative result is recorded so nobody
     re-proposes it.
   Everything else is closed: `restore-conformance.md` (restore works into any
   client, proved for the modes, pen, sticky bundle, parser/decoder, the screen
   cells on both screens at every height, and the tab ruler) and
   `ledger-cleanup.md` (its five parked items plus the ssh-argv host guard) are
   in `specs/archive/` with completion records.
   (Don't look for a living `PLAN.md`: the root one is requirements, and
   everything in `specs/archive/` is closed.)
2. **`SCRATCHPAD.md`** — append-only worklog: proof recipes, measured
   environment facts, break-verify records, and the negative results.
   Read before writing; append after; never delete prior entries.
2b. **`.claude/last-compact-state.md`**, if it exists — written by a
   `PreCompact` hook (`.claude/precompact-snapshot.sh`) at the moment
   compaction started: the commit, what was uncommitted, and which worklog
   round was in flight. Facts, not a summary, and the three things a
   compaction genuinely eats — this file and the spec re-ground you; the
   summary does not. Gitignored, so a stale one is only ever your own.
3. Re-ground against those two files, not against a compaction summary:
   the summary is what dropped the nuance. Check the current work against
   the spec's Goal and Definition of done, not against the summary's
   description of it.
4. Close each round by updating the spec's status block (done ✓, next →) and
   committing a verified checkpoint. One item in flight at a time: a half-done
   item straddling a compaction is the thing most likely to be silently
   abandoned.

New work opens a new `specs/<slug>.md` and gets named in item 1 above;
archive the old one with a completion record rather than editing it. Keep the
live count small — two open specs is already one more than the
one-item-in-flight rule likes, and the second is only there because it is
finished enough to leave alone.

## Settled non-goals — don't build these

Each was decided with a reason; re-opening one needs a new reason, not a
fresh pair of eyes.

- **Windows, tabs, splits.** "Feature-complete multiplexer" is read as
  feature-complete *zmx*, not tmux: the OS window manager (or your
  terminal's tabs) owns composition. Recorded in
  `specs/archive/lean-zmx.md`.
- **An interactive picker.** One was built and shipped (step 8, with a
  passing pty test), then removed: a first-time user ran bare `linger`,
  got a full-screen picker and typed at it as if it were a shell. Bare
  `linger` now prints a listing and exits, and `tests/overview_test.py`
  guards that. Pickers live in `recipes/` (six lines of fish + fzf).
- **Storing images so they survive reattach.** Kitty/sixel/iTerm2
  sequences already pass through byte for byte while attached, and an app
  that redraws re-emits its own images (a reattach at a *changed* size
  nudges it via `SIGWINCH`; at the same size the kernel suppresses the
  signal). Persisting them needs kitty's placement model, only replays
  into the same terminal process that still holds the image — so not after
  a reboot, which is the point of the checkpoint — does nothing for
  sixel/iTerm2, and puts payloads in a periodic on-disk write. See README
  "Graphics" and `tests/graphics_test.py`.
- **Restoring the process tree.** Reboot-resume restores the screen,
  scrollback, modes, labels and cwd — not the programs. The
  tmux-continuum trade, taken deliberately.

## Build

- Always `./lake build` (the wrapper, not bare `lake`): this host's
  glibc 2.26 cannot run the toolchain's bundled clang, the wrapper
  routes C compilation through Homebrew clang. Bare `lake` looks 90%
  green and dies in the C backend.
- `./lake build` = program; `./lake build Theorems Tests` = proofs +
  unit tests. All three must be green before a commit.

## Rules

- `Zmx/Core/*` is pure: no `IO`, no `partial def`, no `sorry`. Effects
  are data (`List Effect`); the runtime executes them.
- Only `Zmx/Posix.lean` and `c/shim.c` touch the OS. Keep the shim
  logic-free (syscall + errno only). It carries a **wrapper-count
  ratchet** (`SHIM_CAP` in `tests/e2e.sh`): it drops silently, but
  raising it is a deliberate edit — the checkpoint for "does Lean core
  already expose this?" before adding a syscall. A source-tree property
  like this can't be a theorem; the grep gate is the right oracle
  (`verifier-in-the-loop`).
- Theorems resolve tensions: when two requirements collide, state the
  invariant in THEOREMS.md and prove it, then code to it.
- A theorem or test that cannot fail is worthless: break the code once
  to see it catch (record the break in SCRATCHPAD.md).
- Session names pass through `Zmx.Core.Name.sanitize` before touching
  any path. Never interpolate raw names into socket/checkpoint paths.
- `./tests/e2e.sh` is the gate before any commit that touches the
  runtime; it must stay green and warning-free.
- Restructure code for provability rather than weakening a theorem:
  name the stages (see `Vt.print*`, `Vt.step*`), clamp bounds locally,
  and prefer order-robust proof scripts (`repeat' split` +
  `all_goals first | …`) so a new branch doesn't break the proof.
- Any poll loop must freeze its fd set before polling (a mid-round
  accept desynced `revents` once and panicked the daemon).
- **A `maxHeartbeats` raise is a measurement, and it expires.** Nothing
  else expires it: a 2026-08-18 sweep deleted 18 of 20, and the control
  showed six were already deletable *before* the file split that
  prompted the sweep — they were budget added when the proofs were
  rougher and never re-measured. After any refactor, try deleting them.
  Ratcheted (`HEARTBEAT_CAP`); a new raise means a proof got harder,
  which is a signal to read, not to silence.
- **A `while`/`for` loop in a `do` block does not need `partial def`.**
  Five of the runtime's seven had it by habit. Two are honest (`pump`,
  `parseLs`) and named in THEOREMS.md §Total; ratcheted
  (`RUNTIME_PARTIAL_CAP`). Don't add a fuel parameter to shed the
  keyword — that converts a hang into a silent drop.
- **A proved pure value needs a grep gate to bite.** `Zmx/Runtime/*` is
  `IO`, so no theorem can see that the daemon calls `Zmx.Core.Buf`
  rather than open-coding the same sums — without the gate the theorems
  are arithmetic about a value nothing forces the runtime to use. Same
  species of oracle as `SHIM_CAP`. When you move a decision into Core,
  gate the runtime against re-growing it.
- **One writer at a time on this tree.** Two agents editing
  concurrently raced the coverage ratchet: untracked files are invisible
  to `git diff -- Zmx/`, so an out-of-band `coverage.py` read caught a
  half-written state and reported 28 unclaimed defs. Both also compile
  the same tree, so each sees the other's partial files as errors.
  Serialize, or give each writer a worktree.

## Scratchpad

`SCRATCHPAD.md` is shared notes. Read before writing; append
`## Step N notes — <ISO date>` after; don't delete prior entries.

## Commits

One commit per spec step: `step N: <summary>`. Don't rewrite pushed
history.
