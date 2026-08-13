# lean-zmx → linger

Session attach/detach + a CLI session overview in pure-function Lean 4.
The binary is `linger` (renamed from `lzmx`; the repo keeps its
historical name, and the checkpoint magic stays "LZMX" — a frozen
format identifier, not branding).
`README.md` is the user-facing overview. `PLAN.md` is the original
requirements (goal-level, not current state); `specs/archive/` holds the
closed build plans with their completion records
(`lean-zmx.md`, `bigger-theorems.md`).

## Where things stand — read this first after any compaction

1. **`specs/grid-fidelity.md` is the ACTIVE plan** — goal,
   definition-of-done, what is already in hand, the steps, and the risks
   that were measured rather than guessed. Its header block is the
   ten-second version. (Don't look for a living `PLAN.md`: the root one is
   requirements, and everything in `specs/archive/` is closed.)
2. **`SCRATCHPAD.md`** — append-only worklog: proof recipes, measured
   environment facts, break-verify records, and the negative results.
   Read before writing; append after; never delete prior entries.
3. Re-ground against those two files, not against a compaction summary:
   the summary is what dropped the nuance.

New work opens a new `specs/<slug>.md` and gets named in item 1 above;
archive the old one with a completion record rather than editing it.

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

## Scratchpad

`SCRATCHPAD.md` is shared notes. Read before writing; append
`## Step N notes — <ISO date>` after; don't delete prior entries.

## Commits

One commit per spec step: `step N: <summary>`. Don't rewrite pushed
history.
