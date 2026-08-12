# lean-zmx

Session attach/detach + a CLI session overview in pure-function Lean 4.
`README.md` is the user-facing overview; `specs/archive/lean-zmx.md` is
the (closed) build plan with the completion record. Re-read
`SCRATCHPAD.md` first after any context compaction — it holds the
proof recipes and the measured environment facts.

New work opens a new `specs/<slug>.md`; don't reopen the archived one.

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
