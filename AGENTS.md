# lean-zmx

Session attach/detach + session-manager TUI in pure-function Lean 4.
`specs/lean-zmx.md` is the living plan (steps, exit criteria) — re-read
it and `SCRATCHPAD.md` first after any context compaction.

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
  logic-free (syscall + errno only).
- Theorems resolve tensions: when two requirements collide, state the
  invariant in THEOREMS.md and prove it, then code to it.
- A theorem or test that cannot fail is worthless: break the code once
  to see it catch (record the break in SCRATCHPAD.md).
- Session names pass through `Zmx.Core.Name.sanitize` before touching
  any path. Never interpolate raw names into socket/checkpoint paths.

## Scratchpad

`SCRATCHPAD.md` is shared notes. Read before writing; append
`## Step N notes — <ISO date>` after; don't delete prior entries.

## Commits

One commit per spec step: `step N: <summary>`. Don't rewrite pushed
history.
