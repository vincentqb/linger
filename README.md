# lean-zmx

Terminal session attach/detach plus a session-manager TUI, written as
pure functions in Lean 4. One binary, `lzmx`; one C file; theorems
where the design has tensions to resolve.

```
lzmx                 open the session manager (list · preview · attach · kill)
lzmx attach work     attach, creating the session if needed
lzmx watch work      attach read-only (mirror without touching)
ctrl-\               detach (session keeps running)
```

Sessions survive detach, ssh disconnects, and reboots: the daemon
checkpoints the terminal state, and attaching to a session whose daemon
is gone replays the old screen into a fresh shell in the same
directory.

## Why this shape

Following [zmx](https://github.com/neurosnap/zmx): session persistence
and window management are different jobs. Your window manager already
does windows — so there are no panes, splits or layouts here, and
nothing sits between your keyboard and the pty but a unix socket. The
TUI is a *manager* (the [zmx-session-manager](https://github.com/mdsakalu/zmx-session-manager)
role): it lists sessions, previews them, and `exec`s the plain client
when you pick one, leaving the byte path entirely.

Read-only observers and "the newest real terminal owns the size" are
borrowed from [abduco](https://github.com/martanne/abduco).

## Commands

| | |
|---|---|
| `attach <name> [cmd...]` | attach; creates the session if absent (upsert) |
| `watch <name>` | read-only attach: output mirrors, keys are dropped |
| `run <name> <cmd...>` | send a command line to a session without attaching |
| `send <name> <text...>` | send raw bytes to the session's pty |
| `detach <name>` | detach every client from a session |
| `list` / `list --porcelain` | live and resumable sessions (`--porcelain` is what remotes parse) |
| `kill <name>` | terminate the session |
| `history <name>` | print the session's scrollback as text |
| `wait <name>...` | block until the session's program exits; exit code follows it |
| `get` / `set` / `unset` / `clear` | session labels (`k=v`) |
| `version` | version plus resolved socket/state directories |

## Layout

```
Zmx/Core/      pure: no IO, no `partial`, no `sorry`
  Wire         framed client↔daemon protocol + incremental decoder
  Vt           restore-grade terminal emulator (grid, scrollback, modes)
  Render       Vt snapshot → ANSI bytes (reattach restore, previews)
  Session      the daemon as `step : State → Event → State × List Effect`
  Checkpoint   reboot-resume codec
  Name         session-name sanitizer
  Tui          the picker: state machine + frame renderer
  Remote       parser for another machine's `list --porcelain`
Zmx/Posix.lean the only module that touches the OS
c/shim.c       the only non-Lean file (syscall wrappers, no logic)
Zmx/Runtime/   IO: daemon loop, client, TUI shell, CLI, resume hooks
Theorems/      proofs; THEOREMS.md maps each § to the tension it settles
Tests/         unit tests (elaboration-time `example`s)
tests/         live suites (real ptys) + `e2e.sh`, the whole-deliverable gate
```

The effects-as-data split is what makes the proofs possible: every
decision is a pure function returning `List Effect`, and the runtime is
a dumb loop that turns fds into events and effects into syscalls.

## Theorems

`THEOREMS.md` is the ledger. The load-bearing ones:

- **§Bound** — nothing grows with uptime. Every buffer has a
  structural cap that `step` preserves for *any* input: wire decoder,
  scrollback ring, CSI parameters, OSC accumulator, client list, label
  table. This is the answer to zellij's crashes under load — there is
  no unbounded queue to fill.
- **§Total** — the emulator cannot crash. `Vt.step` is total (no
  `partial def` in the core, checked by `e2e.sh`), and the cursor plus
  every stashed cursor provably stays inside the grid whatever bytes
  arrive.
- **§Chunk** — re-chunking is invisible: feeding `a ++ b` equals
  feeding `a` then `b`, for the wire decoder and the emulator both.
- **§Detach** — a session with zero clients still advances; detaching
  cannot alter the screen (its only permitted effect is a checkpoint).
- **§Restore** — `load (save s) = some s`, and `load` is total on
  arbitrary bytes: a torn or foreign checkpoint is ignored, never fatal.
- **§Isolate** — many clients on one session: bytes from one cannot
  alter another's record or its half-decoded frame.
- **§Frame** / **§Name** / **§Remote** / **§Row** — protocol round-trip
  with forward-compatible unknown tags; sanitized names cannot escape
  the socket directory; neither a remote listing nor a local daemon'''s
  own reply can inject paths, escape sequences, or a false identity.

## Build

```sh
./lake build lzmx        # the program (use ./lake, not lake — see AGENTS.md)
./lake build Theorems    # the proofs
./lake build Tests       # unit tests (building is running them)
./tests/e2e.sh           # everything, from a clean build
```

Lean 4.32.0 via elan, no external Lean dependencies. `./lake` is a
wrapper that routes C compilation through Homebrew clang, which this
host's glibc 2.26 needs.

## Configuration

There isn't any, by design — one modern default (Dracula, status on
top). The environment knobs that exist are operational:

| | |
|---|---|
| `LZMX_DIR` | override both socket and state directories |
| `LZMX_REMOTES` | comma-separated ssh hosts to list in the TUI |
| `~/.config/lzmx/remotes` | same, one host per line (`#` comments) |
| `LZMX_NO_DETACH_KEY` | disable `ctrl-\` (for programs that need it) |
| `LZMX_SESSION` | set *inside* a session; use it in your prompt |

Sockets default to `$XDG_RUNTIME_DIR/lzmx` (else `/tmp/lzmx-$UID`),
state to `$XDG_STATE_HOME/lzmx` (else `~/.local/state/lzmx`).

## ssh

Remote sessions are ordinary ssh sessions — attaching runs `ssh -t
<host> lzmx attach <name>`, so nothing is tunnelled and no daemon is
shared. The TUI enumerates them with `ssh <host> lzmx list
--porcelain`; an unreachable host contributes nothing and never blocks
the picker.
