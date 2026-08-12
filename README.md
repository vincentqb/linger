# lean-zmx

Persistent terminal sessions — attach, detach, survive reboots — plus a
session-manager TUI. Pure-function Lean 4, one binary: `lzmx`.

## The model

`lzmx attach <name>` gives you a shell that keeps running after you
detach or disconnect; reattach later with the screen intact. Bare
`lzmx` is the **manager** — a picker over existing sessions, not a
shell.

## Build

```
./lake build          # use plain `lake build` on glibc >= 2.34
ln -sf "$PWD/.lake/build/bin/lzmx" ~/.local/bin/lzmx
```

Lean 4.32.0 via elan; no external Lean dependencies.

## Use

```
lzmx attach work      # attach, creating "work" if absent
Ctrl-\                # detach — session keeps running
lzmx                  # manager: pick / create / kill / preview
```

| command | |
|---|---|
| `attach <name> [cmd]` | attach, creating if absent |
| `watch <name>` | attach read-only |
| `run <name> <cmd>` | run a command in a session, don't attach |
| `send <name> <text>` | send raw input to its pty |
| `list [--porcelain]` | live and resumable sessions |
| `history <name>` | scrollback as text |
| `wait <name>` | block until its program exits (exit code follows) |
| `kill` / `detach <name>` | end / disconnect |
| `get` `set` `unset` `clear <name>` | labels (`k=v`) |
| `-r <h1,h2>` | open the manager showing these ssh hosts too |

## Notes

- Reboot-resume is automatic (periodic checkpoint + restore on attach).
- `attach` and bare `lzmx` need a terminal; `run`/`send`/`list` are scriptable.
- Detach key `Ctrl-\`; `LZMX_NO_DETACH_KEY=1` disables it.
- Remotes: `-r host,host` for one run, `~/.config/lzmx/remotes` to persist
  (duplicates are an error). Hosts need `lzmx` on their `$PATH`; attach is
  `ssh -t host lzmx attach <name>`.
- `LZMX_DIR=<dir>` isolates sockets + state on local storage.

## Design

`THEOREMS.md` — the invariants (bounded under load, no crash on any input,
sessions outlive clients, checkpoint round-trips, one session can't leak
into another). `tests/e2e.sh` — the whole-deliverable gate.
`specs/archive/lean-zmx.md` — the build record.
