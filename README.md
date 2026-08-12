# lean-zmx

Persistent terminal sessions — attach, detach, survive reboots.
Pure-function Lean 4, one binary: `lzmx`.

## The model

`lzmx attach <name>` gives you a shell that keeps running after you
detach or disconnect; reattach later with the screen intact. Bare
`lzmx` (or `lzmx ls`) prints an overview of your sessions and exits — a
listing, not a picker.

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
lzmx                  # overview: names, pids, labels; then exits
lzmx attach           # attach the default session ("main")
```

| command | |
|---|---|
| `attach [name] [cmd]` | attach, creating if absent (name defaults to `main`) |
| `attach <name>@<host>` | attach a session on a remote host over ssh |
| `watch <name>` | attach read-only |
| `run <name> <cmd>` | run a command in a session, don't attach |
| `send <name> <text>` | send raw input to its pty |
| `ls` / (no args) `[-r [h,..]]` | overview; `-r` also lists remote hosts |
| `ls --porcelain` | machine-readable listing |
| `history <name>` | scrollback as text |
| `wait <name>` | block until its program exits (exit code follows) |
| `kill` / `detach <name>` | end / disconnect |
| `get` `set` `unset` `clear <name>` | labels (`k=v`) |

## Picking with fzf (optional)

`lzmx` never calls `fzf`. If you have `fzf` installed, a one-line shell
function turns the overview into an interactive picker. In fish:

```fish
function lz --description 'pick a session and attach'
    set -l name (lzmx ls -r --porcelain | awk -F '\t' '$1=="name"{print $2}' | fzf)
    and lzmx attach $name
end
```

It lists the session names — local ones, plus (with a
`~/.config/lzmx/remotes` file) remote ones tagged `name@host` — lets you
pick one, and hands it to `lzmx attach`, which attaches locally or
`ssh`-es to the host as needed. Pulling names from `--porcelain` means
an empty list offers nothing to pick (no stray "no sessions" row). Drop
`-r` for a faster, local-only picker. To create a new session, just
`lzmx attach <newname>`.

## Notes

- Reboot-resume is automatic (periodic checkpoint + restore on attach).
- `attach` needs a terminal; bare `lzmx`/`ls`, `run`, `send` are scriptable.
- Detach key `Ctrl-\`; `LZMX_NO_DETACH_KEY=1` disables it.
- Remotes: `-r host,host` for one run, `~/.config/lzmx/remotes` to
  persist (duplicates are an error). Hosts need `lzmx` on their `$PATH`.
- `LZMX_DIR=<dir>` isolates sockets + state on local storage.

## Design

`THEOREMS.md` — the invariants (bounded under load, no crash on any
input, sessions outlive clients, checkpoint round-trips, one session
can't leak into another, a row's identity is its socket name).
`tests/e2e.sh` — the whole-deliverable gate. `specs/archive/lean-zmx.md`
— the build record.
