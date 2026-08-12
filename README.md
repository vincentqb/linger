# linger

Terminal sessions that stay — attach, detach, survive reboots. Lean
sessions: one binary, pure functions, machine-checked invariants
(Lean 4).

## The model

`linger attach <name>` gives you a shell that keeps running after you
detach or disconnect; reattach later with the screen intact. Bare
`linger` (or `linger ls`) prints an overview of your sessions and exits — a
listing, not a picker.

## Build

```
./lake build          # use plain `lake build` on glibc >= 2.34
ln -sf "$PWD/.lake/build/bin/linger" ~/.local/bin/linger
```

Lean 4.32.0 via elan; no external Lean dependencies.

## Use

```
linger attach work      # attach, creating "work" if absent
Ctrl-\                # detach — session keeps running
linger                  # overview: names, pids, labels; then exits
linger attach           # attach the default session ("main")
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

## Recipes

`linger` never drives fzf, your terminal, or your transport; one-file
recipes in [`recipes/`](recipes/) do the composing (fish functions —
`cp` them into `~/.config/fish/functions/`):

| | |
|---|---|
| `lz.fish` | fuzzy-pick a session (fzf) and attach, local or remote |
| `lzo.fish` | every session on a host as kitty tabs, one shot |
| `lza.fish` | attach that auto-reconnects while a link flaps |
| `ssh_config` | dead links declared in ~15 s — no more `Enter ~ .` |

Transport is yours: `attach name@host` execs ssh, and mosh composes as
`mosh host -- linger attach name` (roaming, instant resume) — the wire
protocol never crosses the network, so any carrier works. Details in
`recipes/README.md`.

## Notes

- Reboot-resume is automatic (periodic checkpoint + restore on attach).
- `attach` needs a terminal; bare `linger`/`ls`, `run`, `send` are scriptable.
- An unreachable or mid-reboot host drops out of `ls -r` after a few
  seconds; `attach name@host` fails with ssh's own error. Once the host
  is back its sessions list as `resumable` and attach restores them.
- A dropped link cannot hurt a session — it detaches; reattach restores
  the screen (see `recipes/` for the client-side comfort).
- Detach key `Ctrl-\`; `LINGER_NO_DETACH_KEY=1` disables it.
- Remotes: `-r host,host` for one run, `~/.config/linger/remotes` to
  persist (duplicates are an error). Hosts need `linger` on their `$PATH`.
- `LINGER_DIR=<dir>` isolates sockets + state on local storage.

## Design

`THEOREMS.md` — the invariants (bounded under load, no crash on any
input, sessions outlive clients, checkpoint round-trips, one session
can't leak into another, a row's identity is its socket name).
`tests/e2e.sh` — the whole-deliverable gate. `specs/archive/lean-zmx.md`
— the build record.
