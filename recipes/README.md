# Recipes

`linger` never drives fzf, your terminal, or your transport. These
one-file recipes do the composing. Fish functions install by copy —
fish autoloads one function per file from this directory:

```fish
cp recipes/lz*.fish ~/.config/fish/functions/
```

| file | gives you | needs |
|---|---|---|
| `lz.fish` | fuzzy-pick a session (local + remote) and attach | fzf |
| `lzo.fish` | every session on a host as kitty tabs, one shot | kitty remote control |
| `lza.fish` | attach that auto-reconnects while a link flaps | — |
| `lzs.fish` | live status board for the sessions you have no tab open on | — |
| `lzh.fish` | detach (ctrl-\\) pops a picker, so it acts as a switch key | fzf |
| `ssh_config` | dead links declared in ~15 s, no `Enter ~ .` | paste into `~/.ssh/config` |

## Transport: ssh, mosh, anything

The session layer is transport-agnostic by construction: client and
daemon always talk over a local unix socket *on the host*; nothing is
tunnelled, so any carrier that can run a remote command with a tty
works interactively:

```
ssh -t host linger attach work      # what `linger attach work@host` execs
mosh host -- linger attach work     # roaming: survives IP changes/sleep
```

mosh needs no reconnect recipe at all — it *is* the reconnect layer —
and pairs with linger exactly: mosh keeps the link alive across networks,
linger keeps the session alive across detaches and reboots. To route a
recipe over mosh, swap its one ssh line (`lzo.fish` shows the variant).

Two things are deliberately ssh-shaped in the binary and cost mosh
users nothing:

* `attach name@host` execs `ssh` (one argv line — the universal
  default; policy like keepalives stays in your `ssh_config`).
* `ls -r` queries hosts over `ssh` necessarily: mosh is a screen-sync
  protocol, not a run-a-command-and-capture-stdout transport — and
  mosh itself bootstraps over ssh, so every mosh user already has ssh
  reachability.

## Why recipes and not built-ins

Each of these is policy — which picker, which terminal, how eagerly to
declare a link dead, when to retry. The binary carries the mechanism
(sessions that survive anything); policy stays in six lines you can
read and edit. Concrete example: `lza.fish` retries on ssh exit 255,
and ssh's exit contract makes "transport died" indistinguishable from
"remote command exited 255" — an acceptable blind spot in a recipe you
can see, not acceptable hidden in a binary.
