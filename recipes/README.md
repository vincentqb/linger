# Recipes

Fish autoloads one function per file:

```fish
cp recipes/lz*.fish ~/.config/fish/functions/
```

| file | gives you | needs |
|---|---|---|
| `lz.fish` | fuzzy-pick a session (local + remote) and attach | fzf |
| `lzo.fish` | every session on a host as kitty tabs, one shot | kitty remote control |
| `lza.fish` | attach that auto-reconnects while a link flaps | — |
| `lzs.fish` | live status board for sessions you have no tab open on | — |
| `lzh.fish` | detach (ctrl-\\) pops a picker, so it acts as a switch key | fzf |
| `ssh_config` | dead links declared in ~15 s | paste into `~/.ssh/config` |

Client and daemon always talk over a local unix socket on the host;
nothing is tunnelled, so any carrier that can run a remote command with
a tty works interactively:

```
ssh -t host linger attach work      # what `linger attach work@host` execs
mosh host -- linger attach work
```

`ls -r` queries hosts over ssh. To route a recipe over mosh, swap its
one ssh line (`lzo.fish` shows the variant).

Each recipe is policy — which picker, which terminal, how eagerly to
declare a link dead, when to retry — kept in a few lines you can read
and edit; the binary carries the mechanism.
