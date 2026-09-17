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
| `lzr.fish` | import tmux-resurrect panes as linger sessions | a tmux-resurrect save |
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

## tmux-resurrect import

```fish
lzr                                      # default `last` save
lzr ~/.tmux/resurrect/last               # explicit save
lzr --restore-processes                  # opt in to saved commands
```

Each `pane` record becomes `<session>-w<window>-p<pane>` in its saved
working directory. A projected name that linger would rewrite or truncate is
rejected instead of being allowed to collide. Identities present in the initial
listing—live or resumable—are skipped, so sequential reruns do not resend
commands. Do not run imports concurrently or create a projected name while an
import is running: `linger run` is an upsert, and the recipe cannot claim a name
atomically without a new binary verb. The default save is `$HOME/.tmux/resurrect/last` when that directory exists;
otherwise `${XDG_DATA_HOME:-$HOME/.local/share}/tmux/resurrect/last`.

Saved commands do not run by default. `--restore-processes` sends a command only
when its first word is in the fixed `allowed` list in `lzr.fish`; review or edit
that list before opting in. The complete matching line is sent to the session's
shell, so inspect the save too. Window layouts, active state, grouped sessions,
and captured pane contents are not imported.

Each recipe is policy — which picker, which terminal, how eagerly to
declare a link dead, when to retry — kept in a few lines you can read
and edit; the binary carries the mechanism.
