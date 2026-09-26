# Recipes

Recipes are editable fish functions and native configuration. They compose
linger with other tools and do not require a Lean toolchain to install or edit.
The larger save importer is an optional Lean executable with a proved parser
and import plan. The program, proofs, and automated test suites are also Lean.

Fish autoloads one function per file:

```fish
mkdir -p ~/.config/fish/functions
cp recipes/lz*.fish ~/.config/fish/functions/
```

| file | gives you | needs |
|---|---|---|
| `lz.fish` | fuzzy-pick and attach; `--loop` returns to the picker after detach | fzf |
| `lzo.fish` | every session on a host as kitty tabs, one shot | kitty remote control |
| `lza.fish` | attach that auto-reconnects while a link flaps | — |
| `lzs.fish` | live status board for sessions you have no tab open on | — |
| `ghostty_config` | new Ghostty windows start `lz --loop` | Ghostty 1.2+, fish, fzf |
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

`lz` selects one session even when `FZF_DEFAULT_OPTS` enables multiple selection
and returns the attach status. `lz --loop` returns to the same picker whenever
attach exits; `lz --loop work@host` attaches that target first. A failed listing
or cancelled picker ends either mode. This replaces `lzh`: update existing
shortcuts and remove its old autoload file.

`lza NAME[@HOST]` returns the attach status
unless it is 255, which triggers another attempt after two seconds. SSH uses
255 for transport errors, but a remote command can return it too.

`lzs '' 2` refreshes local sessions and configured remotes every two seconds;
`lzs host-a,host-b 2` replaces that remote list. The interval must be positive.
`lzo HOST` checks the complete listing before launching and stops if a tab
launch fails; any tabs already opened remain open.

## Ghostty

After installing `lz.fish` above, merge [`ghostty_config`](ghostty_config) into
your Ghostty configuration:

```ini
command = shell:fish -c 'lz --loop'
```

This uses the documented [`command`](https://ghostty.org/docs/config/reference#command)
setting with the `shell:` prefix, available since Ghostty 1.2. The quotes keep
`lz --loop` together as fish's command argument. Reload the
configuration and open a new window. Pick a local or configured remote session;
detaching with ctrl-\\ returns to the picker. Esc or ctrl-c ends the picker.

Ghostty must be able to find fish, linger and fzf on PATH. If needed, replace
`fish` in the setting with its absolute executable path. An existing
`initial-command` overrides `command` for the first window; update or remove
that override to start the picker there too.

## tmux-resurrect import

Build and install the optional `lzr` executable separately:

```sh
./lake build lzr
mkdir -p ~/.local/bin
ln -sf "$PWD/.lake/build/bin/lzr" ~/.local/bin/lzr
```

Its entry point is [`Lzr.lean`](../Lzr.lean); parsing and planning live in
[`Tools/Resurrect.lean`](../Tools/Resurrect.lean). It runs from any shell and
requires `linger` on PATH. If you installed the old fish function, remove
`~/.config/fish/functions/lzr.fish` and run `functions --erase lzr` in open
fish sessions so the executable is used.

```fish
lzr                                      # default `last` save
lzr ~/.tmux/resurrect/last                 # explicit save
lzr --restore-processes                   # opt in to saved commands
```

Each `pane` record becomes `<session>-w<window>-p<pane>` in its saved
working directory. A projected name that linger would rewrite or truncate is
rejected. The complete save is checked for malformed records, duplicate names
and NUL-bearing directory or command fields; all saved directories must be
accessible before any session is created. Identities present in the successful
initial listing—live or resumable—are skipped, so sequential reruns do not resend
commands. The executable and relative state paths are resolved from the
invocation directory while each session starts in its saved directory.
Path resolution follows symlinks before `..`; a state directory may be created
during import. Saved directories also use physical OS traversal.
Do not run imports concurrently or create a projected name while an
import is running: `linger run` is an upsert, and the importer cannot claim a name
atomically. A creation or restore failure stops the import; sessions already
created remain. The default save is `$HOME/.tmux/resurrect/last` when that
directory exists; otherwise
`${XDG_DATA_HOME:-$HOME/.local/share}/tmux/resurrect/last`. An absent or empty
HOME uses the account home for defaults, saved `~` directories and child processes.

Saved commands do not run by default. `--restore-processes` sends a command only
when its first ASCII-space-delimited word is in `Tools.Resurrect.allowed`.
Review that fixed list before opting in; changing it requires rebuilding `lzr`
and updating its exact-membership proof. The complete matching command is sent
unchanged to the session's shell, so inspect the save too. This imports saved
identities and directories, with optional command restart; it does not transfer
running processes. Window layouts, active state, grouped sessions and captured
pane contents are not imported.

[`THEOREMS.md`](../THEOREMS.md#recipe-boundaries) maps each boundary to its
semantic guarantees and IO checks. The four fish helpers keep picker, reconnect,
refresh and terminal-launch policy editable; the standalone importer's typed
records keep parsing and command alignment out of shell bookkeeping.
