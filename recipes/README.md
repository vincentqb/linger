# Recipes

The optional `lz` manager provides session selection and save import in Lean.
It runs from any shell and needs no external picker. The three editable shell
recipes compose existing commands; they run with `/bin/sh`. Ghostty and SSH
examples use those tools' native configuration.

Build and install `lz` separately from `linger`, then install whichever recipes
you want:

```sh
./lake build lz
mkdir -p ~/.local/bin
install -m 755 .lake/build/bin/lz ~/.local/bin/lz
install -m 755 recipes/lza.sh ~/.local/bin/lza
install -m 755 recipes/lzs.sh ~/.local/bin/lzs
install -m 755 recipes/lzo.sh ~/.local/bin/lzo
```

Put `~/.local/bin` and `linger` on PATH. Building `lz` needs the pinned Lean
toolchain; running the installed binary or editing the shell recipes does not.
If you installed earlier fish functions, remove their `lz`, `lzh`, `lzr`, `lza`,
`lzs` and `lzo` autoload files and erase those functions in open fish sessions.
Remove the old standalone `lzr` launcher and update its callers to
`lz import-resurrect`.

| file | gives you | needs |
|---|---|---|
| `lzo.sh` | every session on a host as kitty tabs, one shot | kitty remote control, SSH |
| `lza.sh` | attach that auto-reconnects while a link flaps | linger |
| `lzs.sh` | live status board for sessions you have no tab open on | linger, clear |
| `ghostty_config` | new Ghostty windows start `lz` | Ghostty 1.2+, lz, linger |
| `ssh_config` | dead links declared in ~15 s | paste into `~/.ssh/config` |

## Session selection

```sh
lz                          # select; return to selection after attach exits
lz --help
```

Type a subsequence of the target, such as `wkdh` for
`work@dev-host`. Matches retain listing order; the selected target is passed to
`linger attach` unchanged. ASCII letter case is ignored; other Unicode
characters match exactly. Up/down or ctrl-p/ctrl-n move, Home/End select
first/last, backspace edits, and ctrl-u clears the query. Enter attaches;
Esc, ctrl-c and ctrl-d cancel with status 130. Pasted newlines cannot attach.
An empty result stays editable and never turns the query into a new name.
Create your first session with `linger attach work`, then detach with ctrl-\\
and run `lz`.

The listing refreshes on entry, after attach returns, or on ctrl-r.
Ctrl-r also clears the query. There is no timed remote polling. A failed or
malformed listing ends the manager; the snapshot can become stale before
attach, which retains linger's normal behavior. Selection needs terminal input
and output; help and save import do not. Terminal modes and the picker screen
are restored before attach, refresh or exit.

Client and daemon always talk over a local unix socket on the host;
nothing is tunnelled, so any carrier that can run a remote command with
a tty works interactively:

```
ssh -t host linger attach work      # what `linger attach work@host` execs
mosh host -- linger attach work
```

`ls -r` queries hosts over ssh. To use mosh for a tab's interactive connection,
change the final `ssh -t -- "$host" linger attach "$name"` in `lzo.sh` to
`mosh "$host" -- linger attach "$name"`.

`lza NAME[@HOST]` returns the attach status
unless it is 255, which triggers another attempt after two seconds. SSH uses
255 for transport errors, but a remote command can return it too.

`lzs` refreshes local sessions and configured remotes every five seconds.
It takes no arguments; edit the recipe if you want different refresh timing.
`lzo HOST` checks the complete listing before launching and stops if a tab
launch fails; any tabs already opened remain open.

## Ghostty

After installing `lz` above, merge [`ghostty_config`](ghostty_config) into
your Ghostty configuration:

```ini
command = direct:lz
```

This uses the documented [`command`](https://ghostty.org/docs/config/reference#command)
setting with the `direct:` prefix, available since Ghostty 1.2. Reload the
configuration and open a new window. Pick a local or configured remote session;
detaching with ctrl-\\ returns to the picker. Esc or ctrl-c ends the picker.

Ghostty must be able to find `lz` and `linger` on PATH. If needed, replace `lz`
in the setting with its absolute executable path. An existing
`initial-command` overrides `command` for the first window; update or remove
that override to start the picker there too.

## tmux-resurrect import

The same `lz` executable exposes the noninteractive importer:

```sh
lz import-resurrect                           # default last save
lz import-resurrect ~/.tmux/resurrect/last      # explicit save
```

Its executor is [`Manager/Resurrect.lean`](../Manager/Resurrect.lean); parsing
and planning live in [`Tools/Resurrect.lean`](../Tools/Resurrect.lean).

Each `pane` record becomes `<session>-w<window>-p<pane>` in its saved
working directory. A projected name that linger would rewrite or truncate is
rejected. The complete save is checked for malformed records, duplicate names
and NUL-bearing directory or command fields; all saved directories must be
accessible before any session is created. Identities present in the successful
initial listing—live or resumable—are skipped, so sequential reruns leave them
untouched. The executable and relative state paths are resolved from the
invocation directory while each session starts in its saved directory.
Path resolution follows symlinks before `..`; a state directory may be created
during import. Saved directories also use physical OS traversal.
Do not run imports concurrently or create a projected name while an
import is running: `linger run` is an upsert, and the importer cannot claim a name
atomically. A creation failure stops the import; sessions already
created remain. The default save is `$HOME/.tmux/resurrect/last` when that
directory exists; otherwise
`${XDG_DATA_HOME:-$HOME/.local/share}/tmux/resurrect/last`. An absent or empty
HOME uses the account home for defaults, saved `~` directories and child processes.

Saved commands never run. Each imported session starts a shell in its saved
directory; start the programs you want after attaching. Running processes,
window layouts, active state, grouped sessions and captured pane contents are
not imported. A save filename beginning with `-` needs a path such as `./-save`.

[`THEOREMS.md`](../THEOREMS.md#recipe-boundaries) maps each boundary to its
semantic guarantees and IO checks. Matching, input decoding and import planning
have separate pure modules. The shell helpers keep retry timing, status refresh
and terminal launch commands editable without rebuilding the manager.
