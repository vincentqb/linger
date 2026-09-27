# Terminal and SSH configuration

Every example starts the same `linger` executable. Session selection and save
import are Lean code and work from any shell; recipes only configure the terminal
or transport.

Build and install `linger` as described in the [README](../README.md#build).
Choose a session interactively, or create one by name:

```sh
linger attach work          # create or attach directly
# Detach with ctrl-\.
linger select               # create or attach; return here after each attach exits
linger ls                   # list once, including in a terminal
linger                      # show CLI help
```

`linger select` requires terminal input and output. With no sessions it offers
`Create main`; type a name to create a different one. Bare `linger` shows help
in every stream mode.

## Native terminal settings

Merge the setting for your terminal into its existing configuration:

| Terminal | File | Setting |
|---|---|---|
| Ghostty 1.2+ | [`ghostty_config`](ghostty_config) | `command = direct:linger select` |
| kitty | [`kitty.conf`](kitty.conf) | `shell linger select` |
| WezTerm | [`wezterm.lua`](wezterm.lua) | `default_prog = { 'linger', 'select' }` |

Ghostty's [`command`](https://ghostty.org/docs/config/reference#command) with
`direct:` launches an executable without a shell command string. An existing
`initial-command` overrides it for the first window; update that override if
you want selection there too.

kitty's [`shell`](https://sw.kovidgoyal.net/kitty/conf/#opt-kitty.shell) names the
program to start. WezTerm's
[`default_prog`](https://wezterm.org/config/lua/config/default_prog.html) is an
argument array in the returned configuration. If you already return a config
table, set `config.default_prog = { 'linger', 'select' }` before returning it.

Use the same approach in another terminal: set its startup command to `linger select`.
Open a new window after loading the configuration. The terminal must find
`linger` on PATH, or the setting can name its absolute executable path. The
selector and importer reuse the running executable for local child commands.
Window, tab and split configuration remains with the terminal.

## Selection

Type a subsequence of the target, such as `wkdh` for `work@dev-host`.
Matches retain listing order. ASCII letter case is ignored; other Unicode
characters match exactly. A `Create <name>` row follows the matches when the
typed name is valid and not already listed. The creation row uses the name
exactly as typed; an empty query offers `Create main` if `main` is absent.
An exact existing target has no duplicate creation row.

- Up/down or ctrl-p/ctrl-n move; Home/End select first/last.
- Backspace edits, ctrl-u clears, and Enter chooses the highlighted row.
- Esc, ctrl-c and ctrl-d cancel with status 130.
- Ctrl-r reloads the listing and clears the query.

Both existing and creation choices call `linger attach` with the target unchanged.
Use `name@host` or `name@user@host` to create remotely. Invalid names, including
spaces or slashes in the local name and an empty host suffix, cannot be created;
they stay editable. Pasted newlines cannot choose a row. The listing
refreshes on entry, after attach returns, or on ctrl-r; there is no timed remote
polling. A failed or malformed listing ends selection. The snapshot can become
stale before attach, which creates or attaches according to the session's state then.

Terminal modes and the selector's alternate screen are restored before attach,
refresh or exit. Detaching with ctrl-\ returns to a fresh selection.

## Remote sessions

`linger select` includes hosts from `~/.config/linger/remotes`.
`linger ls -r` lists those hosts once; `linger ls -r host,host` chooses hosts
for one listing. Each host needs `linger` on PATH.

Client and daemon talk over a local Unix socket on the session's host.
Any carrier that can run a remote command with a tty works interactively:

```sh
ssh -t host linger attach work      # what `linger attach work@host` execs
mosh host -- linger attach work
```

[`ssh_config`](ssh_config) is an optional keepalive example to merge into
`~/.ssh/config`, preferably scoped to your session hosts. Transport settings
remain in SSH configuration.

## tmux-resurrect import

The same executable imports saved directories:

```sh
linger import                           # default last save
linger import ~/.tmux/resurrect/last     # explicit save
```

Its executor is [`Manager/Resurrect.lean`](../Manager/Resurrect.lean); parsing
and planning live in [`Tools/Resurrect.lean`](../Tools/Resurrect.lean).

Each `pane` record becomes `<session>-w<window>-p<pane>` in its saved working
directory. A projected name that linger would rewrite or truncate is rejected.
The complete save is checked for malformed records, duplicate names and
NUL-bearing directory or command fields. All saved directories must be accessible
before any session is created. Identities in the successful initial listing—live
or resumable—are skipped, so sequential reruns leave them untouched.

Relative state paths resolve from the invocation directory while each session
starts in its saved directory. Path resolution follows symlinks before `..`;
a state directory may be created during import. Saved directories also use
physical OS traversal. Do not run imports concurrently or create a projected
name during import: `linger run` is an upsert, so the importer cannot claim names
atomically. A creation failure stops import; sessions already created remain.

The default save is `$HOME/.tmux/resurrect/last` when that directory exists;
otherwise `${XDG_DATA_HOME:-$HOME/.local/share}/tmux/resurrect/last`. An absent
or empty HOME uses the account home for defaults, saved `~` directories and
child processes.

Saved commands never run. Each imported session starts a shell in its saved
directory; start the programs you want after attaching. Running processes,
window layouts, active state, grouped sessions and captured pane contents are
not imported. A save filename beginning with `-` needs a path such as `./-save`.

[`THEOREMS.md`](../THEOREMS.md#entry-point-boundaries) maps routing, matching,
input decoding and import planning to their semantic guarantees and IO checks.
Native configuration checks inspect the settings; they do not launch GUI
terminals.

## Earlier installations

Replace `lz` or bare `linger` startup commands with `linger select`, and
`lz import-resurrect` with `linger import`. Remove previously installed `lz`,
`lzh`, `lzr`, `lza`, `lzs` and `lzo` launchers or shell functions. Those shortcuts
are no longer shipped.
