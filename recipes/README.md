# Terminal, prompt and SSH configuration

Every example invokes the same `linger` executable. Session selection, status
counts and save interchange are Lean code and work from any shell; recipes only
configure the terminal, prompt or transport.

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
`+ Create main`; type a name to create a different one. Bare `linger` shows help
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

## Fish prompt

[`fish_prompt.fish`](fish_prompt.fish) is an optional `fish_right_prompt` example.
If you have no right prompt, place its contents in
`~/.config/fish/functions/fish_right_prompt.fish`. If you already have one, merge
these calls as its last displayed segment, keeping your existing formatting:

```fish
command -q linger
and command linger status 2>/dev/null
```

The example saves `$status` before running the command and returns it afterward.
Keep your prompt's existing status handling when merging. Your `fish_prompt`
stays as it is. The quiet builtin lookup avoids fish's diagnostic when `linger`
is absent from PATH; the invocation suppresses command errors and adds no padding.

`2⣿ 1! 1?` means two sessions with unread output, one reporting an unsuccessful
session exit, and one whose status is unknown. `linger status` takes no flags.
It shows local attention counts only, omitting working, idle, resumable and
successful exits; no attention produces no output. Lean owns counting and the
info sampling without marking output seen. Local connections are nonblocking
and all replies share a 250 ms waiting budget. Busy or unanswered peers count as
unknown and keep their sockets. The command never contacts remote hosts.
This is a current snapshot; retired sessions do not become a failure history.

Status is sampled when fish redraws the prompt. It does not update while a
foreground program runs; attached window titles provide live visibility.

## Selection

Type a subsequence of the target, such as `wkdh` for `work@dev-host`.
Matches retain listing order. ASCII letter case is ignored; other Unicode
characters match exactly. A `+ Create <name>` row follows the matches when the
typed name is valid and not already listed. The creation row uses the name
exactly as typed; an empty query offers `+ Create main` if `main` is absent.
An exact existing target has no duplicate creation row.

- Up/down or ctrl-p/ctrl-n move; Home/End select first/last.
- Backspace edits, ctrl-u clears, and Enter chooses the highlighted row.
- Esc, ctrl-c and ctrl-d quit the selector with status 130, leaving session
  programs running. While attached, ctrl-c keeps its normal meaning for the
  foreground program.

Both existing and creation choices call `linger attach` with the target unchanged.
Use `name@host` or `name@user@host` to create remotely. Invalid names, including
spaces or slashes in the local name and an empty host suffix, cannot be created;
they stay editable. Pasted newlines cannot choose a row. The listing refreshes
automatically, starting the next attempt one second after the previous one
completes. Slow remote listings do not block typing or quitting, and only one
refresh runs at a time. Your query and highlighted target survive updates while
that target remains available; otherwise the highlighted row is clamped to the
new list. An unchanged display
is not repainted. A failed or malformed listing ends selection. The snapshot can
become stale before attach, which creates or attaches according to the session's
state then.

Terminal modes and the selector's alternate screen are restored before attach
or exit. Detaching with ctrl-\ returns to a fresh selection.

## Remote sessions

`linger select` includes hosts from `~/.config/linger/remotes`.
`linger ls -r` lists those hosts once; `linger ls -r host,host` chooses hosts
for one listing. Each host needs `linger` on PATH.

Client and daemon talk over a local Unix socket on the session's host.
Any carrier that can run a remote command with a tty works interactively:

```sh
ssh -t host linger attach work      # what `linger attach work@host` invokes
mosh host -- linger attach work
```

[`ssh_config`](ssh_config) is an optional keepalive example to merge into
`~/.ssh/config`, preferably scoped to your session hosts. Transport settings
remain in SSH configuration.

## tmux-resurrect interchange

The same executable imports saved directories:

```sh
linger import                           # default last save
linger import ~/.tmux/resurrect/last     # explicit save
linger export ~/sessions.tmux           # new destination; never overwritten
```

Its executor is [`Manager/Resurrect.lean`](../Manager/Resurrect.lean); parsing,
planning and export policy live in [`Tools/Resurrect.lean`](../Tools/Resurrect.lean).

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

Without a state override, those imported checkpoints use the account home;
ordinary session commands use a temporary fallback while HOME remains absent
or empty. Set HOME to the account home for later listing, export and resume,
or use the same explicit LINGER_DIR for the whole import/export cycle.

Saved commands never run. Each imported session starts a shell in its saved
directory; start the programs you want after attaching. Running processes,
window layouts, active state, grouped sessions and captured pane contents are
not imported. A save filename beginning with `-` needs a path such as `./-save`.

Only the projected session name and directory become native session state.
Foreign titles, commands, layouts, focus, grouping and unknown records are
discarded. No copy of the source save is stored; the original file may be moved
or deleted after import. Old `tmux-import.json` files are ignored and left
untouched.

Export always generates a save from current names and physical working
directories. It includes both live sessions and resumable checkpoints;
an unreadable session or checkpoint fails the export. Existing
destinations, including symlinks, are refused. A complete file is published
atomically with owner-only permissions.

Generated saves contain one window and pane per session. Their tmux session
names use the reserved `linger=` prefix, with `~` encoding `.`; importing these
records recovers the original Linger name. The window name remains readable.
Keep tmux's pane base index at zero for these saves. Changing this reserved
topology or damaging its encoding is rejected instead of silently renaming a
session. Ordinary foreign session names keep the projection described above.

The shared fields are session identity and the physical working directory.
Generated saves require absolute directories and reject spellings the supported
save cycle cannot preserve: control separators, literal backslashes, repeated or
trailing spaces, and expansion characters (`*`, `?`, `[` and `#`). Single spaces,
quotes, dollar signs and backticks are supported. Export does not reconstruct
the original grouping, layouts or save text.

Native `LNGR` checkpoints continue to hold screens, scrollback, terminal modes
and labels. This interchange does not carry those fields or record typed input.
It creates fresh shells; it does not transfer running processes.

[`THEOREMS.md`](../THEOREMS.md#entry-point-boundaries) maps routing, matching,
input decoding and interchange to their semantic guarantees and IO checks.
Native configuration checks inspect the settings; they do not launch GUI
terminals. The recipe suite also runs the prompt example in fish.

## Earlier installations

Replace `lz` or bare `linger` startup commands with `linger select`, and
`lz import-resurrect` with `linger import`. Remove previously installed `lz`,
`lzh`, `lzr`, `lza`, `lzs` and `lzo` launchers or shell functions. Those shortcuts
are no longer shipped.
