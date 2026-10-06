# Terminal, prompt and SSH recipes

[Build and install linger](../README.md#build) before using these examples.

## Native terminal settings

Merge the setting for your terminal into its existing configuration:

| Terminal | Example | Setting |
|---|---|---|
| Ghostty 1.2+ | [ghostty_config](ghostty_config) | `command = direct:linger attach` |
| kitty | [kitty.conf](kitty.conf) | `shell linger attach` |
| WezTerm | [wezterm.lua](wezterm.lua) | `default_prog = { 'linger', 'attach' }` |

The terminal must find `linger` on PATH, or the setting can use its absolute
path. Open a new window after changing the configuration. Ghostty's
`initial-command` overrides `command` for the first window. In WezTerm, set
`config.default_prog` before returning the configuration table.

## Fish prompt

[fish_prompt.fish](fish_prompt.fish) provides a `fish_right_prompt` showing
local attention counts, such as `2⣿ 1!`. If you have no right prompt, install
it as `~/.config/fish/functions/fish_right_prompt.fish`.

For an existing prompt, merge its status call as the final displayed segment:

```fish
command -q linger
and command linger ls --summary 2>/dev/null
```

Preserve the preceding command's `$status`, as the example does, and keep your
existing `fish_prompt` and `fish_title` hooks. Separate nonempty context and
attention with ` · `. Counts refresh when the prompt redraws; attached window
titles update while programs run.

## Selection

Run `linger attach` in a terminal. Type a subsequence such as `wk` for `work`;
ASCII letter case is ignored. The listing refreshes automatically while keeping
your query and selected target when it remains available.

- Up/down or Ctrl-P/Ctrl-N moves; Home/End selects the first/last row.
- Backspace edits, Ctrl-U clears, and Enter chooses the highlighted row.
- Esc, Ctrl-C or Ctrl-D exits, leaving session programs running.
- Ctrl-\\ detaches from a session and returns to selection.

A named invocation, such as `linger attach work`, exits after detaching.

A valid new name adds an explicit **Create** row. With no query, **Create main**
appears if `main` is absent. Existing choices retain their listed names.
Use `name@host` or `name@user@host` for remote sessions.

## Remote sessions

Each host needs `linger` on PATH. List hosts in `~/.config/linger/remotes` to
include them in selection and `linger ls -r`. Use `linger ls -r host1,host2`
to choose hosts for one listing.
Local checks and remote lookups overlap. Up to four SSH lookups run at once,
sharing a three-second deadline; incomplete or failed remote results are omitted.
Output stays in local-session order followed by the configured host order.

```sh
linger attach work@host
ssh -t host linger attach work
mosh host -- linger attach work
```

Merge [ssh_config](ssh_config) into `~/.ssh/config` for optional keepalives,
scoped to your session hosts.

## tmux-resurrect interchange

```sh
linger tmux ls                         # inspect the latest save
linger tmux select                     # choose a saved pane to open
linger tmux import /path/to/save.txt    # import all saved panes
linger tmux export ~/sessions.tmux     # write a new save file
```

Listing and selection show the save path, modification time, names and working
directories. Add `--porcelain` to `linger tmux ls` for machine-readable output.
Selection opens only the highlighted saved pane and returns after detach.

Pass a save path to choose a snapshot explicitly. Otherwise linger queries
tmux's effective `@resurrect-dir`, then uses its `last` file. With no configured
directory or reachable server, it tries `~/.tmux/resurrect/last`, then
`${XDG_DATA_HOME:-$HOME/.local/share}/tmux/resurrect/last`.
A filename starting with `-` needs a path such as `./-save`.

Imported panes become `<session>-w<window>-p<pane>` sessions in their saved
directories. Existing live or resumable identities are skipped by import.
The save and required directories are validated before creating sessions.
Each new session starts a shell; saved commands, running processes, layouts
and pane contents are not restored.

Avoid concurrent imports or creating those names during import. A failed
batch leaves already-created sessions in place. Use a consistent HOME or
explicit `LINGER_DIR` throughout import, listing and recovery.

Export includes current live and resumable session names and physical working
directories. It refuses existing destinations and publishes an owner-only file.
Generated saves use one window and pane per session; keep tmux's pane base
index at zero. Their reserved `linger=` names preserve native names on reimport.

Export requires absolute directories and rejects control separators, literal
backslashes, repeated or trailing spaces, and expansion characters
(`*`, `?`, `[` and `#`). Single spaces, quotes, dollar signs and backticks work.
Screens, scrollback, terminal modes and labels remain in native checkpoints.
