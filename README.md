# linger

Persistent terminal sessions for Linux and macOS. Detach or disconnect while
programs keep running, then reattach with the screen intact.

## Build

Requires Lean 4.34.1 via [elan](https://github.com/leanprover/elan) and a C
compiler. There are no external Lean dependencies.

```sh
./lake build
mkdir -p ~/.local/bin
ln -sf "$PWD/.lake/build/bin/linger" ~/.local/bin/linger
```

Use the `./lake` wrapper and add `~/.local/bin` to your PATH.

## Use

```sh
linger attach work       # create or attach to a named session
linger attach            # choose or create; return here after detaching
linger ls                # list sessions
linger ls --summary      # show local attention counts
linger watch work        # watch a live session without sending input
linger history work      # print live or saved scrollback
linger capture work      # print the live or saved screen
linger kill work         # end the session and its program
linger help              # all commands and options
```

Press **Ctrl-\\** to detach. In `linger attach`, type to filter, use the arrow
keys to move, and press Enter to choose the highlighted session or **Create**
row. Esc or Ctrl-C exits the selector; detaching returns to it. Detaching from
`linger attach work` returns to the shell.

Only interactive selection uses fuzzy matching. Commands take exact names:
1–80 ASCII letters, digits, `-_.+`, with no leading dot. Invalid names are rejected.

Every session command also accepts `name@host` or `name@user@host`, for example
`linger attach work@host` and `linger history work@host`. The host needs `linger`
on PATH. Add hosts to `~/.config/linger/remotes` to include them in the selector
and `linger ls -r`.

Saved tmux-resurrect sessions can be listed with `linger tmux ls`, opened with
`linger tmux select`, or imported with `linger tmux import`. Imports start fresh
shells in saved directories; saved commands are never run.
See [terminal, prompt and SSH recipes](recipes/README.md) for configuration and
save interchange.

## Session status

Listings show one status glyph and `+N` when clients are attached:

| Glyph | Meaning |
|---|---|
| `⣷` | Working |
| `⣿` | Unread output |
| `⣀` | Idle |
| `✓` | Exited successfully |
| `!` | Failed or killed |
| `~` | Saved session available to resume |
| `?` | Status unknown |

`linger ls --summary` prints counts such as `2⣿ 1!` and stays empty when nothing
needs attention. It checks local sessions concurrently with a shared 250 ms reply
deadline; unanswered sessions count as unknown. Reading status does not mark
output seen. Set `NO_COLOR` to disable listing colors. Attached window titles
show the session, application title, and attention counts.

## Graphics

Kitty graphics, sixel and iTerm2 inline images pass through while attached.
Images are not saved. After reattaching, use the application's redraw command
(often Ctrl-L); images from exited programs cannot be recovered.

## Recovery and configuration

Checkpoints restore the screen, scrollback, terminal modes, labels and working
directory after a reboot. Running processes are not restored.

`history` prints scrollback; `capture` prints the visible screen. Both use the
live session when available, or its offline checkpoint without starting a program.
A checkpoint still owned by a daemon in another runtime directory cannot be read offline.

Attaching a session with history **replaces that terminal window's existing
scrollback**. Use `linger history work` to export session history separately.

- `LINGER_DIR` sets both socket and state directories; use local storage.
  Separate directories allow independent sessions with the same name.
- `LINGER_NO_DETACH_KEY=1` disables the Ctrl-\\ shortcut.
- `LINGER_SESSION` identifies the session inside its program.

Contributor guidance: [AGENTS.md](AGENTS.md).
Verification guarantees: [THEOREMS.md](THEOREMS.md).
