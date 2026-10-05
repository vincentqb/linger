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
linger attach work       # create or attach to a session
linger select            # choose or create a session interactively
linger ls                # list sessions
linger status            # show local attention counts
linger watch work        # view a session without sending input
linger history work      # print saved scrollback
linger kill work         # end the session and its program
linger help              # all commands and options
```

Press **Ctrl-\\** to detach. In `linger select`, type to filter, use the arrow
keys to move, and press Enter to choose the highlighted session or **Create**
row. Esc or Ctrl-C exits the selector; detaching returns to it.

For a remote session, use `linger attach work@host`. The host needs `linger`
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

`linger status` prints counts such as `2⣿ 1!` and stays empty when nothing needs
attention. Reading status does not mark output seen. Set `NO_COLOR` to disable
listing colors. Attached window titles show the session, application title,
and attention counts.

## Graphics

Kitty graphics, sixel and iTerm2 inline images pass through while attached.
Images are not saved. After reattaching, use the application's redraw command
(often Ctrl-L); images from exited programs cannot be recovered.

## Recovery and configuration

Checkpoints restore the screen, scrollback, terminal modes, labels and working
directory after a reboot. Running processes are not restored.

Attaching a session with history **replaces that terminal window's existing
scrollback**. Use `linger history work` to export session history separately.

- `LINGER_DIR` sets the socket and state directory; use local storage.
- `LINGER_NO_DETACH_KEY=1` disables the Ctrl-\\ shortcut.
- `LINGER_SESSION` identifies the session inside its program.

Contributor guidance: [AGENTS.md](AGENTS.md).
Verification guarantees: [THEOREMS.md](THEOREMS.md).
