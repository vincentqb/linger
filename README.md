# linger

Terminal sessions that stay — attach, detach, survive reboots.
Pure-function Lean 4, machine-checked invariants.

`linger attach <name>` gives you a shell that keeps running after you
detach or disconnect; reattach later with the screen intact. Bare `linger`
explains the CLI. `linger select` creates or attaches to a session and returns to selection
after detach. `linger ls` lists and exits.

Selection refreshes automatically while preserving your query and highlighted
target. Esc or Ctrl-C quits the selector and leaves session programs running.

## Build

```
./lake build          # always the wrapper, not bare `lake`
mkdir -p ~/.local/bin
ln -sf "$PWD/.lake/build/bin/linger" ~/.local/bin/linger
```

Lean 4.34.1 via elan; no external Lean dependencies.

### Tests

```
./lake build Theorems Tests      # the proofs and the unit fixtures
./lake exe lingertest            # POSIX shim smoke tests
./lake exe e2e <suite>           # one pty suite: attach resume overview remote robust
                                 #   graphics terminal status agent watch recipes delivery manager
./lake env lean E2E/Coverage.lean # resolved renderer/replay references; build the program first
./lake exe e2e ci                # which runners CI asks for (tests/ci-runners.sh)
sh tests/gates.sh                # the fast source-tree gates (seconds)
./tests/e2e.sh                   # everything, in order (minutes)
```

`LINGER_REMOTE=<host> ./lake exe e2e remote-live` exercises the remote
path against a real second machine; opt-in, so it is not in the gate.

Commit-time hygiene is `uvx pre-commit install`. `lean-fmt` is optional
and installed standalone; `.lean-fmt.toml` records the settings. The
[CI installation steps](.github/workflows/ci.yml) pin the formatter source
separately and build it with the project toolchain.

### Layout

| | |
|---|---|
| `Linger/Core/` | pure: no `IO`, no `partial def`, no `sorry`. Effects are data. |
| `Linger/Runtime/` | executes the session core's effects through Lean IO and Posix |
| `Linger/Posix.lean`, `c/shim.c` | raw OS bindings, kept behind one interface |
| `Main.lean` | one executable composing session commands, selection and save import |
| `Tools/`, `Manager/` | pure routing/matching/input/import policies and Lean IO executors, outside the session and VT libraries |
| `Theorems/` | the proofs — what `THEOREMS.md` narrates |
| `Tests/` | Lean fixtures, checked at elaboration time |
| `E2E/` | IO suites against the real binary, with isolated executor probes for failure checks |
| `specs/` | live build plans; `specs/archive/` the closed ones |

## Use

```
linger attach work      # attach, creating "work" if absent
Ctrl-\                # detach — session keeps running
linger select          # create or attach; return after detach
linger ls              # overview: names, pids, labels; then exit
```

| command | |
|---|---|
| (no args) | show help |
| `select` | choose an existing session or create one; requires terminal input and output |
| `attach [name] [cmd]` | attach, creating if absent (name defaults to `main`) |
| `attach <name>@<host>` | attach a session on a remote host over ssh |
| `watch <name>` | input/resize-read-only attach; viewing marks output seen |
| `run <name> <cmd>` | run a command in a session, don't attach |
| `send <name> <text>` | send raw input to its pty (`send <name> -`: stdin, byte-exact) |
| `ls [-r [h,..]]` | overview; `-r` adds remote hosts; `--porcelain` is machine-readable |
| `import [SAVE]` | create shells in directories from a tmux-resurrect save; never replay commands |
| `info <name>` | one session's records: size, cursor, `outseq`, labels… |
| `capture <name>` | the current screen as text, one line per row (marks it seen) |
| `resize <name> <cols> <rows>` | size a detached session (refused while a client is attached) |
| `history <name>` | scrollback as text |
| `wait <name>` | block until its program exits (exit code follows) |
| `kill` / `detach <name>` | end / disconnect |
| `get` `set` `unset` `clear <name>` | labels (`k=v`) |

## Agents

Use `linger ls --porcelain`, `info`, `capture` and `send` to inspect and drive
sessions without owning a terminal. Poll cheaply: `info` reports `outseq`,
a counter that moves once per burst of
output. A `capture` marks the session seen; `history` is an export and
does not. `watch <name>` gives a human a read-only view while an agent
drives. A `resize` is refused — loudly, exit 1 — while an attached
client owns the size. Captures are plain text (one line per grid row,
controls scrubbed), so parse them positionally with `rows` from `info`.

## Session status

Each row in `linger ls` carries one glyph — the most specific state that
applies — plus `+N` when N clients are attached: `⣷` working, `⣿`
unread (output while nobody watched), `⣀` idle, `✓` exited 0, `!`
exited nonzero or killed, `~` resumable (checkpoint on disk), `?`
unknown. `--porcelain` carries the same seven as a `status` field, and
`behind` counts output events that arrived unseen. Unread means "since
anyone last looked", a property of the session, not of you.

## Graphics

Kitty graphics (`APC`), sixel (`DCS`) and iTerm2 inline images
(`OSC 1337`) pass through byte for byte while attached; the emulator
ignores the payloads, so a program streaming megabytes of base64 cannot
grow a session, reach a checkpoint, or wedge the parser (§Bound, §Total
in `THEOREMS.md`). Nothing is stored, so what brings an image back after
reattach is the application redrawing: a changed terminal size delivers
`SIGWINCH`; at an unchanged size the kernel suppresses it — press the
app's refresh key (`Ctrl-L` for most). An image from an exited command
is gone. Both halves are pinned by `E2E/Graphics.lean`; storing images
is a settled non-goal (AGENTS.md).

## Recipes

Ghostty, kitty, WezTerm and other terminals can run `linger select` at startup.
[`recipes/README.md`](recipes/README.md) contains native configuration
examples, selection keys and save-import instructions. Selection offers
`Create main` when there are no sessions; type a name to create a different one.

Selection and `linger import [SAVE]` are Lean code and need no external picker
or shell functions. Their policies and executors stay outside the session and
VT libraries. `attach name@host` execs ssh; any carrier that can run a remote
command with a tty works.

## Notes

- Reboot-resume is automatic (periodic checkpoint + restore on attach).
  The screen, scrollback, modes, labels and cwd come back — not the
  process tree.
- Reattach paints the session's scrollback into your terminal's own
  main screen and scrollback, so attaching a session
  **that has history erases whatever history that window held**
  (`CSI 3 J`); a session with no history leaves your window alone.
  `linger history` prints a session's scrollback without touching the
  terminal. Selection temporarily uses the alternate screen and restores it
  before attach.
- Detach key `Ctrl-\`; `LINGER_NO_DETACH_KEY=1` disables it.
- Detaching hands the terminal back usable, on every exit path. The
  window title is the one thing not put back — we never read yours.
- A dropped link cannot hurt a session — it detaches; reattach restores
  the screen.
- Remotes: `-r host,host` for one run, `~/.config/linger/remotes` to
  persist. Hosts need `linger` on their `$PATH`.
- `LINGER_DIR=<dir>` isolates sockets + state on local storage.

## Design

`THEOREMS.md` — the invariants. `tests/e2e.sh` — the whole-deliverable
gate. `specs/archive/lean-zmx.md` — the build record.

Prior art: [screen](https://www.gnu.org/software/screen/),
[tmux](https://github.com/tmux/tmux/),
[zmx](https://github.com/neurosnap/zmx),
[abduco](https://github.com/martanne/abduco), and
[zellij](https://github.com/zellij-org/zellij).
