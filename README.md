# linger

Terminal sessions that stay — attach, detach, survive reboots. Lean
sessions: one binary, pure functions, machine-checked invariants
(Lean 4).

## The model

`linger attach <name>` gives you a shell that keeps running after you
detach or disconnect; reattach later with the screen intact. Bare
`linger` (or `linger ls`) prints an overview of your sessions and exits — a
listing, not a picker.

## Build

```
./lake build          # use plain `lake build` on glibc >= 2.34
ln -sf "$PWD/.lake/build/bin/linger" ~/.local/bin/linger
```

Lean 4.32.0 via elan; no external Lean dependencies.

## Use

```
linger attach work      # attach, creating "work" if absent
Ctrl-\                # detach — session keeps running
linger                  # overview: names, pids, labels; then exits
linger attach           # attach the default session ("main")
```

| command | |
|---|---|
| `attach [name] [cmd]` | attach, creating if absent (name defaults to `main`) |
| `attach <name>@<host>` | attach a session on a remote host over ssh |
| `watch <name>` | attach read-only |
| `run <name> <cmd>` | run a command in a session, don't attach |
| `send <name> <text>` | send raw input to its pty (`send <name> -`: stdin, byte-exact) |
| `ls` / (no args) `[-r [h,..]]` | overview; `-r` also lists remote hosts |
| `ls --porcelain` | machine-readable listing |
| `info <name>` | one session's records: size, cursor, `outseq`, labels… |
| `capture <name>` | the current screen as text, one line per row (marks it seen) |
| `resize <name> <cols> <rows>` | size a detached session (refused while a client is attached) |
| `history <name>` | scrollback as text |
| `wait <name>` | block until its program exits (exit code follows) |
| `kill` / `detach <name>` | end / disconnect |
| `get` `set` `unset` `clear <name>` | labels (`k=v`) |

## Agents

Everything above the attach line is one-shot and scriptable, so another
program — an AI agent, a monitor, a bot — can see and drive a session without
owning a terminal:

```
linger run work 'make test'        # upsert + type the command
linger resize work 120 40          # deterministic wrap (nobody attached)
linger capture work                # the screen, one line per row
printf 'y\n' | linger send work -  # exact bytes: Enter, ^C, escapes…
linger wait work                   # block until the program exits
```

Poll cheaply: `info` reports `outseq`, a counter that moves once per burst of
output — capture again only when it moved, and treat two equal reads as
quiescence. A `capture` **marks the session seen** (it is a look, so the
`ls` glyph stops saying unread and `behind` counts from your capture);
`history` is an export and deliberately does not. While an agent drives,
`watch <name>` gives a human a read-only view of the same screen. A resize is
refused — loudly, exit 1 — while an attached client owns the size; captures
are plain text (one line per grid row, controls scrubbed), so parse them
positionally with `rows` from `info`.

## Recipes

`linger` never drives fzf, your terminal, or your transport; one-file
recipes in [`recipes/`](recipes/) do the composing (fish functions —
`cp` them into `~/.config/fish/functions/`):

| | |
|---|---|
| `lz.fish` | fuzzy-pick a session (fzf) and attach, local or remote |
| `lzo.fish` | every session on a host as kitty tabs, one shot |
| `lza.fish` | attach that auto-reconnects while a link flaps |
| `lzs.fish` | live status board for sessions you have no tab open on |
| `lzh.fish` | detach (ctrl-\\) pops a picker, so it acts as a switch key |
| `ssh_config` | dead links declared in ~15 s — no more `Enter ~ .` |

Transport is yours: `attach name@host` execs ssh, and mosh composes as
`mosh host -- linger attach name` (roaming, instant resume) — the wire
protocol never crosses the network, so any carrier works. Details in
`recipes/README.md`.

## Session status

Each row in `linger ls` carries one glyph — the most specific state that
applies — plus `+N` when N clients are attached.

| | |
|---|---|
| `⣷` | working — output right now |
| `⣿` | unread — output arrived while nobody was watching |
| `⡀` | idle — nothing since it was last watched |
| `✓` | exited 0 |
| `!` | exited nonzero, or killed by a signal |
| `~` | resumable — no daemon, but a checkpoint is on disk |
| `?` | unknown — the daemon did not answer, or the checkpoint will not load |

Two states share a glyph only when they call for the same action, which is why
a bell folds into unread and a busy daemon folds into unknown. `--porcelain`
carries the same seven as a `status` field (`working`, `wants-you`, `idle`,
`exited-ok`, `exited-bad`, `resumable`, `unknown`), and `behind` counts how
many output events arrived unseen.

Two things worth knowing. Unread means "since anyone last looked", not since
*you* did: it is a property of the session, so if a colleague watched it a
moment ago the output is no longer news to the row. And working is only as
responsive as the daemon's poll round, because freshness is a counter
comparison across polls rather than a stored timestamp.

The column earns its keep for sessions with no tab open — those are the ones
you cannot see. `recipes/lzs.fish` parks it in a tab as a live board.

## Graphics

Images reach your terminal while you are attached, and whether they come
back after a reattach depends on whether the application redraws.

Kitty graphics (`APC`), sixel (`DCS`) and iTerm2 inline images
(`OSC 1337`) pass through **byte for byte**: the daemon forwards every raw
pty chunk to attached clients as it arrives. There is no switch to turn on
— tmux needs `allow-passthrough`, linger does not.

The emulator itself *ignores* the payload: an image sequence parks the
parser in its string state until the terminator and accumulates nothing.
So a program streaming megabytes of base64 cannot grow a session or reach
a checkpoint, and cannot wedge the parser — the same bound that covers any
other hostile output (§Bound, §Total in `THEOREMS.md`).

### On reattach

`restore` repaints from the cell grid, and a cell holds a character, its
combining marks, a width and a pen — there is no image plane. Kitty
placements are overlays anchored to cell coordinates, out of band from
cell content, so a grid repaint cannot carry them. What brings an image
back is the *application* redrawing:

| on reattach | what happens |
|---|---|
| terminal size **changed** | the pty is resized, the program gets `SIGWINCH`, a full-screen app redraws — and re-emits its own images |
| terminal size **unchanged** | the kernel suppresses `SIGWINCH` (it compares the winsize first), so nothing redraws; press the app's refresh key (`Ctrl-L` for most) |
| the image came from a command that has **exited** | nothing will re-emit it — e.g. a `kitten icat` left in scrollback is gone |

An app's own redraw is strictly better than any replay we could do, since
it also refreshes anything the emulator models imperfectly. Both halves of
the size rule are pinned by `tests/graphics_test.py`.

### Why linger doesn't store images

It could be made to work — cap the stored bytes, or remember only kitty
*placements* (an id and a position, which re-place with a payload-free
`a=p` sequence). Neither is free:

- placements only replay into the *same* terminal process that still holds
  the image, so a reattach from elsewhere, or after a reboot, gets
  nothing — and reboot-resume is the whole point of the checkpoint;
- replaying them correctly means implementing kitty's placement model
  (ids, z-index, cropping, whether a placement scrolls with content); an
  image in the wrong place is worse than no image;
- sixel and iTerm2 have no re-place concept at all, so those need the full
  payload or nothing;
- payloads would land in the periodic on-disk checkpoint, turning a small
  timed write into a multi-megabyte one.

So the scope is passthrough plus the application's own redraw. If you want
a picture to survive independently of the program that drew it, give it its
own kitty tab — `recipes/lzo.fish` makes one per session.

## Notes

- Reboot-resume is automatic (periodic checkpoint + restore on attach).
- Images (kitty graphics, sixel, iTerm2) work while attached and vanish
  on reattach — see [Graphics](#graphics).
- Reattach paints the session's scrollback into your terminal's own
  scrollback, so wheel-scroll, search and selection find it. That is one
  buffer shared with your shell — linger never uses the alt screen — so
  attaching a session **that has history erases whatever history that
  window held** (`CSI 3 J`, the sequence `clear` sends) and then pushes up
  to about three thousand lines of the session's own. Attaching a session
  with no history leaves your window alone. `linger history` prints a
  session's scrollback without touching the terminal.
- `attach` needs a terminal; bare `linger`/`ls`, `run`, `send`, `info`,
  `capture`, `resize` are scriptable (see §Agents).
- An unreachable or mid-reboot host drops out of `ls -r` after a few
  seconds; `attach name@host` fails with ssh's own error. Once the host
  is back its sessions list as `resumable` and attach restores them.
- A dropped link cannot hurt a session — it detaches; reattach restores
  the screen (see `recipes/` for the client-side comfort).
- Detach key `Ctrl-\`; `LINGER_NO_DETACH_KEY=1` disables it.
- Detaching hands the terminal back: leaving a full-screen program does
  not leave your shell on the alt screen, with mouse reporting on, no
  cursor, a stale scroll region or line-drawing glyphs. Every exit path
  does it (detach, session exit, dropped link). The window title is the
  one thing not put back — we never read yours.
- Remotes: `-r host,host` for one run, `~/.config/linger/remotes` to
  persist (duplicates are an error). Hosts need `linger` on their `$PATH`.
- `LINGER_DIR=<dir>` isolates sockets + state on local storage.

## Design

`THEOREMS.md` — the invariants (bounded under load, no crash on any
input, sessions outlive clients, checkpoint round-trips, one session
can't leak into another, a row's identity is its socket name).
`tests/e2e.sh` — the whole-deliverable gate. `specs/archive/lean-zmx.md`
— the build record.
