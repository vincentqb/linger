# lean-zmx — session persistence + TUI manager in pure-function Lean 4

Status: active
Updated: 2026-06-01

Deliverable: `lzmx`, one binary. zmx-shape session layer (daemon per
session, attach/detach/list/kill/send/run/history/wait) + a TUI manager
(list/preview/create/attach/kill across local and ssh-remote machines),
with reboot-resume, written as pure state machines + a thin IO runtime +
one small C shim. Theorems resolve the design tensions.

## Scope decision (from PLAN.md, recorded so it isn't relitigated)

"Feature-complete terminal multiplexer ... like zmx" is read as
**feature-complete zmx, not feature-complete tmux**: zmx's philosophy
(and its README comparison table) explicitly rejects windows/tabs/splits
— the OS window manager owns that. The TUI here is the
zmx-session-manager role: see and manage sessions (including remote
ones), not compose panes. The prior attempt (~/lean-tmux) drowned in
tmux fidelity and never shipped a runtime; this repo inverts that.

## Out of scope / non-goals

Windows, panes, splits, layouts, copy-mode, mouse protocols of our own,
tmux command/option compatibility, customization (one modern default,
Dracula), Windows-the-OS, multi-user sockets.

## Architecture

```
lzmx <verb>            argv dispatch (bare `lzmx` opens the TUI)
├── Zmx/Core/*         PURE: no IO anywhere in these modules
│   ├── Wire.lean        framed socket protocol, incremental decoder
│   ├── Vt.lean          minimal VT emulator: grid, scrollback ring,
│   │                    cursor, pen, alt screen, UTF-8 + width
│   ├── Render.lean      Screen snapshot -> ANSI bytes (restore, preview)
│   ├── Session.lean     daemon state machine: step : State -> Event ->
│   │                    (State, List Effect); effects are data
│   ├── Checkpoint.lean  resume codec: save/load session state
│   ├── Name.lean        session/socket name sanitisation
│   ├── Remote.lean      parser for `lzmx list --porcelain` over ssh
│   └── Tui.lean         TUI state machine + pure frame renderer
├── Zmx/Posix.lean     @[extern] bindings, the ONLY module importing C
├── Zmx/Runtime/*      IO: daemon loop, client loop, tui loop, CLI
├── c/shim.c           thin syscall wrappers, no logic beyond errno
└── Theorems/*         proofs; THEOREMS.md names each tension
```

Decoupling: `Session` and `Tui` share nothing but `Wire`; the TUI talks
to daemons only through sockets and the CLI (ssh for remote), so it
could be split into a second binary by adding a lakefile line.

Paths: sockets `$XDG_RUNTIME_DIR/lzmx/<name>.sock` (fallback
`/tmp/lzmx-$UID`), checkpoints `~/.local/state/lzmx/<name>.ckpt`, logs
`~/.local/state/lzmx/logs/`. Env: `LZMX_SESSION` set inside sessions,
`LZMX_REMOTES` + `~/.config/lzmx/remotes` for remote hosts.

## Theorems as tension-resolvers (THEOREMS.md is the ledger)

- §Bound  (zellij crashes under load): every queue/buffer in Session,
  Wire and Vt has a structural cap; `step` preserves it. No unbounded
  channel exists to fill.
- §Chunk  (bytes arrive in arbitrary chunks): Wire decode and Vt feed
  are chunking-invariant: feeding `a ++ b` equals feeding `a` then `b`.
- §Frame  Wire round-trip: `decode (encode m) = [m]`; unknown tags skip
  cleanly (forward compat).
- §Restore  Checkpoint round-trip `load (save s) = some s`; `load` is
  total on arbitrary bytes (a corrupt checkpoint cannot panic a daemon).
- §Name  sanitised names cannot escape the socket directory.
- §Total  Vt.feed is total (no `partial`), cursor stays in bounds, grid
  dimensions are invariant under any input byte.
- §Detach (the zmx decoupling): a session with zero clients still
  advances; attach/detach never change grid contents.

## Steps

Step 1 — Skeleton
  Purpose: repo builds green on this box (glibc 2.26 workaround baked in).
  Writes:  lakefile.lean, lean-toolchain, ./lake wrapper, .gitignore,
           AGENTS.md, Zmx.lean stub, THEOREMS.md stub
  Exit:    `./lake build` exits 0.

Step 2 — Posix surface
  Purpose: smallest non-Lean surface: pty spawn, poll, unix sockets,
           termios raw, winsize, daemonize, kill/waitpid.
  Writes:  c/shim.c, Zmx/Posix.lean, Tests/Pty.lean
  Exit:    test exe spawns `sh -c 'echo hi'` in a pty and reads "hi"
           back through a poll loop; `./lake build` exits 0.

Step 3 — Wire protocol (pure)
  Purpose: framed client<->daemon protocol + incremental decoder.
  Writes:  Zmx/Core/Wire.lean, Theorems/Wire.lean, Tests/Wire.lean
  Exit:    §Frame + §Chunk + §Bound(wire) proved, no sorry; tests green.

Step 4 — VT emulator (pure)
  Purpose: restore/preview-grade terminal state: grid, scrollback ring,
           cursor, SGR pen, alt screen, modes, UTF-8 + width.
  Writes:  Zmx/Core/Vt.lean, Zmx/Core/Render.lean, Theorems/Vt.lean,
           Tests/Vt.lean
  Exit:    §Total + §Chunk(vt) + §Bound(scrollback) proved, no sorry;
           snapshot tests: nvim-like alt-screen flow, wide chars, SGR
           survive a save/render round trip.

Step 5 — Session state machine (pure)
  Purpose: daemon logic as data: attach/detach/input/resize/exit/kill,
           broadcast, checkpoint triggers.
  Writes:  Zmx/Core/Session.lean, Zmx/Core/Name.lean, Theorems/Session.lean
  Exit:    §Detach + §Bound(session) + §Name proved, no sorry.

Step 6 — Runtime + CLI verbs
  Purpose: the IO shell: daemonized per-session server (poll pty +
           socket), raw-mode client, argv dispatch.
           Verbs: attach (upsert), detach, list (+--porcelain), kill,
           send, run, history, tail, wait, get/set/unset labels, version.
  Writes:  Zmx/Runtime/{Daemon,Client,Cli}.lean, Main.lean
  Exit:    scripted pty harness: attach creates live shell; C-\ detaches
           leaving shell running; reattach restores screen; two clients
           mirror; every verb exercised with expected output.

Step 7 — Reboot resume
  Purpose: continuum-shape persistence: periodic + on-detach checkpoint
           (grid, scrollback, cwd, argv, labels); dead-but-checkpointed
           sessions list as resumable; attach resurrects (replay
           snapshot, respawn shell in saved cwd).
  Writes:  Zmx/Core/Checkpoint.lean, Theorems/Checkpoint.lean,
           runtime wiring
  Exit:    §Restore proved; harness: SIGKILL daemon, attach again ->
           old scrollback visible + fresh shell in saved cwd.

Step 8 — TUI
  Purpose: bare `lzmx`: session table (local+remote) with live preview,
           create/attach/kill/filter; Dracula, status top, traffic-light
           state colors (from ~/.tmux.conf); attach = exec, so the TUI
           never sits between you and the pty.
  Writes:  Zmx/Core/Tui.lean, Zmx/Runtime/Tui.lean, Theorems/Tui.lean
  Exit:    harness drives TUI in a pty: navigate, preview shows session
           content, create + kill round trip; §Bound(tui) proved.

Step 9 — Remote over ssh
  Purpose: TUI lists sessions from `~/.config/lzmx/remotes` hosts via
           `ssh host lzmx list --porcelain`; attach execs `ssh -t`.
  Writes:  Zmx/Core/Remote.lean, Theorems/Remote.lean, tui wiring
  Exit:    §Remote proved (total, garbage-tolerant, §Name carries);
           harness with a fake-ssh shim shows remote rows + attach argv.

Step 10 — Verify (terminal)
  Purpose: whole-deliverable check, not per-step bars.
  Writes:  tests/e2e.sh, README.md
  Exit:    one script: build from clean; create 2 sessions; run
           commands; detach/reattach with restore; list/labels/history/
           wait; simulated reboot resume; TUI drive-through; fake-remote
           listing. Exits 0. Zero `sorry`/`partial` in Zmx/Core and
           Theorems. `git grep -n sorry Theorems Zmx` empty.

Round cap: 3 review/revise rounds per step, then re-plan.

## Deliberate simplifications (code-minimalism markers)

- `wait` = wait for session process exit (zmx tracks run-tasks; ours is
  the useful 90%).
- checkpoint interval fixed 60s; no config file for the TUI look.
- completions/print/write verbs: stretch, after Step 10.
