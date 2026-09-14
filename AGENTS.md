# linger

Session attach/detach + a CLI session overview in pure-function Lean 4.
Everything is `linger` as of 2026-08-19: the binary, the Lean library and
namespace (`Linger.Core`, `Linger.Posix`, `Linger.Runtime`), the `Linger/`
tree, the shim's `linger_*` symbols, the `lingertest` smoke exe. The old
`zmx`/`lzmx` name survives in exactly three places, each on purpose:

* **The checkpoint magic is `"LNGR"` v1 and nothing else is accepted**
  (`Linger/Core/Checkpoint.lean`, `save_tag`). The pre-rename `"LZMX"` reader existed
  for exactly one commit: it was there to migrate files written before the rename, and
  once `save` had been writing `"LNGR"` and no old-tag checkpoint was left on disk it
  was deleted rather than carried. **If you ever need to read one, check out
  `e1ac562`** — the reader and its two theorems (`load_legacy_save`, `save_no_legacy`)
  are green there. That is the escape hatch, and it is cheaper than a branch for a file
  nobody has: a checkpoint is a cache, not a contract.
  `stripMagic` stays a **named stage** even though it now checks one tag — naming it is
  what let `load_save` drop its `maxHeartbeats 2000000` raise, measured both ways. Do
  not inline it back.
* **`SCRATCHPAD.md` and `specs/archive/`** keep the old paths in their historical
  entries. The worklog is append-only and the archived specs are closed records:
  rewriting a path inside them would falsify what was true when it was written.
  Entries before 2026-08-19 say `Zmx/…`; read them as `Linger/…`.
* The checkout directory is still `lean-zmx` (renaming it is the user's call, since
  it changes everyone's paths).

Separately, **do not editorialize about other codebases** — the rule is under
§Rules and it is binding. Describe what linger does and why; never characterize,
rank, or make a factual claim about what another project does. `README.md`
§Design's prior-art list — bare names and links, nothing else — is the one
sanctioned place a peer project is named; `4551a5b` cut it back to that shape and
the 2026-09-14 sweep removed the same species of clause from thirty-four other
sites, including four this paragraph used to *instruct you to keep*. That
instruction was the reason the citations kept coming back, which is why it is gone
rather than softened. `tests/gates.sh` now holds the sanctioned list to its bare
shape.
`README.md` is the user-facing overview. `specs/archive/` holds the
closed build plans with their completion records. Read `specs/archive/`
itself rather than trusting a list here to stay current — two counts of
it rotted in this file already.

## Where things stand — read this first after any compaction

1. **One spec is in flight: `specs/scrollback-fidelity.md`.** Steps 1–4 are done
   (2026-09-11) — the emitter, the positive scroll specification, the
   `Fixes (·.sb)` tail, `push_walk`, and the composition: `restore_sb_any` /
   `restore_sb_reachable` / `restore_sb_exact` / `Linger.Core.resume_sb`, plus
   `restore_sb_keeps_of_empty` for the branch the guarded `ED 3` forces. The
   scrollback has left THEOREMS.md's fixture-carried list. **Only Step 5 remains
   and it is optional and off the critical path** (the `+4` slack made honest, and
   `scrollbackAnsi_le` to retire the byte-budget fixtures). Its third item —
   the decision about `Render.history`'s dead `withAnsi` branch — **is discharged
   (2026-09-14): the argument is deleted.** The branch was dead *and* unproved, and
   mutation proved nothing observed it (its body replaced by four junk bytes left
   `./lake build` and `./lake build Theorems Tests` green), so there was nothing to
   preserve. Not wired up as `linger history --color`, and the reason is a cost worth
   not re-deriving: `Msg.history` carries no payload and the tag assignment is frozen,
   so a flag means a new wire tag plus a case in each of `Theorems/Wire.lean`'s four
   exhaustive tag case-bashes — and a *new, weaker* framing claim, because `rowAnsi`
   emits `ESC` and `history_framing`'s "every byte is `LF` or printable" is false of a
   coloured stream. `Render.history` now takes a `Vt` alone; all four of its claims
   (`history_framing`/`history_lines`/`history_records`/`history_screenText_suffix`)
   lost the `false` and the `rw [ite_eq_right …]` that discharged the `if`.
   Read the Step 4 record before
   touching the ring: it names six findings, of which the two most expensive to
   rediscover are that `Fixes` **cannot** state the `ED 3` (it is an invariance
   predicate; the byte walk is by hand) and that `Good` says nothing whatever
   about `sb.start`, so the `ED 3` is the only source in the repo for what
   `push_walk` needs. Also do not re-derive: `replayEq`'s `sb` conjunct is blind
   to bugs *inside* `sbRows` — the literal-anchored fixtures are the oracle for
   the fit and the order — and the twelve mode bytes ending `scrollbackAnsi` are
   behaviourally inert but proof-load-bearing **twice over** now.
   **`specs/archive/vt-toolkit.md` is CLOSED** (2026-09-11, all four steps): `Vt`'s
   twenty fields are `private`, so no importer can write, forge or **read** one. The
   read half was not free when the spec closed and is the audit's finding R6:
   `deriving Repr` was a public, total reader of all twenty (`repr (Vt.init 3 2)` from
   a plain import printed every one, from a `module` importer and a legacy one alike),
   so for three days the seal was write-hiding plus no-forge only. **`deriving Repr` is
   gone as of `25b9dde`** and the record's original wording is true again — which is
   why the archive is *not* edited: a closed record whose claim came true needs no
   correction, and the intermediate weaker state lives in SCRATCHPAD.md where it
   belongs. Three facts worth not re-measuring: no-forge survived `Repr` regardless
   (there is no way back from a printout — `DecidableEq`/`BEq`/`FromJson` all fail to
   synthesize); the removal was **free**, its whole cascade being two `Repr`-only
   clauses on `Terminal.Result` and `Session.State` with no consumer anywhere; and it
   **holds against a re-derive**, because `deriving instance Repr for Vt` from outside
   the seal fails with `Unknown constant` on all twenty private projections — so Lean's
   own "adding `deriving instance` may allow" hint is misleading here, and that is what
   made removal worth doing rather than merely worth wanting. Reach the state through
   the read-only window (`Vt.colCount`/`rowCount`/`cursorPos`/`inAlt`) or a friend
   import; do not re-add a derive to make a `#eval` print.
   The checkpoint decoder validates `Good` **and** `Renderable` and refuses the rest;
   `lean_lib LingerVt` plus an exact-set import grep pin the toolkit's closure; and
   the friend set is computed transitively rather than grepped, because
   **`import all` transits**. Two mechanism facts worth not re-deriving are in its
   record: per-field `private` makes the *constructor* private too (so sealing one
   field buys the whole no-forge property), and `import all` grants access but not
   permission to re-export — a **public** declaration's type may not name a private
   field, which is why 19 `Theorems/` files dropped `public section`.
   **Two findings are open on purpose**, with compiled exhibits in SCRATCHPAD.md
   under "the adversarial audit of the seal": `unsafe` + `@[implemented_by]` can
   make every theorem true of a value the binary never returns (R4 — wants a
   three-line grep in the `@[extern` family, measured at zero current hits), and
   `Classical.choice` on `Nonempty Vt` yields a `Vt` nothing is provable about (R5 —
   the concrete reason the exhaustiveness is compile-time prose and can never be a
   theorem). Neither is a regression; both are why the seal's guarantee is stated
   as a property of *importers* rather than of propositions.
   Everything else is closed and lives in `specs/archive/`; each file records
   its completion. The records carry the nuance this list used to duplicate,
   and the duplicates rotted. (There is no `PLAN.md`: its prior-art links live
   in README §Design, and everything in `specs/archive/` is closed.)
2. **`SCRATCHPAD.md`** — append-only worklog: proof recipes, measured
   environment facts, break-verify records, and the negative results.
   Read before writing; append after; never delete prior entries.
2b. **`.claude/last-compact-state.md`**, if it exists — written by a
   `PreCompact` hook (`.claude/precompact-snapshot.sh`) at the moment
   compaction started: the commit, what was uncommitted, and which worklog
   round was in flight. Facts, not a summary, and the three things a
   compaction genuinely eats — this file and the spec re-ground you; the
   summary does not. Gitignored, so a stale one is only ever your own.
3. Re-ground against those two files, not against a compaction summary:
   the summary is what dropped the nuance. Check the current work against
   the spec's Goal and Definition of done, not against the summary's
   description of it.
4. Close each round by updating the spec's status block (done ✓, next →) and
   committing a verified checkpoint. One item in flight at a time: a half-done
   item straddling a compaction is the thing most likely to be silently
   abandoned.

New work opens a new `specs/<slug>.md` and gets named in item 1 above;
archive the old one with a completion record rather than editing it. Keep the
live count at one — the one-item-in-flight rule. A spec whose remaining steps
are all "optional" is finished; archive it saying so.

## Settled non-goals — don't build these

Each was decided with a reason; re-opening one needs a new reason, not a
fresh pair of eyes.

- **Windows, tabs, splits.** linger multiplexes sessions *over time* —
  attach, detach, survive reboots — not panes inside one terminal: the OS
  window manager (or your terminal's tabs) owns composition. So
  "feature-complete" means every verb of the attach/detach surface, not a
  pane layout engine. Recorded in `specs/archive/lean-zmx.md`.
- **An interactive picker.** One was built and shipped (step 8, with a
  passing pty test), then removed: a first-time user ran bare `linger`,
  got a full-screen picker and typed at it as if it were a shell. Bare
  `linger` now prints a listing and exits, and `E2E/Overview.lean`
  guards that. Pickers live in `recipes/` (six lines of fish + fzf).
- **Storing images so they survive reattach.** Kitty/sixel/iTerm2
  sequences already pass through byte for byte while attached, and an app
  that redraws re-emits its own images (a reattach at a *changed* size
  nudges it via `SIGWINCH`; at the same size the kernel suppresses the
  signal). Persisting them needs kitty's placement model, only replays
  into the same terminal process that still holds the image — so not after
  a reboot, which is the point of the checkpoint — does nothing for
  sixel/iTerm2, and puts payloads in a periodic on-disk write. See README
  "Graphics" and `E2E/Graphics.lean`.
- **Restoring the process tree.** Reboot-resume restores the screen,
  scrollback, modes, labels and cwd — not the programs. Restarting them
  would mean guessing which commands are safe to re-run, and a wrong guess
  is worse than an empty prompt, so the trade is deliberate: the work
  resumes, the programs do not.
- **A shared multi-session server.** One daemon per session is not an
  accident of implementation, and the argument is a *guarantee* argument, so
  it belongs here rather than in a design note. `Session.State`
  (`Linger/Core/Session.lean`) models exactly one session — one `vt`, one
  `scan`, one `clients` list, no session map anywhere in the pure core — so
  §Isolate's `step_bytes_isolates`/`run_bytes_isolates` quantify over
  *clients within one roster*. **Cross-session isolation is therefore not a
  theorem with a narrow scope; it is the absence of a shared object to state
  one about.** A shared server converts that structural containment into a
  proof obligation over a session map, and A2 (`run_wf`) would have to be
  re-derived with the map as its subject. The caps compound it — `maxClients`,
  `maxLabels`, `outbufCap`/`ptyInCap` are per-*process*, so one session's
  client flood cannot deny another a roster slot; inside one heap a cap is
  bookkeeping and exhausting the heap is still global. §Claim gets the same
  benefit: the `flock` *is* the ownership, so a crashed owner releases its
  claim with zero reconciliation, where a shared server must reconcile a
  table. And per-session checkpoints bound a corrupt file's **scope** to one
  session, where `load`'s totality alone only bounds its *kind*.
  Cross-session work goes through the CLI by name — that is the mechanism,
  and `recipes/` uses it (parsing `ls --porcelain`). What this genuinely
  costs is written down rather than denied: N × (process + pty + resident
  `Vt`), a serial `ls` fan-out, no cross-session atomicity (currently
  unexercised — it becomes load-bearing the day a `rename` or `merge` verb
  appears), and **no listing snapshot**: row identity and per-row status are
  sound (§Row), but the *set* is a smear over the fan-out window rather than
  an instant.
- **Terminfo / capability negotiation.** `Render`'s repertoire is fixed and
  linger consults no capability database for its own output, and that is what
  makes the fidelity theorems statable: `restore : Vt → Bytes` and
  `leaveAnsi : Bytes` (a constant with no argument) are pure functions of
  state, so ~40 named fidelity claims conclude `(w.feed (restore v)).X = v.X`
  over an **arbitrary receiver with no hypothesis on it**. A
  `Caps → Vt → Bytes` signature gives every one of them a `caps` binder *and*
  turns the conclusion conditional — "the grid equals `v.grid` **if** `caps`
  declares …" — which re-introduces exactly the receiver preconditions the
  project spent effort removing (`restore_grid_any` shed `u8need` and
  `rows ≥ 2`), and forfeits three properties a capability-typed emitter cannot
  state at all: determinism given state (the oracle behind `replayEq` and the
  golden fixtures), host-independent repaints, and no `TERM`-shaped input to
  our own output. Note the distinction: linger *sets*
  `TERM=xterm-256color` for the child as a literal (`Daemon.serve`) and
  *consults* nothing — `E2E/Terminal.lean` pins parent-`TERM` independence.
  What this costs is graceful degradation, not breakage: conformance entries
  11–12 are inert-on-absence by their own semantics, 8–10 inert or universal,
  1–7 the declared xterm baseline. Exactly two things are user-observable and
  both are already recorded — the window **title** is not restored on detach,
  and attaching a session with history erases the borrowed terminal's saved
  scrollback (`CSI 3 J`), which follows from sharing the user's scrollback
  rather than from this decision. **Do not "fix" the title with the xterm
  title stack**: `Render.lean` already declines it because the sequence is not
  universal, and adding it would make `leave_canonical_all` conditional — a
  weaker theorem bought with a scope increase.
- **Making `attach` switch instead of nest when run inside a session.**
  `LINGER_SESSION` is already exported to the child (`Daemon.serve`) and
  documented, so a user or a recipe can already branch on it; the proposal
  only ever added implicit behaviour on top. Two reasons not to: nesting
  **works**, dully — the inner client intercepts `ctrl-\` first
  (`Client.attach`'s `splitDetach`), so a detach pops you to the outer
  session, which is what you would want anyway — and `attach` doing something
  other than what the user typed, conditional on invisible environment state,
  is the interactive picker's mistake in a new costume. `Linger/Runtime/Cli.lean`
  is `IO`, so no theorem could constrain the new behaviour either. If a real
  wedge ever turns up, the house pattern is to **refuse loudly** (as the
  control-resize refusal does), not to silently switch.
- **A pure poll plan / `revents` classifier.** The premise that made the
  one historical desync a desync — `revents[i]` belongs to `fds[i]` — is
  established by the C loop in `c/shim.c` and is not a Lean-visible fact,
  so the theorem's canonical break (permute the slots) does not catch its
  canonical bug. Killed in `specs/archive/runtime-invariants.md`; the
  negative result is also in SCRATCHPAD 2026-08-18.
  so the theorem's canonical break (permute the slots) does not catch its
  canonical bug. Killed in `specs/archive/runtime-invariants.md`; the
  negative result is also in SCRATCHPAD 2026-08-18.

## Build

- **The pin is `v4.34.0-rc2`, a release candidate**, and that is deliberate:
  `lean-fmt` is the only Lean formatter/linter that exists outside Mathlib,
  it ships one release per toolchain, and every one of its releases
  requires an rc of v4.34. `v4.34.0` stable does not exist yet. **Move the
  pin when it does and lean-fmt tags it** — that is the whole trigger.
  (Re-checked 2026-09-11: upstream's newest tags are still `v4.34.0-rc2`
  on both lean4 and lean-fmt, so the trigger has not fired.)
  The bump cost 152 deprecation renames (all `if_pos`→`ite_eq_left` shaped,
  definitionally identical) and moved no ratchet.
- Always `./lake build` (the wrapper, not bare `lake`): on the AL2 host
  glibc 2.26 cannot run the toolchain's bundled clang, so the wrapper
  routes C compilation through Homebrew clang. Bare `lake` looks 90%
  green and dies in the C backend. The wrapper derives the toolchain
  directory from `lean-toolchain` and fails loudly if it is missing —
  it used to hardcode `v4.32.0`, which meant a version bump broke the
  link on `-lgmp` with nothing to suggest why.
- `lean-fmt` is installed **standalone**, never as a Lake `require`: the
  require-free lakefile and empty `lake-manifest.json` are gates, and
  README promises no external Lean dependencies.
  `make -C <clone> install`, at the tag matching `lean-toolchain`.
- **Its linter and formatter are both adopted** — the format run landed at
  `78cee28` (66 files); pre-commit runs `lean-fmt check`, and CI runs
  `lean-fmt format --check`. `.lean-fmt.toml` carries the settings, the
  history and the measurements; don't copy its numbers here, the copy rotted
  once. `repeat' split` + `all_goals first | …` layout survives formatting;
  commands the engine cannot lay out keep their hand layout, which is why some
  proofs still look hand-laid — that is by design, not drift.

## Gates, hooks and CI

- **`tests/gates.sh` is the only place a ratchet number lives.** The
  purity greps, the OS-surface checks and every ratchet
  (`SHIM_CAP`, `HEARTBEAT_CAP`, `RECDEPTH_CAP`, `RUNTIME_PARTIAL_CAP`,
  `E2E_PARTIAL_CAP`, plus the zero-Python and `Tests/`-vs-`tests/`
  invariants) live there. `tests/e2e.sh` calls it, `pre-commit` calls it,
  CI calls it. Never copy a number out of it — the markdowns did exactly
  that and every copy rotted. **That includes the number of ratchets**,
  which is why the summary line, the hook name and the CI step name all
  say "the ratchets" rather than counting them: "five" was wrong within a
  day of `RECDEPTH_CAP` landing.
- **Two tiers, and the split is by cost.** Commit time is
  `.pre-commit-config.yaml`: whitespace, YAML, and `gates.sh` — about a
  second, and **nothing there compiles Lean**. Everything slow is CI
  (`.github/workflows/ci.yml`): the build, the proofs, the shim smoke
  tests and all ten pty suites, as a ubuntu+macos matrix, because the
  `#ifdef __APPLE__` branch in `c/shim.c` is not compiled on Linux at
  all and a Linux-only CI cannot typecheck code this file claims works.
- There is deliberately **no pre-push hook**. An earlier version ran the
  whole of `./tests/e2e.sh` there and it made pushing cost six minutes,
  which is the wrong tier for it. Run `./tests/e2e.sh` yourself before a
  commit that touches the runtime — that rule has not changed — but
  nothing forces it at push time.
- Install once per clone: `uvx pre-commit install` (or `pre-commit
  install`). Don't reach for `--no-verify`; the hook is the check.
- The framework is a dev tool, not a dependency: the config is YAML and
  the repo-local hook is `language: script`, so nothing Python is
  tracked and `gates.sh`'s zero-Python invariant still checks itself.
- The wrapper branches on `uname -s` and is a **pass-through on macOS**,
  where the same overrides break the build (`LEAN_AR=/usr/bin/ar` is
  Apple's ar, which cannot read lake's `@…rsp` response file). Keep
  using `./lake` on both — the command is the invariant, the workaround
  is the host-specific part.
- `./lake build` = program; `./lake build Theorems Tests` = proofs +
  unit tests. All three must be green before a commit.
- The tree builds and passes `./tests/e2e.sh` on Linux and macOS as of
  2026-08-19. Platform splits live in exactly two places — `#ifdef
  __APPLE__` in `c/shim.c` (CLOEXEC sockets, and `getcwd_of` via libproc
  where there is no `/proc`) and the `ps -o ppid=` in
  `E2E/Harness.lean`'s `Env.daemonPid`, which is the *same* command on
  both platforms and so is not really a split at all. It replaced the
  `/proc`-or-`lsof` fallback that used to be the second one: asking
  `linger info` over `<LINGER_DIR>/<name>.sock` makes the "is this
  daemon mine?" isolation **structural**, so the filter it needed is
  gone rather than ported (2026-08-29, the Lean port of the suites).
  **No errno numbers in Lean**: `-111` for
  ECONNREFUSED in `Daemon.serve` compiled fine and silently disabled the
  stale-socket path on macOS. The shim returns `-errno`; only the shim
  knows the numbers. See the 2026-08-19 port entry in SCRATCHPAD.md.

## Rules

- `Linger/Core/*` is pure: no `IO`, no `partial def`, no `sorry`. Effects
  are data (`List Effect`); the runtime executes them.
- Only `Linger/Posix.lean` and `c/shim.c` touch the OS. Keep the shim
  logic-free (syscall + errno only). It carries a **wrapper-count
  ratchet** (`SHIM_CAP` in `tests/gates.sh`): it drops silently, but
  raising it is a deliberate edit — the checkpoint for "does Lean core
  already expose this?" before adding a syscall. A source-tree property
  like this can't be a theorem; the grep gate is the right oracle
  (`verifier-in-the-loop`).
  **All 22 were re-audited against v4.34.0-rc2 on 2026-09-14 and none is
  removable** — the per-wrapper evidence is in SCRATCHPAD.md so nobody
  re-runs it. The load-bearing negative: core has no `IO.FS.Handle.ofFd`,
  so `Handle.read/write/close/tryLock` cannot reach a raw pty or socket fd;
  no `poll`, no termios, no ioctl, no sockets, no signals, no `getuid`, no
  exec-that-replaces-the-image; and `Child.kill`/`tryWait` exist only on a
  `Child` from `IO.Process.spawn`, with no pid→`Child`, while our
  `childPid` comes from forkpty. Two traps recorded there: `alive` is *not*
  `kill` with signal 0 (composing it would surface the ESRCH distinction
  into Lean), and `flock` is *not* `Handle.tryLock` (that needs an open
  wrapper back, gives no `O_CLOEXEC`, and ties a kernel-released lock to a
  GC-managed handle). **Fewer exports is not automatically more minimal**:
  merging the termios/winsize wrappers costs a mode argument and a branch,
  which is logic in the shim. The count is not the metric; the rule is.
- Theorems resolve tensions: when two requirements collide, state the
  invariant in THEOREMS.md and prove it, then code to it.
- A theorem or test that cannot fail is worthless: break the code once
  to see it catch (record the break in SCRATCHPAD.md).
- Session names pass through `Linger.Core.Name.sanitize` before touching
  any path. Never interpolate raw names into socket/checkpoint paths.
- `./tests/e2e.sh` is the gate before any commit that touches the
  runtime; it must stay green and warning-free. **Run it in the
  foreground** — a `&` job inherits SIGINT disabled, the agent suite's
  `^C` assertion then fails for a reason that is not linger's, and it
  looks exactly like a flake. The script now probes for this and refuses
  to run; the measurement, the reason the probe is behavioural rather
  than `/proc`-based, and the `setsid`/`nohup` nuance all live on that
  check in `tests/e2e.sh` and nowhere else.
- **`Tests/` and `tests/` are two tracked directories** (Lean unit tests
  vs. the e2e orchestrator). On a case-insensitive filesystem they are
  one directory on disk and git will silently record a new `tests/x` as
  `Tests/x`; check `git ls-files --stage` after adding one, or the file
  lands in the wrong directory on Linux only. The pty **suites** are no
  longer under `tests/` at all: they are Lean, in `E2E/`, run as
  `./lake exe e2e <suite>` (2026-08-29). `tests/` now holds only the
  orchestrator `e2e.sh` and `gates.sh`; the coverage gate is
  `E2E/Coverage.lean`.
- **`E2E/` is `IO`, so nothing in it can be a theorem** — that is what
  `Theorems/` and `Tests/` are for, and the split is the point: a pty
  suite drives the real binary through real syscalls. It is Lean anyway
  because a suite in the implementation's own language cannot drift from
  it — `E2E.Watch` compares against `Render.leaveAnsi` and
  `Status.wantsYou` rather than against copies of what they emit, so a
  rename is a compile error instead of a passing assertion. The port
  cost **no new syscall** (`Posix` already had `spawnPty`, `winsizeSet`,
  `kill`, `waitpidNohang`), which is the condition that made it worth
  doing: `SHIM_CAP` did not move.
- Restructure code for provability rather than weakening a theorem:
  name the stages (see `Vt.print*`, `Vt.step*`), clamp bounds locally,
  and prefer order-robust proof scripts (`repeat' split` +
  `all_goals first | …`) so a new branch doesn't break the proof.
- Any poll loop must freeze its fd set before polling (a mid-round
  accept desynced `revents` once and panicked the daemon).
- **A `maxHeartbeats` or `maxRecDepth` raise is a measurement, and it
  expires.** Nothing else expires it: a 2026-08-18 sweep deleted 18 of 20
  heartbeat raises, and the control showed six were already deletable
  *before* the file split that prompted the sweep — they were budget added
  when the proofs were rougher and never re-measured. After any refactor,
  try deleting them. **`HEARTBEAT_CAP` is now 0**: the last raise wanted a
  better closer, not a bigger budget, and `grind` with the four
  `renderable_*` lemmas retired it (and cut `./lake build Theorems` from
  115.9s to 78.2s). `maxRecDepth` had no gate for a year and rotted the
  same way — two of its three raises deleted with the proofs untouched —
  so it is ratcheted too (`RECDEPTH_CAP`, at 1; the survivor is real and
  `grind` cannot retire it either, measured). A new raise means a proof got
  harder or a term got deeper, which is a signal to read, not to silence.
- **A `while`/`for` loop in a `do` block does not need `partial def`.**
  Five of the runtime's seven had it by habit. Two are honest (`pump`,
  `parseLs`) and named in THEOREMS.md §Total; ratcheted
  (`RUNTIME_PARTIAL_CAP`). Don't add a fuel parameter to shed the
  keyword — that converts a hang into a silent drop.
- **Every pure-core def is named by a theorem statement, and the ratchet is now
  zero** (`E2E/Coverage.lean`, `statementCap`, 2026-09-11). That flips its
  meaning: it is no longer a budget to spend but an invariant to keep — a new
  `Linger/Core` def arrives **with its claim, in the same commit**, or the gate
  fails. Break-verified: adding one unclaimed def exits 1. Two lessons from
  getting there. A cap named only inside a `def` or a `structure` field is
  invisible both to the gate and to a reader looking for the claim — that is how
  `csiCap`/`oscCap`/`dcsCap` (in `Scan.Bounded`) and `maxClients` (in `Bounded`)
  hid, and how `maxClients`' *enforcement* ended up with no theorem at all. And
  a claim that will not close may be false rather than hard: `sanitize` is not
  length-non-increasing, because the empty name becomes `"_"`.
- **A proved pure value needs a grep gate to bite.** `Linger/Runtime/*` is  `IO`, so no theorem can see that the daemon calls `Linger.Core.Buf`
  rather than open-coding the same sums — without the gate the theorems
  are arithmetic about a value nothing forces the runtime to use. Same
  species of oracle as `SHIM_CAP`. When you move a decision into Core,
  gate the runtime against re-growing it. The same applies to a *guard*
  no test can observe: two of `Client.attach`'s three `!readOnly` guards
  are semantic no-ops (the daemon drops a non-sizer's input and resize
  regardless), so they are held by greps and **not** by a pty assertion
  pretending to see them — see `specs/archive/pin-the-gaps.md`.
- **"No theorem can see `IO`" still holds at v4.34.0-rc2, and now for a
  named reason rather than an assumption.** Every grep gate above exists
  because of it, so it was re-tested on 2026-09-14 against core's Hoare
  framework: `Std.Do`, `mvcgen`, `mspec` and the `⦃P⦄ prog ⦃Q⦄` notation all
  ship and work — an `Id`-monad triple closes green. But `#synth WP IO`
  **fails**: `IO` unfolds to `EIO` to `EST ε IO.RealWorld`, `EST` is not
  `EStateM` (`rfl` refuses), and core ships `WP` instances for
  `Id`/`StateT`/`ReaderT`/`ExceptT`/`OptionT`/`EStateM`/`StateM`/`ReaderM`/
  `Except`/`Option` and **nothing for `EST`** — zero hits toolchain-wide. A
  runtime-shaped triple does not even elaborate; the wall is structural, not
  tactic immaturity. The only route is a generic-monad rewrite with an
  assumed `@[spec]` on each OS primitive, which axiomatizes the kernel
  instead of proving anything. And note: **even a working `WP IO` would not
  retire these gates** — they assert *syntactic* facts about call sites
  ("the daemon calls `Buf`", "the fallback expression is this one"), which
  is not a Hoare triple's shape. Do not re-derive this; it is in
  SCRATCHPAD.md with the probes.
- **`FAILURES: 0` does not mean anything ran.** Every pty suite carries a
  check-count floor in `tests/e2e.sh` (`suite <name> <floor>`), because a
  suite whose assertions sit in a `for` over a list that went empty still
  prints `FAILURES: 0` — demonstrated, not assumed. Floors only go UP
  without discussion. New suites go in `E2E/` and use `E2E/Harness.lean`.
- **`tests/e2e.sh` and `tests/gates.sh` are the deliberate non-Lean files:**
  gates.sh owns the `git grep` purity gates and every ratchet number,
  e2e.sh sequences the builds and the suites; a Lean program shelling out
  to `git grep` and `./lake` would be a worse shell script. Everything
  else is Lean — if you are about to add a `.py`, don't.
- **The purity greps read prose, not just code.** `native_decide` in a
  *docstring* under `Theorems/` fails `./tests/e2e.sh` step 2 exactly as
  it would in a proof. This has cost a full e2e run twice (`fb6a0e6`, and
  again on 2026-08-29). Say "compiled evaluation" in prose.
- **Do not editorialize about other codebases.** Describe what linger does and
  why; do not describe, characterize, rank, or make factual claims about what
  another project does. The sanctioned exception is a **bare pointer**:
  `README.md` §Design's prior-art list is names and links and nothing else, and
  `tests/gates.sh` holds it to that shape. The line that decides the hard cases
  is **peer vs. environment**:
  * a **peer** mention compares, ranks or validates us against them — "the gold
    standard", "crashes under load", "X needs a switch, linger does not", "still
    more than X's default 2000", "X does the same", "two keystrokes fewer than
    X's prefix+s". Every one of those decorates a claim that is *already stated
    in our own terms beside it*, so the edit is: delete the clause, keep the
    claim. Never delete the claim — restate it if the prose was carrying it.
  * an **environment** mention names something on the wire or on the box that
    linger's own correctness is defined against, and it **stays**: a wire format
    (kitty graphics `APC`, sixel `DCS`, iTerm2's `OSC 1337`), a control sequence
    (`xterm`'s `ED 3`, the title stack `CSI 22 ; 0 t`), a terminfo value
    (`TERM=xterm-256color`, an inherited `xterm-kitty` or `screen`), or a tool a
    recipe drives (`kitty @` in `recipes/lzo.fish`). A format has to be named to
    be supported. And conformance entry 11's receiver list is the *reason* for a
    byte order that `E2E/Attach.lean` step 11 and `Tests/Render.lean` pin —
    delete it and a tested behaviour loses its provenance.
  Borrowing another project's *rule* is fine; **attributing** it is the
  editorial. Name the rule for what it constrains: `Tests/Session.lean`'s
  fixtures are `namespace ObserverAndSizeOwner`, and
  `Theorems/Session.lean`'s `resizeEffects_owner_only` states the size-owner
  invariant without crediting anyone for it. Our own pre-rename name is not in
  scope — see the `"LZMX"`/`lean-zmx` note at the top of this file.
  **Only the prior-art shape is gated**, and the rest is declined on a
  measurement rather than forgotten: a peer wordlist cannot include `screen`
  (463 standalone-word hits, one of them the project) and goes silent on the
  motivating violation once it lets the sanctioned links through. The
  measurement is on the gate in `tests/gates.sh`; read it before building the
  obvious grep.
- **One writer at a time on this tree.** Two agents editing
  concurrently raced the coverage ratchet: untracked files are invisible
  to `git diff -- Linger/`, so an out-of-band `E2E/Coverage.lean` read caught a
  half-written state and reported 28 unclaimed defs. Both also compile
  the same tree, so each sees the other's partial files as errors.
  Serialize, or give each writer a worktree. **`cp -a <tree> /tmp/<name>-wt`
  is the isolation recipe, and it is not idempotent**: if the destination
  already exists, `cp -a` copies *into* it rather than replacing it, so a
  second agent reusing a `/tmp` name inherits the first one's half-finished
  state. That happened on 2026-09-14 and cost a real diagnosis — an agent
  reported "another writer is mid-edit" about work that was only ever in
  its own scratch directory. Use a fresh name, or `rm -r` first.

## Scratchpad

`SCRATCHPAD.md` is shared notes. Read before writing; append
`## Step N notes — <ISO date>` after; don't delete prior entries.

## Commits

One commit per spec step: `step N: <summary>`. Don't rewrite pushed
history.
