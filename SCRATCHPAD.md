# Scratchpad — read before writing; append, never rewrite

## Step 0 notes — recon (2026-06-01)

Settled: scope = feature-complete **zmx** + session-manager TUI, not
tmux. Rationale + non-goals recorded in specs/lean-zmx.md.

Environment (measured):
- Host AL2, glibc 2.26. Lean toolchain v4.32.0's bundled clang cannot
  run here ("GLIBC_2.29 not found"); builds need
  `LEAN_CC=/home/linuxbrew/.linuxbrew/bin/clang` (Homebrew clang 22) and
  the toolchain lib dirs on LIBRARY_PATH. Recipe proven in
  ~/lean-tmux/env/lean_env.sh; baked into ./lake wrapper here.
- elan 4.2.3; toolchains v4.31.0 + v4.32.0 installed. No default set —
  a bare `lean --version` outside a project fails; per-repo
  lean-toolchain file drives it.
- fish is the login shell; fzf present; no zmx binary installed.

Prior art mined (~/lean-tmux STATE.md — worth re-reading when stuck):
- Effects-as-data state machines (`step : State → Event → (State, List
  Effect)`) worked well there; reuse the shape, not the code.
- Their runtime-last ordering meant nothing runnable ever shipped.
  Here runtime lands at Step 6 of 10.
- Lean gotchas recorded there that apply to fresh code: `|>.` binds
  outside an `if`; C-style `u_int` wrap semantics; `decide` can't chew
  big tables (use native_decide); fuel-bounded recursion beats
  `partial def`.

Interface requirements (from ~/.tmux.conf + ~/.config/zellij/config.kdl):
Dracula palette (#282a36 bg, #44475a gray, #f8f8f2 fg, #6272a4 muted,
#ff79c6 pink=selected, #50fa7b green=active/attached, #f1fa8c yellow,
#ff5555 red=dead), status bar at top, activity traffic-light coloring,
truncated fixed-width names (=|14|…), fzf-ish list+preview layout,
minimal chrome (zellij pane_frames false, simplified UI).

zmx facts (README, verbs to mirror): attach is upsert; detach key
ctrl-\ (disable via env NO_DETACH_KEY); multiple clients per session;
socket per session in XDG_RUNTIME_DIR/zmx; ZMX_SESSION env inside;
labels get/set/unset/clear; list --short/--where k=v; history --vt;
wait; run -d; ssh workflow = `ssh -t host zmx attach name`.


## Step 2 notes — 2026-06-01

Settled: entire OS surface = c/shim.c (~25 wrappers) + Zmx/Posix.lean.
Conventions: all Lean object args borrowed (@&); tuples returned as
packed UInt64 (pid<<32|fd) to keep C dumb; read returns Option
ByteArray (none=EOF, some #[]=EAGAIN); write returns Int64 (-1 = peer
gone, a value not an exception, so daemons treat disconnects as data).

New env finding: toolchain's llvm-ar ALSO glibc-blocked (like its
clang); wrapper now sets LEAN_AR=/usr/bin/ar. Lake honors LEAN_AR.

Lean gotchas hit: imports must precede module doc comments; `a |>.f ≥ n`
parses as `a |>. (f ≥ n)` — parenthesize; String.trim deprecated in
4.32 (returns Slice now) — avoided.

Hand-off: daemon loops should poll-then-read (drain in ZTest.lean is
the shape); accept fd must be setNonblock'd (poll/accept race); reap
via waitpidNohang poll loop, -2 means not-our-child (use alive).


## Step 3 notes — 2026-06-01

Settled: wire codec on List UInt8 (runtime converts at the socket
edge) — this bought real ∀-theorems where lean-tmux had native_decide
fixtures. §Frame (decode∘encode = id, incl. stream form), §Chunk
(feed (a++b) = feed a then feed b), §Bound (decoder buf ≤ 4+maxPayload
for ANY input; sticky error on oversize claim; every delivered payload
≤ maxPayload) all proved, no sorry, no native_decide in Theorems/.

Break-verified: oversize branch returning `bytes` instead of `[]`
broke 5 theorems (feed_append, takeFrames_append, errored_buf,
buf_le, msgs_payload_le). Reverted.

Proof recipes that worked (reuse in later steps):
- WF-recursive defs: `rw [f.eq_def]; dsimp only` to unfold one layer;
  `induction xs using f.induct` — name the `have len` binder too, then
  `replace hlen : <real type> := hlen` to zeta-expand.
- let-pattern `let (a,b,c) := e; …`: `rcases h : e with ⟨a,b,c⟩` then
  `rw [h]` — never project h.1/h.2 (Prod eq isn't a structure).
- UInt roundtrips: `apply UInt32.toNat_inj.mp; simp [UInt8.toNat_ofNat',
  UInt32.toNat_ofNat']; omega`.
- decidable-if chains over UInt8 tags: prove per-branch with by_cases;
  in a POSITIVE branch simp [hK] alone collapses the whole chain.
- `split` cannot reach ifs under a projection like (if..).payload —
  by_cases instead.
- decide fails on WF-recursion (kernel can't reduce takeFrames);
  tests of runtime behavior use native_decide, golden encode tests
  stay decide.

Hand-off: tags frozen in Tests/Wire.lean golden frames (input=0,
output=1, resize=2, attach=3, detachAll=4, kill=5, info=6, infoReply=7,
history=8, exited=9, wait=10, labelSet=11, labelUnset=12, labelClear=13,
done=14, err=15). New tags append; never reuse.


## Step 4 notes — 2026-06-01

Settled: Vt = per-byte `step` + `feed = foldl step` (so §Chunk is
List.foldl_append, definitional); restore-grade scope (no reply
channel, no reflow-on-resize, OSC8/sixel skipped) — rationale in
Vt.lean header. Render.restore replays main+alt when in alt screen.

Proved (Theorems/Vt.lean): `Good` composite invariant — cursor + saved
+ alt-stashed cursors in bounds, top≤bot<rows, scrollback ≤ 10000, CSI
params ≤ 16, OSC acc ≤ 2048, u8need ≤ 3 — preserved by step/feed for
ANY byte stream (§Total+§Bound), plus feed_append + feed_singletons
(§Chunk) and resize/init Goodness. ~45 lemmas.

The theorems caught two real bugs while proving:
1. subFlags array could outgrow its guard (only params was checked) —
   fixed by construction: one Array (Nat × Bool).
2. resize didn't clamp the SAVED cursor — DECRC after a shrink would
   restore out of bounds. Fixed + the resize cursor-rides-down idea
   simplified to plain clamp.
Break-verified: uncapping Ring.push broke 3 theorems. Reverted.

Downgraded (recorded honestly): dims-invariance of step is NOT a
proved theorem — every op preserves cols/rows syntactically except RIS
(re-derives via clampDim, identity under Good), but stating it needs
per-op dims lemmas through ite/foldl compositions (~25 more lemmas).
The runtime re-reads cols/rows after feed, so nothing depends on it.
THEOREMS.md §Total row updated.

Proof recipes added this step:
- Restructure code for proofs: tuple-lets → named ites; big functions
  → named stages (printWrap/printPut/...; stepGround/stepCsi/...);
  computed bounds → local `min` clamps. Each turned a stuck proof
  into a 5-liner.
- Good-preservation via obtain 15 fields / rebuild ⟨tuple⟩ — record
  updates are defeq so the same tuple often just works.
- Case-order-robust dispatch: `repeat' split; all_goals first | exact
  lemA | ...` instead of positional bullets (match arms with
  multi-patterns expand unpredictably).
- `rw [if_pos hc]/[if_neg hc]` after by_cases when `split` can't see
  through a projection-of-ite; `set` is Mathlib-only (unavailable).
- NEVER `git checkout <file>` to revert an experiment on UNCOMMITTED
  work (was lucky: file was untracked). String-level revert instead.

Hand-off (step 5+): daemon feeds Vt via feedBytes; reattach sends
Render.restore v; preview via Render.previewLines; runtime must clear
v.bell after signaling activity; resize via Vt.resize (Good-preserving).


## Step 5 notes — 2026-06-01

Settled: Session = effects-as-data machine (step : State → Event →
State × List Effect); decoding lives IN the machine (per-client
Wire.Decoder), so §Bound covers it. maxClients 16, maxLabels 64,
checkpoint cadence 60s via tick. Clean child exit DROPS the
checkpoint (resume is for crashes/reboots, not completed work).

Proved: §Detach (closed/detachAll leave vt+labels untouched with zero
effects; zero-client ptyOut advances vt identically; attach preserves
scrollback; input never touches vt), §Bound(session) (clients/labels/
decoder caps preserved by step for any event), §Frame machine-half
(unknown + wrong-direction msgs → (s, [])), step_vt_good (daemon's Vt
stays Good under any event stream — composes Vt.Good with the machine).
§Name: sanitize establishes Valid for ANY input (no /, no NUL, no
leading dot, nonempty, ≤80) + no-escape corollary.

Break-verified: gating ptyOut's vt.feed on attachment (the zmx
anti-pattern) broke 3 theorems + 2 tests. Reverted.

New recipes:
- `first`-alternative lists: a bare `simp` that PARTIALLY succeeds
  eats the goal and reports unsolved at the end — always `(simp;
  done)` inside `first`.
- foldl-with-lookup preservation: name the fold (feedMsgs) in the CODE
  so theorems can target it; induction generalizing the accumulator.
- `set` tactic is Mathlib-only; `generalize h : expr = x` is the core
  replacement (after dsimp to zeta-reduce lets).
- Msg-driving tests via real Wire.encode frames double as decoder-path
  integration tests.

Hand-off (step 6 runtime): effects contract — send/close/writePty/
resizePty/killChild/checkpoint/dropCheckpoint/exit; runtime owns
per-client outbufs (cap 4 MiB, disconnect on overflow — the §Bound
half that lives outside the machine, document in AGENTS); wait replies
arrive via childExited; runtime supplies Event.tick every poll round.


## Step 6 notes — 2026-06-01

lzmx is a working program: attach(upsert)/run/send/detach/list
(--porcelain)/kill/history/wait/get/set/unset/clear/version/help.
Verified via tests/attach_test.py (pty-driven, 8 checks): detach key
ctrl-\, restore-on-reattach, two-client mirroring, background
advance, exit-status through `wait`.

Runtime shape: Daemon.pollRound (fd→Event) + pump (Effect→syscall,
follow-up events re-enter the machine so the roster stays true);
per-conn outbufs capped 4 MiB (runtime §Bound half: slow client =
disconnected, never growth). Client polls at 200ms and diffs
winsizeGet for resize (no signal machinery at all).

Bugs found live:
- pollRound iterated rt.conns AFTER accepts appended to it → revs
  index misalignment → daemon panic "index out of bounds". Fix:
  snapshot `polled` before poll; conns joined mid-round wait for the
  next round. LESSON: any poll loop must freeze its fd set.
- one-shot verbs that expect no reply (send/kill) must not drainReplies
  — added Client.sendOnly; detachAll now replies done.
- python pty.fork() gives 0x0 winsize → clamps to 1x1 grid — set
  TIOCSWINSZ in test harnesses (a real terminal always has a size).

Gotchas: Int64.toNat is toNatClampNeg in 4.32; `(a, b : T)` tuple
ascription must be ((a, b) : T); pkill -f 'lzmx' matches the CALLING
shell's own cmdline — use pkill -x lzmx.

Step-7 seam ready: Cli.Hooks {save, drop, load}; daemon calls
save/drop on checkpoint effects; connectUpsert calls load for
resume-cwd; __daemon passes restoreVt into serve.


## Step 7 notes — 2026-06-01

Settled: checkpoint = magic "LZMX"+v1, LEB128 Nats (UNCONDITIONAL
roundtrip — no fits-in-u32 caveats anywhere), full Vt minus parser
state (Vt.quiesce; a checkpoint loses at most one partial escape
sequence), ring geometry verbatim. Atomic write (tmp+rename); corrupt/
torn/foreign file → load = none → fresh start (§Restore totality is
by construction: R α = List UInt8 → Option, structural recursion).
Save points: 60s-while-dirty tick + last-attached-client detach.
Clean child exit DROPS the checkpoint; SIGKILL keeps it.

Proved: rt_* combinator ladder → load_save (exact modulo quiesce) +
load_save_exact. §Detach restated: detach's only permitted effect is
checkpoint. Fixed en route: marks-cap 8 in Vt.print (unbounded
combining-mark growth — a §Bound hole found by checkpoint design
review).

Verified live (tests/resume_test.py, 7 checks): detach-checkpoint,
SIGKILL survival, restore of screen+labels+cwd on reattach, clean-exit
drop, corrupt-checkpoint tolerance.

New recipes:
- do-notation Option chains reduce with `simp only
  [Option.bind_eq_bind, Option.bind_some]` + RT-lemmas as simp args —
  but ONLY if RT is an `abbrev` (a `def` Prop wrapper makes hypotheses
  opaque to simp).
- UInt8 literal toNat needs `show (128:UInt8).toNat = 128 from rfl` in
  simp sets (toNat_ofNat' covers ofNat-applications only).
- set_option goes BEFORE the doc comment.
- `clear` UInt-typed hypotheses before omega when they drag opaque
  atoms in.
- Test-harness lesson: `list` shows the SHELL pid; the daemon is
  `pgrep -f '__daemon <name>'` + /proc environ filter for isolation.
- My python -c inline edits fail silently on quote/escape collisions —
  ALWAYS verify with grep after, or use str_replace on files.


## Step 8 + abduco review notes — 2026-06-01

Step 8 done: pure fzf-shaped picker (Core/Tui: step + render, one
mode, Dracula/status-top per the user's configs) + terminal shell
(Runtime/Tui). Attach EXECS the plain client — TUI never sits in the
byte path. §Bound(tui) proved (sel clamped into matches, query ≤ 64).
8/8 pty-driven checks (tests/tui_test.py) incl. type-to-create and
C-x C-x confirm-kill.

PLAN.md updated by user: added abduco reference ("but unmaintained").
Reviewed abduco README; borrowed 3 cheap wins, all tested:
1. `lzmx watch <name>` — read-only attach (observer attaches 0×0,
   input dropped daemon-side too — theorem onMsg_input_readonly).
2. Newest-real-attacher owns the pty size (Session.sizeOwner);
   observers and older mirrors can't fight the active user's size.
3. `clients` count in info (abduco's `*` marker, as data for list/TUI).
Rejected: keep-corpse-for-exit-status (conflicts attach-is-upsert;
our `wait` + exited-frames cover it), SIGUSR1 socket recreation
(checkpoint+resume already covers daemon-loss better), configurable
detach key beyond the env kill-switch (PLAN: no customization).
Deliberate stale-size-on-owner-detach: §Detach purity (detach's only
effect is checkpoint) outranks perfect mirror re-fit — documented.

Step 9 (remote over ssh) next: Core/Remote parser + TUI wiring
(hostLabel/Host.remote already in place), then Step 10 verify.


## Steps 9 + 10 notes — 2026-06-01 (spec closed)

Step 9: Core/Remote parses `list --porcelain` from other machines.
Threat-model treated as hostile-by-default: §Name carries (proved) so
a remote name can't build a path, and display fields are `scrub`bed of
control bytes (proved) so a remote can't inject ANSI into our frame.
Unreachable host → [] (BatchMode + ConnectTimeout 3), never blocks the
picker. Attach = `ssh -t host lzmx attach name`, exec'd; nothing is
tunnelled. Verified with a fake `ssh` on PATH (tests/remote_test.py,
8/8) which is also how the argv is pinned.

Step 10: tests/e2e.sh is the whole-deliverable gate — clean rebuild,
warning-free, no sorry/partial/IO in the core, extern-only-in-Posix,
one C file, then all four live suites. Green. README + THEOREMS "what
these do not settle" written; spec moved to specs/archive with a
completion record and the scope-conditioned gaps.

Test-harness lesson: my sanitizer assertion was wrong, not the code —
`sanitize "../../etc/passwd"` = `_._.._etc_passwd` (only a LEADING dot
is rewritten; interior dots are legal and harmless with no `/` left).
Check what the code actually returns before "fixing" it.

State: PLAN.md delivered. Anything further (copy-mode, panes, config)
opens a NEW spec — the archived one is closed.


## Concurrency review — 2026-06-01 (answering "any theorems for concurrency?")

Audit result: the honest answer was "not labelled as such" — so §Isolate
was added and the gaps documented in THEOREMS.md § Concurrency.

Measured, not assumed:
- No data races possible at all: no threads / IO.Ref / Task anywhere
  (grepped), all signal() calls are SIG_IGN|SIG_DFL, client polls
  winsize instead of trapping SIGWINCH. Concurrency = interleaving only.
- §Chunk (per-connection) + §Isolate (cross-client) + §Restore
  (tmp+rename & total load) are the three that carry it.
- NEW §Isolate: step (.bytes id) leaves every other client's record —
  decoder included — bit-identical. Break-verified: making setClient
  share one decoder across clients broke setClient_other AND
  decOk_setClient. Reverted.

Two suspicions investigated; one was wrong, which is worth recording:
- WRONG: "a slow daemon gets its socket unlinked by a concurrent list."
  It does not — the unlink is gated on connect() failing, and a unix
  connect completes from the listener's backlog without the daemon
  being scheduled. Probed with SIGSTOP + list: socket intact, session
  reachable after CONT. (Real but cosmetic finding: a silent daemon
  yields an empty-field row, so `list` prints a blank line. Unfixed,
  noted.)
- REAL: session-identity race in Daemon.serve (probe → unlink-stale →
  bind). With a stale socket + two concurrent starts, daemon B can
  unlink A's live socket; A survives holding an unreachable shell.
  Six-way concurrent creation with no stale socket is clean (1 daemon,
  losers die on EADDRINUSE before spawnPty) — measured. Fix shape:
  mkdir-lock (atomic, no new C — IO.FS.createDir throws on EEXIST)
  around probe→unlink→bind + staleness steal. NOT applied: it changes
  startup semantics and needs a staleness-timeout decision from the
  user; also the backlog-full case would make `list` hang rather than
  report, which the same lock work should address.


## Robustness pass — 2026-06-01 (§Row + name-ownership lock)

**§Row (new theorem).** `Core/Tui.rowOfInfo` now builds a list row from
the socket filename + the info reply, and the *name is a function of
the filename alone*. Fixes the blank-row bug (a daemon too busy to
answer within the 2s window listed as an empty line) and closes an
identity hole: a reply can no longer rename/blank a row, which matters
because that row set is also the porcelain remotes parse. Display
fields reuse `Remote.scrub`. Break-verified: taking the name from the
reply broke 4 theorems. `list` also renders `(busy)` instead of `pid`
with empty fields.

**Name-ownership lock.** `Daemon.serve` takes `flock(<name>.lock)`
before the probe→unlink→bind sequence and holds it for process life;
losing the lock = exit (the spawning client polls and finds the winner).

Why flock and not the mkdir lock I first proposed: `mkdir(2)` and
`open(O_CREAT|O_EXCL)` ARE atomic create-if-absent, which is why
they're classic locks (git's index.lock), but they have no automatic
release — a SIGKILLed holder leaves a lock nobody can clear, which is
exactly why such designs need a staleness timeout, and every timeout
value is wrong (short → steals live locks; long → sessions unstartable
after a reboot). flock is kernel-released on death/close, so the
timeout question disappears. Never unlink a lock file: a newcomer would
lock a fresh inode while the owner holds the old one.

Rejected alternatives: abstract sockets (Linux-only, loses fs
permissions), bind-tmp-then-`link()` (works, but needs a new syscall
plus a retry loop for no gain over flock), readers taking the lock to
test liveness (a `list` could momentarily block a starting daemon).

New suite `tests/robust_test.py` (10 checks, wired into e2e as step 8):
SIGSTOP'd daemon lists by name and keeps its socket; stale socket + 8
concurrent starts → exactly 1 daemon, 1 shell, reachable; name
re-claimable right after the owner exits (proves no stale lock).

Gotcha: `Row` needed `DecidableEq` derived for whole-record test
comparisons. And my first two assertions in the new suite were wrong,
not the code (lock files persist by design; `(busy)` is the new
rendering) — check what the code returns before "fixing" it.


## NFS audit + §Claim — 2026-06-01

Q: "anything else unreliable over NFS?" Audited every fs call
(readDir ×2, removeFile ×5, rename, read/writeBinFile, createDirAll,
chmod, bind, flock, readlink). Three assume local storage:

1. socket dir (only via LZMX_DIR): unix sockets are host-local; bind
   often fails on NFS, and on a SHARED dir other hosts' sockets appear
   in list, answer nothing locally, and our stale-cleanup would delete
   a live remote socket. Defaults are tmpfs//tmp → unaffected.
   LZMX_DIR on a network mount = unsupported (documented).
2. flock: NFS-unreliable → §Claim's Exclusive fails there. Moot,
   since (1) already breaks that setup.
3. state dir: DEFAULT sits under $HOME, which is NFS on many corp
   boxes — the one hazard that arrives by accident. Two hosts sharing
   $HOME + a session named "work" → clobbered checkpoints.
   FIXED: default state dir namespaced by hostname (also the right
   semantics — replaying host B's screen on host A describes a working
   tree that isn't there). Explicit LZMX_DIR stays verbatim, which is
   what keeps the test suites' single-dir layout working.
   Measured on this box: $HOME is ext4 and XDG_RUNTIME_DIR is tmpfs, so
   there was no live exposure here.
Unaffected: readDir staleness (cosmetic), single-writer log. Noted, not
fixed: 0700 on the socket dir is only as strong as the fs enforcing it
(NFSv3 auth_sys ≈ not at all).

Q: "does advisory-ness give us a theorem?" Yes — a CONDITIONAL one, and
that shape is the point. Theorems/Claim.lean models the claim sequence
as a trace of (agent, action):
  * Exclusive (hypothesis) = the kernel grants ≤1 flock holder — the
    single line we trust, with its three side conditions spelled out
    (hold for life, never unlink the lock file, local fs).
  * Guarded (proved for our sequence) = only the holder unlinks/binds.
  * at_most_one_owner / at_most_one_unlinker / owner_holds_lock follow.
Break-verified: describing the pre-fix sequence (bind without lock)
breaks all three. Honest caveat recorded in the file: it is a model of
serve, not an extraction; correspondence is by inspection + pinned by
robust_test.py. This is the general recipe for OS primitives in this
codebase — axiomatize the contract as a hypothesis, prove the protocol
against it, so what is trusted is one reviewable line.


## Checkpoint cost + RLE — 2026-06-01

Q: "do we have shutdown-resume, and doesn't it need periodic disk
writes?" Yes (step 7) and yes. But MEASURED the cost first and it was
bad: blank 80x24 = 22.7 KiB, +5000 lines = 4.7 MiB, wide 200x50 +5000
= 11.7 MiB. Cause: every cell stored verbatim w/ full pen (~12 B),
so a 25-char line paid for 80 cells — ~935/960 B was trailing blanks.

Fix: run-length encode the cell stream (wRLE/rRLE + runs/expand in
Core/Checkpoint). Exact fidelity, no dependency, and the §Restore
proof composes — added rt_rle resting on expand_runs (unRle∘rle=id),
rt_row now uses rt_rle rt_cell. Re-measured: 22.7K→1.7K (13x),
11.7M→2.0M (5.8x); "wide" == "deep" now since extra cols are all
one blank run. Remaining ~400 B/line is real text + per-cell pen.
Break-verified: expand off-by-one broke expand_runs → load_save.

Cadence (confirmed, was already right): dirty flag set on ptyOut,
cleared on checkpoint; 60s tick + last-detach; idle sessions never
re-write; clean exit drops the ckpt. Write is synchronous in the pump
and atomic (tmp+rename) — a big write briefly stalls the poll loop,
another reason the RLE shrink matters on slow/NFS state dirs.

Tests: Tests/Checkpoint.lean (6) pins runs/expand, that a blank row
is <20 B AND round-trips, and end-to-end feed→save→load screen match.
resume_test.py still green (format changed, behavior identical).

Possible future win if ever needed (NOT done, YAGNI): identical-row
RLE for many blank rows, or gzip. Per-cell RLE already gets the 6-13x;
row-level would add maybe 2x on mostly-blank screens for real proof
cost. Left as a one-line note.


## Real second-machine test on gpu2/gpu3 — 2026-06-01

Goal: validate the remote-over-ssh path against a REAL machine (only
fake-ssh-shim tested before). Did it on gpu2 + gpu3 (AL2023, glibc
2.34). All live checks green: TUI lists remote sessions over real
`ssh HOST lzmx list --porcelain`, previews via `ssh HOST lzmx history`,
attach execs `ssh -t HOST lzmx attach NAME` into the real remote shell,
detach leaves it alive; and LZMX_REMOTES=gpu2,gpu3 aggregates BOTH real
hosts into one local TUI (multi-host fan-out — never exercised by the
fake test). New test: tests/remote_live_test.py (needs a reachable
remote; NOT in e2e.sh, which stays hermetic).

REAL PORTABILITY BUG FOUND + FIXED (the main outcome):
- lzmx wouldn't build on gpu2. Chain of wrong theories, each killed by
  looking rather than guessing:
  1. "glibc 2.34 merged libutil into libc, drop -lutil" — WRONG. The
     Lean toolchain links with `--sysroot` into its OWN bundled glibc
     (lib/glibc), not the host's. The rsp proves it.
  2. The bundled glibc has NO libutil and its libc.so lacks forkpty
     (nm count 0). Lean expects the SYSTEM to supply forkpty. That works
     on my box only because ./lake uses Homebrew clang, which also
     searches /usr/lib64 (glibc 2.26 has libutil.so + forkpty). Under
     the toolchain's own clang+sysroot on gpu2, forkpty is simply
     unreachable — bundled libc lacks it, no bundled libutil, system
     libs sysrooted away.
  - FIX: rewrote zmx_spawn_pty from forkpty(3) (libutil) to the
    posix_openpt/grantpt/unlockpt/ptsname/setsid/TIOCSCTTY sequence —
    all plain libc, present in the bundled glibc. Removes the libutil
    dependency ENTIRELY: no -lutil, no lakefile conditional, no wrapper
    env var. Builds clean on glibc 2.26 (./lake) AND 2.34 (plain lake).
    ldd on the gpu2 binary shows no libutil. Local ztest + full e2e
    still green (the delicate pty/ctty path is covered by the
    interactive suites).
  - Dead ends I tried first and reverted: conditional -lutil via
    get_config? (a top-level `def` can't see -K config), then via
    run_io+env (worked mechanically but the whole approach is wrong on
    modern glibc since forkpty isn't in libutil there anyway).

OPERATIONAL findings (compute-gpu-jobs domain):
- ssh-agent wedged MID-SESSION (was flaky from the start: `ssh-add -l`
  → "agent refused operation"). Symptom: `ssh gpu2 true` hangs to
  timeout while the box is fine. Fix: `-o IdentityAgent=none` (skill's
  documented pitfall) or unset SSH_AUTH_SOCK. lzmx's own `ssh` children
  need the agent env removed too, else fetchRemote hangs — the live
  test pops SSH_AUTH_SOCK from the child env.
- rsync `c/shim.c HOST:dir/` FLATTENS to dir/shim.c (not dir/c/shim.c).
  Cost me a rebuild-on-stale round. Use explicit dest `dir/c/shim.c`
  or `-R`. Lake then also cached the stale .o — had to rm the shim
  artifacts to force recompile.
- AL2023 build is actually CLEANER than my box: glibc 2.34 runs the
  toolchain's bundled clang, so plain `lake build` works with none of
  this box's Homebrew-clang / LEAN_AR workarounds.
- Setup on a fresh box: elan install (--default-toolchain none) + rsync
  source + `lake build lzmx` (first run fetches toolchain) + symlink
  binary into ~/.local/bin (on the non-interactive ssh PATH so bare
  `lzmx` resolves for `ssh HOST lzmx ...`).



## §Preview added (the one theorem the gpu test earned) — 2026-06-01

Reviewed each gpu-test case for "worth a theorem?" — mostly NO, and
said so rather than manufacturing them:
- forkpty→posix_openpt: C shim, the IMPURE surface by design. Not
  Lean-provable; its contract is checked by ztest (OS-as-oracle tier).
  Nothing to prove; nothing would have "caught" a link/toolchain bug —
  the durable guard for that class is a CI build on a modern-glibc box,
  not a proof.
- ssh-agent wedge / IdentityAgent=none: operational, local env. Runbook.
- rsync flatten: my tooling slip. Not a property of lzmx.
YES, one: multi-host aggregation exercised a code path (async preview
replies from N hosts into one pane, same NAME possibly on several) that
NOTHING pinned. Added §Preview (Theorems/Tui.lean):
  step_previewUpdated_reject/accept + step_preview_no_cross_host —
  a previewUpdated (name,host) mutates the pane iff the selected row
  matches BOTH fields. It's §Row's "identity is (name,host)" applied to
  async previews. Break-verified: dropping the host check breaks all
  three (no_cross_host becomes false — gpu3's scrollback would paint
  gpu2's row). Concrete test in Tests/Tui.lean (same name on gpu2+gpu3).
Now 14 § sections. The pre-existing stale-preview test only covered the
name dimension; multi-host added the host dimension, which is exactly
what the real two-box test walked through.



## Shrank the shim via Lean core primitives — 2026-06-01

Followed the "shrink the trust boundary" plan from the C-vs-Rust
discussion. Probed 4.32 core (grepped the toolchain src, not guessed)
and found exact equivalents for 3 of the 30 wrappers:
  zmx_monotonic_ms → IO.monoMsNow
  zmx_getpid       → IO.Process.getPID
  zmx_chmod        → IO.Prim.setAccessRights (the lean_chmod extern)
Reimplemented Posix.monotonicMs/getpid/chmod as one-line Lean defs over
core; call sites unchanged (same names/sigs). Deleted the 3 C funcs.
Shim 30→27 wrappers, 581→564 lines.

Kept (no core equivalent, confirmed by grep): sockets+poll (core has
neither), pty/termios, fork/exec/waitpid/kill/alive, flock, spawn
detached, getuid, isatty, gethostname, getcwdOf(/proc), realtimeS
(core has monoMsNow but NO wall clock), init/ignoreSighup (signals),
raw fd read/write/close/setNonblock.

All 3 replaced funcs are on live-covered paths (chmod=ensureDir,
getpid=daemon meta→list, monotonicMs=checkpoint cadence→resume), so
ztest + e2e (5 suites) exercise them. Green. No portability risk: the
core prims are toolchain-provided, identical on my box and gpu2/3.

Deliberately did NOT chase marginal ones (writeAll→stdout: also used on
socket fds; spawnDetached→IO.Process.spawn: no setsid/daemonize). The
remaining 27 are genuine syscalls Lean core doesn't expose — exactly
the surface I argued Rust wouldn't improve either.



## LZMX_REMOTES env → -r/--remote flag + dup-errors — 2026-06-01

User was right on both counts:
1. Remotes is per-invocation input = a CLI option, not an env var
   (env-for-per-invocation is the anti-pattern: invisible, inherited by
   children). Replaced $LZMX_REMOTES with `lzmx -r|--remote h1,h2`.
   Persistent set stays in ~/.config/lzmx/remotes. Flag OVERRIDES the
   file (not union) — fixes the earlier env-vs-file precedence
   inconsistency the user also caught; now uniform with LZMX_DIR.
2. Duplicates are a hard error, not silent dedup/union. Especially
   right for a TUI: a warning would be swallowed by the alt-screen, so
   the check runs BEFORE enterTerm and refuses to start, naming the
   host. Also moved the resolve+check ABOVE the isatty check so a bad
   argv reports itself even when piped (argv validation precedes env
   checks).

Made the validation pure: Core.Remote.checkHosts : List String →
Except String (List String) (Nodup → .ok, else .error naming the dup).
Theorem checkHosts_ok_nodup: a validated list is duplicate-free, so the
query loop provably never double-queries a host. (This is the
enforcement the user asked about, at the pure layer — cf. the shim
ratchet, which is the source-tree analog that can't be a theorem.)

Plumbing: Tui.main takes Option (List String); resolveRemotes replaces
remoteHosts; remotes threaded through gatherRows/runEffects/loop. Cli
tui thunk became `Option (List String) → IO UInt32`. Dropped the env
read entirely.

Verified: gate green (5 suites); fake-remote test (now -r driven) incl.
new "duplicate -r host errors loudly"; rebuilt gpu2+gpu3 and re-ran the
live single-host + multi-host (-r gpu2,gpu3) tests over real ssh — all
green. Nested-comment gotcha: `-r/--remote` in a doc comment contains
`/-` which opens a nested block comment (Lean nests) → "unterminated
comment"; reworded to `--remote` (`-r`).



## Empty-TUI UX fix — 2026-06-01

User ran bare `lzmx` (no sessions), saw "a strange vertical bar", typed
`ls`, it flashed, then `exit` → "session 'ls' ended". NOT a bug — the
software did exactly as told, but the UX led them in:
- 0 sessions → both panes empty → only the list/preview divider `│`
  rendered = the "vertical bar down the middle."
- bare `lzmx` is the MANAGER (picker), not a shell; typed chars go into
  the query box (which doubles as the new-session name). They treated
  it as a shell prompt.
- Enter on no-match created session "ls" + exec'd attach → the "flash"
  was the picker→shell transition. `exit` ended it.

Root cause = my design: empty state was a cryptic bar with no guidance,
and the type=filter=name model wasn't conveyed. Fix (Core.Tui.render,
pure): when st.rows.isEmpty, draw a guidance block ("No sessions yet.
Type a name above and press Enter… or run lzmx attach <name>. Esc
quits.") instead of the divider grid; query line shows a muted
placeholder while empty so it doesn't read like a shell prompt; also a
"(no match — Enter creates 'X')" hint when a query hides all rows.
Regression check added to tui_test.py (empty TUI must say "No sessions
yet" + "lzmx attach"). The "flash" itself is inherent (attach exec
replaces the full-screen picker) — not a defect.

Lasting lesson for the README quick-start I keep deferring: lead with
"lzmx attach <name> gives you a shell; bare lzmx is the manager" — the
model is the thing users miss.



## Deleted the TUI → CLI overview — 2026-08-12

User ran bare `lzmx`, hit "a strange vertical bar in the middle", typed
`ls` (it flashed), `exit` → "session 'ls' ended". Same report twice.
Root cause was the picker itself, not a bug: bare `lzmx` opened the
full-screen fzf-shaped manager; on 0 sessions only the list/preview
divider `│` drew (the "vertical bar"), typed chars went into the
query=name box, Enter created a session named `ls` and exec'd attach
(the "flash"). We'd already softened the empty state once (guidance
block), but the real fix the user asked for is: no TUI at all. zmx
itself has no TUI — it uses fzf. The poll/2s-refresh/re-ssh-every-cycle
was the over-built, flashing part.

DELETED: Zmx/Core/Tui.lean, Zmx/Runtime/Tui.lean, Theorems/Tui.lean,
Tests/Tui.lean, tests/tui_test.py (−952 lines). Bare `lzmx` and
`lzmx ls` now print a plain overview and EXIT (Cli.overview →
cmdList). Net −889 lines.

Verb changes (Cli.lean):
- bare `lzmx` == `lzmx ls`: one-shot listing, pipeable, never blocks.
- `attach` with no name defaults to `main` (`defaultName`) — "just give
  me my session" without inventing one. `run`/`send` still require an
  explicit name (first arg is ambiguous there).
- `ls -r [hosts]` lists remotes too (flag arg else ~/.config/lzmx/
  remotes); plain `ls` stays local (common case ssh-free).
- NEW `attach name@host` → `exec ssh -t host lzmx attach name`. This is
  the remote-attach that the picker's Enter-action used to do; now it
  also lets the fzf recipe feed a listed row (`name@host`) straight to
  `attach`. GOTCHA: `local` is a reserved token in Lean 4 — the match
  binder had to be `sess`, not `local` (first build died on it).

§Row re-homed (was Theorems/Tui.lean, which is gone). The property —
a listed session's identity is its socket filename, never the `info`
reply (matters because that row set is the porcelain a remote `-r`
parses) — was enforced inline in cmdList. Extracted to pure
Core.Listing.rowFields + proved in Theorems/Listing.lean:
  rowFields_name (lookup "name" = sanitize socketName for ANY info) and
  rowFields_reply_excluded (the reply's name is physically dropped, not
  shadowed). cmdList now calls rowFields. Break-verified: making
  rowFields take the name from the reply → rowFields_name unsolved.
§Bound(tui) and §Preview DELETED from THEOREMS.md (picker-only; they
died with the TUI). Now 12 § sections. THEOREMS.md concurrency section
still cites §Row correctly (identity-is-socket-name).

Dead code removed: Render.previewLines (picker preview feed, no
consumer left). Render.history stays (`lzmx history`). Cosmetic "TUI"
comments in Vt/Render/Remote/Tests/AGENTS reworded to "overview/
listing".

Tests:
- NEW tests/overview_test.py (e2e step 6, replaces tui_test.py):
  bare/`ls` print the list and EXIT (stdin=DEVNULL + timeout=15 → a
  picker that blocked on stdin trips the timeout). Break-verified:
  `IO.sleep 16000` in overview → all 5 assertions FAIL on timeout.
- REWROTE tests/remote_test.py: fake ssh now keys off `ls` (listRemote
  runs `lzmx ls --porcelain`, not `list`); overview folds in remote
  rows via captured stdout (no pty); `attach remote-work@dev-a` in a
  pty execs `ssh -t dev-a lzmx attach remote-work` (argv pinned).
- REWROTE tests/remote_live_test.py (not in gate) to the CLI shape:
  `-r HOST` listing + `attach alpha@HOST` into the real shell + survive
  detach. Dropped the preview/filter checks (no preview in CLI). NOT
  re-run on gpu2/3 this pass (needs remote redeploy + alpha/beta setup);
  the fake-ssh test pins the same argv.
- e2e.sh step 6 relabeled; still "5 live suites" (attach, resume,
  overview, remote, robust). Full gate GREEN.

Lasting note: the model users miss is "attach = a shell; bare lzmx =
a listing." README now leads with exactly that + an OPTIONAL fish fzf
function (`lzmx ls -r | fzf | ... | lzmx attach`) — lzmx never calls
fzf itself.



## Review pass on the TUI-deletion change — 2026-08-12

Ran the semantic reviewer on the staged diff before committing (large
change: subsystem deletion + a re-homed security theorem). It cleared
the risky bits (no verb dropped, §Row non-vacuous, no dangling picker
refs) and caught one real bug + one asymmetry in the NEW code:

1. (Medium, real) `attach name@host` couldn't round-trip a `user@host`
   remote. Rows are `{rname}@{host}`; a host like `deploy@prod` made the
   row `rname@deploy@prod`, and `splitOn "@"` → 3 parts missed the
   2-part remote arm → SILENT local attach on a bogus name. The fzf
   recipe feeds rows verbatim, so this broke a common ssh config.
   NOTE: the reviewer suggested split-on-LAST — that's WRONG here
   (`rname@deploy@prod` last-split → sess=`rname@deploy`). The row is
   name-then-host, so split on the FIRST `@`: sess before, host =
   everything after (host may itself be `user@host`). Verified by
   reasoning + the new test (`-t -- me@dev-a lzmx attach remote-work`).
   Correct only if names can't contain `@` → see the sanitize change.
2. (Low-Med) remote-attach `exec` omitted the `--` host separator that
   `listRemote` uses; a `-`-leading host would be read as an ssh option
   (e.g. -oProxyCommand). Added `ssh -t -- host ...`. Host is
   operator/trusted so defense-in-depth, but the asymmetry was real.

Fixes:
- Reserved `@`: dropped it from Name.okChar (session names can no longer
  contain `@`), so any `@` in an attach arg unambiguously means remote.
  This makes the first-@ split correct even for remote-parsed names.
  The §Name proofs were UNAFFECTED (they only `decide`/`simp` about
  `/`, NUL, `_` — never `@`; shrinking okChar only strengthens Valid).
  ADDED theorem sanitize_no_at (+okChar_no_at): no sanitized name
  contains `@`. It's SELF-break-verifying — it only compiles because
  okChar excludes `@`; re-adding `@` → okChar_no_at unsolved (confirmed,
  reverted). THEOREMS.md §Name row notes the reservation.
- cmdAttach: split on first `@`; empty sess or host → loud
  `malformed remote target` error (was a silent odd local session);
  `ssh -t -- host lzmx attach sess`.
- README fzf recipe hardened: pull names from `--porcelain`
  (`awk -F '\t' '$1=="name"{print $2}' | fzf`) so an empty list offers
  nothing to pick — kills the "no sessions" line being selectable (the
  same bug class this whole change removed).
- Tests: attach_test +bare-`attach`→"main"; remote_test +user@host
  round-trip (first-@) + trailing-@ loud error. Existing argv assertion
  already tolerated the `--`. Full e2e green.

Didn't commit the review doc under semantic-review/ (transient
artifact, not a deliverable). Minor items left as-is by design: the
isatty check stays BEFORE the @-parse (both local and remote attach
need a tty), so malformed-@ is only reported interactively.



## Bigger theorems: §Stream, trace lift, §Replay opened — 2026-08-12

User asked "is there a bigger theorem that would imply a bunch of ours?"
Answer recorded in specs/bigger-theorems.md: across trust boundaries NO
(that factoring is the design; a whole-system refinement is seL4-scale
and its hypotheses would swallow the gain), and cross-client
commutativity is FALSE (sizeOwner depends on attach order; pty input
interleaves) — but three composed statements were worth having. All
three landed; the third is opened + pinned, proofs staged.

**Step 1 — §Stream (Theorems/Wire.lean).** The composed §Frame∘§Chunk:
ANY well-formed msg sequence, encoded, re-chunked ARBITRARILY →
feedAll returns exactly that sequence, clean decoder. New Core def
`Decoder.feedAll` (spec of the runtime read loop; structural recursion,
projection-shaped, so inductions step through it). Proof chain:
`takeFrames_leftover_stable` (a leftover re-parses to itself — the
missing quiescence fact) → `feedAll_flatten` (chunked = one-shot, for
quiescent-buffer decoders; errored case rides feed_errored) →
`decode_encode_chunked`. decode_encode/decode_encode_stream are now
corollaries (one message / one chunk). Break-verified: feedAll dropping
r.2 (earlier chunks' msgs) broke the theorem AND the new 7-byte-chunk
test in Tests/Wire.lean.
  Proof gotchas: `[].flatten` needs List.flatten_nil before append_nil
fires; `{} : Decoder` field access reduces definitionally so plain
`simp` closes the fresh-quiescence side goal; the `show` +
`rw [List.flatten_cons, Decoder.feed_append, ih]` pattern closes cons.

**Step 2 — trace lift (Theorems/Session.lean).** New Core def
`run : State → List Event → State × List Effect` (the poll loop's fold,
same projection shape). Theorems: `run_eq_foldl` (run IS the
effect-accumulating foldl — pins state threading + effect order; proved
via a ∀-fx accumulator generalization), `WF := Bounded ∧ Good`,
`step_wf`, `run_wf` (no trace of any length breaks caps or screen
invariant), `run_bytes_isolates` (a client's whole chunked stream
leaves other records bit-identical). Tests/Session.run now DELEGATES to
Core run, so all 16 scenario tests pin it concretely.
  Break-verified: run not threading state (`run s evs` instead of
`run r.1 evs`) broke run_eq_foldl (both `show` steps) + 6 scenario
tests. Honest note (recorded in spec): run_wf alone cannot catch
threading bugs — ANY composition of WF-preserving steps preserves WF —
which is exactly why run_eq_foldl exists.

**Step 3a — §Replay opened (Tests/Render.lean, spec step 3).** Target:
`(Vt.init v.cols v.rows).feed (restore v) ≃ v`. Emitter/parser
alignment review found SEVEN real infidelities in Render.restore; all
pinned by fixtures that FAILED pre-fix (build log kept: the 7 failing
native_decides), then fixed in Render:
  1. marks on a wide char live on its width-0 continuation cell;
     rowAnsi skipped width-0 entirely → marks lost. Fix: emit marks of
     shadow cells (re-attach lands on the shadow again — incl. the
     wrap-pending margin case, where print's `pending` branch targets
     cursor.x itself).
  2. charset (g0Line/g1Line/shiftOut) never replayed → ESC (0 / )0 / SO
     after repaint (stored glyphs are pre-translated; box chars don't
     re-translate since decLine only maps ASCII).
  3. saved (DECSC) never replayed → park penSgr+CUP+ESC 7. Must be
     AFTER the alt switch (enterAlt(true) clobbers saved) and BEFORE
     DECOM (address is absolute).
  4. modes.origin + modes.insert missing from modesAnsi (insert
     non-private CSI 4h). Emitted after repaint (IRM would shift
     repaint cells), before final CUP (DECOM homes).
  5. final CUP must be region-relative under DECOM.
  6. custom tab stops → CSI 3g + CHA+ESC H per stop, only when ≠
     defaultTabs.
  7. alt-screen stash: paint-then-switch stashed whatever cursor/pen
     the main repaint ended with. Fix: park stash cursor/pen before
     ?1049h.
  The ≃ (`replayEq`) compares grid/cursor-pos/pen/region/modes/title/
tabs/charset/saved/alt-stash + replay-ends-ground; EXCLUDES sb (restore
repaints the screen, not history), bell, and every wrap-pending flag
(unrepresentable via CUP; stash/saved pending carved out for the same
reason). 14 fixtures incl. kitchen sink. Proof campaign staged in the
spec: 3b parser-ground lemmas (no digit semantics needed), 3c value
fidelity (needs a digit-roundtrip; likely a bespoke digit emitter in
Render for provability), 3d grid induction (wide/marks/wrap; known
edge: resize can strand a wide base in the last column — that
well-formedness hypothesis belongs to 3d).
  Live impact: restore byte stream changed → attach_test + resume_test
re-run green (real terminals tolerate the additions; they're standard
sequences).

**Steering extras (same session):** listRemote gained
ServerAliveInterval=2/CountMax=2 — ConnectTimeout only bounds the
connect phase, so a HALF-UP host (accepts TCP mid-reboot, then wedges)
could previously hang `ls -r` indefinitely; now bounded ~4-6s. The
remote-attach exec gained ServerAliveInterval=5/CountMax=3: a VPN/wifi
drop otherwise leaves that ssh hung until a manual `Enter ~ .`;
aggressive detection is the right default HERE (unlike bare ssh)
because dying is free — the session detaches and survives. The ghost
half of that story is already covered: a dead client's outbuf hits the
4 MiB cap and is disconnected (runtime §Bound half); an idle ghost is
sshd's to reap (server-side ClientAlive*, outside lzmx). Fake ssh
strips `-o` pairs generically; the two argv-pinning regexes in
remote_test.py updated to tolerate them. README: kitty
`lzo` recipe (one tab per remote session incl. resumable = whole
workspace back after either machine reboots; kitten @ launch, remote
control required) + Notes bullets on unreachable-host and link-drop
behavior. THEOREMS.md: §Stream row, §Replay row (open, precedent:
"listed before its first proof"), trace-lift paragraph under
Reading-a-row.



## Reversal: no transport policy in the attach exec — 2026-08-12

User pushed back on baking ServerAlive into `attach name@host`'s ssh
argv ("ssh hanging sounds like an SSH problem, not an lzmx problem") —
and the layering argument beats yesterday's convenience argument:
command-line `-o` silently OVERRIDES the user's ~/.ssh/config (ssh
takes the first obtained value; CLI wins), so lzmx was imposing
interactive transport policy in a place the user can't undo. Reverted
to plain `ssh -t -- host lzmx attach sess`; the comment now documents
why NOT. README gained a "Flaky links" section: the ssh-config snippet
(set once, fixes the `Enter ~ .` dance for ALL their ssh use), an
autossh-style `lza` fish recipe, and the mosh composition
(`mosh host -- lzmx attach work`).

KEPT: keepalives on `ls -r`'s ssh (2×2). Different justification — that
ssh is a non-interactive QUERY the tool itself initiates while building
a listing; a listing must terminate. Policy on our own batch query is
operational necessity; policy on the user's interactive session is
overreach. The line to hold.

Auto-reconnect (autossh-style) evaluated for the BINARY and rejected,
with a concrete reason worth keeping: ssh's exit contract makes 255
mean "transport error" OR "remote command exited 255" —
indistinguishable. Combined with attach-is-upsert, a baked-in retry
loop would silently respawn a FRESH session when a shell exits 255
(clean exit drops the checkpoint, so the loop re-creates from nothing).
Acceptable blind spot in a 6-line recipe the user can read; not
acceptable hidden in the binary. (mosh solves the problem properly —
own UDP protocol with sequence numbers — which is exactly why "compose
with mosh" beats reimplementing it.)

Coupling audit (the actual question "have we tied lzmx to ssh too
much?"): TWO argv call sites total (listRemote's query; cmdAttach's
exec). Nothing tunnelled, no ssh library, the wire protocol never
crosses a network (unix sockets only), remote = "run the same CLI over
any exec-a-command transport + parse porcelain". The ssh-shaped parts
are the `name@host` syntax and the PATH assumption. Verdict: thin, and
thinner after this reversal.



## recipes/ folder — 2026-08-12

Recipes had accumulated in the README (fzf picker, kitty tabs,
reconnect loop, ssh_config snippet) and it had crept from 59 to ~130
lines. Extracted to `recipes/`, one file per recipe, README back to 83:
lz.fish / lzo.fish / lza.fish / ssh_config + recipes/README.md (install
= `cp` into ~/.config/fish/functions/ — fish autoloads one function per
file, so the file layout IS the install format; all three checked with
`fish -n`). Each file carries its own caveats as comments (lza's ssh
exit-255 blind spot, lzo's allow_remote_control, ssh_config's
override-precedence note), so copying a recipe copies its warnings.

Transport transparency (user asked "can we transparently use ssh or
mosh?"): answered in recipes/README.md. Interactive session layer is
transport-agnostic by construction (unix socket on the host; nothing
tunnelled) — ssh, mosh, anything that execs a remote command with a
tty. Two deliberately ssh-shaped spots in the binary, both zero-cost to
mosh users: `attach name@host` execs ssh (the universal default; a
recipe swaps one line for mosh), and `ls -r` MUST use an
exec-and-capture transport, which mosh is not (screen-sync protocol) —
and mosh bootstraps over ssh anyway, so mosh users always have ssh
reachability. If demand emerges for the name@host shorthand itself
picking mosh, the principled extension is a GIT_SSH-style override —
noted, not built (argv shapes differ; PLAN says no customization).



## Rename: lzmx → linger — 2026-08-12

Naming rounds settled on `linger` (real word = the product's one idea:
sessions linger after you leave; systemd's own term for user processes
surviving logout — `loginctl enable-linger`; collision-checked clean in
CLI space, while `lem` died to the Common Lisp editor + the rems-project
spec language, and the -mux family was rejected for advertising
multiplexing we deliberately don't do). Lean lives in the tagline
("Lean sessions" — prover + doctrine), not the binary name.

Renamed: lake exe target (`lake build linger`), all user-facing strings
(usage/version/error prefixes), env vars LZMX_*→LINGER_* (DIR,
NO_DETACH_KEY, SESSION, and test-only TEST_DIR/REMOTE — hard cutover,
no compat reads), default dirs (/tmp/linger-$UID, $XDG_RUNTIME_DIR/
linger, ~/.local/state/linger/<host>, ~/.config/linger/remotes), the
self-invocation argv (`ssh host linger ls --porcelain`, remote attach
exec), tests (incl. fake-ssh + argv regexes), README (title now
"linger" + tagline), recipes (function/file names lz/lzo/lza KEPT —
user-editable, zero churn), AGENTS.md title.

Deliberately NOT renamed:
- Checkpoint magic bytes "LZMX": frozen on-disk format identifier
  (wire-tag analog); changing it would orphan every checkpoint.
  Comment added at the def.
- `Zmx` module namespace + repo dir/name: internal lineage,
  implementation detail; rename is available as a later cosmetic pass.
- SCRATCHPAD history + specs/archive: append-only records.

Migration notes (small fleet, hard cutover):
- Old-name dirs (/tmp/lzmx-*, ~/.local/state/lzmx/*) are invisible to
  the new binary: live pre-rename sessions stay reachable only via the
  old lzmx binary until they end; old checkpoints don't list. Fleet is
  dev box + gpu2/3 with throwaway sessions — acceptable, told user.
- Compat symlink lzmx→linger installed alongside the real one in
  ~/.local/bin (covers anything still invoking the old name over ssh
  during transition). `__daemon` re-exec uses IO.appPath, so it never
  depended on the name.
- sed gotcha: `\blzmx\b` misses `\r\nlzmx:` inside Lean string
  literals (the preceding backslash-n keeps it a word char in fish's
  quoting of the pattern? — either way 4 literals needed manual
  str_replace). Grep-audit after any bulk rename.



## Naming: CLOSED — 2026-08-12

Final: binary `linger`, repo name unchanged. Post-rename rounds
considered and declined: `leanger` (pun kills sayability; leANGER;
spelling trap at the ssh seam), `lnger`/`lingr`/`lger` (vowel-drops:
save ≤2 chars, lose wordness), `lien` (best lean-pun — homophone of
lean, "a standing claim", maps to §Claim — but aurally collides with
the `lean` prover binary in this very repo's company), `leanto`,
`glean` (Glean-the-company), `pisa`. Lean lives in the tagline ("Lean
sessions"), not the name. Typing cost is an abbr (`abbr lg linger`).
Do not reopen without new information; the discussion cost more than
§Stream.

Cleanup deferred: drop the lzmx→linger compat symlinks on the three
hosts once nothing has invoked `lzmx` for a while.



## §Replay stage 3b — restore leaves the parser in ground — 2026-08-12

**The blocking discovery: String-assembled output is unprovable in
principle.** `"\x1b[".toUTF8.toList = [27, 91]` fails by BOTH `rfl` and
`decide` (kernel gets stuck on the String primitive; probe recorded).
So no theorem could ever see restore's bytes while Render built Strings.
Rewrote Render byte-native (`Bytes := List UInt8`) with named stages:
`escB`/`csiB`/`digits`/`utf8`/`utf8s`/`csiNum`/`csiNum2`/`csiPriv`/
`penSgr`/`cellText`/`rowAnsi`/`joinCRLF`/`gridAnsi`/`modesAnsi`.
`restore`/`history` now return Bytes (call sites in Session dropped
their `.toList`). `rowText` stays String — there its output IS text.
The 14 §Replay fixtures + all Vt fixtures caught nothing = refactor was
behavior-identical. THAT is what the 3a oracle was for; it made a
risky rewrite of the live restore path safe.

Two hypothesis-free emit guards added (both needed for the proofs AND
genuinely defensive): `safeChar` maps C0/DEL to U+FFFD before emitting
(a cell CAN hold a control codepoint — an overlong UTF-8 sequence
decodes to one — and emitting it raw would be re-parsed as a command,
desyncing the replay); `utf8`'s codepoint is `min c.toNat 0x10FFFF`
(the AGENTS.md local-clamp idiom: identity on every real Char, but it
turns each emitted byte's range into an omega fact instead of a
`Char.valid` derivation — `isValidChar` is root-namespace over UInt32
comparisons and was fighting me).

Proved, bottom-up:
1. Byte facts: `digits_range` (every digit byte 0x30..0x39),
   `ofNat_no_ctl`, `utf8_no_ctl`, `utf8s_no_ctl`, `*_no_esc`.
2. NEW pstate layer in Theorems/Vt.lean (~18 lemmas): ps_clearPending/
   carriageReturn/putCell/moveTo/moveRel/setCol/scrollUpIn/scrollDownIn/
   eraseRowSpan/lineFeed/reverseIndex/backspace/tab/printWrap/
   printWideWrap/printShift/printPut/printAdvance/print/acceptChar/ctl/
   abortUtf8/stepGround. This is the same shape of work the step-4 notes
   DOWNGRADED for cols/rows ("~25 lemmas") — turns out it's cheap when
   staged, so the pstate version is now proved.
3. `Ends bs := ∀ v, ground → (v.feed bs).pstate = ground`, closed under
   append/ite/flatten/flatMap + `Ends.text` (no-ESC runs — covers the
   whole grid repaint).
4. **`ends_csi_seq`**: `CSI <params> <final>` → ground, for ANY param
   string of 0x30..0x3F bytes. Instances: ends_csiNum, ends_csiNum2,
   ends_csiPriv. This is the one that matters — cursor addressing, mode
   set/reset, scroll region and the tab ruler are all instances.

Break-verified: dropping the CSI final byte from `csiNum` breaks
`ends_csiNum` (type mismatch) AND 2 fixtures. Reverted.

CODE CHANGE for provability: `Vt.step`'s inline UTF-8-abort `if` became
a named `Vt.abortUtf8` — `split` targets the pstate MATCH, so the
scrutinee had to be rewritable (`ps_abortUtf8`) for the match to reduce.
`Good.step`'s proof needed `unfold Vt.step Vt.abortUtf8` after that.

Scoped out honestly (in spec + THEOREMS): `Ends` covers pstate only
(u8need needs per-op lemmas through csiDispatch and buys far less — a
trailing partial UTF-8 mis-renders ONE glyph, a stuck .csi swallows
everything; replayEq pins it). ends_penSgr needs penSgr's param body as
a named stage (as written it associates `(csiB ++ digits 0) ++ …` so the
chunk isn't syntactically separable — the emitter restructure is
cleaner than re-associating in the proof). OSC-title + ESC-singles +
the top `Ends (restore v)` are 3b-rest.

Lean gotchas (new, worth reusing):
- `Fintype` is MATHLIB: `revert b; decide` over `∀ b : UInt8` fails to
  synthesize. Byte-range guards must go through
  `UInt8.le_iff_toNat_le` + literal `show (0x39 : UInt8).toNat = 57 from
  rfl` + omega. Wrote `u8_bounds` once and reused it.
- Dot-namespaced lemma names SHADOW same-named defs: `ParamBytes.digits`
  made `digits n` inside that namespace resolve to the LEMMA (type
  mismatch Prop vs List UInt8); `Ends.csiNum` made `unfold csiNum` see a
  "local variable". Renamed to `paramBytes_digits` / `ends_csiNum`.
- `exact` against a mismatched goal can whnf a huge term to death
  (max-recursion on the print chain). Use the lemmas as guided
  REWRITES (`simp only [ps_ctl, ps_acceptChar]`) instead.
- `rcases h with h | h` on an Eq auto-substitutes and CLEARS h, so a
  following explicit `subst h` errors "unknown identifier" — use
  `try subst h`.
- `repeat' split` + `all_goals first | …` beats positional bullets:
  `split` peels ONE level and picks the first splittable term (in
  `Vt.print` that's the charset if, not the width if).



## §Replay 3b-rest — restore_quiesced, the parser half complete — 2026-08-12

Finished everything scoped out of the previous pass. Now proved, for ANY
Vt with NO hypotheses:

  restore_quiesced : ((Vt.init c r).feed (restore v)).pstate = ground
                     ∧ ((Vt.init c r).feed (restore v)).u8need = 0

i.e. a reattaching client's parser is never left wedged mid-sequence and
never holds a half-decoded character, so the application's next byte is
read as itself and a checkpoint taken right after a restore is exact.

Ladder (Theorems/Render.lean, ~600 lines total):
  Ends.text (no-ESC runs) · ends_csi_seq (the workhorse) · ends_penSgr ·
  ends_escSeq (ESC 7/=/H) · ends_escCharset (ESC ( 0 etc.) · ends_osc
  (ESC ] 2 ; payload BEL) · ends_rowAnsi/ends_joinCRLF/ends_gridAnsi ·
  ends_{screens,region,tabs,saved,charset,title,modes,cursor}Ansi ·
  ends_restoreBody → ends_restore → restore_quiesced.

Key insight that made the u8need half CHEAP (I had scoped it out as
"~25 lemmas through csiDispatch, low value"): restore ENDS with the
cursor's `CSI … H`. Its leading ESC clears any pending UTF-8 (abortUtf8
fires for any byte < 0x80), and every byte after it is < 0xC0 so none can
re-arm one. So `u8_zero_after_csi` needs nothing about the grid
repaint's multi-byte encodings — the tail sequence re-establishes the
property regardless of the prefix. (I still wrote the un_* layer, which
is what makes "no later byte re-arms it" provable: ~30 equation-form
lemmas incl. un_csiDispatch over its ~30-arm match.)

Emitter stages named for provability (all behavior-identical, fixtures
confirmed): penSgrBody/sgrAttr/sgrColor (so the SGR param chunk is
syntactically separable), escSeq/escCharset (so `a ++ escB ++ [b]`
doesn't associate as `(a ++ escB) ++ [b]` and split a sequence in two —
this association trap cost 3 build cycles), screensAnsi/regionAnsi/
tabsAnsi/savedAnsi/charsetAnsi/titleAnsi/cursorAnsi/restoreBody.

Two break-verifies: (1) drop the CSI final byte → ends_csiNum type
mismatch + 2 fixtures fail; (2) safeChar := id → safeChar_ge unprovable,
cascading through ends_cellText → ends_rowAnsi → ends_gridAnsi →
ends_restore. Both reverted.

New recipes:
- Equation-form lemmas (`(f v).field = v.field`) beat implication-form
  (`v.field = 0 → (f v).field = 0`) because simp can use them as GUIDED
  rewrites; `exact` against a mismatched branch whnf's the print chain
  to death (max-recursion). Only stepEsc needed the "stays zero" form
  (its RIS branch rebuilds through Vt.init).
- `Array.foldl_toList` bridges Array folds to List folds; with a generic
  `invariant_foldl` that made ends_rowAnsi/ends_gridAnsi short — no need
  to restructure the emitter's folds.
- Right-vs-left association of `++` bites constantly: `a ++ b ++ c` is
  `(a ++ b) ++ c`, so compose proofs as `(ha.append hb).append hc`.
- `Ends.ite` needs its condition given explicitly (`(c := …)`) when the
  emitter's guard is a Bool coercion (`(x != 0) = true`, not `x ≠ 0`).
- omega needs UInt8 literals pre-evaluated: keep a
  `show ((0xNN : UInt8)).toNat = NN from rfl` list in the simp set.

Remaining §Replay work (3c/3d, unchanged): the VALUE fidelity half —
grid/cursor/pen/region/modes equality after replay. Needs a digit
round-trip (parser accumulator vs `digits`) and a per-cell print
induction. Still pinned by the 14 replayEq fixtures.



## §Replay 3c — the digit round trip — 2026-08-12

Proved that the emitter and the parser are inverse on NUMBERS, which is
the foundation under every value-fidelity claim (cursor, scroll region,
mode numbers, colour components):

  accDigits_digits : accDigits 0 (digits n) = min n 65535

`accDigits` models the CSI parameter accumulator exactly as `stepCsi`
runs it (`min (cur*10 + (b - '0')) 65535` per byte), so the 65535 is the
parser's own documented clamp, not a weakening. Lifted to the emulator:
`csi_digit_step` (one digit byte, all other CsiState fields kept),
`csi_digits_feed` (a whole run), `csi_digits_value` (from `cur = 0`:
`cur = min n 65535`, `haveCur = true`, `params` untouched).

Break-verified: emitting least-significant-digit-first (a real bug class
— `CSI 21H` for row 12) breaks `accDigits_digits` AND 10 round-trip
fixtures. Reverted.

Arithmetic note: the induction is over `digits.induct`, and the clamp
case needs `n/10 ≥ 6554 → n ≥ 65535` handed to omega explicitly;
`Nat.div_add_mod'` supplies `n/10*10 + n%10 = n`.
Gotcha (again): after `rw [hw]` on a match scrutinee you need
`dsimp only` before `unfold` can see inside the branch — omitting it was
one failed cycle.

## Scoped for next: cursor fidelity needs the dims layer

Discovered while scoping: `w.cursor = v.cursor` after a replay needs
`w.cols = v.cols` / `w.rows = v.rows`, because `moveTo` clamps against
the replayed state's dimensions. So a THIRD invariance layer
(`cols`/`rows`) comes first — the very gap the step-4 notes recorded as
"by construction, not by theorem". Same equation-lemma shape as the
`pstate` and `u8need` layers (~25 lemmas); the interesting case is `RIS`,
which re-derives dims via `clampDim` and so preserves them *given*
`Good v` (already anticipated in that step-4 note).

Real infidelity found while scoping (documented, not fixed): under DECOM
the cursor can sit OUTSIDE the scroll region, because `VPA` (CSI d)
ignores origin mode. A region-relative CUP cannot reproduce such a
position, and the obvious alternative — emit an absolute CUP before
enabling DECOM — does not work either, since setting DECOM homes the
cursor. So the cursor theorem will carry `origin = false` (or an
in-region hypothesis) rather than pretend to cover it. The replayEq
fixtures include a DECOM case with the cursor inside the region, which is
the reachable-in-practice shape.



## The dims layer — closing the step-4 gap — 2026-08-12

Step 4 recorded honestly: "dims-invariance of step is NOT a proved
theorem — every op preserves cols/rows syntactically except RIS (which
re-derives via clampDim, identity under Good), but stating it needs
per-op dims lemmas (~25 more lemmas)". §Replay's cursor claim finally
needed it (moveTo clamps against the REPLAYED state's dimensions, so
`w.cursor = v.cursor` is only meaningful once `w.cols = v.cols`), so it
is now proved:

  dims_feed : Good v → dims (v.feed bs) = dims v      -- dims v = (cols, rows)

~28 equation lemmas, third instance of the layer recipe (after pstate
and u8need). Stating it over the PAIR `dims v` rather than two separate
cols/rows layers halved the work. The only conditional case is RIS, and
`Good`'s `1 ≤ cols ≤ 1000` is exactly what makes `clampDim` the
identity — the step-4 note predicted this correctly.

Break-verified: making RIS rebuild at `Vt.init (v.cols+1) v.rows` breaks
dims_stepEsc (and the older Good.stepEsc case). Reverted.
THEOREMS.md §Total row and the "what these do not settle" list updated —
that bullet had said "by construction, not by theorem" since step 4.

Gotcha: after `unfold Vt.stepEsc; dsimp only` the goals appear in
UNFOLDED pair form `(v.lineFeed.cols, v.lineFeed.rows) = …`, so
`simp only [dims_lineFeed]` does not fire — use `exact dims_lineFeed v`
(defeq) instead. Same class as the earlier "guided rewrite vs exact"
note, in the opposite direction.

Cursor fidelity remains scoped in the spec: the tail chain (`;` push →
csiFinish → CsiState.arg over Array.getD/push → moveTo) is all that is
left, and it is local to cursorAnsi because CUP sets the cursor
outright. Deliberately did NOT leave a partial proof with a `sorry` —
the purity gate forbids it and half-proofs rot.



## §Replay 3c — CUP delivers its parameters to the cursor — 2026-08-12

Proved `cup_step_cursor`: with a row parameter already pushed and a
column in the accumulator, the `H` byte moves the cursor to exactly
(col-1, row-1). Plus the two supporting rungs: `csi_semi_step` (`;`
closes a parameter via csiPush) and `arg_of_two` (CsiState.arg over a
literal two-parameter array). Break-verified by transposing moveTo's
arguments in csiDispatch's CUP arm — the classic row/col bug — which
breaks the theorem AND 8 Vt fixtures.

Stated about the state just before the final byte rather than about the
whole sequence, deliberately: that is where the content is (params →
moveTo → cursor), and it keeps the lemma free of prefix bookkeeping.

Proof-engineering notes (all new traps):
- `rw [hp]` where `hp : s.params = …` FAILS with "motive is not type
  correct" when the params occurrence is the scrutinee of `arg`'s
  dependent match. Fix: don't rewrite into the match — state a lemma
  over a LITERAL params array (`arg_of_two`) and normalize the record
  first (`hs4 : {s with params := s.params.push …} = {s with params :=
  #[…]}`), which is a non-dependent field rewrite and goes through.
- `CsiState.arg`'s `match … with | 0 => d | n => n` is best converted to
  `if a = 0 then d else a` by `cases a <;> simp` inside the helper, so
  call sites never see the match.
- The `csiFinish`/`csiDispatch` guard chain needs its `if_neg`s in
  emission order with `by decide` for the concrete final byte (0x48) and
  `by simp [h]` for the state-dependent ones (inter, ignore, haveCur).

Two rungs remain for the restore-level cursor claim, recorded in the
spec: (1) the prefix `ESC [ digits ; digits` preserves cols/rows/modes
(four one-liners — each step is a single pstate record update), and
(2) ORIGIN FIDELITY — a session with origin=false must replay with
origin=false. Only modesAnsi can emit `CSI ? 6 h` and it doesn't in that
case, but proving it needs a `Preserves`-style layer over the stream
(same shape as `Ends`, ~15 lemmas). That layer is the right next
investment because pen, region and modes fidelity all need exactly it.



## §Replay 3c rungs 1+2 — 2026-08-12

**Rung 1 done.** `cup_places_cursor`: feeding the whole `CSI row ; col H`
that cursorAnsi emits places the cursor at exactly (col-1, row-1). The
lift from cup_step_cursor needed one fact — the prefix `ESC [ digits ;
digits` leaves the fields CUP reads alone — carried by a `Frame` bundle
(cols, rows, modes), one lemma per step kind (each is a single pstate
record update). csi_digits_value now also returns inter/ignore/curSub/
priv, all free because csi_digits_feed returns a record UPDATE.

**Rung 2 layer done** (composition still open). ~30 `org_*` lemmas in
Theorems/Vt.lean, fourth instance of the invariance-layer recipe. The
structural fact that made it cheap: `modes` is written ONLY by setMode,
which csiDispatch reaches only via the h/l finals. So there is exactly
one conditional rung — `org_setMode`: only PRIVATE mode 6 writes origin
— and org_csiDispatch/org_csiFinish/org_stepCsi carry it. Design fix
found while writing: state org_csiFinish's hypothesis as `(s.priv ==
0x3F) = false` rather than three per-record conditions; every record
csiFinish builds keeps priv, so one hypothesis covers all three dispatch
sites (`hnot _ rfl`).

**Design error caught by a sorry, worth recording.** I first wrote
`KeepsOriginOff bs := ∀ v, origin off → origin off after feed` with NO
pstate premise. It is FALSE for a bare text run: fed in the middle of a
CSI with priv=0x3F and cur=6, an `h` byte completes DECOM. The premise is
load-bearing, so the right predicate BUNDLES the two claims:

  Quiet bs := ∀ v, pstate = ground → origin = false →
                (pstate = ground ∧ origin = false) after feed

which composes over ++ exactly like Ends, and whose pstate half is
already proved construct-by-construct by the ends_* family. I removed
the sorry-bearing lemma rather than commit it (purity gate), kept the
three org_step_of_{ground,esc,csi} lemmas and org_feed_ground (which DOES
carry the pstate premise) — all green.

Remaining for restore_cursor: Quiet's plumbing + one origin half per
construct. Only csiPriv is interesting: its own bytes set priv = 0x3F, so
it needs the state tracked to the final byte to show the pushed parameter
is min n 65535 ≠ 6 — which is why csi_digits_value now returns priv.
Then restore_cursor = cup_places_cursor at the mid-state, with dims_feed
and Vt.init's clamp (identity under Good) supplying the bounds.



## §Resume + the anchor set — consolidating ~370 lemmas — 2026-08-12

Asked: "can we have a bigger theorem that simplifies the set, or a
cleaner smaller set we can anchor on?" Two answers, both landed.

**1. The bigger theorem exists and is a composition.** Theorems/Resume.lean:

  resume_quiesced : ∃ c', load (save c) = some c'
                     ∧ (init cols rows).feed (restore c'.vt) ends quiesced

That is the product's own promise — crash, reboot, reattach — as ONE
statement, composing §Restore (load_save) with §Replay
(restore_quiesced). Landed first try; the rungs were already the right
shape. `resume_exact` is the runtime's form (a quiescent checkpoint comes
back byte-identical), and `resume_cursor_shape` states the cursor half at
the top level so the finished claim's shape is on the record next to the
part that is done. Deliberately keeps its own gap in the same file as the
claim: a reader shouldn't have to hunt THEOREMS.md to learn what is not
proved.

**2. THEOREMS.md is now two-level.** An ANCHOR SET of four — A1 session
survives a crash (§Restore∘§Replay), A2 daemon unbreakable by traffic
(run_wf + run_bytes_isolates), A3 transport invisible
(decode_encode_chunked), A4 one owner per name (§Claim) — over the
14-rung table, which stays because each anchor is a composition OF rungs.
"Read four statements if you only read four."

**3. Named the actual sprawl, and the fix, without doing it.** Four
invariance layers (pstate, u8need, dims, origin) are ~110 lemmas that are
the same ~28 written four times: "op X doesn't write field F". Lean can't
quantify over "fields this definition doesn't write" — that's syntactic,
invisible to the type system as Vt is shaped. Two collapses recorded in
THEOREMS.md:
  (a) CHEAP: bundle the fields into one `Untouched v w` conjunction,
      proved once per op instead of once per op per field → ~28 replaces
      ~110, each layer becomes a projection. No Core change.
  (b) REAL FIX: split Vt into {screen, parser, meta} and give
      printing/erase/scroll the type Screen → Screen, lifted by one
      `onScreen`. Then "printing never touches the parser" is the TYPE,
      not 28 theorems, and the next field costs zero instead of 28.
      Cost: refactor of the core module every proof depends on.
Honest reason (b) hasn't happened: each layer was written to unblock a
specific §Replay rung, and by the time the pattern was obvious three
existed. Right trade to reach a proof, wrong one to keep — recorded so
nobody hand-writes a fifth copy.
