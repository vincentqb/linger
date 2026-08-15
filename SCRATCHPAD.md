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



## Frames — the right generalization of the four layers — 2026-08-12

User pushed twice: the ~110 lemmas have "very similar shape, that we can
generalize", and the Vt-split fix is "right headed, but not enough?".
Both correct, and the second one identified a real flaw in my proposal.

WHY THE SPLIT IS NOT ENOUGH: the read/write distinction is PER-OPERATION,
not global. `print` READS cols/rows (to clamp) and READS modes (wrap,
insert) while writing neither. So `{screen, parser, meta}` with
`print : Screen → Screen` still permits a resize — the dims invariance I
proved 28 times is not recovered by that type. And `modes` is read-only
for ~20 ops but writable for `setMode`; no global partition says that.
The refactor that WOULD capture it moves read-only data into PARAMETER
position (`print : Dims → Modes → Cells×Cursor → Cells×Cursor`), i.e.
separating context from state — much bigger, and mostly subsumed by:

THE ACTUAL GENERALIZATION: a FRAME condition per operation, stating its
footprint once, covering every field.

  frame_putCell : v.putCell x y c = { v with grid := (v.putCell x y c).grid }

= "putCell writes only grid". Demonstrated in Theorems/Vt.lean on
putCell/moveTo/eraseRowSpan/scrollUpIn/lineFeed, with all FOUR existing
layers derived from one `frame_scrollUpIn` in a single `rw` each — plus
`top` and `saved`, which no layer ever covered. So:
  * ~28 frames replace ~110 single-field lemmas;
  * a fifth field costs ZERO (vs another 28);
  * complete, not "the four fields I needed" (that's why it beats
    bundling);
  * no Core refactor, no existing proof disturbed (that's why it beats
    splitting).
Proof shapes: `rfl` for plain record updates, `unfold; split <;> rfl` for
branching ops, staged composite for print. Gotcha: after `rw [frame_X]` a
goal about a `def`-wrapped projection (`dims`) needs an explicit `rfl` —
rw's implicit one is reducible-transparency only.

HONEST LIMIT, stated in THEOREMS.md and the spec: a frame says what an op
leaves ALONE, never what the written fields BECOME. Grid fidelity
(§Replay 3d) needs the positive spec, which is content, not bookkeeping.
Frames retire the sprawl; they do not shorten that road. Conditional cases
(RIS, setMode) stay conditional — frames localize them to one theorem per
op instead of one per op per field.

Conversion recorded as step 4 in specs/bigger-theorems.md: frames for the
~28 ops → re-derive the layers' entry points keeping their names (so no
downstream proof changes) → delete the ~110.



## Frames, measured: a partial win — NEGATIVE RESULT — 2026-08-12

Asked "so that sounds like a net win?" — checked instead of agreeing, and
the check DOWNGRADED my own claim. I had written "~28 frames replace ~110
lemmas". That is too strong. Spiked the two operations that decide it:

* `frame_print` (full stage chain): (deterministic) timeout at whnf. The
  monolithic unfold is too large for a per-branch `rfl`.
* `frame_csiDispatch` (~30-arm match): `rfl` fails on the fold arms —
  `List.foldl (fun a _ => a.tab) v (range n)` is not a syntactic record
  update, so those arms need an induction and manual gluing.

Both spikes removed from the tree (they don't compile); the finding is now
in THEOREMS.md and specs/bigger-theorems.md.

THE PRINCIPLE: a frame proves by `rfl` exactly when the operation's result
is a SYNTACTIC RECORD UPDATE. True for leaf ops (~20 of them, and most of
the 110 lemmas), false for compositions and folds. Gluing staged frames
would need footprints as first-class data — a field-set type, a
`WritesWithin` predicate, monotonicity lemmas — i.e. a small effect
system, which is LARGER than the sprawl it would remove. That is the real
answer to "is the structural fix enough?": no, and the fully general fix
costs more than the problem.

Revised verdict: frames retire ~60% of the sprawl cheaply and leave the
composite/fold ops as they are (which is also where the conditional cases
RIS/setMode live). Still a net win, smaller than advertised. Recommended
timing: do it immediately BEFORE the next field layer is needed (pen
fidelity would want one), not as standalone cleanup — the sprawl costs
readability today and nothing else.

Method note worth keeping: the useful move here was spiking the hardest
case before believing the generalization. Two builds, and it turned an
overclaim into a calibrated one.



## Frames landed for the leaves — 2026-08-12

Asked "why wait?" about my own recommendation to defer the conversion.
No good answer: the work was loaded in context, the cost is identical
later, the benefit starts immediately, and doing a mechanical refactor
while the gate is green is the SAFEST moment. That recommendation was
reflexive conservatism, not prudence. Did it.

Landed: 30 `frame_*` theorems for the leaf operations, and 28 of the four
layers' proofs collapsed to a single `rw [frame_X]` — 86 proof lines
removed, Theorems/Vt.lean 1935 → 1851 despite gaining 30 theorems. Full
gate green, no sorry.

Two mechanical gotchas worth keeping:
- ORDER MATTERS: the frames had to be relocated ABOVE the four layers
  (they were appended at the end), or the collapsed proofs cite
  not-yet-defined names. Moved with a script; the demo block's `dims`
  example then referenced a def that now comes later, so it was restated
  over the raw `cols` field.
- The `dims_*` conversions need `rw [frame_X]` followed by an explicit
  `rfl`: `dims` is a plain `def`, and rw's implicit rfl is
  reducible-transparency only.

Left un-converted, on the measurement from the previous entry: `print`,
`csiDispatch`, and the fold-based ops (`eraseScreen`, `insertLines`,
`deleteLines`). Their per-field lemmas stay, which is also where the
conditional cases (RIS, setMode) live — the residue is precisely the part
that was never mechanical.

Method note: the whole sequence here — claim, spike, downgrade, then do
the part that survived — cost about four builds and produced a smaller,
truer result than the confident version would have.



## Session continuity wiring — 2026-08-12

This session is long and has been compacted at least once, and the
durable anchors had two real gaps:

1. `AGENTS.md` — the file a post-compaction agent re-reads — named only
   the ARCHIVED spec. Nothing pointed at `specs/bigger-theorems.md` as
   the live plan, and the root `PLAN.md` is the original REQUIREMENTS,
   which a resuming agent would mistake for current state. Fixed: a
   "Where things stand — read this first after any compaction" block
   naming the active spec, then SCRATCHPAD, then "re-ground against those
   two, not against a compaction summary".
2. `specs/bigger-theorems.md` had status buried in 200 lines of step
   prose. Fixed: header block with Goal / Definition-of-done / a status
   table / **Next step →** / Decided-do-not-relitigate / Open questions.

Division of labour between the three files, now explicit: PLAN.md =
requirements (frozen), spec = forward state (rewritten in place),
SCRATCHPAD = append-only backward log (this file). Nothing else changes;
the per-increment commit + gate-green discipline was already the
checkpoint habit the skill asks for.

Nothing is in flight: last increment (frames for leaf ops) is committed,
pushed, gate green.



## Step 3c-rest notes — `Quiet` and the cursor claim — 2026-08-12

Landed `Quiet`, the bundled parser-state + DECOM predicate, and with it
`restore_cursor` / `resume_cursor`. Full reasoning is in
specs/bigger-theorems.md (stage 3c-rest); what belongs here is the
mechanics.

### Proof recipes that worked

- **The `ite` combinator should take the condition.** `Quiet.ite` is
  `(c → P a) → (¬c → P b) → P (if c then a else b)`, not
  `P a → P b → …`. That single change is what lets a *guarded emit* prove
  something: the mouse branch gets `h : (mouse != 0 && mouse != 6) = true`
  and reads `mouse ≠ 6` straight out of it
  (`simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact h.2`), and
  the DECOM branch consumes the theorem's own hypothesis in place
  (`fun h => absurd (ho.symm.trans h) (by simp)`) instead of rewriting the
  goal. Prefer this shape for any new stream predicate.
- **Projecting a frame.** `congrArg (·.2.2) (frame_csi_digits_feed …)`
  pulls `modes` equality out of a `Frame` equality; `.1` is cols, `.2.1`
  is rows. This is how the digit run inside a *private* CSI was proved
  origin-preserving without a new `org_*` lemma — frames covering a proof
  they were not written for.
- **Splitting a feed** is always
  `rw [show ∀ (w : Vt), w.feed (a ++ b) = (w.feed a).feed b from fun w => by
  simp [Vt.feed, List.foldl_append]]`, and `w.feed [b] = w.step b` is
  `rfl`. Stating them as `∀ w` and rewriting is far less brittle than
  naming the intermediate term, which gets long fast.

### New traps

- **`absurd`/`False.elim` in a branch breaks implicit inference.**
  `have e9 := Quiet.ite (c := …) (fun h => absurd …) (fun _ => Quiet.nil)`
  fails with "don't know how to synthesize implicit argument `a`" — the
  then-branch bytes are never mentioned. Annotate the `have` with the full
  `Quiet (if … then … else …)` type, spelled the way Lean elaborates it
  (`if c = true then …`, `if true = true then 0x68 else 0x6C`).
- **`rw [show (P = True/False) from …]` on an `ite` condition** →
  "motive is not type correct" (same family as the `CsiState.arg` trap).
  Don't rewrite the condition; take it as an argument (above).
- **`|>.field` inside a type ascription doesn't parse**:
  `have h : x |>.modes = y := …` gives "unexpected token '='; expected
  ':=' or '|'". Parenthesise: `(x).modes`.
- **A tightened definition can *remove* work.** `ParamBytes` at 0x30–0x3F
  admitted the private marker, which forced a second parameter predicate
  for `Quiet` and with it a clone of the whole SGR chain
  (`sgrAttr`/`sgrColor`/`penSgrBody`). Tightening it to 0x30–0x3B made one
  predicate serve both layers; the only casualties were two call sites
  that pass a marker, which now go through `ends_csi_priv_seq`. Look for
  this shape before duplicating a predicate: the duplicate is often a
  symptom of the original being too loose.

### Break-verification: shape breaks are not tests

Three breaks, two of them weak, recorded because the failure mode is
easy to repeat:

| break | result | verdict |
|---|---|---|
| delete the `mouse != 6` guard | `Type mismatch` on the `ite` shape | weak — only proves the proof mentions the guard |
| append `csiPriv 6 0x68` to `regionAnsi` | `Type mismatch`, term shape changed | weak, same reason |
| `set 2004 true` → `set 6 true` in `modesAnsi`, proof updated to follow | `decide proved that the proposition 6 ≠ 6 is false` | **real** — a restore stream that turns DECOM on is rejected |
| guard `!= 6` → `!= 7` (shape preserved) | `¬mouse = 7 but expected mouse ≠ 6` | **real** — the guard is load-bearing for exactly DECOM |

Rule: change a *value*, keep the term's shape, and update the proof the
way a maintainer following the emitter would. A break that changes the
shape tests the proof script, not the theorem.

### Negative result: don't abstract the stage lemmas yet

Sketched a `StreamPred` bundle (P, nil, append) so `Ends` and `Quiet`
would share one set of ~13 restore-stage lemmas. Blocker: `modesAnsi`'s
DECOM branch is hypothesis-free for `Ends` and hypothesis-bearing for
`Quiet`, so the shared lemma needs
`v.modes.origin = true → P (csiPriv 6 0x68)`, which turns
`restore_quiesced` from "no hypotheses" into "one vacuous hypothesis".
Not worth it to dedupe thirteen 3-line proofs. Revisit if a third layer
wants the same skeleton.

Also deleted `KeepsOriginOff` (~85 lines at the end of
Theorems/Render.lean): dead, and three of its lemmas *shadowed* the more
general `org_step_of_*` now in Theorems/Vt.lean. Its own comment already
said the bundled predicate was what was wanted.

Gate green, no sorry, `./lake build Zmx Theorems Tests linger` clean.



## Step 3d notes — the byte layer, and a real bug the proof found — 2026-08-12

### The decomposition that makes grid fidelity tractable

Reduce the byte stream to *emulator operations* first, then argue fidelity
with no bytes left in the argument. Landed:

- `utf8_feed` — feeding the bytes `utf8` emits for a printable codepoint
  **is** `Vt.print` of that codepoint. Four cases over encoding length,
  sharing three lead-byte lemmas (`step_lead2/3/4`) and two continuation
  lemmas (`step_cont_more`, `step_cont_last`), so `stepGround`'s eight-way
  byte ladder is walked once per rung instead of once per case.
- `utf8s_feed` — a glyph run is `List.foldl print`.
- `cellText_feed` — a painted cell is its base glyph then its marks.
- `crlf_feed` — the row separator is exactly `carriageReturn.lineFeed`.

`utf8_feed` needs **no** DEL exclusion: 0x7F prints as a glyph, and only
`safeChar` cares. Dropped that hypothesis when the build flagged it unused.

### THE BUG: the SGR parameter cap swallowed whole pens

Counting parameters while setting up the pen round trip: `penSgrBody`
emitted `0` + up to 7 attributes + up to 5 fg + up to 5 bg = **18**
parameters. The parser honours 16 and sets `ignore` on the 17th, dropping
the entire sequence. Confirmed by evaluation before touching anything:

```
pen      = all 7 attrs, fg = rgb 10 20 30, bg = rgb 40 50 60
params   = 18
roundtrips = false
replayed pen = ALL DEFAULT   -- every attribute and both colours lost
```

The state is reachable — an application sets attributes and colours in
separate SGRs and nothing merges them — so this was a live reattach bug,
not a theoretical one. Fourteen fixtures missed it because none combined
*all* attributes with truecolour on *both* fg and bg.

Fix: `penSgr` now emits up to three sequences (attributes, then fg, then
bg), at most 8 parameters each, with no colour triplet able to straddle a
boundary. `sgrColorSeq` returns `[]` for a default colour rather than
`sgrOf []`, because `CSI m` with no parameters is a *reset* and would wipe
the attributes the previous sequence just set. `sgrAttr`/`sgrColor`/
`penSgrBody` are gone, replaced by `colorCodes`/`penAttrCodes` (parameter
*numbers*) plus `joinSemi`/`sgrOf` (the byte assembly) — the separation
that made the count visible in the first place.

Two fixtures added: the 18-parameter pen (fails before the fix — that is
the break-verification) and the 14-parameter 256-colour version as the
boundary case that already passed.

**This is the eighth §Replay infidelity, and the first found by proving
rather than by testing.** The others came from reading the emitter against
the parser; this one only showed up because setting up the pen round trip
required counting parameters. Worth remembering when judging whether a
proof effort "pays": the count was the payment.

### Traps

- **`rw` matches the OUTERMOST subterm.** A chain of continuation-byte
  steps all match `?v.step (UInt8.ofNat (0x80 + ?m))`, so the first
  `rw [step_cont_more]` fired on the *last* byte. Pin `(m := …)` (and
  `(acc := …)`) explicitly on every step of a chain.
- **`feedN` as `rfl` times out at `whnf`**; `by simp [Vt.feed]` is instant.
  Same family as the `frame_print` timeout.
- **`rw [hg]` rewrites the goal's right-hand side too.** A `pstate` rewrite
  inside a proof whose RHS mentions the same state turns `{v with …}` into
  a record that no longer matches. Put the rewrite in a bridge lemma whose
  statement doesn't mention the field (`step_cont_bridge`).
- **Frames DO reach `print`** — `frame_print` as one `rfl` still times out,
  but *peeling* the stage frames inside a field projection works
  (`ua_print` is four `rw`s). The earlier "out of reach" note was about the
  composite equation, not about the technique.
- `rw [joinSemi]` on a 3-arm match generates a side goal
  (`m :: ns = [] → False`); `rw [show … from rfl]` avoids it.



## bigger-theorems closed; grid-fidelity opened — 2026-08-12

The consolidation spec is done and archived with a completion record
(`specs/archive/bigger-theorems.md`). All four steps met the
definition-of-done; nine emitter bugs were fixed along the way.

What is *not* done is the **values** — replayed cells and pens equalling
the saved ones — so that got its own spec, `specs/grid-fidelity.md`, rather
than being left as an "open question" bullet on a closed plan. Different
kind of work: consolidation is about what an operation does *not* touch,
value fidelity is a positive specification of what it *writes*.

`penSgr_under_cap` landed as the durable form of the parameter-cap lesson:
attributes ≤ 8, each colour ≤ 5, against a cap of 16. Break-verified by
adding an eighth attribute code to `penAttrCodes` — `omega` then cannot
prove the bound, so a future attribute forces a conscious look at the cap
instead of silently reintroducing an 18-parameter sequence. That is the
right shape for this class of lesson: the failure is *silent* (an over-long
SGR is dropped whole, not mis-applied), so a fixture alone would only ever
catch the instances someone thought to write down.

Housekeeping: `specs/bigger-theorems.md` was referenced from five source
files. Forward-looking references now point at `specs/grid-fidelity.md`,
rationale/history references at the archive path. The stale "converting the
rest is the recorded next simplification" note in Theorems/Vt.lean is now
"the leaf conversion is done; what stays per-field is `print`,
`csiDispatch` and the folds".



## Epic audit against PLAN.md, and the graphics question — 2026-08-12

Stepped back to ask which epics the project actually wants and whether
they are done. Audited PLAN.md line by line rather than from memory.

| PLAN.md asks for | state |
|---|---|
| feature-complete multiplexer | **done**, read as feature-complete *zmx*: attach/watch/run/send/wait/ls/history/kill/detach/get/set/unset/clear. Windows/tabs/splits rejected on purpose (`specs/archive/lean-zmx.md`) |
| decouple session layer from TUI | **done, and then some** — the TUI was built, shipped, user-tested and *removed*; `ls` + `recipes/` replaced it |
| non-Lean surface as small as possible | **done** — `Zmx/Posix.lean` + `c/shim.c`, with the `SHIM_CAP` wrapper-count ratchet |
| runs in userspace | **done** |
| reboot-resume like tmux-continuum | **done** — periodic checkpoint + restore on attach, §Restore proved |
| see sessions on other machines over ssh | **done** — `ls -r`, `attach name@host`, §Remote proved, fake-ssh harness |
| modern clean default, no customization | **done** — by *deleting* the TUI, this became "your terminal + six-line recipes" |
| theorems preventing crashes under load (the zellij complaint) | **done** — anchor A2: `run_wf`, `run_bytes_isolates` over any trace |
| high-quality theorems resolve tensions | **ongoing by nature** — 4 anchors over 15 rungs; A1's value half is specced in `specs/grid-fidelity.md` |

So every epic in the requirements is closed. What was *never audited* was
graphics, which is what prompted the question.

### Do we support kitty images? Measured, not guessed

Read the data path, then tested it. `Zmx/Core/Session.lean` on
`.ptyBytes chunk` does two things: `vt.feed chunk` **and**
`broadcast s chunk` — the raw chunk, verbatim, to every attached client,
which `Runtime/Client.lean` writes straight to stdout. Meanwhile
`stepEsc` sends `ESC P` (DCS/sixel), `ESC X`, `ESC ^` and `ESC _`
(APC/kitty) to `PState.str`, and `stepStr` discards bytes until `ESC \`
without accumulating.

Consequences, all now covered by `tests/graphics_test.py` (7 checks):

- kitty APC and sixel DCS **pass through byte for byte while attached** —
  no `allow-passthrough` switch needed, unlike tmux;
- the payload never reaches the text grid (verified against
  `linger history`);
- a payload cannot wedge the session or grow it — the `.str` state
  accumulates nothing, so §Bound is trivial for a megabyte of base64;
- **images are gone on reattach**: `restore` repaints from the cell grid,
  which holds no image data. The text screen returns exactly.

That last one is asserted *positively* in the test, so the README and the
behaviour cannot drift apart.

Decision recorded in AGENTS.md as a settled non-goal: do **not** store
images for replay. It would put unbounded program-controlled bytes into
the periodic checkpoint — the one thing §Bound exists to prevent — and
would need kitty's whole placement model (ids, z-index, cropping, scroll
behaviour) to be reimplemented. tmux and screen leave redraw to the
application; so do we. `recipes/lzo.fish` already puts each session in its
own kitty tab for people who want a picture to survive.

### Test-writing trap worth keeping

First version of check 4 ("payload does not reach the text grid") FAILED,
and the test was wrong, not the code: `/bin/sh` **echoes the command
line**, so a literal marker inside `printf '...'` appears in the grid as
echoed input. Fix: octal-encode the marker (`\107\106\130…`) so only the
real payload contains it. General rule for pty tests — anything typed at a
shell arrives twice, once as echo and once as output; make the two
distinguishable at the byte level before asserting on either.

Break-verified the passthrough itself by stripping ESC from `broadcast`:
the two passthrough checks fail while liveness and restore keep passing,
so the test discriminates images specifically rather than "the session
works".



## The repaint shortcut, measured — 2026-08-12

Asked why images don't come back on reattach and whether there's a repaint
shortcut. There is, it already works, and my earlier write-up was too flat
("images are gone on reattach"). Corrected in README/THEOREMS/AGENTS.

### Why a grid repaint cannot carry them

A `Cell` is `{base, marks, width, pen}`. There is no image plane, and kitty
placements are *overlays anchored to cell coordinates*, out of band from
cell content. So it is not that `restore` forgets to emit them — a
grid-shaped repaint has nowhere to put them.

### The shortcut: the application's own redraw

Measured, both halves:

| reattach | SIGWINCH to the program |
|---|---|
| same size (80x24 → 80x24) | **no** — Linux `tty_do_resize` compares the winsize and skips the signal |
| new size (80x24 → 100x30) | **yes** — one signal |
| resize while attached | **yes** — one signal |

So a full-screen app redraws on a size-changing reattach and re-emits its
own images; at the same size nothing redraws and `Ctrl-L` (or the app's
refresh key) is the manual version. An image from a command that has since
exited is unrecoverable by any redraw.

An app's own redraw is *better* than our replay would be: it also refreshes
whatever the emulator models imperfectly. Worth remembering as a general
point — for a full-screen program the multiplexer's grid is a cache, and
the authority is the program.

Both halves are now checks 8 and 9 of `tests/graphics_test.py` (9 total),
which also guards the `sizeOwner`/`resizePty`-on-attach path from
regressing.

### Correcting my own overreach

I had written that storing images "would put unbounded program-controlled
bytes into the checkpoint, which is the one thing §Bound exists to
prevent". That is rhetoric, not an argument: a cap makes it bounded by
construction. The honest reasons are four, and they are now in README:
placements only replay into the same terminal process that still holds the
image (so nothing after a reboot — which is the point of the checkpoint);
correct replay needs kitty's placement model (ids, z-index, cropping,
scroll behaviour) and a misplaced image is worse than none; sixel and
iTerm2 have no re-place concept so they need full payloads or nothing; and
payloads turn a small timed checkpoint write into a multi-megabyte one.

### Three test bugs in a row, same family

Getting this measured took three wrong tests, all of the same shape —
**the observation channel was contaminated by the thing being observed**:

1. `trap 'echo SAW-WINCH' WINCH` reported a signal on *every* reattach.
   The marker was in the echoed command line, which `restore` repaints, so
   I was reading the repaint as a signal.
2. Fixed the marker (runtime arithmetic, `$((20+2))`) and got zero
   everywhere — because the reporter had been started with `&`, and a
   background process group receives no `SIGWINCH` at all.
3. Also mid-way: a `linger run`-spawned reporter logged nothing, for the
   same foreground-process-group reason.

Rules for pty tests, now applied in `graphics_test.py`: put the observation
in a **file**, not on stdout (stdout is grid state and gets replayed); keep
the observer in the **foreground** process group; and make anything typed
at a shell distinguishable from its own echo at the byte level (runtime
arithmetic, or octal-encoded markers). A green pty test that reads stdout
for a marker it also typed is not evidence.



## grid-fidelity step 2, semantic half — 2026-08-12

`pen_codes_recover`: `Vt.applySgr` inverts the pen encoding, from any
starting pen. ~120 lines, and the risk assessment in the spec was **wrong
in the useful direction** — I had flagged `applySgr`'s fuelled fold as "the
largest single unknown" with a fallback plan. No fuel machinery was needed
at all: every sequence is applied at exactly `length + 1`, which is what
the fold consumes, so the concrete cases close directly. Left the mistaken
risk note in the spec with the correction, rather than deleting it.

### The two proof shapes that made it cheap

- **Attributes: 128 concrete branches.** `obtain ⟨…⟩ := p` then `cases` on
  each of the seven `Bool`s, then one `simp [penAttrCodes, applySgr.go]`.
  Compiles in 4.7 s. Much cheaper than the seven step lemmas plus a
  composition law I had planned — brute force over a *finite* dimension
  beats structural elegance when the dimension is small and the leaves are
  trivial. Spiked it first precisely because it was the cheapest possible
  experiment on the biggest unknown.
- **Colours: make the value concrete, and the guard chain evaporates.**
  `applySgr`'s fold is a ~19-rung `if`-chain on the parameter number, so a
  symbolic `30 + i.toNat` leaves simp stuck with a rung per SGR code. The
  16-colour forms are only 8 codes each, so `rcases` into concrete values
  and every guard decides by computation. Better still, `simp [← key]`
  (where `key : UInt8.ofNat i.toNat = i`) rewrites `i` itself to a literal,
  which makes `i.toNat` *compute* — so the range hypotheses `h8`/`h16`
  became unused simp arguments, and the build's unused-argument warning is
  what pointed that out.

### Traps

- **`split` on a catch-all `match` gives a destructured hypothesis, not an
  equation.** `match colorCodes c isFg with | [] => q | ns => f ns` splits
  into `[]` and `x :: xs`, so there is no `hns : … = ns` to rewrite with.
  Fix: define proof-side mirrors with `if … = default then` rather than a
  catch-all match, and prove the characterisation (`colorCodes_eq_nil`)
  separately — which is a fact worth having anyway, since `sgrColorSeq`
  uses emptiness as its "send nothing" test.
- `UInt8.ofNat_toNat` takes its argument implicitly; `UInt8.ofNat_toNat i`
  is a type error ("function expected").
- `rw [iff_lemma]` on a `≠` goal does not fire (the goal is
  `¬(… = …)`, and the rewrite looks inside a `Not`). Apply the `.mp`
  directly: `fun h => hc ((colorCodes_eq_nil c isFg).mp h)`.

Break-verified by changing the 16-colour foreground base from 30 to 31 in
the emitter: `penAfter_colorCodes` fails on the fg case (the parser reads
`.idx (i+1)`), while the bg case and the other three forms stay green — so
the lemma pins each form separately rather than passing on a shared
shortcut.

Remaining for step 2: the parser half — that the CSI accumulator delivers
these numbers. Recipe recorded in the spec: state the run lemma with the
*pushed* array rather than with `dropLast`/`getLast`, since `csiFinish`
performs exactly that push and the induction then follows `joinSemi`'s own
three-arm recursion.



## grid-fidelity step 2 CLOSED — a pen replays exactly — 2026-08-12

`penSgr_feed`: feeding the sequences `penSgr` emits to a quiet emulator sets
its pen to `p` and changes nothing else. §Replay's pen axis is closed;
what remains of anchor A1 is the cells.

Parser half, on top of the semantic half from the previous entry:

- `step_of_csi_quiet` — with nothing half-decoded, `step` is `stepCsi`. The
  `.csi` twin of `step_of_ground_quiet`, and the same trick: keep the
  `pstate` rewrite inside a bridge lemma so it cannot touch a caller's
  right-hand side.
- `csi_param_run_frame` — a parameter run changes **nothing but** `pstate`.
  Deliberately separate from the contents lemma: mixing "what moved" with
  "what it holds" in one statement is what made the first attempt unwieldy.
  The two views are identified afterwards through `PState.csi.inj`.
- `csi_joinSemi_feed` — the contents, stated in terms of the array *after*
  the final push. That was the key choice: `csiFinish` performs exactly that
  push, so the induction follows `joinSemi`'s three-arm recursion and
  `dropLast`/`getLast` never appear.
- `sgrOf_feed` / `sgrColorSeq_feed` / `penSgr_feed` — the walk and the
  composition.

### Traps

- **`rw [lemma h1 h2]` picks the wrong state when a hypothesis is `rfl`.**
  `rfl` cannot determine the implicit `{v}`, so unification grabbed the
  *outer* `v` and the rewrite looked for `v.step 109` instead of
  `(record).step 109`. Pin it: `rw [step_of_csi_quiet (v := …) (s := …) …]`.
- **`subst` on `h : a = b` may eliminate the name you meant to keep.**
  `subst hid` removed `s'`, so every later mention became "unknown
  identifier". `rw [hid] at hframe` keeps both names alive and is what the
  rest of the proof wants anyway.
- **A record's default-valued field is *dropped* by the elaborator's
  normal form.** After `simp only [hpriv]` rewrote `s'.priv` to `0`, the
  goal held a `CsiState` literal with no `priv` field at all, so a helper
  stated as `{ s' with params := … }` (which carries `priv := s'.priv`) no
  longer matched. Fix: state such helpers **universally quantified over the
  record**, with the field of interest as a hypothesis
  (`∀ t, t.params = … → t.sgrParams = …`), then apply with `rfl`.
- `rw` into a `match` scrutinee is the usual motive failure, so proof-side
  mirrors of emitter functions get an `if` and a characterisation lemma
  (`sgrColorSeq_eq`) rather than a catch-all `match`.
- Resolving range guards *before* a `match` on the result lets the match
  reduce by iota: `by_cases h8 : i.toNat < 8` then `rw [if_pos h8]` turns
  the scrutinee into a literal list, and `simp` finishes.

### Break-verification, and two more shape-only near-misses

Reordering `penSgr`'s three sequences broke three proofs — but all on term
*shape* (the appends reassociate), which tests the scripts, not the claims.
The real catch needed a same-shape content change: **the leading `0` in
`penAttrCodes` changed to `39`** (reset-foreground, which does not reset
attributes). Then `penAfter_attrCodes` demands `q.bold = false ∧ …` of an
*arbitrary* starting pen and cannot be proved — which is exactly the content
of "from any starting pen". Third time this session that a shape break
masqueraded as verification; the rule is holding up.



## grid-fidelity step 3 started — one glyph, placed — 2026-08-12

`print_narrow`: under the conditions a repaint actually runs in — insert mode
off, no charset translation, no pending wrap, cursor in bounds — printing a
width-1 glyph writes exactly `{base := ch, marks := [], width := 1,
pen := v.pen}` at the cursor. Four of `print`'s five stages are the identity
there; the fifth writes the cell.

### A gap in §Bound this turned up

`putCell` writes through `setIfInBounds`, so a row shorter than `cols` would
swallow the write **silently**. Every reachable state has
`row.size = cols` and `grid.size = rows` — `Vt.init` builds them that way,
`resize` re-fits, `putCell` preserves them — but **`Good` does not say so**.
So `print_narrow` carries the two shape facts as hypotheses, and step 1's
`Renderable` is where they belong (or `Good` itself, which would be the
better home since it is §Bound's business). Worth noting that a *silent*
no-op is exactly the failure mode a grid-shape invariant exists to exclude;
nothing in the test suite would catch a short row either.

### Traps

- **`simp only [frame_X]` loops.** The frames are self-referential by
  construction (`v.op = { v with f := (v.op).f }`), which is fine for a
  single `rw` but makes `simp` rewrite forever — "maximum recursion depth".
  When a *normalising* rewrite is wanted, use the direct definitional
  equation instead: `have hcp : v.clearPending = { v with cursor := … } :=
  rfl`, whose right-hand side does not mention `clearPending`.
- **The two `getD` positions must agree syntactically.** `putCell` writes at
  `v.clearPending.cursor.y` while the read is at `v.cursor.y`; they are
  definitionally equal, but `rw [getD_set_self]` needs one metavariable to
  match both, so `clearPending` has to be normalised away first.
- `rw [if_neg …]` matches the **first** `if` in the goal, which after
  `unfold Vt.print` is the *width* test, not the charset test — the reported
  side goal was `¬charWidth ch = 0`, which is how it showed up. Normalising
  with `simp only [htr, …, hw]` picks the intended ones by content instead of
  by position.
- Two `Array.getD`/`setIfInBounds` lemmas had to be proved by hand
  (`exact?` finds only `Array.size_setIfInBounds`): `getD_set_self` and
  `getD_set_ne`. The latter needs `Ne.symm h`, since the residual goal comes
  out as `x = j → …` while the hypothesis is `j ≠ x`.

Break-verified: `printPut` writing `pen := {}` instead of `pen := v.pen`
makes `print_narrow` fail with the same term shape. A content break at last
on the first attempt — the pattern is that a break inside a *record field*
keeps the shape, whereas a break in a *list or append structure* does not.

Remaining in step 3: the wide-glyph group (a width-2 cell plus its shadow),
the mark case, and the frame (`print` leaves every other cell alone), which
needs `getD_set_ne` lifted through both array levels.



## grid-fidelity step 3 — the frame — 2026-08-12

`print_narrow_frame`: a narrow glyph touches **no other cell**. With
`print_narrow` (which cell it writes) this is the pair a row induction needs
— "writes this one, leaves the rest" — and together they are the whole
observable content of one glyph.

Both array levels go through `getD_set_ne`, with a three-way split: a
different row is untouched; the same row at a different column is untouched
within the row; and if the row index is out of bounds `setIfInBounds` is the
identity, so the read is too. That last case is not hypothetical — the lemma
takes no bounds hypotheses at all, which is what makes it usable at the edge
of a row induction without carrying bounds around.

### Traps (both already in this file, both bit again)

- `subst hy'` eliminated `y'`, so the very next `by_cases hg : y' < …` failed
  with "unknown identifier". Second time this session. After a `subst`, refer
  to the *surviving* term (`v.cursor.y`), or use `rw … at` instead.
- `exact getD_set_ne _ _ _ _ _ h` gave "typeclass instance problem is stuck"
  and a type mismatch: the goal is the row equality with `.getD x' default`
  applied to *both* sides, not the raw row equality. Wrap it:
  `congrArg (fun r => Array.getD r x' default) (getD_set_ne …)`. Underscores
  hid the shape mismatch behind an instance error, which is the misleading
  part — read the mismatch, not the instance complaint.

Break-verified: `printPut` writing at `x+1` instead of `x` fails four
proofs. A record-field break for `print_narrow` (wrong pen) and an index
break for the frame — the index one is what the frame specifically catches,
since writing one cell to the right leaves the cursor cell untouched *and*
disturbs a cell the frame promises is untouched.

Step 3 remaining: the wide-glyph group (a width-2 cell plus its width-0
shadow, written by the same `printPut`) and the mark case (a zero-width char
attaches to the cell *before* the cursor — §Replay fix 1, and the reason
marks are replayed at all).



## grid-fidelity step 3 CLOSED — wide glyphs and marks — 2026-08-12

`print_wide` and `print_mark` finish the per-glyph layer:

- **`print_wide`** — a width-2 glyph writes *two* cells: the glyph with
  `width := 2` at the cursor, and a `width := 0`, `base := ' '` **shadow** to
  its right. Both come from the same `printPut`, so reading the glyph cell
  means stepping *past* the shadow write with `getD_set_ne` (`x ≠ x + 1`)
  before the glyph's own `getD_set_self`.
- **`print_mark`** — a zero-width char attaches to the cell *before* the
  cursor, appending to its `marks`. Carries `cursor.x ≠ 0` and the §Bound cap
  `marks.length < 8` (past eight the mark is dropped, so an adversarial mark
  stream cannot grow a cell).

Together with `print_narrow` + `print_narrow_frame` that is the whole
observable content of one glyph, and it explains §Replay fix 1 from the other
direction: a mark parks on a wide char's *shadow*, so `rowAnsi` has to
re-emit the marks of width-0 cells even though it skips their blank base.
Dropping them would lose the mark — which is exactly the bug fix 1 was.

### Trap: nested `if`s resolve outside-in, and a failure cascades

`print_mark`'s two rewrites failed *together*, and the second failure was a
red herring: the cap `if`'s cell mentions `cx`, and `cx` was still an
unresolved `if` because the rewrite above it had failed. So "pattern not
found" for the cap test was caused by the cx test, not by anything about the
cap. Fixing the outer one fixed both. General rule: in a chain of
`rw [if_neg …]`, fix the *first* failure and re-read; later "pattern not
found" errors in the same chain are usually downstream of it.

Also: `by simp [hx0]` did not discharge `¬((v.cursor.x == 0) = true)` from
`hx0 : v.cursor.x ≠ 0`; `by simp only [beq_iff_eq]; exact hx0` did.

Break-verified: the shadow cell's `width := 0` changed to `1` fails three
proofs. A record-field break again, which is the reliable kind.

### Step 4 is where this stops, deliberately

The remaining work — a row, then the grid — is one large induction with
several interacting invariants, and I would rather leave it unstarted than
half-landed. What the per-glyph layer now hands it:

- each glyph's effect is `print_narrow`/`print_wide` (what it writes) plus
  `print_narrow_frame` (what it leaves alone), with **no bounds hypotheses**
  in the frame, so the induction need not thread bounds for the frame half;
- `cellText_feed` already turns a cell's bytes into those prints;
- `penSgr_feed` turns `rowAnsi`'s conditional pen emission into `pen := c.pen`.

The two shapes to design for before writing any of it:

1. **The fold's invariant.** `rowAnsi` threads `(bytes, pen)` and emits
   `penSgr` only when the cell's pen differs, so the invariant is "the
   emulator's pen equals the pen `rowAnsi` is carrying" — which `penSgr_feed`
   maintains at each change and which holds vacuously when there is none.
2. **The step is a glyph *group*, not a cell.** A width-2 cell and its
   width-0 shadow are written by one `print`, so the induction must consume
   two array positions at once there. Stating it over positions rather than
   over a list of cells is what will keep that honest.



## BLOCKER for step 4: marks on a wide cell replay onto its shadow — 2026-08-12

Found while designing step 4's induction, *before* writing it. Measured:

```
markOnWide := screen 12 3 "漢\x1b[2G\u0301"
  live:     cell 0 = 漢 width 2, marks ['́']   |  cell 1 (shadow) marks []
  replayed: cell 0             marks []       |  cell 1 (shadow) marks ['́']
  roundtrips = false
```

**Cause.** `cellText c = utf8 (safeChar c.base) ++ utf8s c.marks`. Printing a
width-2 base advances the cursor by 2, so the marks that follow attach at
`cursor.x - 1`, which is the *shadow*, not the base cell.

**Reachable**: print a wide char (cursor lands at x+2), move the cursor back
one column with `CSI 2 G`, print a combining mark — `print` attaches it at
`cursor.x - 1 = x`, the wide cell itself. Nothing exotic; any editor moving
the cursor into a CJK line can do it.

### Why this blocks step 4 rather than being a side quest

The row induction needs "feeding a cell's bytes reproduces that cell". For a
wide cell with marks that is **false**. The tempting way out is a
`Renderable` clause saying width-2 cells have no marks — but that clause is
*false for reachable states*, so it would be weakening a theorem to hide a
bug, which AGENTS.md explicitly forbids ("restructure code for provability
rather than weakening a theorem"). The emitter has to be fixed first.

### The fix, and the trap in it

Step back one column before the marks, then forward again:

```
utf8 (safeChar c.base) ++ [0x08] ++ utf8s c.marks ++ csiNum 1 0x43   -- BS … CUF
```

**But not unconditionally**, and this is the part that needs care. When a
wide char ends exactly at the right margin (`x + 2 = cols`), `printAdvance`
clamps the cursor to `cols - 1 = x + 1` and sets wrap-pending. The mark
branch then takes `cx = cursor.x` (because pending), which is `x + 1` — the
shadow — and that is *already correct* for a shadow's marks but *wrong* for
the base's. A blind backspace would move it to `x - 1`, i.e. corrupt the
previous cell. So the emitted form depends on the column, which `rowAnsi`
knows (it is folding over positions) but `cellText` does not.

Two candidate shapes, neither verified:

1. Give `cellText` the column and the width (`cellText (atMargin : Bool) c`),
   and have `rowAnsi` pass it. Smallest change; makes `cellText`'s contract
   positional, which the §Replay proofs then have to carry.
2. Emit the base, then an absolute `CHA` (`CSI <x+1> G`) before the marks and
   another after — no dependence on pending or on the margin, at the cost of
   two sequences per marked wide cell. More obviously correct, and absolute
   addressing is what the rest of `restore` already prefers (fix 5's cursor).

I did not implement either: a half-verified change to the repaint path is
exactly what breaks resume for everyone, and the margin case needs its own
fixture before I would trust it. Recorded here so the next session starts
with the finding rather than rediscovering it mid-induction.

### Ledger note

That is **ten** §Replay infidelities: seven from reading the emitter against
the parser (stage 3a), one from stating the cursor claim (fix 5), one from
counting SGR parameters (the 18-parameter pen), and now one from designing
the grid induction. The last three all came from *proving*, and each was
invisible to a fixture suite that was passing. The pattern is worth naming:
every one surfaced at the moment someone had to state precisely what a
function's output means, rather than check an example of it.



## Fix 8 landed: marks on a wide cell — 2026-08-12

The blocker from the previous entry is fixed. `rowAnsi` now carries the
**column** in its fold accumulator (`Bytes × Pen × Nat`), and for a wide cell
with marks emits

```
utf8 (safeChar base) ++ CHA (x+2) ++ utf8s marks ++ CHA (x+3)
```

parking the cursor between glyph and shadow so `print`'s `cursor.x - 1`
lands on the glyph, then moving past the shadow for whatever follows.
Verified: `roundtrips markOnWide` went `false` → `true`, with the mark back
on cell 0 and the shadow empty.

**Absolute `CHA`, not a relative backspace** — and the right margin is why.
When a wide char ends at the last column, `printAdvance` clamps the cursor
and arms wrap-pending; the mark branch then reads `cx = cursor.x`, which is
already the shadow. A backspace there would land a column too far left and
corrupt the *previous* cell. `CHA` is correct in both cases because it
addresses by column and clears pending. Two fixtures: the fix itself, and the
margin case where the correction must not change the outcome.

**Residual limit, documented in `rowAnsi`**: at the right margin, a wide cell
with marks on *both* the glyph and its shadow is not expressible — the
shadow's marks need wrap-pending still armed, and the absolute move that
fixes the glyph's marks clears it. Same shape as the DECOM cursor limit:
named in the emitter rather than papered over.

### Proof repairs the accumulator change forced

`ends_rowAnsi` and `quiet_rowAnsi` fold over the accumulator, so both needed
updating — which is the cost of making the emitter positional, and it was
small because both were already written in the order-robust style
(`repeat' split` + `all_goals first | …`): the new branch just adds
alternatives. Two things bit:

- `ends_utf8s [c.base]` is **not** what the emitter emits — that is
  `utf8 (safeChar c.base)`. Extracted the inline argument from
  `ends_cellText` into `ends_utf8_safe` (and the `Quiet` twin) so both
  callers share it.
- **Association.** The emitted body is one parenthesised chunk appended to
  the accumulator: `acc.fst ++ (((b1++b2)++b3)++b4)`, not
  `((((acc++b1)++b2)++b3)++b4)`. The `Ends.append` term has to mirror that
  exactly. Third time this session that `++` association cost a build; the
  reliable move is to read the *expected* type in the mismatch and bracket to
  match it, rather than reasoning about the emitter's source text.



## Alt-screen bug hunt: 3 bugs, one fixed (fix 9) — 2026-08-12

Delegated an empirical hunt over the alt-screen path (96 probes, 33 failures).
The prediction held: the stages whose *value* claims were unstated are where
the bugs were. Probes left in `/tmp/alt0{1..7}.lean`.

### FIXED — fix 9: the stashed main pen leaked into the alt repaint

Reproducer, one cell: `screen 1 1 "\x1b[7m\x1b[?1049h"` → `roundtrips false`.

`screensAnsi` emits `penSgr mpen` immediately before `?1049h` so the switch
stashes the right pen — correct, and the ordering claim in its doc comment is
sound. But it leaves the *live* pen set to `mpen`, and the alt repaint that
follows is `gridAnsi v.grid`, whose fold seeds "pen already in effect" with
the **default**. `rowAnsi` emits an `SGR` only when a cell's pen differs from
that, so a leading run of default-pen alt cells emitted nothing and inherited
`mpen`. Corruption ran row-major from (0,0) until the first cell whose pen
differed — that cell's `SGR` leads with `0`, which heals the rest.

Severity: for a blank alt screen the *entire* screen replayed in the shell's
pen. A `vim` reattach after `\x1b[41m` came back fully red.

**Fix**: `gridAnsi` now leads with `CSI 0 m`. Establishing the assumption
where it is made, rather than trusting each call site — `restoreBody`'s own
leading reset becomes redundant but harmless, and the alt path stops being a
special case. 33 of the 33 failures in this class are gone; three fixtures
pin it, including the heal-at-first-non-default shape that made it invisible.

**Why the suite missed it**: the pre-existing alt fixture puts `\x1b[33m`
*before* the first alt glyph, so cell (0,0) is non-default and its `SGR`'s
leading `0` masked the leak. Move the colour one glyph later and it fails.
A fixture can pass for the wrong reason; this is the third time that has
bitten in this project.

### NOT FIXED — two grid shapes `rowAnsi` cannot express

Both reachable via `ICH`/`DCH`, both *not* alt-specific — the alt path just
exposes them in `stash.grid`, which nothing else exercises.

- **Wide leading cell in the final column.** `screen 6 2 "ab漢cd\x1b[1;1H\x1b[3@"`
  — `ICH` pushes a wide char's shadow off the row end. `rowAnsi` emits the
  glyph at the last column; on replay `printWideWrap` sees `x+1 ≥ cols` with
  wrap still on (`modesAnsi` sets `?7l` only later) and wraps to the next
  row, then the joining CRLF scrolls at the bottom — the whole grid shifts.
  *Candidate fix*: emit `CSI ?7l` before the repaint and let `modesAnsi`
  restore the real wrap mode after. That also protects the last cell of every
  row from spurious wrap, so it is worth doing on its own merits.
- **Orphaned width-0 cell.** `screen 6 2 "漢ab\x1b[1;1H\x1b[1P"` — `DCH`
  deletes a wide char's leading cell, leaving its shadow. `rowAnsi`'s
  `width == 0` branch emits marks and no glyph, but the live cell occupies a
  column, so everything right of it paints one column left. *Candidate fix*:
  emit a space when a width-0 cell is not preceded by a width-2 cell; the
  fold already carries the column, so it can carry the previous width too.

### NOT FIXED — `cursorAnsi` Nat-truncates under DECOM

`screen 10 6 "\x1b[2;5r\x1b[?6h\x1b[1d"` — with `cursor.y = 0 < top = 1` and
DECOM on, `cursor.y - v.top + 1` is `0 - 1 + 1 = 1` in `Nat`, so it emits row
1, which DECOM resolves back to `top`. Reachable because `VPA` (`CSI d`) sets
`y` with no region clamp, unlike `moveTo`. This is the documented DECOM
residual, but it produces a *silently wrong* address rather than being merely
inexpressible, which is worse. At minimum the emitter should not pretend:
either clamp explicitly and document, or refuse the region-relative form when
`cursor.y < top`.

### What the hunt confirmed about the emitter's own claim

`screensAnsi`'s ordering claim is sound for what it claims: the subagent could
not break `stash.cur`, `stash.pen`, `saved`, region, modes, tabs, charset,
title or pen in the alt path across 63 passing probes. The invariant that
broke was the **unstated** one — `gridAnsi` is only correct when the incoming
live pen is default, and `screensAnsi` was the one call site that deliberately
violated it. Worth generalising: the bugs are not in the claims people wrote
down, they are in the assumptions nobody wrote down.



## Two §Replay fixes are in tension at the right margin — 2026-08-12

Tried the recorded candidate fix for the wide-glyph-in-last-column bug: turn
wrap **off** for the repaint (`?7l` after the clean slate) and let `modesAnsi`
restore it. It works — the `ICH`-pushed wide glyph stops wrapping and the grid
stops shifting — and it **broke fix 8's margin fixture**, which is why that
fixture exists.

**The conflict.** With wrap on, `printAdvance` arms wrap-pending at the
margin, and that pending flag is the *only* way a combining mark can be
attached to the last column: the mark branch reads `cx = cursor.x` when
pending, and `cursor.x - 1` otherwise, and with wrap off the cursor can never
exceed `cols - 1`, so `cx ≤ cols - 2` always. So:

- a wide **glyph** in the last column needs wrap **off** (or it wraps away);
- a **mark** in the last column needs wrap **on** (or it lands one left).

A global switch cannot satisfy both. Resolving it needs per-row wrap control
(turn wrap off for rows with no last-column mark, on for the rest), which is
a real design decision and not a one-liner. Reverted the `?7l`; the reasoning
is now in `restoreBody`'s doc comment so the next attempt starts from it
rather than rediscovering it.

**Kept** the independent half: `modesAnsi` now states wrap
*unconditionally* (`set 7 v.modes.wrap`) instead of only when it is off, so
the repaint no longer depends on the fresh terminal's default being wrap-on.
Self-contained for the same reason fix 9 made `gridAnsi` self-contained.

**What this says about the method.** The fixture that caught it was written
one commit earlier, *for the case the fix was about to break*. Break-verifying
fix 8 at the margin is what made fix 10's failure loud instead of silent —
the argument for pinning the boundary case even when it already passes.

## Answering "how do we catch unwritten assumptions?" — 2026-08-12

All four proving-found bugs are the same shape: **a function correct only
under a precondition on the emulator state it is fed into, which its caller
violated.** `gridAnsi` assumed a default pen (fix 9); `cellText` assumed the
cursor lands one column right (fix 8); `penSgrBody` assumed ≤ 16 parameters;
`cursorAnsi` assumes `cursor.y ≥ top`.

So the detector is a theorem *shape*, and it is mechanical:

    feed (stage v) from ANY quiesced emulator = ⟨stated pure effect⟩

with **no hypotheses on the incoming state beyond quiescence**. A stage that
cannot be stated that way is either not self-contained (make it so — that is
exactly what fix 9 did) or is carrying an unstated precondition. `Ends`/`Quiet`
already have this shape for the *parser*; no stage had it for *values*, which
is precisely where all four bugs were.

Two cheap mechanical nets, neither built yet:

1. **Unclaimed-surface gate.** Every `def` in `Zmx/Core/Render.lean` must be
   named by some theorem in `Theorems/`. Grep-able, same shape as the
   `SHIM_CAP` ratchet. Would have flagged `screensAnsi` as having parser
   claims but no value claim — which is where fix 9 was hiding.
2. **A fuzzer over `roundtrips`.** The delegated hunt hand-fuzzed 96 cases and
   found three bugs in one pass. Random escape-sequence strings + `roundtrips`
   as oracle + shrink on failure is ~30 lines and runs forever. It targets
   this bug class *precisely*, because it explores state combinations nobody
   thought to write down. Highest value-per-line available right now — higher
   than the next proof, on the evidence of this session.



## The fuzzer, and what it found in its first run — 2026-08-12

`Tests/Fuzz.lean`: a pure LCG splices escape-sequence fragments, feeds them,
checks `roundtrips`. A failing *seed* is a bug with a reproducer attached.
Two claims, `native_decide`d so they gate the build: 400 short cases (6
fragments) and 150 long ones (14).

**It found three bugs on the first run**, all in the deep set — which
confirms the reason for having a deep set at all: fix 9 needed a pen *and* an
alt switch *and* a default-pen first cell to show up, so breadth alone would
never have reached it.

**Seed 3 is the important one, because it corrects the exclusion list I had
just written.** I had held out `ICH`/`DCH` as the only way to reach a
width-2 cell in the final column. Wrong: `\x1b[?7l` plus a wide glyph gets
there too. With autowrap off, `printWideWrap` does not pre-wrap, so a wide
glyph printed at the last column writes its base there and its shadow falls
off the row end. **Any program that disables autowrap and prints CJK near the
margin produces the state** — vastly more reachable than the ICH route
implied, and it means the wrap-off idea from the previous entry would not just
conflict with fix 8, it would *manufacture* this shape.

The lesson is about the exclusion list, not the bug: I wrote "these two
mutations are the only route" from reading the code, and a dumb random
generator refuted it in one pass. **An exclusion list justified by reading is
a hypothesis; only a search can support it.**

Seeds 24 and 139 are also wide-glyph cases (charset and mark interactions)
and are not yet narrowed.

Pinned as `failingDeep 150 = [3, 24, 139]` rather than hidden — the
`SHIM_CAP` idiom, so the list can only shrink and any *new* failure breaks
the build. Delete a seed when its fix lands.

**Why this was worth building before the next proof.** One file, ~100 lines,
found three bugs immediately and refuted a stated assumption. On this
session's evidence the ordering is: fuzz first, then prove the things the
fuzzer cannot reach (it can only check states it can *generate*, so it says
nothing about the universally-quantified claims — the two are complements,
not substitutes).



## The unclaimed-surface gate — 2026-08-12

`tests/e2e.sh` step 2b: for every `def` in `Zmx/Core/*.lean`, is its name
mentioned by any theorem in `Theorems/`? A ratchet at `CLAIM_CAP=17`, the
same idiom as `SHIM_CAP` — it may only go down, and raising it is a
deliberate edit meaning "new surface, no claim yet".

Current 17 of 187, and the list is worth reading because it is **not** noise:

    blankRow  chunksOf  ckptIntervalMs  decLine  defaultTabs  erased
    feedBytes  firstDupHost  infoText  isWide  isZeroWidth  outputChunk
    outputMsgs  resizeEffects  resizeRow  rowText  sizeOwner

`isWide`, `isZeroWidth`, `decLine`, `blankRow`, `erased`, `resizeRow` are
exactly the width and grid-shape functions the three open wide-glyph bugs run
through. The gate pointed at the bug cluster without being told where to look
— which is the whole claim for it. `sizeOwner`/`resizeEffects` are the
attach-time size policy that `graphics_test.py` had to pin behaviourally
because no theorem covers it.

Deliberately crude: it asks "is this name mentioned", not "is the right thing
claimed about it". `screensAnsi` would pass despite fix 9 having lived there,
because its *parser* claims mention it. So the gate catches unclaimed
surface, not under-claimed surface. The stronger check is the theorem *shape*
from the previous entry (a stage stated with no hypotheses on the incoming
state), which cannot be grepped — that one needs the claims to exist first.

Cheap enough to be worth it anyway: a name with no theorem at all is a
surface nobody has had to think precisely about, and on this project's record
that is where the bugs are.



## Fix 11: the emulator stops producing unrenderable grids — 2026-08-12

Decision taken: go with **"every reachable state is renderable"** as the
theorem to aim at, which means the *emulator* must not reach shapes the
painter cannot express. First instance landed.

`Vt.printPut` now stores a **blank** when a wide glyph has no room for its
shadow (`w == 2 && x + 1 ≥ cols`). Previously it wrote a width-2 cell in the
final column and silently dropped the shadow — reachable whenever autowrap is
off, since `printWideWrap` only pre-wraps when wrap is on. On replay that
glyph wrapped to the next row and the joining CRLF scrolled the whole grid.
Half a glyph is not displayable anyway, so a blank is what a terminal shows.

**The fuzzer confirmed it**: `failingDeep 150` went `[3, 24, 139]` →
`[24, 139]`, so the pinned list shrank exactly as the ratchet intends. Seeds
24 and 139 remain (wide-glyph cases with charset and mark interactions, not
yet narrowed).

This is the shape the rest of `Renderable` should follow: rather than adding
side conditions to `row_exact`, remove the states. Still to do on the same
principle: `deleteChars`/`insertChars`/`eraseChars`/`resize` must blank a wide
glyph they split, which is the orphaned-width-0-cell bug.

### Cost of the change

Six proofs needed the extra branch, all mechanically: `Good.printPut` and four
`split <;> rfl` field-preservation proofs (`repeat' split` + `all_goals rfl`),
plus `print_narrow`'s and `print_wide`'s `printPut` helpers. `print_wide`'s
helper had to *gain the fit hypothesis* — it was stated `∀ w`, which is no
longer true, and that is the change telling the truth: a wide glyph only
writes two cells when there is room for two.

`repeat' split <;> rfl` does **not** parse as intended — the `<;>` binds
inside the `repeat'`. Use two lines: `repeat' split` then `all_goals rfl`.
That is why the house style spells it that way.


## §Status: the seven states, and a theorem that they partition — 2026-08-12

Settled the listing-status design and gave it a Core module plus proofs.
The design rule that produced the set, stated once because it resolved four
separate arguments: **two states share a glyph only when they call for the
same action.** Merged under it -- bell into wants-you (both "go look"),
waiting-at-prompt into wants-you (same observation without OSC 133, same
response with it, which takes the one expensive feature off the critical
path), never-looked into wants-you, and busy into unknown (both "we cannot
tell you the truth about this row"). Kept distinct where the response
differs: exited-ok vs exited-bad, idle vs wants-you.

Final set, priority order: \`?\` unknown, \`!\` exited-bad, \`✓\` exited-ok,
\`~\` resumable, \`⣿\` wants-you, \`⣷\` working, \`⣀\` idle. Plus a plain
\`Nat\` client count in its own column, which is what the whole third
"modifier axis" collapsed to.

Two corrections I had to make along the way, both from the user pushing:
\`x\` for a successful exit was carrying the wrong meaning (\`✓\` is right,
\`!\` was already the failure glyph), and \`⣀\` idle vs \`…\` busy were
near-identical low dots meaning opposite things -- which is what forced the
busy/unknown merge.

### The theorem

A legend is a claim and can be wrong three ways: two different rows show the
same glyph, a row matches no glyph, or a glyph is unreachable. \`Theorems/
Status.lean\` rules out all three -- \`cover\`, \`disjoint\`,
\`classify_sound\`/\`classify_unique\`, \`reachable\`.

The load-bearing choice is that \`Is\` (the legend as predicates) is written
**independently of \`classify\`'s cascade**. If \`Is\` were the guards with
earlier branches negated, cover and disjointness would be tautologies and the
theorems would say nothing. As written, \`classify_sound\` is a real claim
about the cascade, and mis-ordering two guards breaks it -- which is the
break-verification: swapping the \`fresh\` and \`unseen\` tests fails 6 proofs.

\`icon_injective\` is the one I would not have thought to write without the
history: an earlier draft reused \`!\` for both a bell and a failed exit, and
this theorem rejects exactly that. Break-verified by pointing two states at
\`?\` -- 3 proofs fail. It makes the design rule enforceable: a future merge
has to delete a state, not quietly overload a symbol.

\`name_clean\` states the porcelain invariant that came out of the JSON
discussion: no field carries a tab or newline, which is what makes
tab-separated rows unambiguous without an escaping pass. That is the theorem
JSON would have discharged by construction -- worth having explicitly since
we chose TSV.

Not built: the runtime side. \`classify\` needs \`lastOutput\` and
\`lastDetach\` in the daemon (one struct change, two assignments in the poll
loop) and wiring into \`Listing\`. Five of the seven states are computable
from data that already exists. Known limit to document when it lands:
\`lastDetach\` is per-daemon, not per-viewer, so with two people on one
session \`⣿\` means "unread by whoever looked last".



## The unread counter, per-session not per-client — 2026-08-12

Landed `outSeq`/`lookSeq` in `Session.State`, plus `unseen` and `behind`.
`outSeq` bumps per pty-output event; `lookSeq` catches up on attach and on any
output that arrives *while somebody is attached*. So `unseen` means "output
arrived while nobody was watching" — a property of the **session**.

The user killed my first design and was right: keying read state to a viewer
id would allocate durable, checkpoint-persisted state for a stranger who
connects once, and would stop a listing row being a fact about the session.
"Last looked" is a session *event* (attach, or output-while-attached), not a
viewer attribute. Once it is an event, two `Nat`s carry it.

I also overstated the case for counters earlier: I claimed a timestamp in
`State` would break A2, because `step` must be a function of the trace. Not
so — `Event` already has `.tick (nowMs)` and `State` already holds
`lastCkptMs`, so time is threaded through the *event list* and timestamps were
expressible all along. The counter still wins, for weaker reasons: `unseen`
stays exact and needs no tick to be correct, and `outSeq - lookSeq` gives
"behind by N" free where a `Bool` throws it away.

### The implementation lesson: keep the conditional out of the handler

Three attempts. Putting `if hadAttached then … else …` in `step`'s `.closed`
branch broke four proofs, because `step`'s **branch structure** is what a
dozen proofs `split` on. Hiding it in a `markLooked` helper did not help
either — `(markLooked s id).dropClient id` is no longer `rfl`-transparent for
field preservation.

What worked: put the conditional in a **field value**, not a branch.

    outSeq  := s.outSeq + 1,
    lookSeq := if s.clients.any (·.attached) then s.outSeq + 1 else s.lookSeq

`step`'s branch shape is untouched, so every existing `split`-based proof
still applies, and exactly one theorem statement had to change
(`step_ptyOut_no_clients`, which now records the counter bump — honest, since
output with no clients advancing the counter *is* the unread mechanism).
Worth generalising: **in a state machine whose proofs case-split on the
handler, new behaviour is cheapest as data inside an existing branch.**

### Scope of what is proved

`outSeq_ptyOut`; `unseen_ptyOut` (output while attached is seen as it happens,
with nobody attached it is not — the whole `wantsYou` mechanism); and
`lookSeq_le_ptyOut` (the mark never overtakes the counter, so `behind` never
underflows to a misleading zero).

**Not proved, and named rather than asserted**: the `∀ ev` monotonicity
versions. They need an induction showing `feedMsgs` preserves `outSeq` —
client messages never touch it, but the `.bytes` case folds a whole message
list and is opaque to arithmetic. `onMsg_seq` then `feedMsgs_seq` by fold
induction is the shape; two lemmas, next increment. I cut them rather than
leave a `sorry`, and `unseen_ptyOut` carries `lookSeq ≤ outSeq` as a
hypothesis where the trace theorem would have supplied it.



## All seven states wired — 2026-08-12

Daemon side: `freshFlag`/`tickOutSeq` in `State`, refreshed on `.tick` by
comparing `outSeq` across ticks — freshness from a **counter comparison**, not
a stored timestamp, so the core still needs no clock arithmetic. `infoText`
now reports `unseen`, `fresh`, `behind`, and `exit` when the child is gone.

Client side: `Listing.rowStatus` builds `Status.Obs` from two sources — the
daemon's reply for activity, and the caller for what only it can know (socket
present, daemon answered, checkpoint loads). That split is what extends §Row
to the status column, and `Theorems/Listing.lean` now states it:
`rowStatus_unanswered` (a live socket that did not answer is `unknown`
whatever the reply said), `rowStatus_resumable`, `rowStatus_gone`,
`flag_absent` (a missing flag reads `false`, so an omission cannot make a row
look fresher than it is).

### A bug the theorem found, in the theorem's own subject

`rowStatus_resumable` would not close by `rfl`, and the reason was real:
`classify` tests `exit` **before** `daemonUp`, so an `exit` key in a reply
made a socket-less row classify as a completed run. A peer crafting `exit 0`
could have shown a dead session as finished-successfully. Fixed where it
belongs — `rowStatus` only reads `exit` when a socket is present, since
without a daemon there is nobody who could have observed the child. Then the
three theorems are `rfl`.

That is the fifth bug found by stating a claim rather than by testing, and it
is the first one *outside* the emitter. The pattern holds exactly: the claim
was "a reply cannot lie about a row's health", writing it down forced the
question "which fields come from the reply?", and one of them should not have.

### The handler-shape lesson, twice more

Adding the tick refresh as a `let` before the `if` hid the `if` from the two
proofs that `split` on that handler. Putting it in **both branches as field
values** kept the shape and cost one proof line (`.tick`'s second bullet,
which now needs the same conjunction as the first instead of a bare
hypothesis). Same lesson as the `.ptyOut` counter: in a state machine whose
proofs case-split on the handler, new behaviour is cheapest as data inside an
existing branch — and a `let` in front of the branch is the specific thing to
avoid.

Remaining before this ships as a visible column: `Cli` rendering (icon +
client count) and a live test. The pure and proved parts are done — all seven
states are now computable from data that exists.



## The status column ships — 2026-08-12

`linger ls` renders one glyph per row plus a client count; `--porcelain` gains
a `status` field. `Status.ofName` parses it back, with `ofName_name` proving
the two columns can never disagree about a row. Live test as e2e step 10
(seven live suites now): attach marks a session seen, output while away marks
it unread, `behind` counts, and the human listing shows the glyph.

Verified by hand first, which is how the next finding surfaced:

    ⣿ demo   pid 141908  /…/fish
    unseen true · fresh false · behind 2 · status wants-you

### A gap the *existing* test caught, which is the point of it

`robust_test`'s §Row case asserted the exact human line for a busy daemon, so
adding the glyph broke it — expected. But the value it broke *to* was `⣀`
(idle), not `?` (unknown). A busy daemon connects and answers with an empty
reply, and I had hardcoded `answered := true` at the call site, so "did not
answer" could never arise: a session too busy to report would have been shown
as a healthy idle one.

Fixed with `Listing.answered info`, which asks whether the reply carried
`pid`/`cmd` at all — the fields a real reply always has. Now a busy row reads
`? busy (busy)`, and `answered_nil` / `rowStatus_empty_reply` state it.

The test's assertion is now **stronger** than before: it pins §Row (the row
keeps its real name) *and* that an unreadable row is not reported as healthy.
Worth noting the shape — an exact-output assertion that looks brittle earned
its keep, because "the format changed" and "the meaning changed" arrived
together and only the exact assertion could tell them apart. If it had matched
loosely on `busy` being present, the idle-vs-unknown bug would have shipped.

That is the sixth bug found by stating a claim, and the second outside the
emitter. Both of those came from wiring a *proved* core into the runtime,
where the mismatch is between what the theorem assumes and what the call site
passes — `rowStatus`'s `answered` parameter was proved correct and then fed a
constant.

### Left for later

`⣷ working` has the tick interval as its granularity, so it is only as
responsive as the poll period — check that is what it should be keyed to
before advertising it. And `⣿` means "output since *anyone* last looked"
(the deliberate per-session choice); that belongs in the README when this is
documented for users.



## Fixing the failure mode, not watching for it — 2026-08-12

The bug from the previous entry was: a proved function, fed a constant at the
call site, so a case the theorem quantified over became unreachable.
`rowStatus (socketPresent answered ckptLoadable : Bool)` got a literal `true`
for `answered`, and "the daemon did not answer" could never happen — a busy
session listed as healthy-idle while the theorem about it stayed true.

Detecting that class is awkward (grep for literal booleans at call sites?).
**Removing it is easy**: replace the booleans a caller has to get right with a
sum type that carries the case.

```lean
inductive Row
  | live (info : List (String × String))   -- a socket accepted; info may be empty
  | stale                                   -- no socket, a checkpoint file exists
  | broken                                  -- no socket, the checkpoint won't load
  | remote (live : Bool)                    -- from a peer's porcelain
```

Each constructor carries exactly the facts its case has, so **there is no
argument left to pass wrongly**. The three call sites became `.live info`,
`.stale`, `.remote rlive` — no literals at all. Boolean-blindness was the
underlying smell; the constant was the symptom.

A second thing fell out of the refactor that the booleans had hidden: `Cli`
lists checkpoint *names* without probing them, so `unrestorable` was never
produced. Under the old signature that was a `true` passed for
`ckptLoadable`; now it is an **unused `.broken` constructor**, which is visible
in the source instead of buried in an argument. That is the general benefit —
a sum type makes an unhandled case look unhandled.

### The two flagged items, closed

- **`⣷ working` granularity**: fine. `.tick` fires every poll round
  (`Daemon.lean:260`, after `pump`), not on the checkpoint schedule, so
  freshness is poll-period granular. `ckptIntervalMs = 60000` is *not* the
  granularity — worth having checked, since keying it to the checkpoint clock
  would have made "right now" mean "within a minute".
- **`⣿` semantics documented**: README gains a status table, with both caveats
  stated — that it means "since *anyone* last looked" (a property of the
  session, not of a viewer), and that `⣷` is only as responsive as the poll
  round.

Remote rows are the honest weak spot and are labelled as such in `Row.remote`:
a peer forwards liveness but not activity, so `⣀` there means "alive, activity
unknown". The fix is to forward the peer's own `status` field — `ofName` exists
for exactly that and `ofName_name` already proves the round trip — but it needs
`listRemote` extended, so it is named rather than half-done.



## Remote rows: `?`, and then better than `?` — 2026-08-12

The user caught me breaking my own rule. I had a live remote row report
`⣀ idle` on the strength of liveness alone — but `idle` asserts "nothing since
it was last watched", which is a claim about activity we never read. The rule
established two entries earlier is that **a glyph is the most specific *true*
statement**, and by that rule the answer was `?`.

Better than relabelling it: the peer's porcelain now *emits* `status`, so parse
it. `RemoteRow.status` carries the peer's own name (scrubbed like any other
display field), `Row.remote` takes it, and `Status.ofName` interprets it —
total, mapping anything unrecognised, including an absent field from an older
peer, to `unknown`. So the weak spot is gone rather than documented:

- a peer that reports a status is taken at its word (`rowStatus_remote_reported`,
  via `ofName_name` — it is the authority on its own session);
- a peer that reports nothing readable is `unknown`
  (`rowStatus_remote_unreadable`, `rowStatus_remote_absent`), never `idle`.

`ofName`'s totality is doing real work here: it is what makes "a peer cannot
claim a state we could not read" true by construction rather than by a check
someone has to remember. I wrote it as a convenience for parsing our own
porcelain back; it turned out to be the §Remote safety property.

Also worth noting how the fix arrived: I had *labelled* the weak spot in a doc
comment and moved on, which felt like diligence. It was not — the label was
accurate and the behaviour was still wrong. A known-wrong behaviour with a
comment explaining it is still known-wrong; the comment only makes it survivable.


## recipes/lzs.fish notes — 2025-06-14

New recipe: a live status board (`linger ls -r` on a loop) for the one
case the status column is *for*. Sharpened while answering "can kitty
show session status in a tab title?" — it can (OSC 2), and it would be
useless: a session with a tab open is one you can already see. Status is
information about sessions you are **not** attached to, so it belongs in
`ls`, and the gap versus a remote multiplexer is not the glyph but
tmux's *in-band window list* — state for windows you aren't looking at,
inside one connection. `lzs` fills that without windows/panes (settled
non-goal): one small tab, N sessions reported, terminal still owns
composition.

Two environment facts, both measured, one of which killed an assumed bug:

* fish `--argument-names x` with the arg omitted leaves `x` an **empty
  list** (`count $x` = 0), not a one-element empty string — so
  `linger ls -r $hosts` collapses to a bare `-r` and reads
  `~/.config/linger/remotes`. My first check simulated this with
  `set -l hosts ""`, which is a *one-element* list containing "" and
  expands to `''`; the simulation disagreed with the real mechanism.
  Reproducing the actual construct is worth the extra command.
* That sim implied `lzs '' 2` (default hosts, custom interval) would
  `ssh` to an empty hostname. It does not: `resolveRemotes` already
  filters `!h.isEmpty && !h.startsWith "#"`, so `ls -r ''` is local-only,
  verified directly. Negative result — no guard needed in the recipe, and
  the escape hatch is documented in its comment.

Break-verify: not applicable (no theorem, no runtime change — recipes and
docs only, so `e2e.sh` was not the gate here). Behaviour checked against
the real binary: `linger run board-demo sleep 300`, then three redraws
observed under `timeout 3 fish -c '… lzs "" 1'` with `cat -v` confirming
`ESC[H ESC[J ESC[3J` before each table and the `⣿` row present; session
killed afterwards.


## recipes/lzh.fish notes — 2025-06-14

"No prefix key" (the reason ctrl-\ is a single action, not a leader) has
a real cost: no `prefix + s` to switch sessions. Closed it outside the
binary instead of reopening the decision — wrap `attach` in a loop, so
detach falls into the picker and you land in the next session. ctrl-\
becomes a switch key with no keybinding, no leader, and no new syscall.
Falls out of a property already true: detach returns control to the
caller, so the caller can decide what "detach" means. Worth remembering
as a shape — in-session verbs can live in the *wrapper* rather than in a
key vocabulary inside the client.

Two properties it gets for free: rows are `name@host` (`ls -r`), so the
switcher spans machines, which a tmux session list cannot — its server
is per-host; and fzf's nonzero exit on Esc is the loop's only exit, so
quitting the picker quits the wrapper.

Verified `set x (cmd)` propagates the substitution's status in fish
(`set -l x (false)` → `$status` 1). `lz.fish` already depended on this
via `and`; now a `break` does, so it was worth confirming rather than
inheriting. Control flow exercised with stubbed `linger`/`fzf` (a real
`attach` wants a tty): attach → pick `b@gpu2` → attach → Esc(130) →
clean exit 0; bare `lzh` starts at the picker; Esc with nothing to pick
exits 0 without attaching.

## Step 1 notes — 2026-08-13T19:04:22Z

Landed the pure bounded terminal mediator in `Zmx/Core/Terminal.lean` plus
`Theorems/Terminal.lean` and `Tests/Terminal.lean`. `Terminal.feed` feeds `Vt`
byte-by-byte, then classifies the same byte for ownership, so CPR samples the
cursor at the query's stream position. The API returns final VT/scanner plus
visible bytes and the ordered reply stream; `finish` returns only pending
presentation bytes and ground, so an EOF flush cannot feed `Vt` twice.

Scanner shape: CSI and OSC retain reversed candidates under 128/256-byte caps;
DCS buffers only after exact `+q`/`$q` prefixes under the 2048-byte cap. APC,
SOS, PM, rejected DCS (including sixel `DCS q`), and over-cap candidates enter
payload-free passthrough states. Per-byte feed uses a bounded left append
(normally a singleton), so megabyte graphics are linear rather than repeated
whole-buffer appends.

Proved: full-result `feed_append` (VT, scanner, visible concatenation, reply
concatenation); exact `Vt.feed` projection; one-step and arbitrary-stream
scanner bounds; exact CSI/OSC profile classification; exact arbitrary-payload
XTGETTCAP/DECRQSS negatives; owned exclusion versus unowned exact release;
CPR origin-row cases; `finish_exact`; and quantified APC/sixel passthrough for
all payloads without their own `ESC \\` terminator. Twenty owned request forms
(accepted aliases and OSC terminators included) pass at every byte split;
every proper owned-query prefix passes the EOF flush check. Cap overflow and
query-looking bytes inside >cap graphics are concrete regressions.

Fixed the pre-existing parser bug: final `u` restores only when `s.priv == 0`.
Private `CSI ? u` is state-neutral; public ANSI `CSI u` still restores cursor
and pen. General dispatch theorems and a parser-level fixture cover both.

Break verification (all same-shape value changes, all reverted):
- inverted the private/public `u` guard (`== 0` → `!= 0`): both dispatch
  theorems and the concrete VT fixture failed; the existing replay fuzzer also
  changed its pinned failure set;
- changed the short DA1 recognizer final from `c` to `d`: `classifyCsi_da1`
  became unprovable and the all-owned/all-splits test failed;
- changed APC's string-introducer byte from `_` to `` ` ``: the quantified
  `apc_passthrough` theorem failed and the concrete APC payload test detected
  the embedded DA1 being consumed.

Gate after restoration: `./lake build Theorems Tests` green and warning-free.
Hand-off: Step 2 should store exactly one `Terminal.Scan`, mediate `.ptyOut`
once, write `Result.replies` once via `Effect.writePty`, broadcast only
`Result.visible`, and flush `finish` before child-exit notifications/closes.

## Step 2 notes — 2026-08-13T19:20:34Z

Integrated the pure terminal mediator as the PTY-facing owner. `Session.State`
now carries one `Terminal.Scan`; `.ptyOut` calls `Terminal.feed` once, writes
its ordered replies once, and broadcasts only visible bytes. Empty visible
output produces no output frame. `.childExited` calls `Terminal.finish`, resets
the scanner, broadcasts any pending prefix before exit notifications and
closes, then drops the checkpoint and exits. `Daemon.serve` gives every child
the fixed profile `TERM=xterm-256color`, `TERM_PROGRAM=linger`, and
`TERM_PROGRAM_VERSION=0.1.0`; no mediator or runtime branch inspects the child
executable, argv, shell, or attached terminal type.

Proved scanner boundedness through `onMsg`, `step`, and arbitrary `run` traces;
exact `.ptyOut` VT/scanner/effect projections; roster-independent reply
selection; and exact EOF scanner/effect ordering. Session fixtures cover
zero/one/two attached clients, a split request, hidden owned bytes, and
flush-before-exit ordering. The generic raw-PTY live probe confirms one exact
DA1 reply before any attach and with one/two clients, ordinary presentation
output, parent-`TERM` independence, and the fixed three-variable child profile;
fish remains only a detached-command regression.

Break verification (all restored):
- Changed reply emission from `r.replies.isEmpty` to `s.clients.isEmpty`.
  Session effect theorems and concrete ownership tests failed: detached replies
  disappeared and attached non-query output could generate an empty PTY write.
- Reordered child-exit effects from `flush ++ notify` to `notify ++ flush`.
  `step_childExited_effects` ceased to be definitional and the exact Session
  exit-order fixture failed, proving pending presentation bytes must precede
  exit notification. Restoring `flush ++ notify` made both green.
- Changed the child profile from `TERM=xterm-256color` to `TERM=screen` and
  rebuilt `linger`. The raw-PTY suite failed exactly the stable-profile check
  for zero, one, and two clients while all DA1 progress/reply checks still
  passed. Restoring `xterm-256color` returned all ten probe checks to green.

Final Step 2 gate after restoration: `./lake build Theorems Tests`,
`python3 tests/terminal_query_test.py`, `python3 tests/graphics_test.py`, and
`./tests/e2e.sh` all pass warning-free. The source-claim ratchet remains 17,
the shim ratchet did not rise, and all eight live suites are green.


## Step 3 notes, part 1 — the emulator stops producing unrenderable grids — 2026-08-14T02:41:36Z

The two deep fuzz seeds pinned as failing (24 and 139) were **the same bug**, and
not the one the exclusion list described. Narrowed by evaluating both cases
cell by cell rather than reasoning from the code:

```
idx 24  6x3  …漢 at cols 1-2, then CUP 1;1, then é A
  live y0: (é,w1,m[301]) (A,w1) (sp,w0) …      ← orphaned shadow at col 2
  rep  y0: (é,w1,m[301]) (A,w1) (sp,w1) …
idx 139 4x2  漢́ at cols 0-1, then … b at col 0
  live y0: (b,w1) (sp,w0,m[301]) …             ← orphan carries the mark
  rep  y0: (b,w1,m[301]) (sp,w1) …             ← mark re-attached to the wrong cell
```

**Printing a narrow glyph over a wide base orphans that base's shadow.** No
`ICH`/`DCH` involved — any redraw over CJK text does it, which makes the four
held-out `knownGap` mutations a special case of a much more reachable bug. The
exclusion list's stated cause was wrong for the second time (fix 11 refuted it
once already); "reachable only via X" from reading the code keeps being a
hypothesis a search refutes.

### What landed

Repair at the mutation, generalizing fix 11 from printing to every row write:
`Row.halfPair` (is this column half a pair?), `Row.mendAt` (blank a half,
keeping its background), `Row.mend` (sweep a row), `Vt.mendAt`/`mendAround`
(the O(1) pair a print needs)/`mendRow`. Call sites: `printPut` mends the two
columns a write can half-orphan; `printShift`, `eraseRowSpan`, `deleteChars`,
`insertChars` and `resizeRow` mend the row. `Vt.printPut`'s fix-11 branch stays.

Two other normalizations, both of which remove a case rather than handle it:

* **Marks attach to a wide glyph's base, never its shadow** (`Vt.printMark`).
  A shadow is a blank column a repaint re-creates from its base, so a mark
  parked there cannot survive `rowAnsi`; `rowText` skipped it outright, so it
  never appeared in `linger history` either. This **retires the documented
  right-margin limit** ("a wide cell with marks on both glyph and shadow is not
  expressible"): at the margin only an armed wrap-pending flag can address the
  last column, and no absolute cursor move reproduces that — so the fix is to
  keep marks off shadows, not to address them.
* **C0/DEL become U+FFFD on store** (`Vt.printableChar`). `Render.safeChar`
  already substituted on emit, so a stored control byte made live and replayed
  screens differ. DEL arrives as itself and an overlong UTF-8 sequence decodes
  to a C0, so both are reachable. `safeChar` stays as the emit-side guard — it
  still has work to do for a decoded checkpoint.

### A latent emitter bug the mark change exposed

`rowAnsi`'s fold carries a **cell index**, and a width-2 base advanced it by two
while its shadow advanced it by one — three per pair. The `CHA` emitted for the
*second* marked wide glyph in a row therefore addressed one column too far
right, the rest of the row drifted, and its last cell wrapped into a line feed
that scrolled the whole grid. Invisible before because marks used to land on
shadows, leaving wide bases mark-free and that branch nearly dead code; with
marks on the base it fires for an ordinary `漢`+mark, and the fuzzer found it at
two independent seeds immediately. `Zmx/Core/Render.lean` and
`Tests/Render.lean` were added to Step 3's `Writes` for this (spec amended
first) — the repair belongs with the change that exposed it.

### Gate

`knownGap = #[]` with all four former entries in `frags`; `failing 400 = []`;
`failingDeep 150 = []`. Out of band, 4600 further cases across four
generator/depth combinations (3000 x6, 800 x14, 400 x24, 400 x18) are also
clean, so the repair generalizes rather than relocating the failure. Fixtures
added for every removed failure plus the overprint, mirror-overprint, partial
erase, insert-shift, resize-truncation, DEL and overlong-C0 cases.
`CLAIM_CAP` **lowered 17 → 16** (`erased` is now claimed).

### Proof work

`mend_halfPair`: after `Row.mend`, no column of any row is a half pair — the
postcondition `Renderable` will rest on. Ladder: `halfPair_eq_false_iff` (the
predicate in `Prop`, where pair reasoning is legible), `halfPair_of_width_one`,
`mendAt_ne`/`mendAt_self_of_*`, `halfPair_mendAt_lt`/`_self`, `mendUpto_spec`
(the sweep induction via `List.range_succ`), `size_mend`.

`Vt.printChar` and `Vt.printMark` were extracted as named stages because
`split` picks the first splittable term it finds: with the charset test and the
control test inline in `print`'s width scrutinee, `Good.print` and the four
invariance layers had to peel two `if`s they did not care about, and
`Good.printPut` timed out at `whnf` descending into the repair's `getD` chains.
Frames for `mendAt`/`mendAround`/`mendRow`/`printMark` reduce each layer to one
`rw`. `getD_set_self`/`getD_set_ne` moved from private copies in
`Theorems/Render.lean` up to `Theorems/Vt.lean`.

`Vt.mendAround` gained an `x == 0` guard. Not a bounds nicety: `x - 1` collapses
to `x` there, so the repair would read the column the write just filled, and the
guard is what makes `getCell_mendAround` provable. Its hypothesis is stated
`x + 1 ≠ xw`, not `x ≠ xw - 1`, because truncated subtraction makes the latter
false at column 0 — exactly where the repair is skipped.

`print_narrow_frame` had to weaken: a narrow glyph now touches its own cell and
possibly the two beside it, since the repair blanks an orphan. The sharper
"touches one cell" form needs the row to be pair-consistent, which is
`Renderable`'s job, so it is stated there rather than assumed here.

### Break verification

| break | result | verdict |
|---|---|---|
| shadow guard reads `width != 1` instead of `!= 2` | 7+ replay fixtures fail; `halfPair_eq_false_iff` type-mismatches | **real** (fixtures), weak (theorem — the lemma restates the definition) |
| a shadow looks *right* for its base (`x + 1`) | same shape | weak — the characterization lemma names the offset |
| repair writes `Cell.shadow` instead of a blank | type mismatch | weak — the lemma names the written value |
| sweep stops one column short (`range (size - 1)`) | `ICH`, insert-mode and resize-truncation fixtures fail; `mend_halfPair` unprovable | **real** |

**Negative result, and it corrected a comment I had just written.** Sweeping
right to left (`mendAt (size - 1 - x)`) passes every fixture and the entire fuzz
corpus. The sweep order is genuinely unobservable: `mendAt` blanks a column only
when its partner is *already* gone — a shadow with a width-2 base on its left is
left alone, and a base with a width-0 shadow on its right is left alone — so a
blank can never create a new half pair and there is no cascade to order. My
`Row.mend` comment had claimed left-to-right was what made one pass enough;
that justification was wrong and is corrected in both the code and
`halfPair_mendAt_lt`. Measuring the mutation is what caught it.

### Deliberately not done, with the measurement behind it

Using `Row.mend` on the print path too would make every mutation end in a
whole-row sweep, so `Renderable`'s pair half would follow from `mend_halfPair`
uniformly with no local index reasoning — a large proof saving. Rejected:
`putCell` is O(1) amortized (Lean updates a uniquely-referenced array in place),
while a row sweep is O(cols) *per glyph*, so this would put an asymptotic
regression on the hottest path in the daemon to save proof work. `mendAround`
stays O(1) and `printPut` keeps its bounded case analysis. (An attempt to
measure the crossover with `#eval` timings was inconclusive — a closed payload
term is constant-folded before the first clock reading, and even a
clock-seeded payload reported 0 ms for 3.2 MB, so the numbers are not
trustworthy and the argument above rests on the complexity, not on them.)

Hand-off: `Renderable`/`LiveReachableVt`/`renderable_of_liveReachable` and the
Session trace lift are the rest of Step 3. `mend_halfPair` discharges the pair
clause for every row-sweeping mutation; `printPut` is the one site needing the
window argument (changed columns are `x`, `x+1` from the write and `x-1`,
`x+w` from the repair, so only `halfPair` at `x-2 … x+w+1` can move).


## Step 3 notes, part 2 — correction, §Renderable, and a review that earned its keep — 2026-08-14T03:43:17Z

### Correction to part 1 (read that entry with this one)

Part 1 describes a design the tree does **not** ship. It recorded `Vt.mendAround`
— an O(1) repair of the two columns beside a write — and a "deliberately not
done" decision rejecting whole-row mending on the print path as an *asymptotic*
regression. Both are wrong, and the reasoning behind the rejection was the wrong
part:

`Vt.putCell` reads its row out of the grid before writing it back, so the row is
shared and the inner `setIfInBounds` **copies it**. Printing was already O(cols)
per glyph. A whole-row sweep is therefore a constant factor over a copy that
already happens, not a new asymptotic class — so the trade I had "measured" did
not exist. `Vt.mendAround` is gone; `printPut` and `printMark` both end in
`Vt.mendRow`, and every row mutation now ends in the same place.

What that bought is the reason to prefer it: the pair invariant is established
**once**, by `mend_pairOk`, for any input row at all. The window design would
have needed a bounded case analysis at every write site (changed columns `x`,
`x+1` from the write and `x-1`, `x+w` from the repair, so `halfPair` moves at
`x-2 … x+w+1`) and would have had to be redone for each mutation. This is the
AGENTS.md rule working as intended: restructure the code for provability rather
than weaken the theorem — and my part-1 note had it backwards.

Part 1's hand-off also lists `Renderable` as remaining; the definitions landed
(below). Its break-verification table stands as recorded.

### §Renderable landed, partly

`Row.mendAt` now also **canonicalizes** a whole pair's shadow, so a shadow holds
exactly what repainting its base re-creates and nothing of its own. That upgrade
is what makes the sweep establish the *full* pair rule rather than just widths:
`PairOk` says a base keeps a canonical shadow and a shadow keeps its base, and
`mend_pairOk` proves it for every column of any mended row.

Landed: `CellOk`/`RowOk`/`GridOk`/`Renderable`, `renderable_init`,
`mend_pairOk`, `mend_keeps_narrow`/`mend_keeps_wide` (the sweep is the identity
on a well-formed write — what lets a repaint read back what it painted),
`print_narrow_eq`/`print_wide_eq`/`print_mark_eq` (print reduced to its write,
so the per-glyph theorems never walk five stages), the write-then-repair
read-back layer, and `GridOkExcept` plus the fold lemmas for the remaining rung.

**Not landed**: `renderable_step`, and therefore `LiveReachableVt` and
`renderable_of_liveReachable`. Stopped deliberately rather than half-built. The
shape of what remains: `renderable_congr` discharges every operation that leaves
`grid`/`cols`/`rows`/`altGrid` alone (most of `csiDispatch`) from its existing
frame; the dozen that write cells go `GridOk → GridOkExcept y → write → mendRow`
via `gridOkExcept_set`/`gridOkExcept_replace`/`gridOk_of_except`; `resize` and
the alt swap need `Array.extract`/append cell lemmas; `RIS` reuses
`renderable_init` under `Good`'s `clampDim` identity.

**Step 4 (`restore_grid`) was not started, on a scope check rather than a
whim**: it is the row/grid replay induction — `rowAnsi`'s combined pen-and-column
fold, `joinCRLF` and its scroll interaction, `screensAnsi`'s alt switch, the
wide-with-marks `CHA` moves — comparable in size to the whole §Replay parser
half, which took several sessions. Step 3 removed the *side conditions* it would
have needed on the emulator side; the induction itself is untouched.

### The review found a bug in my own documentation, and two vacuous theorems

Ran the semantic reviewer on the working tree. Verdict NEEDS_CHANGES, 10
findings, **none in runtime behavior** — every defect was in a claim. Worth
recording because two of them are the failure mode this project keeps hitting: a
theorem that cannot fail.

1. **I destroyed a THEOREMS.md row.** Inserting §Renderable ate `§Status`'s row
   prefix and glued its body on, giving a 7-cell row where every other row has 4
   — so a shipped, proved family silently stopped being documented. A pipe count
   per line would have caught it instantly. Restored.
2. **`ptyOut_reply_roster_independent` could not fail.** Its conclusion mentioned
   only `Terminal.feed s.vt s.scan chunk`, which cannot depend on the roster *by
   construction*, so the theorem stayed green when `.ptyOut` was mutated to gate
   replies on `s.clients` — the exact regression it was cited for in THEOREMS.md.
   Restated over `(step s (.ptyOut chunk)).2`, filtered to the child writes, with
   a new `broadcast_no_writePty` doing the real work. **Break-verified after the
   fix**: the roster-gating mutation now fails it (plus two other theorems).
   This is the third time in this project that a theorem about a *helper* has
   been mistaken for a theorem about the *machine*; the rule is that a claim
   about `step` must mention `step`.
3. **`finish_exact` is `rfl` on its own definition** and was cited for "released
   once at EOF and never re-fed to the VT" — neither of which it states. The
   citation now points at `step_childExited_effects`, which is `rfl` against the
   literal effect list and does carry the ordering.
4. **The §Terminal row over-credited passthrough**: `apc_passthrough`/
   `sixel_passthrough` cover two protocols under an unmentioned `StFree`
   hypothesis, while ordinary-ANSI and vendor-query passthrough rest on fixtures.
   The row now says exactly that, and names the general conservation lemma as not
   yet stated. The reviewer also supplied its inductive step: every `Scan.step`
   transition satisfies `pending ++ [b] = visible ++ pending'` (or `= seq` on
   completion), including the two that look like drops (`.csi`/`.csiPass` on ESC
   retain the byte as `.esc`'s pending).

Also fixed: `printMark`'s `cx0 - 1` is now guarded by `cx0 != 0` — a width-0 cell
in column 0 is unreachable but `renderable_step` does not yet *prove* it, and the
failure mode was silent (mark parked on column 0, then blanked by the repair);
`broadcast`'s empty guard is documented and pinned by `broadcast_empty`
(`chunksOf n [] = [[]]`, so without it every owned query would push a zero-length
frame to every client — a state unreachable before the mediator existed);
`Tests/Fuzz.lean`'s header, which still claimed a hold-out list that is now
empty; the stale window language in `print_narrow_frame` and a fixture comment;
and `rowAnsi`'s width-0 comment, which said a shadow paints nothing while the
branch still emits marks found there (dead for live grids, defensive for a
decoded checkpoint).

Gate after all fixes: `./lake build`, `./lake build Theorems Tests`, and
`./tests/e2e.sh` green and warning-free, `CLAIM_CAP` 16, `git diff --check`
clean. The review doc is in `semantic-review/` and is a transient artifact, not a
deliverable.

Hand-off: `specs/terminal-contract.md` stays **active** with per-step status
written in it; it is deliberately *not* archived, because Steps 3–5 exit criteria
are unmet and archiving with unmet criteria is the one thing the spec's own
re-plan clause forbids.


## Step 3 CLOSED — §Renderable is an invariant, not a hypothesis — 2026-08-14T04:25:42Z

`renderable_of_liveReachable` is proved, so Step 3's exit criteria are met. Every
state a live session can hold — fresh emulator, any byte stream, any resize, a
checkpoint quiesce — stores only grids `Render.rowAnsi` can express. Lifted to
the daemon by `Session.run_vt_renderable` for any event trace.

### What made the campaign tractable

Two structural choices did most of the work, both instances of "restructure for
provability rather than weaken the theorem":

1. **`Renderable` is stated over the grid array with a fixed default row**, not
   over `Vt.getRow` (whose default carries the current pen). That single choice
   means every operation which does not touch `grid`/`cols`/`rows`/`altGrid` is
   discharged by its existing *frame* through one lemma (`renderable_congr`) —
   which is most of `csiDispatch`, all of the cursor motion, SGR, modes, tabs and
   the parser transitions. Only about a dozen operations write cells.
2. **Every cell write ends in `Row.mend`**, so `mend_pairOk` discharges the pair
   rule once for any input row. The per-operation obligation collapses to "the
   cells I wrote are reproducible", and *where* they were written never matters —
   which is why `cells_foldl`/`cells_set` need no index reasoning at all. A copied
   cell is reproducible because out-of-range reads are a default cell, which is
   itself reproducible; that is the trick that keeps column bounds out of the
   proofs entirely.

`renderable_row_mutation` is the shape every row mutation shares (fold writes,
mend, put back), so erase/ICH/DCH/IRM are one line each.

### A vacuity trap I walked into, and the break check that caught it

`CellOk.base` was first stated as `printableChar c.base = c.base`. That is a
**tautology against the function that establishes it**: mutating `printableChar`
to never substitute (`||` → `&&`) weakens the predicate and the storer together,
so `renderable_step` still proved — while the DEL and overlong-UTF-8 replay
fixtures failed. The invariant was true and useless.

Fixed by stating the clause concretely: `Emittable c := 0x20 ≤ c.toNat ∧
c.toNat ≠ 0x7F`, with `printableChar_emittable` as a claim about `printableChar`'s
*range*. Re-ran the same mutation: it now breaks `printableChar_emittable`. This
is the same failure mode the reviewer found twice in the Session theorems
(a claim about a helper mistaken for a claim about the machine), arrived at from a
third direction — defining an invariant in terms of the code it constrains. Worth
generalising: **an invariant must be stated in vocabulary the implementation does
not get to redefine.**

### Code restructured for the proof, behaviour unchanged

`resizeRow` and `Vt.resize`'s `fit` were rewritten from `extract`/`++` splicing
to a **map over the target range**. Same semantics — column `i` keeps its cell if
the old row had one, row `j` comes from the bottom-aligned source or is blank —
but the result's width and per-row contents are then one step from the
definition, so `rowOk_resizeRow`/`gridOk_fit` need one generic lemma
(`getD_map_range`) instead of three about array splicing. Verified
behaviour-identical by the resize fixture, the fuzz corpus and the live
attach/resume/graphics suites, all green.

Two elaboration traps worth keeping, both the same shape: `exact f h rfl rfl` fixes
an implicit state to the *incoming* one before the conclusion is seen, so an arm
like `csiDispatch`'s `DECSTBM` (`{v with top := …}.moveTo 0 0`) or
`stepGround`'s continuation byte (`{v with u8need := …}.acceptChar n`) does not
unify. Fix: state a `*_congr` helper over the *result* record and use `refine …
?_ ?_ ?_ ?_ <;> rfl`, which unifies the conclusion first. `renderable_stepGround`
also needs `maxHeartbeats 2000000` on top of `maxRecDepth 4096`.

### Gate

`./lake build`, `./lake build Theorems Tests`, `./tests/e2e.sh` green and
warning-free. `CLAIM_CAP` **16 → 12** — the new theorems claim `isWide`,
`isZeroWidth`, `blankRow` and `resizeRow`, which the ratchet had been pointing at
as the unclaimed width/grid-shape cluster since it was introduced. That cluster
was exactly the bug neighbourhood, and it is now covered.

Step 4 (`restore_grid`) remains, and now starts from a *discharged* shape
hypothesis: the row/grid replay induction is the only thing left in it.


## Step 4 recon — the `Keeps` rung, spiked and reverted — 2026-08-14T04:40:00Z

Spiked the next rung of `restore_grid` and **reverted it**: the shape is right and
the ladder is worth recording, but the UInt8 guard chain fought back and a
half-fought block in the tree is worth less than a note.

### The rung, and why it comes first

`restore` paints the grid and then emits the tail — scroll region, tab ruler,
DECSC slot, title, modes, charset, pen, final cursor. For `restore_grid` to be a
claim about the *repaint*, none of that tail may write a cell, and that is not
obvious from reading it: `CSI r` moves the cursor, a private mode set can home it,
`ESC H` edits the ruler, and `modesAnsi` is one guard away from emitting a
screen-switch. So the tail needs its own stream predicate, third after `Ends`
(parser ends ground) and `Quiet` (DECOM stays off):

```lean
def Keeps (bs : Bytes) : Prop :=
  ∀ v : Vt, v.pstate = .ground → v.u8need = 0 →
    ((v.feed bs).pstate = .ground ∧ (v.feed bs).u8need = 0
      ∧ (v.feed bs).grid = v.grid)
```

Bundled for the same reason `Quiet` is: the grid half needs the parser half at
every step. `u8need` rides along so a stream cannot leave a half-decoded
character armed for the next one. Combinators are copies of `Quiet`'s
(nil/append/append3/ite/flatMap) and compiled first try.

### What made it work, and what stopped it

The load-bearing reuse is **`csi_param_run_frame`**: from `.csi s`, a parameter
run is `{ v with pstate := .csi s' }` — a record update — so the grid is
unchanged for free and the *only* place a CSI sequence can touch the grid is
`csiDispatch s final`. That collapses the whole tail to one walk plus one fact
per final byte used (`H` → `frame_moveTo`, `G` → `frame_setCol`, `m` →
`frame_applySgr`, `g`/`r` → record updates or `moveTo`). Factor the walk as
`keeps_csi_tail` over `.csi s` so the private form (`CSI ? n h/l`, which is what
a mode replay *is*) can prefix its own marker step — `0x3F` is outside
`ParamBytes` (0x30–0x3B), which is the first thing that bit.

What stopped it: re-deriving `stepCsi`'s guard chain. `omega` cannot see UInt8
comparisons, so each `if_neg` needs the house pattern — `u8_bounds h1 h2` then
`simp only [UInt8.le_iff_toNat_le, show ((0xNN : UInt8)).toNat = NN from rfl] at`
— which `csi_final_step` already does for the *pstate* half. **The right move next
time is to generalize `csi_final_step` to return the resulting state**
(`v.step b = v.csiFinish s b`) rather than just its `pstate`; then `Keeps`'s CSI
case is three lines and every guard is discharged in one place, once, for both
layers.

### Also needed for `restore_grid`, in dependency order

1. `Keeps` for the tail (above) — mechanical once the guard lemma is generalized.
2. `grid_setMode` for the mode numbers `modesAnsi` actually emits: it must exclude
   47/1047/1049, and it can, because `modesAnsi` never emits them — the same
   guarded-emit argument `quiet_modesAnsi` already makes for mode 6.
3. The **row induction** — the real content, and unchanged by any of this:
   `rowAnsi`'s combined pen-and-column fold, painting cells [0,i) with the cursor
   at column i, plus the wide-with-marks `CHA` excursion and the wrap-pending
   state at the right margin.
4. The grid induction over `joinCRLF`, where the row separator's `lineFeed` must
   not scroll — true because `regionAnsi` comes *after* the paint, so the region
   is full-screen throughout, but it needs saying.
5. `screensAnsi`'s alt switch, then `resume_grid` composing with §Restore.

Step 3's `renderable_of_liveReachable` means none of these needs a side condition
on the grid; every one of them is now purely about the emitter and the parser.


## Step 4, first rung landed — `Keeps`, the grid stream layer — 2026-08-14T05:05:00Z

The rung the previous entry spiked and reverted is in, done the way that entry
said to do it: **generalize the guard lemma first**, then the layer falls out.

`csi_final_guards` factors `stepCsi`'s six pre-final guards (all false below
`0x40`) out of `csi_final_step`, and `csi_final_step_eq` is the state equation
the grid layer needs — `v.step b = v.csiFinish s b`, given `s.inter = 0`, which is
what separates a dispatched sequence from an ignored one. `csi_final_step` now
uses the shared guards, so the UInt8 comparison work exists once instead of per
layer. That was the whole blocker last time.

`Keeps bs` is the third stream predicate: from ground with nothing half-decoded,
feeding `bs` returns to ground, leaves nothing half-decoded, and **leaves the
grid alone**. Bundled like `Quiet` and for the same reason. Combinators are
copies. The CSI walk is done once in `keeps_csi_tail`, resting on
`csi_param_run_inter` (a parameter run is a `pstate` record update *and* keeps
`inter` — the new part, since `csi_param_run_frame` gave only the record shape),
so each construct supplies just one fact about its own final byte:
`keeps_csiNum`, `keeps_csiNum2`, `keeps_csiPriv`, with
`grid_csiDispatch_{cup,cha,sgr,tbc,stbm}`.

### Traps, all the same shape as before

* `keeps_csi_open` first claimed `ESC [` lands in `{v with pstate := .csi {},
  u8need := 0, u8acc := 0}`. Wrong: with nothing pending, `abortUtf8` is the
  *identity*, so `u8acc` is carried through unchanged. Over-claiming a record
  field is easy when the field is irrelevant to the conclusion — state the
  minimum (`{v with pstate := .csi {}}`) and pass `u8need = 0` as a hypothesis.
* A `match` on a **literal** final byte does not reduce under `dsimp only` or
  `repeat' split`, and `simp [Vt.csiDispatch, hi]` normalizes the branches into a
  form a hand-written `have` will not match. What works is `show` with the
  reduced term spelled out: it forces whnf through the literal match. Spell the
  guard exactly as the source does — DECSTBM's is `t < b && b < rows` (Bool
  `&&`), and writing `∧` fails the pattern.

### Break verification, and why it is shape-only here

Mutated `csiDispatch`'s `CHA` arm from `setCol` to `eraseChars` (a grid write):
`grid_csiDispatch_cha` fails. That is a **shape** break, and for this class it is
the honest one — a "this final writes no cell" claim can only be broken by making
it write, which necessarily changes the dispatch term. The content-bearing claim
in the block is `keeps_csi_tail` ("a CSI sequence touches the grid *only* through
its dispatch"), and its content is carried by `csi_param_run_inter`, whose own
break would likewise be structural. Recorded rather than dressed up as a value
break, per the rule from the §Replay 3c-rest entry.

### What is left in `restore_grid`

Unchanged from the recon, minus this rung: `Keeps` instances for the non-CSI tail
(`escSeq`, `escCharset`, the OSC title, `[0x0E]`), `grid_setMode` restricted to
the mode numbers `modesAnsi` actually emits (it never emits 47/1047/1049 — the
same guarded-emit argument `quiet_modesAnsi` already makes for mode 6), then the
row induction, the `joinCRLF` grid induction, and the alt switch.


## Step 4, second rung — the SGR pen and the mode fact — 2026-08-14T05:20:00Z

Two more `Keeps` pieces, both first try, because `keeps_csi_seq` had already paid
for the walk: `keeps_sgrOf`/`keeps_sgrColorSeq`/`keeps_penSgr` (an SGR pen writes
no cell, for any pen and however `penSgr` splits it across sequences — the piece
`savedAnsi` and `restoreBody`'s trailing pen both rest on) and `grid_setMode`.

`grid_setMode` is the interesting one. A mode set writes no cell **unless it
switches screens**: `47`, `1047` and `1049` swap the grid for the alternate one,
and nothing else in `setMode` touches a cell. So the theorem carries those three
as hypotheses, and `modesAnsi` discharges them by never emitting them — the same
guarded-emit argument `quiet_modesAnsi` already makes for DECOM. The emitter is
what keeps the claim true, which is the right place for it: a reachability
invariant on `Vt` would have been the alternative, and one guarded emit is cheaper
than a field every constructor must maintain.

### The bridge the mode instance still needs

`Keeps (modesAnsi v)` does not follow yet. `grid_csiDispatch` for the `h`/`l`
finals has to know `s.arg 0 0 ∉ {47, 1047, 1049}`, and `s.arg 0 0` is what the
*parser* accumulated — so it needs the digit round trip (`accDigits_digits` /
`csi_digits_value`) to identify the emitted number with the parsed one. That
bridge exists, and is exactly what the pen and cursor rungs were built on; it just
has not been pointed at the mode numbers. That is the next step, and it also
unblocks the remaining non-CSI instances (`escSeq` for DECSC/HTS/app-keypad,
`escCharset`, the OSC title, the shift-out byte), each of which is a short byte
walk in the style of `ends_escSeq`/`ends_osc` plus a grid fact per step.


## Generalizing the repeated shapes — measured, and smaller than it looks — 2026-08-14T05:40:00Z

Two duplicated shapes collapsed. The first was on a recorded trigger: the §Replay
3c-rest entry sketched a `StreamPred` bundle, rejected it ("not worth it to dedupe
thirteen 3-line proofs"), and said **"revisit if a third layer wants the same
skeleton."** `Keeps` is that third layer, so the condition was met rather than
guessed at.

### 1. `StreamPred` — the stream-layer skeleton

`Ends`, `Quiet` and `Keeps` are each a predicate on a byte string closed under
concatenation, and each needed the same five derived combinators — fifteen proofs
of five facts. Everything derived follows from `nil` and `append` alone, so those
two are the bundle (`StreamPred`) and `append3`/`append4`/`ite`/`flatten`/`flatMap`
are generic. Each layer now has a one-line `streamPred` instance and five one-line
derivations **keeping their own names**, so no downstream proof changed — the
conversion rule from the frames pass.

The boundary is the interesting part, and `Keeps` is what settles it: **only the
combinators generalize.** `Ends.text` and `Quiet.text` both say an ESC-free run is
harmless; the same statement for `Keeps` is **false**, because printable bytes are
exactly what writes cells. So a shared *instance* ladder would have to weaken to
accommodate the third layer — the same trap the original sketch hit from the other
side (`modesAnsi`'s DECOM branch is hypothesis-free for `Ends`, hypothesis-bearing
for `Quiet`). The earlier refusal was right for two layers and right again now for
the instances; it was only the combinators that were worth pulling out.

One mechanical note: `StreamPred.ite` does not use its bundle argument at all (an
`if` needs no closure law), so it takes `_hP` — kept as a parameter only so
`Ends.streamPred.ite` reads like its siblings.

### 2. `invariant_foldl` — fold invariance, once

`invariant_foldl` already existed in `Theorems/Render.lean`, and I had then written
its statement out four more times in `Theorems/Vt.lean` for `Good`, `Renderable`, a
row's cells and a grid's rows. Moved the general lemma up into `Theorems/Vt.lean`
(where `Render` sees it through `open`) and made all four derivations; a sixth
predicate now costs one line.

### The honest measurement

**This is not a line win.** Proof code went from ~67 lines to ~82; the diff's
+119/−71 is mostly the doc comment explaining the boundary above. What actually
improved:

* a fourth stream layer costs one instance instead of five proofs;
* a sixth fold predicate costs one line instead of a six-line induction;
* the `ite` and `text` asymmetries are now stated in exactly one place, where the
  next person will read them, instead of being implicit in which of three files
  happened to have a hypothesis.

Same shape of result as the frames pass, and worth recording in the same terms: a
real but smaller win than "fifteen proofs become five" suggests. The value is in
what the *next* layer costs, not in what this diff removed.


## Step 4, third rung — the non-CSI tail — 2026-08-14T05:55:00Z

Five of `restoreBody`'s eight tail stages are now proved to write no cell:
`regionAnsi`, `cursorAnsi`, `savedAnsi`, `tabsAnsi`, `charsetAnsi`. Each is a
two-line composition, which is the shape the earlier rungs were paying for.

Three new primitives, each a short walk whose steps are record updates on some
*other* field — the saved slot, the tab ruler, a mode flag, the charset flags,
`shiftOut`:

* `keeps_escSeq` for `ESC 7` (DECSC), `ESC H` (HTS), `ESC =` (app keypad);
* `keeps_escCharset` for `ESC ( x` / `ESC ) x`;
* `keeps_shiftOut` for the bare `SO` byte.

Supporting them: `step_of_esc_quiet` and `step_of_escInter_quiet` (the `.esc` and
`.escInter` twins of `step_of_csi_quiet`), plus `esc_step_eq` — `ESC` from ground
as an *equation* rather than only a `pstate` fact, which is what a layer that cares
about other fields needs.

One trap, and it is the mirror of the `keeps_csi_open` over-claim from two rungs
ago: `SO` leaves the parser exactly where it was, so `Keeps`'s ground component is
discharged by the incoming hypothesis `hg`, not by `rfl`. Reaching for `rfl` on a
component that happens to be *unchanged* rather than *established* is the same
mistake in the opposite direction — there I claimed a field was zeroed when it was
carried through, here I claimed a field was re-established when it was carried
through.

### What is left

`modesAnsi` is the only tail stage still open, and it needs exactly the bridge
recorded two entries ago: `grid_setMode` excludes 47/1047/1049, `modesAnsi` never
emits them, but the `h`/`l` dispatch reads `s.arg 0 0` — the number the *parser*
accumulated — so the digit round trip (`csi_digits_value`, already built for the
pen and cursor rungs) has to identify the two. Then `keeps_restoreTail` is a
composition, and what remains of `restore_grid` is the row induction, the
`joinCRLF` grid induction, and the alt switch.


## A real restore bug, found by setting up the last tail stage — 2026-08-14T06:15:00Z

Setting up `Keeps (modesAnsi v)` needed `grid_setMode`'s hypotheses discharged —
that the replayed mode is not 47, 1047 or 1049, the three that switch screens. So:
can `v.modes.mouse` hold one of those? Checked instead of assuming, and it can.

**`Checkpoint.load` reads `mouse` as an arbitrary `rNat`**, and §Restore is
deliberately total on arbitrary bytes ("corrupt/torn/foreign file → load = none →
fresh start" applies to *parse failure*, not to field values a parse accepts). So a
corrupt, tampered or foreign checkpoint can carry `mouse = 1049`, and `modesAnsi`
replayed it verbatim behind a **denylist** (`!= 0 && != 6`). The emitted
`CSI ? 1049 h` would switch the reattaching client to the alt screen *in the middle
of the restore* — blanking the very screen being restored, and leaving the client
in alt with the real content stashed.

The `!= 6` half was already there for exactly this class: private mode 6 is DECOM,
and replaying a `mouse` of 6 would silently turn origin mode on (`quiet_modesAnsi`
turns on that guard). The guard was right about the mechanism and incomplete about
the values — a denylist naming one of four hazards.

**Fix: allowlist.** `modesAnsi` now emits the mouse mode only when it is one of
1000/1002/1003, which is what `setMode` can actually store. That closes DECOM and
all three screen-switches at once, cannot grow a fourth hole, and makes both proof
obligations trivial by construction. Strictly more defensive than extending the
denylist, and the same reasoning that made `printableChar` a store-time guard
rather than an emit-time one: name what is allowed, not what is forbidden.

`quiet_modesAnsi`'s DECOM branch got *simpler* — the allowlist gives `mouse ≠ 6` by
`omega` from three concrete values, instead of unpacking a two-clause `bne`.

### Break verification — a content break, first try

Two fixtures assert on the **grid**, not `replayEq`: the allowlist deliberately
does not replay a mode the emulator cannot hold, so `modes` is *expected* to
differ. What must survive is the screen and the absence of an alt switch
(`w.grid == v.grid && w.altGrid.isNone`). Reverting to the denylist fails both;
the allowlist passes both. A legitimate `?1002h`/`?1006h` session still round-trips
in full, so the guard did not just disable the feature.

My first draft of those fixtures used `roundtrips` and failed — correctly, and the
fixture was wrong rather than the code, which is the third time that has happened
in this project. `replayEq` compares `modes`, and not replaying a bogus mode means
`modes` cannot match. Assert the property you actually claim.

### Where this leaves the tail

Six of eight stages proved (`regionAnsi`, `cursorAnsi`, `savedAnsi`, `tabsAnsi`,
`charsetAnsi`, and now `modesAnsi` is *unblocked* rather than proved — the
allowlist supplies the values, the digit bridge still has to identify the emitted
number with the parsed one). `titleAnsi` (OSC) is the other one left, and it is a
straightforward accumulate-then-`oscFinish` walk in the style of `ends_osc`.


## Step 4, fourth rung — the title, and the tail is down to one stage — 2026-08-14T06:35:00Z

`keeps_titleAnsi` lands, so **seven of `restoreBody`'s eight tail pieces are proved
to write no cell**: `regionAnsi`, `tabsAnsi`, `savedAnsi`, `titleAnsi`,
`charsetAnsi`, the trailing `penSgr`, and `cursorAnsi`. Only `modesAnsi` is left.

An OSC is the one tail construct with an unbounded payload, so it is the one that
needed an induction (`osc_accum_run`). Every step is still a `pstate` record update
— the accumulator lives *inside* the parser state, which is what makes this cheap —
and `oscFinish` writes the title and nothing else. The payload cannot terminate its
own sequence because `utf8s` emits nothing below `0x20`, the same fact `ends_osc`
turns on; `utf8s_no_ctl` supplies it, so no new reasoning about the payload.

Supporting: `step_of_osc_quiet` (the fourth of the `step_of_*_quiet` family, after
ground/csi/esc/escInter), `osc_accum_eq`, and `grid`/`u8need`/`pstate` facts for
`oscFinish`.

One trap: **`stepOsc`'s guards are in a different order than I assumed** — ST
(`esc && b == 0x5C`) comes *first*, then BEL, then ESC, then the 2048-byte cap. I
wrote two `if_neg`s for the first two guards and got a mismatch against the
`.osc acc true` branch. Read the guard chain in the source rather than the order the
doc comment lists the cases in.

### The one remaining stage

`modesAnsi` needs the digit bridge and nothing else now: `grid_setMode` is proved,
the allowlist supplies mode numbers that are none of 47/1047/1049, and what is
missing is the identification of the *emitted* number with `s.arg 0 0`, the number
the parser accumulated. `accDigits_digits` and `csi_digits_value` already do exactly
that for the pen and cursor rungs; `keeps_csi_tail` has to be given a variant whose
`hgrid` may depend on the accumulated state rather than being universally quantified
over it. Then `keeps_restoreTail` is a composition and `restore_grid` reduces to the
row induction, the `joinCRLF` grid induction, and the alt switch.


## Step 4, fifth rung — the digit bridge, and the tail is DONE — 2026-08-14T07:10:00Z

`keeps_modesAnsi` lands and with it **`keeps_restoreTail`: everything `restore`
emits after the repaint is proved to leave the painted grid alone** — all eight
stages (`regionAnsi`, `tabsAnsi`, `savedAnsi`, `titleAnsi`, `modesAnsi`,
`charsetAnsi`, the trailing `penSgr`, `cursorAnsi`).

`modesAnsi` was the one stage whose grid claim depends on *which number* it emitted:
`grid_setMode` holds for every mode but the three that switch screens. The emitter
never emits those, but the dispatch reads `s.arg 0 0` — the number the **parser**
accumulated — so the two had to be identified. `csi_digits_run_eq` is that bridge:
it welds the record equation from `csi_param_run_inter` to the accumulated value from
`csi_digits_value`, identifying their two existential states through
`PState.csi.inj`. On top of it, `keeps_csi_digits_tail` + the private/non-private
wrappers `keeps_csiPriv_arg` / `keeps_csiNum_arg`.

### The trap that cost the first attempt

I first instantiated the digit run at the *call site*, naming the collector state as
`{ (default : CsiState) with priv := 0x3F }`. `rw` then could not find it: the goal
held the state the way `stepCsi` had built it, and **`{}` and `default` do not
elaborate to the same term** (the error prints `let __src := default; …`). The fix is
structural, and is the better design anyway: do the digit run *inside*
`keeps_csi_digits_tail`, where the state is still a bound variable, so unification
picks it up from the goal and nothing has to be spelled out. Rule of thumb — never
write a mid-walk state literal; take it as an implicit and let `rfl` discharge it.

### Break-verify (required by AGENTS.md)

Changed `modesAnsi`'s `set 1006 true` to `set 1049 true` (a real screen switch).
`keeps_modesAnsi` stopped compiling at its final composition, since `grid_setMode`
has no case for 1049 — the theorem is exactly what forces the allowlist. Honest
caveat: the same edit also tripped `ends_modesAnsi` and `quiet_modesAnsi`, which pin
the literal positionally, so the break is not a clean isolation of the grid claim;
the `Keeps` failure is the one that names the reason. Restored, 0 errors/warnings.

### What is left of `restore_grid`

Only the repaint: the row induction over `rowAnsi`, the `joinCRLF` separator, and the
alt switch. The tail is no longer in the way.


### Sixth rung, same session — the non-repaint remainder

`keeps_sgrReset` and `keeps_park` close out everything in `restore` that is neither
the clear nor the paint nor the switch. Both are compositions of pieces already
proved, so they cost nothing; the point is the resulting statement of position:

> The only bytes in `restore` that may legitimately touch a cell are `CSI 2 J`
> (clear), `gridAnsi` (paint), and `CSI ? 1049 h` (alt switch).

`keeps_park` is stated on bare naturals rather than on a cursor record so that all
three occurrences of the shape instantiate it (DECSC replay, alt-stash parking, final
placement). Note it will not slot in by `rw` as-is: `++` is right-associative, so
`penSgr p ++ csiNum2 … ++ rest` parses as `penSgr p ++ (csiNum2 … ++ rest)` and the
parking pair is not a syntactic subterm of either `savedAnsi` or `screensAnsi`. The
eventual decomposition has to re-associate explicitly (the
`rw [show … = … from by simp]` move used throughout this file) — which it would have
had to do anyway.

Next, in the order I would take them: (a) `CSI 2 J` blanks the grid — self-contained,
needs `eraseDisplay`'s post-state to line up with a blank-grid term, and does not
depend on the row induction; (b) the `rowAnsi` induction; (c) `joinCRLF`; (d) the alt
switch. (a) is the one to try next because it is independent of the hard part.


### Seventh rung — the clear, framed

`eraseScreen_two_frame`: `CSI 2 J` leaves the dimensions, the pen, the cursor and the
row count alone. This is the useful statement about the clear, since it is the one
part of `restore` that is *supposed* to change cells — and the repaint that follows
depends on all four. `eraseRowSpan` turns out to be a single `grid` record update, so
its frame lemmas are `rfl`; only the fold over rows needed an induction
(`foldl_erase_frame`).

Two things worth recording:

- **`ps_eraseRowSpan` and `un_eraseRowSpan` already existed.** Grep before adding a
  frame lemma; this file is at 350+ theorems and the invariance layer is dense.
- **An in-tactic `match m with` on a variable leaves `match 2 with …` unreduced**,
  and `dsimp only` with no lemmas will not iota-reduce it, so the subsequent `rw`
  cannot see through it. The fix is an equation lemma (`eraseScreen_two_eq`, which is
  `rfl` because `2` hits the `_` arm) proved *outside* the frame proof. Same family of
  trap as the `{}`-vs-`default` one: keep concrete state terms out of tactic blocks.
- I had written the frame for all four ED modes; cut it to mode 2, which is the only
  one `restore` emits. `foldl_erase_frame` stays general, so the others are a
  three-line each if ever needed.


### Eighth rung — `restore_grid`, reduced to the paint

`restore_grid_of_paint` turns the tail work from a scratchpad claim into a theorem:
**if the clear-and-paint prefix leaves the grid equal to `v`'s, the parser in ground,
and no UTF-8 half-decoded, then all of `restore` leaves the grid equal to `v`'s.**
Everything after the paint is `keeps_restoreTail`. The three hypotheses are precisely
what the repaint half still owes, about a prefix three constructs long.

`restore_split` is the one re-association it needs (`++` is right-associative, so
splitting off the prefix is not free) — the same associativity tax noted for
`keeps_park`.

Break-verify, in the form Step 4's exit criterion asks for (*a same-shape value
mutation breaks the proof*): changed `cursorAnsi`'s final byte from `0x48` (CUP) to
`0x40` (ICH), which shifts cells. `keeps_cursorAnsi` stops compiling — `grid_csiDispatch_cup`
correctly has nothing to say about ICH — and the failure propagates through
`keeps_restoreTail` to `restore_grid_of_paint`. Three other layers caught it too
(`ends_`/`quiet_`/a `rfl` at 2640). Restored, 0 errors/warnings.

Spec header updated: it still said Step 4 was *not started*, stale by ten commits.
Now records tail-done/paint-open with the list of landed pieces. The original scope
check is kept verbatim rather than softened — the tail work does not shrink the
induction, it clears everything around it.

### The paint, when it is next opened

`gridAnsi grid = csiNum 0 0x6D ++ csiB ++ [0x48] ++ joinCRLF rows` where `rows` is a
fold of `rowAnsi` carrying the pen across rows. In order of dependency:

1. **`ED 2` blanks every cell** (cell-level, not just the frame proved above). Needs
   a row-size hypothesis: the inner fold uses `setIfInBounds`, so a row shorter than
   `cols` would not become `blankRow cols`. `renderable_of_liveReachable` should
   supply it — check what shape it gives before writing the induction.
2. **`rowAnsi` writes its row.** The hard one: one fold carrying `(bytes, pen, x)`,
   with the wide-with-marks branch emitting two `CHA` moves.
3. **`joinCRLF`** separates rows without scrolling — interacts with the scroll region,
   so `regionAnsi` ordering matters (§Replay fix 1).
4. **The alt switch** — `csiPriv 1049 0x68` is the one emitted screen switch, and it
   is deliberate here (unlike the `modesAnsi` bug); `grid_setMode`'s excluded cases
   are exactly the three it belongs to.
