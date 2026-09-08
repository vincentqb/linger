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


## Step 4, ninth rung — into the paint, and an honest scope map — 2026-08-14T08:20:00Z

Asked to finish Step 4. It is **not finished**, and this entry says exactly where it
stands so the next session does not re-derive the map. What landed: the `Row.mend`
fixed-point lemmas, which are what the row induction needs, plus two findings that
change the plan.

### Landed

`mend_of_pairOk` — **`mend` is the identity on a row whose pairs are whole and whose
shadows are canonical.** This is the lemma the row induction turns on: every
cell-writing operation ends in `Row.mend`, so painting cell `k` re-mends the whole
row, and the induction has to know that does not disturb columns `< k`. It does not,
and the reason is exactly `RowOk.pairs`. Supporting: `set_self_eq` (writing back the
value already there is identity), `mendAt_of_pairOk`, `mendAt_of_width_one`,
`width_at_blankRow`, `mend_blankRow`.

Note `PairOk` gives the *cell* equation `row.at (x+1) = Cell.shadow (row.at x)` while
`halfPair_eq_false_iff` wants the *width* form; converting is one `rw`, but the
mismatch is not visible from the names.

### Finding 1 — `ED 2`'s blanking is NOT on the critical path

I was about to prove "`CSI 2 J` blanks every cell", listed as the next step last
session. It is not needed. `gridAnsi` paints `grid.size` rows of `cols` columns and
**every column is written**: a width-1 cell by its own print, a width-2 base by its
print, and a shadow by its base's print (`printPut` writes both halves). A stored
width-2 base in the final column cannot occur in a `RowOk` row — `mend` blanks it as
a half pair — so there is no uncovered column. The clear therefore matters only for
what it *leaves alone*, which `eraseScreen_two_frame` already proves. That deletes a
planned induction outright.

### Finding 2 — the pen stream round-trip is a prerequisite I had not listed

`(w.feed (penSgr p)).pen = p` is **not proved**. The semantic half is
(`pen_codes_recover`: `applySgr` inverts the encoding, from any starting pen), and the
file says so at its §"pen round trip" header — what is missing is that the CSI
accumulator delivers those numbers, i.e. a *multi-parameter* version of
`csi_digits_run_eq` for `joinSemi`-separated lists. `restore_grid` needs it, because
`rowAnsi` only emits `penSgr` on a pen *change* and the replayed pen must track the
emitted one cell by cell.

### The remaining work, in dependency order

1. **Multi-param accumulator bridge** → `(w.feed (penSgr p)).pen = p`. Generalizes
   `csi_digits_run_eq` from one number to a `;`-separated list. Medium; the
   single-param case is done and the semantic half is done.
2. **`SGR 0` sets the pen to `{}`** — the single-param special case of (1), and what
   makes the paint's initial pen match `rowAnsi`'s `startPen = {}`.
3. **`CSI H` homes the cursor** — bare `CSI H` with default args; `cup_places_cursor`
   is the two-arg analogue.
4. **The row induction** — the large one. `rowAnsi`'s fold carries `(bytes, pen, x)`;
   the proof needs `Array.foldl` → list fold, a prefix-decomposition of the emitted
   bytes, and a per-cell step through `printWrap`/`printWideWrap`/`printShift`/
   `printPut`/`printAdvance` under wrap=true, insert=false (both hold during the
   paint, since `modesAnsi` comes *after* it — which is §Replay fix 1's ordering
   earning its keep a second time). Three cell cases: width 1, width 2 with room,
   width 0. The wide-with-marks branch emits two `CHA` moves, so the invariant must
   survive an absolute cursor jump. `mend_of_pairOk` is the stability argument.
5. **`joinCRLF`** — the row separator, and the argument that no `LF` scrolls (the
   last row has no separator, which is why `joinCRLF` special-cases `[b]`).
6. **The alt switch** — `csiPriv 1049 0x68` is deliberate here, unlike the
   `modesAnsi` bug; `grid_setMode`'s three excluded modes are exactly this one's.
7. **Compose**: `restore_grid` (via `restore_grid_of_paint`, already proved),
   then `restore_grid_reachable` (add `LiveReachableVt` →
   `renderable_of_liveReachable`), then `resume_grid` in `Theorems/Resume.lean`.

Item 4 is the bulk. The original scope check — "comparable in size to the entire
§Replay parser half, which took several sessions" — still looks right, with items
1–3 and 5–7 the smaller half around it.


## Negative result — painting with autowrap off is WRONG, not merely awkward — 2026-08-15T12:40:00Z

Tried the change I had recommended: emit `CSI ?7l` before the repaint in
`restoreBody` so the row-replay induction would not have to carry wrap-pending
(`printAdvance` never arms it, `printWrap`/`printWideWrap` collapse to no-ops), with
`modesAnsi` restoring the session's real wrap value afterwards. **Reverted: it breaks
combining marks in the final column.**

`Tests/Fuzz.lean`'s `failingDeep 150` went from `[]` to `[33, 110]` immediately. Both
seeds are the same shape — a combining mark on the bottom-right cell of a 2×2 screen.
Case 33 is `\x1b[?1047h\x1b[3;5H\x1b[4hb\x1b[1;2;3;4;5;7;9mb\x1bH\x1b[?47l\x0e\x1b(0\x1b[0g\x1b[3;5Hé\x1b[41m`.

Live row 1 is `space`, `'e'`+1 mark. Replayed row 1 was `space`+1 mark, `'e'`+0 — the
mark landed one column left.

### Why

`Vt.printMark` picks its target with

```
let cx0 := if v.cursor.pending then v.cursor.x
           else if v.cursor.x == 0 then 0 else v.cursor.x - 1
```

At the right margin `printAdvance` parks the cursor *on* `cols-1` and arms `pending`
— but only when wrap is on. So `pending` is what distinguishes **"parked on the
margin cell I just wrote"** from **"positioned before writing it"**. With wrap off both
states are `x = cols-1, pending = false`, and `printMark` steps left. `printMark`'s own
doc comment already said this ("at the right margin the cursor sits on the shadow with
wrap pending — the one position no absolute cursor move can address"); I read it as a
remark about `Row.mend`'s shadow redirect and missed that it is also the reason the
*flag* has to exist.

The alternatives are worse: no absolute cursor move can express "on the margin cell,
after writing it", so making the painter emit an explicit move instead would require
changing `printMark`'s live semantics; and emitting `?7l` only for rows without a
trailing mark makes the wire format depend on cell contents.

### What this means for the row induction

Wrap-pending is **load-bearing state, not proof noise**. The induction must carry
`cursor.pending` through every cell, and the invariant at the end of a full row is
`x = cols-1 ∧ pending = modes.wrap`, not `x = cols`. That is the cost of the feature,
and the theorem should model it rather than legislate it away. The `Renderable`
robustness argument I also offered for wrap-off (a width-2 base at the final column
pre-wraps under wrap-on and shifts the rest of the paint) stands on its own but is
unreachable, so it does not justify the change.

Vindication for the fuzz layer: this is exactly the "an emitter stage correct only
under a precondition on the emulator state" shape `Tests/Fuzz.lean`'s header describes,
and it was caught in one build. The proof-side lesson is the opposite of the one I
proposed last session — do not simplify the emitted stream to make the induction
cheaper without checking the emulator's own preconditions first.


## Bug fix — restore assumed a pristine client, and leaked the old one's modes — 2026-08-15T14:10:00Z

Found by asking why every §Replay bug has the same shape. The answer was in the
*quantifier*, not the encoding: `restore_grid`'s statement is
`(Vt.init cols rows).feed (restore v) ≃ v`, and `Vt.init` is the one receiver state
in which every precondition the emitter depends on already holds. `Session.onMsg`
sends `restore` on attach with **nothing** before it, so a real client is whatever
its previous occupant left behind.

### The leak

`modesAnsi` was *set-only* for eight modes — it emitted nothing when the session had
them off (`if v.modes.origin then set 6 true else []`, and the same for appCursor,
appKeypad, bracketed paste, the mouse modes, SGR mouse, focus events, IRM). Only
wrap was emitted both ways, and `cursorVisible` was emitted only when hidden. So:

* client IRM on, session off → the repaint **shifts cells as it paints**, and IRM
  stays on afterwards;
* client DECOM on → stays on, and `cursorAnsi`'s absolute address is reinterpreted
  region-relative, landing the cursor in the wrong row;
* client mouse reporting on from a crashed program → stays on, and mouse events flow
  into the session as input;
* client on the **alt screen** → the main-grid repaint lands there, and
  `screensAnsi`'s own `?1049h` is then a no-op, so the main screen is never painted;
* stale scroll region → the repaint's line feeds **scroll**;
* DEC line-drawing G0 → the ASCII the painter emits comes out as box glyphs.

### The fix

`prologueAnsi` establishes the receiver state the repaint depends on — `?1049l`,
`4l`, `?6l`, `?7h`, `1;rows r`, `(B`, `)B`, `SI` — and `modesAnsi` now emits every
mode **both ways**, clearing all three mouse modes before setting the live one.
`?7h` sets wrap **on**, deliberately: the 2026-08-15 negative result above is why.

Pinned by `Tests/Render.lean`'s new `dirty` receiver and `roundtripsFrom`: a client
with all of the above turned on, restored into, must match the session — including a
wide glyph plus combining mark, and an alt-screen session. Break-verified by deleting
`prologueAnsi v ++` from `restoreBody`: 7 tests fail. Fuzz stayed green throughout
(`failing 400 = []`, `failingDeep 150 = []`).

### Proof-engineering notes, all of them elaboration cost rather than logic

* **`++` is left-associative in Lean.** I "fixed" the append chains to be right-assoc
  and it was wrong. The chains must peel from the **right**:
  `refine Ends.append ?_ (last)` repeatedly. Doing it as one giant `exact` of a
  nested chain, or in the wrong direction, makes the elaborator reconcile the two
  shapes by unfolding `List.append` — at a dozen chunks that is a heartbeat timeout,
  which is what all the `whnf` timeouts in this change were.
* **A `let`-bound lambda in a definition costs a beta-redex per use at proof time.**
  `modesAnsi`'s `let set := fun n on => …` timed out once there were 13 modes;
  promoting it to `def modeSet` made every chunk match structurally. Same instinct as
  "name the stages".
* **`(dims X).1 = X.cols` by `rfl` forces `X` to whnf.** With `X` a `feed` of the
  whole restore stream that is a timeout. `dims_fst`/`dims_snd`, proved once on a
  *variable*, fix it — the lemma is trivial but the call site is not.
* `escSeq`'s allowlist needed `ESC >` (DECKPNM) added in four places, since keypad
  mode is now emitted both ways.
* `quiet_modeSet_decom_off` is the one genuinely new proof: the `≠ 6` family says a
  mode replay cannot turn origin *on*, and the prologue needs the complement, that
  `?6l` turns it *off*. Proved at the dispatch (`org_setMode_decom_off` →
  `org_csiDispatch_decom_off` → `org_csiFinish_decom_off` → `org_step_of_csi_decom_off`).


## Step 1 of restore-conformance — `Sets`, and two more instances of the same bug

Wrote `Sets P x bs := ∀ w, P (w.feed bs) = x` — "feeding `bs` to **any** state leaves
`P` at `x`" — with `prefix`/`suffix`/`ite` laws. The asymmetry is the content:
appending on the *left* is free, which is precisely what makes both-ways emission
provable, while a right-append needs the suffix to preserve `P`.

Then tried to prove an instance and could not, for a reason that turned out to be two
more bugs of the family this spec is about.

### Bug: a receiver mid-OSC or mid-DCS swallowed the whole restore stream

`Vt.stepOsc` accumulates any byte that is not `BEL` or `ST` — including our leading
`ESC`, after which our `[` is not `\\` so it is accumulated too. `Vt.stepStr` (DCS,
APC, SOS, PM) only leaves on `ST`. So a client left in either state consumed **every
byte of `restore`** into a window title or a discarded string, and displayed nothing.

Fix: `prologueAnsi` leads with `escSeq 0x5C` = `ESC \\` (ST). It terminates both, and
from `ground`/`esc`/`escInter`/`csi` it lands in `ground`. The one side effect is that
in `escInter` the `ESC` designates a charset from a junk byte and the `\\` then prints
a backslash — both erased by the `ED 2` two lines later, and `charsetAnsi` re-emits
the real designation. `stepEsc` sends `0x5C` to its default arm, so no new parser
surface was needed; the `escSeq` allowlist grew by one byte in four places.

### Bug: an empty session title left the client's old title on display

`titleAnsi` was `if v.title.isEmpty then [] else …` — the same set-only shape as the
modes. Now emitted unconditionally; an empty OSC 2 clears the title. This also
simplified its three predicate proofs from `ite` to a single branch.

Both break-verified: removing the ST lead-in fails 4 tests, and `Tests/Render.lean`
now carries one receiver per parser state (`midOsc`, `midDcs`, `midCsi`,
`midEscInter`, `midUtf8`) plus a non-vacuity check that `midOsc` really is stuck.

### Where Step 1 stands

The predicate and its laws are in; no field instance is proved yet. What each needs is
a *dispatch fact* — "after feeding `csiPriv n final` from ground, the state is
`u.csiDispatch t final` with `t.arg 0 0 = n` and `u.modes = w.modes`" — which is the
walk `keeps_csi_digits_tail` already performs internally but only exposes for the
grid. Factoring that walk out so both the grid and the mode claims consume it is the
next edit, and it is a refactor of proved code rather than new reasoning.


## Step 2, first half — `restore` grounds ANY receiver, proved — 2026-08-15T16:05:00Z

`restore_grounds (v w : Vt) : (w.feed (restore v)).pstate = .ground`. No hypothesis on
`w` at all: not `ground`, not `Vt.init`, nothing. This is `restore_quiesced`'s parser
claim with the receiver quantified, and it is the first theorem in the file to have
that shape — the whole point of `specs/restore-conformance.md`.

The chain:

* `un_abortUtf8_esc` — `ESC` is neither ASCII nor a continuation byte, so `abortUtf8`
  clears any half-decoded character.
* `esc_lands` — one case per `PState` for where `ESC` puts you: `.esc` from
  `ground`/`esc`/`csi`, `ground` from `escInter`, and the two string states with their
  ST check armed. This is the case analysis that says the lead-in cannot be swallowed.
* `st_finish` — `\` sends each of those four to `ground`. The `ground` case is the
  interesting one: the `\` *prints a backslash*, which is why the lead-in must precede
  `ED 2` rather than follow it.
* `st_grounds` — their composition, over all `w`.
* `prologue_grounds`, then `restore_grounds` — `Ends` carries the remaining chunks
  once the first two bytes have established `ground`.

### Notes

* **`show` with underscores does not reduce a match.** `match h : e with` substitutes
  the scrutinee, so `rw [h]` is then redundant *and* fails; but `show _ = _` will not
  iota-reduce the substituted match either. Only an explicit `show <full term>` does.
  Both mistakes cost a build cycle each; the working pattern is
  `match h : e with | .ctor => show <explicit>; unfold; rw [...]`.
* `Vt.abortUtf8` contains an `if`, so an unguarded `rw [if_neg …]` after
  `unfold Vt.step` can hit *that* `if` instead of the intended one. The explicit
  `show` also fixes this by pinning which term is being rewritten.
* The break-verify is not clean: deleting the ST lead-in trips `ends_prologueAnsi` on
  the shape mismatch before `restore_grounds` is reached. Non-vacuity is what carries
  it instead — `Tests/Render.lean` asserts `(midOsc 6 3).pstate == PState.ground` is
  `false`, so the `∀ w` really does range over states that would otherwise swallow the
  stream.

### What is left of Step 2

The `u8need` half. `st_grounds` proves it for the lead-in, but carrying it through the
remaining chunks needs each of them to preserve `u8need = 0` from an arbitrary start,
which is the same per-chunk work `Keeps` already does for the grid. `Quiet`'s origin
half needs the same treatment. Then Step 1's field instances become provable, since
each will be able to assume `ground` at its own chunk boundary.

## Step 0 of restore-conformance — the audit, and the bug on the way OUT — 2026-08-15T20:10:00Z

Step 0 asked: is the bug family exhausted? It is not, and the miss was one of
**direction**. Every fix so far concerned what `restore` assumes about the client it
writes into. Nothing asked the same question about what linger *leaves behind* — and
the answer was a user-visible defect with no test, no theorem and no recorded
decision anywhere.

### Measured, before any change

`Client.attach`'s only cleanup is `termRestore`, which restores **termios** — the
kernel's line discipline. Terminal state is not termios. A probe (a full-screen
app's opening sequences from inside the session, then `ctrl-\`):

```
bytes the client wrote after the detach key:
b"\r\r\nlinger: detached from 'probe'\r\n"
```

Nothing else. So the shell that gets the terminal back is left on the **alt
screen**, with **mouse reporting** on (clicks arrive as escape garbage on the
command line), the **cursor hidden**, **bracketed paste** on, **autowrap off**, a
**six-line scroll region**, **DEC line drawing** selected (every ASCII character
renders as a box glyph) and a **bold red pen**. Reachable by detaching from vim,
htop, less, fzf — the ordinary way to leave a session.

This is the same class as `87f64b3` (restore assumed a pristine client) with the
arrow reversed: an emitter — here, the *absence* of one — correct only under an
unstated precondition about a stateful thing it hands to someone else.

### The fix

`Render.leaveAnsi`, a **constant**: what linger hands back does not depend on what
the session was doing. Same discipline as `prologueAnsi`, same ST lead-in (a program
that died mid-OSC/DCS would otherwise swallow the whole hand-back exactly as it
swallowed `restore` before `cd7c17b`), plus the modes that only matter *afterwards*
(`?25h`, `?2004l`, the three mouse modes + `?1006l`, `?1004l`, `?1l`, `ESC >`) and
`SGR 0`. Written in `Client.attach`'s `finally`, so every exit — detach key, session
exit, EOF, decoder error, exception — goes through it, and both `attach` and
`watch` (read-only) get it.

Two orderings are forced, and neither is obvious:

* **`DECOM` reset and `DECSTBM` both home the cursor** — in our `Vt` (`setMode 6`
  ends in `moveTo 0 0`; `0x72` likewise) *and* on real terminals. So the cursor
  cannot be preserved across the hand-back; it has to be **placed**. `CSI 999 ; 1 H`
  parks it bottom-left, clamped by the receiver so the stream needs no size — where
  a program that painted the screen and exited leaves the next prompt.
* **`SGR 0` last.** DECSC/DECRC-style bundling (a real terminal's DECRC restores
  pen, charset, origin and wrap together) would otherwise undo resets emitted
  before it. This is also why the hand-back does *not* use DECSC/DECRC to save the
  cursor: the bundle it restores is exactly the state being reset.

`ESC \` from true ground is clean in both our model and reality (`stepEsc`'s default
arm → `ground`, nothing printed). The one state where our model prints a stray
backslash is a receiver caught in `escInter`: the `ESC` is consumed as a charset
designator and the `\` then prints. Real terminals treat ESC as a cancel-and-restart,
so the model is the pessimistic one; `restore` erases it with `ED 2`, and the
hand-back accepts one stray character in that rare state rather than risk the whole
stream being swallowed.

### Break-verified

`tests/attach_test.py` step 9 dirties the terminal from inside the session, detaches,
and asserts every reset plus "the stream leads with ST". Deleting the one
`writeAll` line in `Client.attach` fails 12 of the 13 assertions and the ST index
lookup raises. The sanity check ("the app state really reached the client terminal")
is there so the test cannot pass vacuously by the session never dirtying anything.

### What is NOT fixed, deliberately

The **window title**. `titleAnsi` sets it on attach, so linger is not yet invisible
to the terminal it borrows. We never read the user's title and the emitter does not
guess; xterm's title stack (`CSI 22 ; 0 t` / `CSI 23 ; 0 t`) would do it properly and
is not universal. Recorded as a known limit rather than left silent.

### Why this belongs in the theorem ladder, and where

`leaveAnsi` is a **strictly easier instance of Step 1's target**: no `ite`, no
dependence on `v`, and the canonical values are literals. So the `Sets` ladder that
Step 1 needs for `modesAnsi` should be built on the hand-back first and then reused
with `Sets.ite` for the session-dependent case, rather than the other way round.
The prerequisite is unchanged and is the edit Step 1 already named: factor the CSI
walk so it exposes the **dispatch**, not just the grid fact — `csi_digits_run_eq`
already carries `ignore` and `priv` through, and `org_*_decom_off` is the template
for one field.

## Step 0, second finding — XTGETTCAP echo was a command-injection channel — 2026-08-15T22:30:00Z

The Step 0 audit (a fanned-out read with adversarial verification) surfaced more
siblings than the hand-back. The one that mattered most is a **security** bug, and
it is the §Replay family pointed at the *child* rather than the client.

### The bug

`Terminal.xtgetcapReply payload = ESC P 0 + r ++ payload ++ ESC \` echoed the
requested capability name **verbatim**. That reply is routed by
`Session.onMsg .ptyOut` as `.writePty r.replies` — i.e. written into the child's own
pty **input**. And an XTGETTCAP request is child *output*: it arrives from whatever
the child prints, which includes untrusted data — `cat evil.txt`, an ssh stream, a
tailed log, a crafted filename in `ls`.

So a hostile file containing `ESC P + q 5 4 <CR> ; i d > /tmp/x <CR> ESC \` makes
linger write `ESC P 0 + r 5 4 <CR> ; i d > /tmp/x <CR> ESC \` into the shell's stdin.
On a cooked-mode tty the CR commits a line, and `;` separates commands, so the
injected `id > /tmp/x` runs. Classic terminal-reply injection (the xterm CVE class),
reintroduced because we echoed unvalidated child bytes.

Confirmed at the byte level:
`(feed (Vt.init 80 24) .ground [ESC,P,+,q,'5','4',CR,';','i','d',ESC,\]).replies`
= `[27,80,48,43,114,53,52,13,59,105,100,27,92]` — the CR (13) and `;id` are present.

Only `xtgetcapReply` echoes child bytes; every other owned reply is fixed
(`da1/da2/status/version/palette/decrqss`) or built from `digits` of the cursor/size
(`cpr`, `textArea`), all `0x30–0x39`. So the injection surface is exactly one builder.

### The fix

`xtgetcapReply` now filters the echo to the legal XTGETTCAP alphabet — hex digits and
`;` (`capByte`) — which is the payload format a conforming request uses, so it is the
identity on real queries (tmux's `ESC P + q 544e ESC \` is unchanged), and strips
exactly the bytes that could terminate a line from a malformed one. `54;d` remains
from the evil payload above: harmless, since no CR/LF means the shell never commits it.

Faithfulness notes: we still always reply *negative* (`0`), which is honest (we
support no cap); DECSTR-style broad resets were rejected for the same reason as in the
restore prologue (varies by terminal, and we would trust bytes we do not parse); and
the filter, not a reject, keeps the reply "shaped like" the query.

### The theorem, and why it is stream-wide

`feed_replies_noNl` (Theorems/Terminal.lean): for any `v`, scanner state and child
input, `(feed v s bs).replies` contains **no `0x0D` and no `0x0A`**. This is the
real invariant — "linger never writes a line terminator into the child" — and the
reason to state it over the whole stream rather than just `xtgetcapReply` is
regression: a *future* reply builder that echoed child bytes would fail this proof
rather than ship. Structure: `NoNl` (+ `nil`/`append`), one lemma per builder
(`noNl_digits` via `digits_range`, `noNl_filter` via `capByte_no_nl` + `List.mem_filter`),
`classifyCsi/Osc_reply_noNl` (a `repeat' split at h` case analysis — **`split_ifs`
does not exist here, there is no Mathlib**; core `split` with `repeat'` fully splits
the if-chain), `complete_reply_noNl`, `step_reply_noNl` (`cases s <;> simp only
[Scan.step] <;> (repeat' split)` then `all_goals first | …`), and `feed_replies_noNl`
by induction on the input.

`capByte_no_nl` is `⟨by rintro rfl; revert h; decide, …⟩` — no `∀ b : UInt8` decide
(no Fintype instance without Mathlib); substitute the concrete terminator, then the
`capByte 0x0D = true → False` goal is closed-term-decidable.

### Break-verified

Delete `.filter capByte` from `xtgetcapReply`: `noNl_xtgetcapReply`'s proof
(`noNl_filter _`) no longer typechecks — the no-newline invariant is *unprovable* for
the raw echo — and `xtgetcapReply_exact`'s `rfl` fails. So the theorem catches the
missing guard. Pinned three ways: the Lean proof, `Tests/Terminal.lean` (`evilXtget`
reply `.contains 0x0D = false`, with a non-vacuity check that the raw payload did
carry the CR), and `tests/terminal_query_test.py` step (the evil query over a real
pty, asserting the bytes linger wrote back carry no CR/LF and a filtered negative
reply still came back).

### The rest of the audit's survivors, recorded not fixed

The audit found more real ones, none a security hole, none fixed this session (one
item in flight). Triaged in `specs/restore-conformance.md` "Step 0 findings ledger"
so they are not lost:
- **resize-at-same-size wipes scroll region + tab ruler** (`Vt.resize` resets
  `top/bot/tabs` unconditionally; reattach at unchanged size → no SIGWINCH → the
  child never re-establishes them). Also makes `tabsAnsi` dead on the attach path.
  In-family and in-scope for a future restore step.
- **label values are not tab/newline-scrubbed** → a label can forge a row/status in
  `infoText`'s tab-separated listing (`name_clean` is proved for the status column
  only). Local-listing `cmd`/label fields also lost their `Remote.scrub` in a refactor.
- **pty input buffer (`rt.ptyIn`) is uncapped**, unlike the per-client 4 MiB output
  queue — §Bound's runtime half is asymmetric.
- **resume spawns the pty at hardcoded 80×24** while the restored `Vt` keeps the
  checkpoint's size, until the first sizing attach (narrow: `linger run` on a
  checkpointed-not-live session).
- **modes `Vt` does not model** (DECSCNM, ?1005/?1015, DECSCUSR) can be neither
  established nor cleared in either direction — a completeness limit of the model.
- **`.err` is dropped by `Client.attach`** (only `drainReplies` prints it) — a
  "too many clients" refusal reads as a clean detach.

## Ledger item 1 fixed — same-size reattach no longer wipes the scroll region/tabs — 2026-08-16T00:10:00Z

`Session.onMsg .attach` resized the `Vt` for every sizer client with no dimension
guard, and `Vt.resize` unconditionally sets `top := 0`, `bot := rows-1`,
`tabs := defaultTabs cols`. So a reattach at the *same* size wiped a child's
`DECSTBM` scroll region and custom tab ruler from the model — and since the winsize
did not change, the kernel sends no `SIGWINCH`, so the child (the only author of
those) is never nudged to re-emit them. Reproducible with `tabs -4` in your own
shell then `linger attach`.

Fix: guard the attach resize on an actual dimension change
(`s.vt.cols != cols.toNat || s.vt.rows != rows.toNat`). A genuine resize still runs
(the region and ruler are size-relative, so resetting them there is correct); a
same-size reattach now leaves the emulator alone. Chosen over guarding inside
`Vt.resize` to keep that heavily-depended-on def (and its `Good`/`renderable`/
`LiveReachable` proofs) untouched.

Theorem `onMsg_attach_same_size_vt`: with `s.vt.cols = cols.toNat` and
`s.vt.rows = rows.toNat`, `(onMsg s c (.attach cols rows)).1.vt = s.vt` — the whole
emulator, region and ruler included, is preserved. Executable pins in
`Tests/Session.lean`: child sets `CSI 2;4 r` + `CSI 3 g`, reattach at 20×5 keeps
`top=1 bot=3` and cleared tabs; a reattach at 40×10 resets `top=0 bot=9`
(non-vacuity — the guard, not a dead resize, is what preserves it). Break-verified:
dropping the guard fails both the test and the theorem.

Residual (still in the ledger): `tabsAnsi` is set-only, so restoring into a *fresh*
terminal whose ruler differs is not repaired by `restore` — the emitter would need to
be both-ways. Out of scope for this fix, which is about the same-size reattach.

## A5 outbound proved — the hand-back leaves canonical modes for ANY receiver — 2026-08-16T02:30:00Z

`leave_canonical (w : Vt) : (w.feed leaveAnsi).pstate = .ground ∧ (w.feed leaveAnsi).modes = ({} : Modes)`,
for **any** `w`, no hypothesis. This is A5's outbound value half — the theorem the
Step-0 hand-back finding earned — and the first receiver-quantified *value* claim in
the file (parser-quantified `restore_grounds`/`leave_grounds` came first).

### The predicate that worked: `MMap`, not `Sets`

`Sets P x bs := ∀ w, P (w.feed bs) = x` is **false for a lone chunk**: a receiver
mid-OSC swallows `modeSet 7 true` entirely, so `modes.wrap` is whatever it was. The
`∀ w` only becomes true once the stream is grounded first. So the working predicate
is the *from-ground* one — `MMap (f : Modes → Modes) (bs) := ∀ v, ground → u8 0 →
ground ∧ u8 0 ∧ (v.feed bs).modes = f v.modes` — the modes analog of `Keeps`, with a
`comp` law. `leave_modes` peels the `ESC \` lead-in with `st_grounds` (which grounds
any `w`), then composes the tail from ground. This is the generalization the spec's
open question anticipated ("can `Keeps` carry an arbitrary property"): yes — `MMap`
carries the modes projection; `Keeps` is the grid instance.

### The dispatch-exposing bridge (the spec's named prerequisite)

`modeSet_modes (n on) (0<n) (n<65535) (ground) (u8 0) : (v.feed (modeSet n on)).modes
= (v.setMode true n on).modes ∧ ground ∧ u8 0`. Feeding a private mode set from
ground has modes *exactly* `setMode true n on` — for **any** `n`, alt-screen modes
included. `keeps_modeSet` had to exclude 47/1047/1049 (they change the grid), but the
parser and the modes projection don't care, so `modeSet_modes` is unconditional in n.

Chain: `esc_step_eq` → `csi_open_step` → `csi_marker_step` (the `?`) → the digit run
carried by `Frame` (`= (cols,rows,modes)`, so `frame_csi_digits_feed` gives modes
preserved) → `csi_final_step_eq` → the dispatch, read off by `modes_csiDispatch_sm/rm`
(the `match` on the concrete final byte reduces, so those are `rfl` after the ignore
guard). `modes_setMode` (setMode's modes-output is a function of the input modes
alone; `split <;> (repeat' split) <;> simp_all` over setMode's arms, with
`modes_moveTo`/`leaveAlt`/`enterAlt` as the three "modes untouched" facts) ties the
walk-state's modes back to `v`'s.

### Per-chunk bridges and the fold to `{}`

`mmap_modeSet` (via `modeSet_modes` + `smMod`, the setMode-modes-as-a-function
witness), `mmap_irm` (the non-private IRM, a marker-free clone of the walk),
`mmap_keypad` (`ESC =`/`ESC >`), and the preservers `mmap_id_csi_seq` (+
`modes_csiDispatch_{stbm,cup,sgr}` — the last two by `exact modes_moveTo`; `stbm` by
`split <;> first | (rename_i heq; absurd heq (by decide)) | ((repeat' split) <;> …)`,
discharging the wrong-final arms of `csiDispatch` by their false byte equation),
`mmap_id_charset`, `mmap_id_si`. `leave_modes` composes them right-associated and
`MMap.congr`s the composite transform to `fun _ => {}` — provable by `rfl` because
each `smMod`/insert/keypad reduces at its literal mode number and every field ends at
its default.

### Engineering notes (Mathlib-free)

* **No `set` tactic** (Mathlib). Abstract the marker state as a `∀`-quantified helper
  (`modeSet_tail`) applied to the concrete walk, rather than `set w3 := …`.
* **No `split_ifs`** — core `split`, and `repeat' split` to exhaust nested ifs.
* **No `∀ b : UInt8, … := by decide`** (no Fintype instance) — substitute the concrete
  byte (`rintro rfl`) and decide the closed goal.
* `dsimp only` does **not** iota-reduce a `match` on a UInt8 literal, but `exact`/`rfl`
  (defeq) and `simp [·]` do; `csiDispatch`'s outer match is best left to `split` +
  absurd-arm discharge.
* Passing a hypothesis term (`hu : v.u8need = 0`) to a lemma with an implicit receiver
  **pins that receiver to `v`**; pass `(by rw [hu])` instead so the receiver unifies
  from the goal.

### Not yet: inbound, and the non-modes fields

`restore_modes_any` (inbound, certifies `87f64b3`) is the same machinery pointed the
other way; it waits on `MMap id (gridAnsi)` — the repaint preserves modes, i.e.
`quiet_gridAnsi` (origin only) lifted to the full record, plus `eraseScreen`'s
modes-frame for `ED 2`. Since `modesAnsi` overwrites every mode field absolutely, the
prefix only needs to be `MMap`-*something* (ground-preserving), not `MMap id`. The
non-modes projections (charset/region/pen/alt) repeat the `MMap` shape. All are
carried meanwhile by `Tests/Render.lean`'s `dirty`-receiver round-trips.

## A5 inbound proved — restore installs the session's modes into any receiver — 2026-08-16T05:30:00Z

`restore_modes_any (v w : Vt) (hmouse : v.modes.mouse ∈ {0,1000,1002,1003}) :
(w.feed (restore v)).modes = v.modes`. The mirror of `leave_modes`, and the
theorem that certifies `87f64b3` (the both-ways modes fix) instead of the tests
carrying it alone. Same `MMap` machinery pointed inbound.

### The discovery that made it cheap: no paint ladder needed

I set out expecting to need `MMap id (gridAnsi)` — lifting the whole repaint to
"preserves modes". **Not needed.** `restore v = PREFIX ++ modesAnsi ++ SUFFIX`, and
`modesAnsi` overwrites *every* mode field absolutely. So the prefix's effect on
modes is irrelevant; the prefix only has to reach `pstate = ground` so `modesAnsi`
parses. And it does: `prologue_grounds` grounds any `w`, then the `Ends` ladder
(already proven, `ends_screensAnsi` etc) carries `ground` through the paint —
**pstate only, no modes, no u8need for the paint.** The paint never enters a modes
proof. This corrected the plan the spec had recorded ("lift quiet_gridAnsi").

The one subtlety was `u8need`: `modesAnsi`'s first chunk is `modeSet 7` = `ESC [ …`,
and `MMap` wants `u8need = 0` at its start. The state entering `modesAnsi` is after
`titleAnsi`, whose leading `ESC` clears `u8need` and whose OSC body preserves 0
(`uz_titleAnsi`, built on `un_osc_run` + `uz_step_esc`). So `g1` is `ground ∧
u8need 0` without any paint-u8need reasoning either.

### The mouse allowlist is a real hypothesis, not a blemish

`restore_modes_any` is FALSE without `hmouse`. `modesAnsi` clears mouse (1000/1002/
1003 off) then re-sets the live one *only if it is in the allowlist* — a foreign
checkpoint with `mouse = 5` restores as mouse-off, not mouse-5. That is the
documented allowlist behavior (`modesAnsi`'s comment: 47/1047/1049 would switch
screens, 6 is DECOM), so the honest theorem carries `v.modes.mouse ∈
{0,1000,1002,1003}` — which `setMode` guarantees for any live `Vt`, so it discharges
for real sessions and is stated rather than hidden.

### Engineering notes

* `mmap_modesAnsi`'s composite of 13 record-update transforms is **exponential under
  `rfl`/`whnf`** (nested `{· with f}` has no sharing — each update copies 10 fields,
  ×13 = 10¹³ term). `rfl` and even single-field `rfl` time out at 1M heartbeats. The
  fix: a `cases`-based `Modes.ext'`, then each field via **`simp`** (which shares
  subterms and pushes projections top-down) rather than `rfl`. Nine fields close by
  `simp`; the mouse field needs `rcases hmouse` to decide the ite.
* Give each mode chunk its *explicit* record-update transform (`mmap_wrap` etc =
  `mmap_modeSet …|>.congr`), not the opaque `smMod`, so the composite is shallow
  record updates rather than nested `setMode` unfoldings.
* `MMap.ite` composes the transform by the same condition as the bytes; the mouse
  chunk (`if cond then modeSet mouse true else []`) uses it, with `0 < mouse` /
  `mouse < 65535` discharged from the ite's condition hypothesis.
* All Mathlib-free: no `set` (abstract via `∀`-helpers or explicit exprs), no
  `split_ifs`, no `tauto` (explicit `Or.inl`/`Or.inr`).

Break-verified: deleting `modeSet 25 v.modes.cursorVisible` from `modesAnsi` breaks
`ends_modesAnsi`, `quiet_modesAnsi` and `mmap_modesAnsi` together. Non-vacuity by
eval: a dirty client restored into a session with mouse=1000 ends with the session's
modes, and the client's own modes differ.

### What is left of A5

The non-modes restored fields — charset flags (`g0Line`/`g1Line`/`shiftOut`), scroll
region (`top`/`bot`), pen, alt-screen flag — as their own `MMap`-projection claims.
Each is touched by few chunks and repeats this pattern; carried meanwhile by the
`dirty`-receiver `roundtripsFrom` fixtures. The grid *cells* remain §Replay's open
induction (Steps 3–4), unchanged.

## Coverage enforcement + A5 pen + README-promise audit — 2026-08-16T08:00:00Z

Five things, from the "how do we enforce coverage" review.

### Gate hardening (tests/e2e.sh)
* **native_decide banned in `Theorems/`** — `! git grep -nE '\bnative_decide\b' --
  'Theorems/*'`. THEOREMS.md always promised proofs reduce in the kernel; now
  enforced. (Reworded Wire.lean's one comment that contained the literal token so
  the grep is a clean oracle — `verifier-in-the-loop`: a source-tree property can't
  be a theorem, the grep is the gate.)
* **Fuzz corpus un-held-out** — grep asserts `knownGap = #[]` and that the
  `failing 400 = []` / `failingDeep 150 = []` assertions exist un-weakened. The
  Tests build already *proves* they hold; this stops the assertions themselves from
  being shrunk.
* **No external Lean deps** — fail-closed `require`-in-lakefile + empty
  `lake-manifest` packages check (closes a README-promise gap, below).

### CLAIM_CAP 12 → 10
Claimed two genuinely-theoremed defs: `resizeEffects_owner_only` (only the size
owner resizes the pty — abduco's rule as a theorem, names both `resizeEffects` and
`sizeOwner`) and `resizeEffects_atMostOne`. Real invariants, not ratchet-gaming.
The residual 10 are constants (`ckptIntervalMs`, `outputChunk`), width/charset
helpers, and `infoText`/`rowText` — the last two want the label-scrub fix (Step-0
ledger item 2) before a clean claim, so they stay unclaimed honestly.

### A5 pen (a non-modes restored field)
`restore_pen_any (v w) : (w.feed (restore v)).pen = v.pen`, for any receiver.
`penSgr_feed` already gave `feed (penSgr p) = {v with pen := p}` from ground+u8need0;
the new machinery is the **pen-projection CSI walk** (`pen_moveTo`,
`pen_csiDispatch_cup`, `csi_tail_pen`, `pen_cursorAnsi`) showing the trailing
`cursorAnsi` (`CUP`/`moveTo`) preserves pen. u8need-at-penSgr threaded via
`un_modesAnsi` (modesAnsi ends in `CSI 4`, and `u8_zero_after_csi` zeroes u8need for
any prior state) + `mmap_id_charsetAnsi` carrying 0 through the charsets. This is
the FIRST non-modes field lifted off the fixtures. `csi_tail_pen` is a near-clone of
`csi_tail_modes` — the remaining fields (g0/g1/shiftOut, top/bot, altGrid) should
motivate generalizing `csi_tail` to an arbitrary projection rather than cloning it
three more times.

### README-promise coverage audit (workflow, 6 agents)
Classified all 72 README promises: 22 proved, 41 test-pinned (runtime IO, on
`tests/` by design), 6 bounded by a limitation/non-goal, 2 gaps — both fixed
(no-deps gate; LINGER_NO_DETACH_KEY test). Ledger + maintenance rule written into
THEOREMS.md "Coverage ledger": every README promise maps to a theorem, a test, a
limitation, or a non-goal — an unmapped promise is the shape that let the hand-back
ship, so it's a bug, not a doc lapse. Re-derivable by re-running the audit; a review
gate, not an automated one (a grep can't judge "does this sentence have backing").

## Step 1 notes (sticky fields) — 2026-08-16

**Claim landed.** `restore_sticky_any (v w) (Good v) (w.rows = v.rows)
(v.top < v.bot) : stick (w.feed (restore v)) = stick v`, where
`stick v = (rows, top, bot, g0Line, g1Line, shiftOut, altGrid.isSome)`. Three named
projections: `restore_region_any`, `restore_charset_any`, `restore_alt_any`. With
`restore_modes_any` and `restore_pen_any` this is **every restored field except the
screen cells**, all quantified over the receiver.

**Why these three needed different machinery from the modes and the pen.** Those
two are emitted in the *tail* (after the title), so their proofs stepped over
`gridAnsi` entirely — the prefix only had to reach `ground`. The sticky fields do
not: `regionAnsi` runs before the title, and `screensAnsi` switches screens **in
the middle of the repaint**. So `SMap id (gridAnsi …)` was unavoidable, and with it
the two operations the frames pass could not cover (`print`, `csiDispatch`).

**Design choices, with the reasons:**

1. **One bundled projection, not four `org_`-style families.** `Vt.stick`. Four
   layers × the un-framed operations ≈ 40 lemmas; the bundle ≈ 10. The frames note
   rejected bundling for fixing "only the fields we happened to need" — the answer
   is that this bundle is *closed*: `rows` has to be in it because `DECSTBM`'s
   clamp and the alt switch's region reset both read it. Everything framed is a
   one-line `by rw [frame_X]; rfl` (the trailing `rfl` is needed — `rw`'s implicit
   one only has reducible transparency and `stick` is a plain `def`).
2. **`csi_tail_proj`** — the CSI walk with the projection as a parameter, its one
   requirement being `PsBlind π` (a bare `pstate` update cannot move `π`; `rfl` for
   every field accessor **except `pstate` itself**, which is the one projection this
   walk cannot serve — and does not need to, since its conclusion pins the parser). `csi_tail_modes` and `csi_tail_pen` are now one-line
   instances, so the walk's *proof script* is written once instead of three times.
   Measured, because the first draft of this note said "shrank the file" and that is
   false: the region grew ~22 lines (the new docstrings outweigh the ~17 saved script
   lines), and ~5 lines even against the three-hand-copies counterfactual. The honest
   claim is that it paid for itself at the third projection and keeps a fourth free.
   `keeps_csi_tail` (grid) is *also* an instance — grid is `PsBlind` by `rfl` and its
   `hgrid` is `hπ`; a probe file derived its exact shipped statement from
   `csi_tail_proj`. It keeps its own copy only because it sits 1200 lines earlier in
   the file; collapsing it needs `PsBlind`/`csi_tail_proj` hoisted above the `Keeps`
   section (feasible — the proof's dependencies all precede it). The first draft of
   this note gave "a dispatch does write cells" as the reason, which is wrong: the
   *not*-writing is the hypothesis, discharged per final byte by the caller.
3. **`smap_csi_one_arg`** — the digit-run-and-dispatch walk, once for both markers
   (`CSI ? n h/l` and `CSI n h/l`), where `mmap_irm` and `modeSet_tail` had each
   done it by hand. Delivering the *closed collector's contents* (`t.params =
   s0.params.push (n, s0.curSub)`) rather than a computed `arg` is what let the
   same lemma serve the two-parameter `DECSTBM` walk: stage one closes the first
   parameter with `;` (`stick_csi_semi_open`), stage two is `stick_csi_arg_tail`
   again with a one-element collector.
4. **`SMap` carries no `u8need`.** This is the discovery of the round and it is why
   the repaint is affordable as a chunk. Every CSI/ESC chunk clears a half-decoded
   character at its own leading `ESC` (`uz_step_esc` needs no hypothesis), and a
   text run cannot move a sticky field whatever is pending. So `SMap` is the
   `Quiet` shape, not the `MMap`/`Keeps` shape — and the text case (`SMap.text`,
   excluding only `ESC`/`SO`/`SI`) is *true*, where `Keeps.text` would be false.
5. **`dims_feed_ne_ris`** — the dims layer's `Good` hypothesis exists for `RIS`
   alone, and no linger stream emits `ESC c`, so the `ST` lead-in's height fact
   holds for **any** receiver. Needed because the lead-in *can* move a sticky field
   (a receiver caught mid-`ESC (` reads our `ESC` as the designator byte), so the
   value chain starts from an unknown state whose only known field is `rows`.

**Two long-range dependencies, now visible in the theorems.** `charsetAnsi` is
set-only for the shift state (`if v.shiftOut then [SO] else []`) and `regionAnsi`
emits nothing for a whole-screen region. Both claims therefore run back through the
whole repaint to the prologue's `SI` and `CSI 1 ; rows r`. They hold, and
`smap_charsetAnsi`'s transform (`so := if v.shiftOut then true else s.so`) now says
out loud that it *rests on* the prologue. Same set-only shape `87f64b3` fixed in
`modesAnsi`; deliberately **not** changed, because the dependency is now proved
rather than assumed and making it absolute would move emitted bytes for no
behavioural gain. Worth watching if either emitter is reordered.

**Hypotheses, and what they exclude.** `Good v` bounds `v.rows ≤ 1000` (so
`DECSTBM`'s parameters are never clamped to 65535) and gives `v.bot < v.rows`.
`v.top < v.bot` is the region `DECSTBM` will *accept* — the exact analog of
`restore_modes_any`'s mouse allowlist, and needed for the same reason
(`Checkpoint.load` is total on arbitrary bytes, so a foreign checkpoint can hold a
region no emulator would produce). The excluded case is a one-row region
(`v.top = v.bot`): `CSI t ; t r` is refused here and on every real terminal, so
there is nothing to install and nothing to claim.

**Break-verified.** Two isolating breaks and two cascading:
* `charsetAnsi`'s shift-state condition negated (`if !v.shiftOut then [SO]`) —
  fails **only** `smap_charsetAnsi`. ✓
* `regionAnsi`'s `DECSTBM` top parameter off by one (`v.top + 2`) — fails **only**
  `smap_regionAnsi`. ✓
* prologue resets `?1048l` instead of `?1049l` — fails `ends_prologueAnsi`,
  `quiet_prologueAnsi`, `prologue_grounds` **and** `restore_sticky_any`.
* `charsetAnsi` designates G0 as set `1` instead of `0` — fails the older
  `ends`/`quiet`/`keeps`/`mmap` charset lemmas **and** `smap_charsetAnsi`.
The cascades are because the older ladder names the mode number / designator byte
explicitly; the two isolating breaks are the evidence that the *new* claims are not
implied by anything already proved.

**Negative results / traps hit, so the next session does not repeat them:**
* A multi-line `{ s with f := …, g := … }` must indent its continuation lines at
  least to the **first field's** column, not just past the `{`. Otherwise the
  parser stops at the comma with "unexpected identifier; expected '}'" and the
  `have` recovers as a truncated record — which then shows up as a confusing
  *elaboration* error somewhere else.
* Composing the twenty per-chunk transforms symbolically and evaluating the nest at
  the end blows up: each record update duplicates its argument once per field, so
  the goal became megabytes (same failure mode as `mmap_modesAnsi`'s 13-transform
  `rfl`). Fix: `sput_step`/`sput_congr` — carry explicit *values* and normalize
  after every rung. Destructuring the one opaque intermediate (`obtain ⟨Ar, At, …⟩`)
  is what makes the per-rung `show`s small enough to write.
* `congrArg Sticky.top h` for the field corollaries times out at `whnf` (the
  elaborator tries to reduce `stick (w.feed (restore v))`). Fix: projection lemmas
  on a *variable* receiver (`stick_top (u : Vt) : (stick u).top = u.top := rfl`) and
  `rw [← stick_top _, h, stick_top]`.
* `split` on `Vt.setMode` reverts hypotheses mentioning `n`, so a `by_cases n = 47`
  *before* the split is useless in the split's branches. Case on the three
  screen-switch numbers with `subst` + `show` instead, and let the catch-all arm's
  own disequalities discharge `stSetMode`.
* `intro a b - -` does **not** anonymously introduce in Lean 4 core `intro`; the
  `-` parses as subtraction and the goal becomes `Int`. Use `_`.
* Never build these edits with a Python `s[i:j]` slice whose indices can invert:
  `s.replace('', new)` inserts `new` between *every character* (373 MB file, 251k
  copies). Recovered by `s.replace(new, '')`, but use exact-string edits.

### A5 outbound, same round
`leave_canonical_all (w) (2 ≤ w.rows)`: parser `ground`, modes default, sticky
canonical (`⟨rows, 0, rows-1, false, false, false, false⟩`) and pen reset. Item 2b of
the spec's Definition of done had asked for the non-modes fields on the hand-back
side too, and `leave_canonical` covered only modes + parser — so marking 2b done on
that basis would have been an overclaim, and the asymmetry (inbound complete,
outbound modes-only) is the same shape that let the hand-back ship. Cost with `SMap`
already in place: one more `sput` chain plus two small pieces.
* `smap_stbm_plain` — `CSI r`, `DECSTBM` with **no** parameters. Not an instance of
  `smap_csi_one_arg` (nothing to walk) nor of `csi_tail_proj` (the dispatch is the
  point): both arguments fall back to their defaults, `1` and the **receiver's own**
  `rows`, which is how the hand-back names "the whole screen" without knowing the
  size. Hence the `2 ≤ w.rows` hypothesis — a one-row region is refused by DECSTBM
  here and on every real terminal, so nothing can be established.
* The trailing `SGR 0` **is** `penSgr {}` (`penAttrCodes {} = [0]`, both colours
  default so `sgrColorSeq` is `[]`), modulo two `List.append_nil`s — so
  `penSgr_feed` gives the pen with no new machinery. `show csiNum 0 0x6D ++ [] ++ []
  = csiNum 0 0x6D; simp` is the way to state that (simp with the defs unfolded
  strands `sgrOf [0] = csiNum 0 109`; `show` gets there by defeq instead).
* `smap_id_irm_reset : SMap id (csiNum 4 0x6C) := smap_id_irm false` — a chain of
  `sput_step`s has to match the emitter's bytes *syntactically*, and
  `smap_id_irm false` states them as `csiNum 4 (if false then 0x68 else 0x6C)`.
  Defeq is not enough once you want to `rw` the byte list.
Not covered outbound, deliberately: the final **cursor position** (`CSI 999 ; 1 H`
is clamped by the receiver) and the **window title** (we never read it — the
standing known leak).

### Adversarial review of this round (workflow: 5 lenses, per-finding refutation)
Ran before committing. **No defect in the Lean survived refutation** — the proofs and
their hypotheses held up, including a specific attempt to show `v.top < v.bot` was
misattributed as "the analog of the mouse allowlist" (refuted: `Checkpoint.load` is
total on arbitrary bytes for both fields, so the analogy is exact). What did survive
was one real product bug and six prose defects; all are fixed above or recorded:

* **The bug: `tabsAnsi` is set-only.** Now ledger item 0 in the spec and the twelfth
  infidelity in THEOREMS.md. Found by asking this spec's own question of a field no
  theorem covers, and *reproduced against `replayEq`* rather than argued. Worth the
  lesson: the review found it because the finder was pointed at "what does `restore`
  write that has no receiver-quantified theorem", which is a question the summary
  prose ("only the cells remain") had actively obscured.
* **"Only the screen cells remain on the round-trip fixtures" was false** — title,
  tab ruler and DECSC slot also have no receiver-quantified theorem, and
  `restore_cursor` is still `Vt.init`-quantified. Fixed in THEOREMS.md and the spec;
  the four are now named, because an inaccurate "what's left" list is precisely what
  stops the next round from asking the question that just paid.
* Spec's "Steps 3–4 are the only part of the Definition of done still open" —
  item 3 (Step 2's u8need half) is open too. Fixed.
* Spec's Step 1 body still read "**Inbound, the next step** … the one missing bridge
  is `MMap id (gridAnsi)`", contradicting the front block's own note that no paint
  ladder was needed. Rewritten past-tense.
* Ledger item 1 still read as "real, not yet fixed" in the present tense though
  `33b107e` fixed it — and its fix is *what made item 0 reachable*, so the staleness
  hid a live bug. Struck through with that connection recorded.
* "`PsBlind` is true of every field accessor by `rfl`" — `pstate` is the exception.
  Fixed in THEOREMS.md and above.
* "the refactor reduced/shrank the file" — measurably false. Corrected above.
* `csi_tail_proj`'s docstring blamed the grid walk's hypothesis shape; the real
  reason is file order, and a probe file derived `keeps_csi_tail` from
  `csi_tail_proj` to prove it. Docstring corrected.

Method note worth keeping: the lens that paid was "**does the prose match the
Lean?**", and it paid *because* the prose was where the overclaim lived. Two lenses
aimed at the Lean itself (vacuity, transform-vs-semantics) found nothing that
survived — which is the outcome to expect when the theorems were built against the
emitter, and is the reason to keep spending the review budget on the summary
documents instead.

### Ledger item 0 fixed — `tabsAnsi` emitted unconditionally
Same session it was found, because it is a *behaviour* bug and the reproduction was
already in hand. `tabsAnsi` no longer guards on `v.tabs == defaultTabs v.cols`; it
always sends `CSI 3 g` then one `CHA`+`HTS` per stop. Cost: ~70 bytes per attach for
an 80-column default ruler. Benefit: the field stops being right-only-when-the-
client-is-pristine, which is the one thing this spec says a client never is.

Measured, before and after, with `./lake env lean` on a probe (`sess := screen 20 3
"hi"`, receiver `dirtyTabs` = `CSI 3 g` + CHA/HTS at 5, 9, 13, 17):
* `(tabsAnsi sess).length`: 0 → 17
* `((dirtyTabs 20 3).feed (restore sess)).tabs == sess.tabs`: false → **true**
* `... == (dirtyTabs 20 3).tabs`: true → **false** (the leak is gone)
* `roundtripsFrom (dirtyTabs 20 3) sess`: false → **true**
* `roundtripsFrom (dirty 20 3) sess`: true → true (the old dirty receiver never
  moved the ruler, which is exactly why it missed this)

Proof churn was mechanical and small: `ends_`/`quiet_`/`keeps_`/`smap_id_tabsAnsi`
each lost their one `*.ite` line, since the guard they were splitting on is gone.
Nothing else referenced the emitter's shape.

Break-verified: restoring the guard fails the three new `dirtyTabs` fixtures
(`Tests/Render.lean` — the was-false-before assertion, the round trip, and the
`isEmpty` non-vacuity) plus the four proofs whose `ite` line went away.

The fixture set now includes a second non-vacuity case worth keeping: feeding only
`prologueAnsi ++ SGR 0 ++ ED 2` into the dirty-ruler receiver leaves its ruler
untouched. That is the assertion that says *why* the emit is load-bearing — no `TBC`
in the prologue, and `ED 2` does not touch tab stops — rather than just that it
happens to work.

`restore_tabs_any` is now provable and deliberately not proved: `tabs` is an
`Array Bool`, so it is not a scalar to fold into `stick`, and it wants its own
projection plus a `TBC`-then-`HTS`-fold argument. Cheapest remaining
receiver-quantified field; noted in the spec as a warm-up option before the grid
induction. **The ordering lesson: this is the one field where the fix had to precede
the theorem, because the theorem would have been false.** Which is the answer to
"why prove what the tests already cover" — the proof attempt is what makes you look,
and looking is what found it.

## Step 2 notes — 2026-08-17

**Closed, and the second half cost almost nothing.** `restore_u8_zero (v w) :
(w.feed (restore v)).u8need = 0`, for any receiver, no hypothesis — fifteen lines.
The insight is the mirror of the lead-in: `restore` *ends* with `cursorAnsi`, one
`CSI … H`, and `u8_zero_after_csi` zeroes `u8need` whatever the incoming state was.
A CSI's final byte cannot leave a character half-decoded, so the whole stream in
front of it is irrelevant to this half. `restore_quiesced` had the same proof but
over `Vt.init cols rows`; generalizing it was a matter of not instantiating the
receiver. Composed as `restore_quiesced_any` and (Theorems/Resume.lean)
`resume_quiesced_any`, which lifts anchor A1's parser half off `Vt.init`.

**The exit criterion was wrong and this is the same correction item 1 needed.** It
asked for `Ends`/`Quiet`/`Keeps` themselves to drop the ground-parser hypothesis. A
per-chunk predicate *cannot*: a receiver mid-OSC swallows a lone chunk, which is
precisely why `Sets` became `MMap`. Receiver-quantification belongs at the top level,
with `st_grounds` peeling the lead-in exactly once. Restated in the spec that way —
worth keeping as a pattern, because both halves of this spec discovered it
independently before anyone wrote it down.

`Quiet`'s origin half is **subsumed**, not carried: a receiver-quantified "DECOM ends
off" is the `origin` component of `restore_modes_any`. What is genuinely not done is
`restore_cursor` off `Vt.init` — where the cursor lands depends on where the paint
left it, so it is a grid-level claim and belongs with Step 4, not here. Moved.

Break-verified: appending a dangling UTF-8 lead byte (`0xC3`) to `restore` fails
`restore_u8_zero`; replacing the prologue's `ESC \` with `ESC 7` fails
`restore_grounds`. Both also fail `restore_sticky_any` — the value claims are
sensitive to *both* ends of the stream, which is a fact worth having recorded.
Witnessed in `Tests/Render.lean`: receivers mid-UTF-8, mid-OSC and mid-CSI each come
back quiesced.

### The vacuity lens, done by hand
The review workflow's `vacuity` agent never returned — 28 agents, 27 results, and
that one ran ~9.5 h (still writing, 42 `Bash` calls, so looping rather than hung).
Killed it and did the lens directly. It found one real thing, which is why it was
worth not skipping:

* **`Good v` was stronger than the proof needs.** `restore_sticky_any` used it for
  three arithmetic facts only (`botLt`, `rowsLe` → the parameter clamp, `rowsPos`),
  while `Good` also asserts things about the cursor, the saved slot, the scrollback
  and the CSI accumulator that the proof never reads. A hypothesis a proof does not
  use makes the theorem weaker than it is, so the primary form now takes
  `v.top < v.bot`, `v.bot < v.rows`, `v.rows < 65535` — the region `DECSTBM` accepts
  plus the clamp, i.e. exactly what the emitter's guards are about — and
  `restore_sticky_good` is the `Good`-flavoured entry point. Same for the three
  projections.
* Non-vacuity is now witnessed rather than argued (`Tests/Render.lean`): the `dirty`
  receiver differs from the session on *every* group the bundle names before the
  restore and agrees on all of them after; the session-side hypotheses hold for an
  ordinary 3-row screen; and the excluded case (a one-row session, `top = bot`) is
  pinned so it cannot be mistaken for an oversight.

Lesson for the next review round: run the lens aimed at the *hypotheses* even when
the theorem is green, and cap the agent — the one that found a real defect is also
the one that would have run forever.

## Step 3 notes (the layer under the induction) — 2026-08-17

Mapped the existing machinery with a fanned-out read before writing anything, and the
map changed the plan: the row induction was blocked on **named facts**, not on the
induction. Landed the three clusters it found, all break-verified.

**1. `OffScreen` — the cut `print` induces.** The frames pass named two operations it
could not cover; `print` is one. `Vt.offScreen` bundles everything outside
`grid`/`cursor`/`sb`, so `off_print` composes its five stages **by transitivity**,
which a frame equation cannot do, and each field invariance is one `congrArg`. This is
the same move as `stick` (§Restore) at a different cut, and it is the general answer to
"a fifth invariance layer costs 28 lemmas": bundle at the cut the *operation* makes,
not at the fields you happen to want.
Payoff beyond the obvious (`pen_print`, `ins_print`, `wrap_print`, charsets): **`u8acc`**.
`Render.cellText_feed`/`utf8s_feed` carry `u8acc = 0` as a hypothesis, so a row
induction must re-establish it per cell, and nothing said a print preserves it.
`ua_print'` is now a `congrArg`.

**2. Where the cursor goes.** All three `print_*_eq` lemmas take
`cursor.pending = false`, so the induction re-establishes it for column k+1 or it
stops. `cursor_printAdvance_lt`/`_ge` + `cursor_print_narrow_fits`/`_margin`,
`cursor_print_wide_fits`/`_margin`, `cursor_print_mark`. The margin cases are the
2026-08-15 negative result *as a theorem*: at the right margin the advance clamps the
column and arms wrap-pending, which no absolute cursor move can express.
Proof idiom worth reusing: `write_frame`, a private helper taking the write as a
function `f` plus `∀ u, offScreen (f u) = offScreen u ∧ (f u).cursor = u.cursor`, and
returning the three facts `printAdvance` needs about its input. Both narrow and wide
cases instantiate it; the wide one just chains one more `off_putCell'`.

**3. The two byte→cursor bridges.** `cup_places_cursor` covered two-argument `CUP`
only, and the repaint uses two other addressing forms with no bridge at all:
`home_places_cursor` (bare `CSI H`, both arguments defaulted — what establishes column
0 row 0 for the first cell, and why `?6l` must precede it) and `cha_places_cursor`
(`CSI n G` = `setCol (n-1)`, row untouched and wrap-pending cleared — what the
wide-with-marks branch needs, since the mark must land between glyph and shadow).

Also: `paint_grounds`, hypothesis 1 of `restore_grid_of_paint`, for any receiver.
Hypothesis 2 (`u8need = 0` after the paint prefix) is **not** free the same way and the
asymmetry is worth naming: the whole stream ends in a `CSI … H`, so `restore_u8_zero`
is three lines, but this *prefix* ends in glyph bytes. It goes with the cell induction.

**Traps hit:**
* `rw [congrArg Field h]` fails where `exact congrArg Field h` succeeds: the rewrite
  wants a syntactic match for `(offScreen X).cols`, the goal has `X.cols`, and they are
  only defeq. Use `exact` for projection-of-bundle facts.
* `unfold Vt.csiFinish` leaves `let s := …; let v := …` in the goal; a later
  `rw [show … csiDispatch …]` then finds no match. Insert `dsimp only` after the
  `if_pos`/`if_neg` pair. (Cost me one build cycle; it is the same trap as
  SCRATCHPAD:3369.)
* `printChar_id_of_ascii`: reduce the *inner* `if` before the outer one, via
  `rw [show (if (false : Bool) = true then decLine c else c) = c from rfl]`. Going
  outer-first makes `if_neg`'s side goal contain free variables and it is rejected
  ("Expected type must not contain free variables").
* Two 60-second breaks plus a restore exceeds a 2-minute Bash timeout, and the timeout
  leaves **Core mutated**. Run one break per invocation and `diff` Core against the
  backup before doing anything else.

**On the map itself — the lesson is about the worklog, not the agents.** The readers
reported `mend_of_pairOk`, `mendAt_of_pairOk`, `mend_blankRow` as non-existent (they
are in `Theorems/Render.lean`, not `Theorems/Vt.lean`) and reported `penSgr_feed` /
`sgrOf_feed` as gaps by quoting SCRATCHPAD entries written *before* those landed.
Every disputed claim was grepped before being planned on. **A stale worklog entry is
indistinguishable from a current gap**, which is an argument for closing entries when
the thing lands, not only appending. The genuinely-missing list survived the check and
is what got built.

### The hazard enumeration for Steps 3–4 — what it changed
Two agents enumerated cell shapes and the row→grid boundary against the emitter and
the parser. The synthesizer that was to turn it into a design **stalled and the
workflow failed** (I inlined the maps *and* the hazards into its prompt at
`effort: 'max'` — too big; next time pass a digest or let it read the journal). The
enumeration itself was the valuable half, and five of its findings are now recorded in
the spec because each is a way the obvious statement would have been **wrong**:

1. The parser component is a **triple** (`pstate`, `u8need`, `u8acc`), not a pair —
   the wide-with-marks rung goes CSI → glyph inside one cell, so `u8acc = 0` has to be
   re-established, not assumed once.
2. **The wide pair is one induction step advancing `k` by two.** If `k` ever sat
   between base and shadow, `halfPair (k-1)` is true at that moment and the re-mend
   blanks the base the previous rung painted. I would have written it as two steps.
3. **The row-exit `pending` is branch-dependent**: `modes.wrap` after a plain last
   cell, **false** after a marked wide last cell (its trailing `CHA` cleared it). So
   the conclusion must claim `x = cols - 1` and let the following `carriageReturn`
   re-establish `pending` — it discards it unconditionally.
4. `RowOk` is load-bearing for row **isolation**, not just agreement: a width-2 base
   in the final column would wrap and the joining CRLF would scroll the whole grid.
5. `cols = 1` must not be excluded (the fuzz `dims` includes `(1,1)`); `cols = 0`
   needs no side condition.

**And it corrected Step 4's plan.** The spec said the no-scroll argument "needs Step
1's scroll-region claim". It does not — citing `restore_region_any` or
`restore_alt_any` there is a category error, because those are *end-of-stream*
conclusions and `regionAnsi` is emitted **after** the paint. The paint needs three
*mid-stream* facts about what the prologue leaves (`top = 0 ∧ bot = rows - 1`,
`altGrid = none`, `origin = false`), the first of which exists today only inside
`restore_sticky_any`'s proof and has to be lifted out. Two named traps: `smap_id_gridAnsi`
looks like a no-scroll theorem and is only region-*persistence*; `stick_lineFeed` is an
unconditional theorem about the operation that *does* scroll.

**One genuine new receiver hypothesis, and it is a real limit on "any receiver".**
`ED 2` does not make the receiver's rows the right length — `eraseScreen` is a fold of
`eraseRowSpan`, which writes into *existing* cells, so a receiver with short rows stays
short and writes past the end vanish. The grid claim needs `GridOk w.cols w.rows w.grid`
(i.e. `Renderable w`) on the receiver, alongside `w.cols = v.cols` and
`w.rows = v.rows`. Worth stating in the theorem rather than a comment: unlike the modes,
pen and sticky claims, the *cells* cannot be claimed for a literally arbitrary receiver.

## Coverage, generality, and whether the target is too strong — 2026-08-17

Asked to check that the theorem shapes are general enough, that they are about the
code that runs, and that coverage is **enforced**. Measured rather than reassured;
three real problems, all now fixed or named.

### 1. The old coverage gate was theatre, and provably so
`CLAIM_CAP` grepped all of `Theorems/*.lean` for each core def's name. It cannot tell
a claim from a word, and it was fooled in the worst possible place: **`Render.history`
— a byte stream the binary writes to the user's terminal — counted as "claimed"
because the word "history" appears in a doc comment in `Theorems/Session.lean`.**
Measured: of the ten it flagged, **nine had zero mentions anywhere**, so what it
actually measured was "is this name absent entirely".

`tests/coverage.py` replaces it with two checks a grep genuinely *can* judge:
* **statement-level ratchet** — comments stripped, and only the text between
  `theorem <name>` and the `:=`/`by` counts. Honest number: **27 of 229** core defs
  named by no theorem statement, where the old gate said 10. The real uncovered
  surface was 2.7× the ledger's claim.
* **runtime-emitter classification** — every `Render.<f>` returning `Bytes`/`String`
  that is referenced outside `Zmx/Core/Render.lean` must be listed as proved or
  bounded. The runtime's emitter surface is exactly three: `restore`, `leaveAnsi`,
  `history`.

Break-verified, three ways: claiming `history` is theorem-backed fails (it is in no
statement); lowering the cap by one fails; pointing the runtime at a fourth emitter
fails *and* the now-stale entry for the old one fails, so the list cannot drift into a
description of the past.

Trap worth keeping: my first version of the emitter check reported `rowAnsi`,
`rowText` and `safeChar` as runtime-emitted — all three hits were **doc comments** in
`Zmx/Core/Vt.lean`. I had written a gate that reads prose while complaining about a
gate that reads prose. `strip_comments` is load-bearing in both checks.

### 2. Not general enough — found and fixed
`restore_cursor` and `resume_cursor` were still quantified over `Vt.init v.cols v.rows`.
That was an artefact of *when* they were written, not of what they need: the claim is
about the stream's final `CUP`, which addresses absolutely. The three facts the
fresh-emulator form got for free are all available for any receiver now — parser
ground (`restoreBody_grounds`, new), DECOM off (`restoreBody_modes_any`, new — this is
`restore_modes_any` one chunk earlier), dims unchanged (`dims_feed`). So
`restore_cursor_any` and `resume_cursor_any`, lifting **anchor A1's cursor half** off
the fresh-terminal assumption.
`Good w` on the receiver is honest and load-bearing: `dims_feed` needs it because
`RIS` re-clamps through `Vt.init`, and `dims_feed_ne_ris` is too crude here — the
*painted text* contains the byte `0x63`, so "no `ESC c`" is not a byte-set property of
the stream. Every client's emulator satisfies `Good` (`good_of_liveReachable`).
Combined with last round's `Good v` → three-inequality weakening of
`restore_sticky_any`, the over-hypothesis sweep is done for the value claims. The
remaining `Vt.init`-quantified theorems are either superseded-but-kept
(`restore_quiesced`, `resume_quiesced`, `resume_exact`) or genuinely *about* `Vt.init`
(`good_init`, `renderable_init`, `init_dims`, `liveVt_init`).

### 3. Too strong? — the fear is well placed, and the answer is opportunity cost
`restore_grid_any` is the one candidate for over-reach, and the hazard enumeration
priced it: it needs `GridOk w` **plus** `w.cols = v.cols` **plus** `w.rows = v.rows`,
so it is *not* "any receiver" — `ED 2` does not make a short-rowed receiver's rows the
right length. Against that, the spec's own evidence: of the twelve infidelities found
in `restore`, **zero** would have been caught by the row induction. It buys
universality over the fuzz corpus, which is worth having and worth having last.
Meanwhile the statement-level measure names a queue that is *more* likely to catch
something, because it is claim-less runtime-facing surface: `infoText` (and Step 0
ledger item 2 is an **unfixed injection bug** in exactly that framing — labels are not
tab/newline scrubbed, while `name_clean` proves the status column is), `outputMsgs`/
`outputChunk` (what a client receives), and the checkpoint codec's
`parseRecord`/`records`/`knownTag`/`magic`/`writeU32`.
Recommendation recorded: keep the grid induction last, and treat the claim-less
runtime surface as the higher-yield queue — the same argument the spec used to order
Step 1 before Step 4, applied one level out.

## Ledger item 2 fixed and proved — the forged listing record — 2026-08-17

Went to the top of the queue the new statement-level coverage measure produced, and it
was there for a reason: `infoText` had no theorem **and** a live injection bug.

`infoText` framed records as `k` TAB `v` LF through a `String` interpolation, and
`.labelSet`/`linger set` apply no filter — so `linger set s x=$'a\nstatus\tlive'` forged
an extra record, including a `status`/`state` pair that `linger list` would display as
the session's state. `Status.name_clean` proves the *status* column carries no framing
byte; every other column bypassed it.

**Fixed at the emit site, not at `.labelSet`.** `infoText` now builds `List UInt8` with
`Render.utf8s`, which maps a C0 control — tab and newline included — to U+FFFD. Same
argument `gridAnsi` makes for establishing its own pen: a guard at the emit site needs
no invariant about where the field came from, and it covers fields nobody has added yet.
A scrub at the setter would have had to be repeated for every future field.

**The restructure is what made it provable, and that is the transferable part.** The old
shape ended in `String.toUTF8`, and a `String` does not reduce in the kernel — the exact
argument in `Zmx/Core/Render.lean`'s header. Byte-level now, so:
* `infoText_framing` — every byte is a framing byte or printable content;
* `infoText_records` — as many newlines *and* as many tabs as fields. This is the
  anti-forgery claim: an injected newline would push the count above the field count,
  and `Remote.parseRecord` reads one record per line.
`infoFields` split out as a named stage so the framing claim has something to count.

Fixture pins the **before** as well as the after, which is worth doing when the fix
deletes the buggy shape: `Tests/Session.lean` computes the old
`String.join`/`toUTF8` path on the same state and shows it emits *one newline too many*.
So the channel is documented, not merely closed. Break-verified: restoring the
interpolation fails both theorems and three fixtures.

### What the coverage gate did while I worked
It fired twice, correctly, and both times on real signal rather than noise:
* after the restructure, `Render.utf8s` became byte-producing code reached from outside
  `Render` (by `Session.infoText`). The gate demanded it be classified. It is genuinely
  theorem-backed (`utf8s_no_ctl`, `utf8s_no_esc`, `utf8s_no_esc_bel`, and the new
  `utf8s_no_frame`), so classifying it was the right answer rather than a workaround —
  and the EMITTERS table is now a more complete description of the code than it was.
* the statement-level ratchet dropped 27 → 26 the moment `infoText` acquired a claim,
  which is the ratchet doing exactly what it is for. Lowered the cap in the same commit.

Two `Vt.init`-quantified theorems remain that are *not* about `Vt.init`:
`restore_quiesced` and `resume_quiesced`/`resume_exact` — kept deliberately, since the
fresh-terminal form is what `Tests/` exercises and the `_any` versions supersede them.

### §Chunk at the session layer — 2026-08-17
Next off the coverage queue: `chunksOf`, the function that splits what a client
receives into ≤ 64 KiB `output` frames. It had appeared in `Theorems/` exactly once, in
a **comment** — the same blindness that hid `infoText`. Two claims, both about what the
runtime sends: `outputMsgs_faithful` (the payloads concatenate back to exactly the bytes
handed in, so a reattaching client gets the whole repaint rather than a prefix) and
`outputMsgs_bounded` (no frame exceeds the cap, which is what makes every `output`
message well-formed by `Wire`'s §Bound measure). Ratchet 26 → 23.

Proof note: `chunksOf` recurses on `l.drop n` under a well-founded measure, and
re-supplying its `decreasing_by` inside a theorem fought the auto-bound hypothesis
names. Inducting on a length **bound** instead (`chunksOf_flatten_aux`, `chunksOf_le_aux`)
keeps both proofs Mathlib-free and short. Watch the `nil` base case: `split` still
generates the `isFalse` branch, which is impossible because `[].length ≤ n` always —
discharge it with `absurd (Or.inl …) h` rather than expecting `simp` to see it.

**The break-verify found a defect in my own statement, which is the lesson worth
keeping.** `outputMsgs_bounded` was first stated as `∀ c ∈ chunksOf outputChunk bs,
c.length ≤ outputChunk`. Doubling `outputMsgs`' chunk size — the exact regression the
claim exists to catch — left it **green**, because the statement never mentioned
`outputMsgs`. Restated through `outputMsgs_payloads` (the frames' payloads *are* the
chunker's output), and both claims now fail on that break. Generalizing: a claim whose
statement does not mention the function that runs is a claim *next to* the code, not
about it — which is the same failure the coverage gate was built to catch, one level in.
This is now the second time today that shape appeared; worth watching for in the
remaining queue.

### The last limitation closed — `history` proved — 2026-08-17
`Render.history` was the one entry in `tests/coverage.py`'s EMITTERS table classified as
*bounded* rather than proved, because it was assembled through `String`
(`rowText` → `String.intercalate` → `String.toUTF8`) and a `String` does not reduce in
the kernel. Walked the route the entry itself recorded: `rowChars` and
`dropTrailingBlanks` as named stages, `rowText : Row → Bytes`, and `history`'s plain
branch as `rows.flatMap (fun row => rowText row ++ [0x0A])`.

* `history_framing` — every byte is a line terminator or printable content.
* `history_lines` — the newline count **is** the row count. This is the claim that
  matters: `linger history` is line-oriented output a caller may parse, and a cell is
  attacker-influenced (a program in the session writes whatever it likes into the grid),
  so "a cell cannot forge a line" is the same §Row-integrity property as `infoText`'s.
* `rowChars_scrubbed` — the scrubbing happens at the **fold**, not only at the encoder.
  Worth its own theorem: `rowText_scrubbed` is true regardless, because `utf8s` scrubs
  again on the way out, so without this the claim would rest on a single guard.
  Break-verified by dropping the `safeChar` in the fold — only `rowChars_scrubbed` fails,
  which is exactly the point (the outer guard still holds).

Behavioural note recorded in the docstring: the old shape emitted a lone newline for an
*empty* row list, the new one emits nothing. Unreachable for a live session (`clampDim`
keeps a grid at ≥ 1 row) and the more honest output for a decoded checkpoint.

`Tests/Vt.lean`'s harness used `rowText` for readable string assertions; the decode
(`plain`) moved into the harness rather than keeping the production path on `String`.
The test harness adapts; the production code gets to be provable.

**EMITTERS is now four entries and no limitations**: `restore`, `leaveAnsi`, `history`,
`utf8s` — all proved. Statement ratchet 27 → 21 over this request.

## Step 3 notes (the invariant and its frame) — 2026-08-17

`PaintState` + `Matches` + `prefix_kept` landed, with the three within-row write frames
they rest on. All five design constraints recorded before the proof survived contact:
the parser component really is a triple, the frontier really has to be a glyph-group
boundary, `Matches` really can say nothing about columns ≥ k.

**`prefix_kept` is the delicate one and the shape matters.** "A write at or past the
frontier leaves the painted prefix alone" cannot be proved per *row*: `Vt.mendRow` sweeps
the whole row and on a row with broken pairs `mendAt` may rewrite any column — which is
exactly the mid-paint situation, because every unpainted column still holds the previous
occupant's junk. `mend_of_pairOk` (row-level) is therefore unavailable mid-induction, and
that is what forced the per-column route: `mend_keeps_narrow`/`mend_keeps_wide` need no
global pair-consistency, so each column is discharged with **its own shape**, which the
induction knows because the prefix already equals the source there. `RowOk.pairs` is what
turns "width 0 at j" into "a whole pair at j-1", so `mend_keeps_wide` gets a pair rather
than half of one. Carrying the shape is the price of quantifying over an arbitrary
receiver, and it is a price the induction can pay.

**The frontier hypothesis is verified load-bearing**: replacing it with `True` collapses
exactly the width-2 case. That is the case where the base sits at k-1 and its shadow at
k — unpainted — so the sweep sees a half pair and blanks the base the previous rung just
painted. Recorded because a reader will otherwise read `frontier` as bookkeeping.

New write frames (`at_putCell_ne`, `getCell_write_mendRow_keep_narrow`,
`getCell_write_mendRow_keep_wide`) all compiled first try — the frames pass really did
leave the layer in a state where the missing lemmas are one `rw` each.

Break-verified the mend layer as a whole: making `Row.mendAt` blank a settled narrow cell
fails `mendAt_self_id`, the foundation everything here rests on. Worth noting the shape of
that result honestly — for pure frame lemmas over Core operations, *any* Core break lands
at the base rather than on the new lemma, so the informative check for new content is
whether its own hypotheses are load-bearing (the `frontier` test above), not whether a
Core mutation reaches it.

Remaining for Step 3: the step lemmas (narrow, wide, mark, pen change) and
`rowAnsi_writes_row`. Known missing pieces for them, from writing the narrow one on
paper: `safeChar_of_emittable`, and size/grid-size preservation through `print`
(`Row.mend` preserves size via `setIfInBounds`, but nothing names it).

### Step 3: the first step lemma — `step_narrow` — 2026-08-17
One narrow, mark-free cell in the interior of a row: `Matches … k → Matches … (k+1)`,
re-establishing all fifteen fields. The rung the whole row walk is built from.

Shape: `cellText_feed` turns the cell's bytes into one `print`; `print_narrow_eq` turns
that print into a write plus an advance; `cursor_print_narrow_fits` gives the cursor;
`off_print`'s corollaries give pen/parser/modes/charsets; `write_shape` (new) gives the
two shape fields; `prefix_kept` gives columns `< k` and `getCell_write_mendRow_narrow`
gives column `k`. Nothing in it is novel — which is the point of having built the layer
first.

Plumbing that was missing and is now in: `safeChar_of_emittable` (the emit-side guard is
the identity on what a cell may hold — `printableChar` on store and `safeChar` on emit
share `Emittable`'s range), `size_getRow_putCell_any`, `grid_size_mendRow`,
`size_getRow_mendRow`, `Cell.ext'` (no `ext` without Mathlib), and `write_shape` — stated
about the *composite* `((u.putCell x y c).mendRow y).printAdvance n` rather than about
`print`, because under `print_narrow_eq`'s hypotheses that composite **is** the print,
whereas a general statement for `print` would have to reason through `printWrap`'s scroll,
which those hypotheses exist to rule out.

Traps:
* `subst` on `hje : j = k` eliminates `k`, so afterwards everything is phrased in `j`; and
  `rw [← hx]` to align the write's index rewrites *inside* `g.at k` too, breaking the
  cell hypotheses. Rewrite the goal's index forward (`rw [hx] at hrl ⊢`) instead.
* `size_mendAt` and `size_mend` already existed (2218, 2366) and I added duplicates.
  Second time this session that "verify before adding" would have saved a build — the
  first was the map's false gaps. Grep for the *name* before writing the lemma, always.
* All three hypotheses (`hfit`, `hmk`, `hpen`) verified load-bearing by replacing each
  with `True`. **My first attempt at that test reported `hfit` as not load-bearing**, and
  it was a quoting bug in the shell loop that fed python a pattern matching something
  else. A broken break-test reads exactly like a passing one — so when a hypothesis comes
  back "not load-bearing", check the harness before believing it, and prefer one explicit
  invocation per hypothesis over a loop.

### Step 3: the mechanical rungs — margin and the wide pair — 2026-08-17
`step_narrow_margin` and `step_wide`, plus a refactor that unblocked the second.

**The refactor: `prefix_kept` became `mend_keeps_prefix`.** The original bundled "the
writes missed the prefix" with "the sweep keeps it", which only fits a *single* write —
and the wide rung does two. Separating them makes one lemma serve every cell shape: each
rung shows its own writes are invisible below the frontier (one `at_putCell_ne` per write)
and then applies the sweep lemma. `step_narrow` moved onto it unchanged in substance.

`step_narrow_margin` is the rung the interior case cannot cover: the advance clamps the
column and arms wrap-pending. Note what it does *not* claim — `x` does not move (it is
already `cols - 1`), and the row-exit shape is `x = cols - 1` rather than a claim about
`pending`, because the following `carriageReturn` discards it. That is recorded constraint
3 landing as a signature.

`step_wide` consumes the pair in one rung, `k` to `k+2`. Constraint 2, and it is a
correctness requirement not a convenience: a frontier between base and shadow makes
`halfPair (k-1)` true at that moment and the sweep blanks the base just painted. The
shadow's own slot in `rowAnsi`'s fold emits nothing, so there is no second rung to give
it. `shadow_congr` (`Cell.shadow` reads only the pen) is what identifies the shadow the
print writes with the one the source row holds.

Traps, both recurrences:
* **multi-line structure instances again.** `{ base := …, marks := [], width := 2,` then a
  continuation indented below the first field's column is a parse error ("unexpected
  identifier; expected '}'"), and it surfaces as a confusing *elaboration* error further
  down. Third time this session. Keep structure instances on one line even at the cost of
  going slightly over the column budget.
* `decide` on `(Cell.shadow (g.at k)).width ≠ 2` is rejected — the expected type contains
  a free variable. `show (0 : Nat) ≠ 2` first (the shadow's width field is the literal 0,
  so it is defeq), then `decide`.
* `mend_keeps_prefix`'s `u` is inferred from `hrow : RowOk u.cols g`, which unifies with
  the *unwritten* receiver first. Pass `(u := …)` explicitly. Both wide and narrow rungs
  need it.
* Both rungs need `set_option maxHeartbeats 1000000`: `Matches` has fifteen fields, each
  mentioning the fed state, so unifying against the `putCell`/`mendRow` composite is a
  defeq check per field. Cheaper than splitting the invariant into smaller records, which
  would move the cost to every call site.

### `step_pen`, `shadow_emits_nothing`, and a correction to Definition-of-done item 4
`step_pen` — `rowAnsi` emits `penSgr c.pen` before a cell whose pen differs from the one it
carries, and that is the whole of the SGR handling, because the glyph bytes carry no colour:
the cell the receiver *stores* takes the receiver's current pen (`Vt.printPut`). So this rung
is what makes the cell rungs' `hpen` hypothesis dischargeable, and it is where the
invariant's `pen` field earns its keep.
One trap worth keeping: `Vt.getRow`'s *default* row is `blankRow cols pen`, so changing the
pen changes the default — and a `getCell` read only survives a pen change because
`Matches.inGrid` says the row index is in the grid, making the default unreachable
(`getD_of_lt`). Without that field the pen rung would be unprovable.

`shadow_emits_nothing` — the pair's second slot in `rowAnsi`'s fold appends `utf8s c.marks`,
which is empty for a shadow. That is *why* `step_wide` has to advance the frontier by two:
there is no rung available for the shadow's column. Stated about the source row via
`RowOk.pairs` rather than assumed, because `rowAnsi`'s width-0 branch is defensive code for
a decoded checkpoint that carries no such guarantee.

**Correction to DoD item 4, recorded rather than quietly dropped.** The item says
"`PaintState` … with `rowAnsi` threading it". `rowAnsi` must **not** thread `PaintState`:
two of its four fields — `y` and `pending` — are *receiver* state the emitter cannot see and
must not carry. `rowAnsi` already threads the emitter's half, `(bytes, pen, x)`;
`PaintState` is the receiver's half; `Matches` is what ties them. Writing the item's literal
text would have put receiver state into the emitter, which is the opposite of what this
spec is about. The remaining work under item 4 is `rowAnsi_writes_row`, not a refactor.
Third DoD item this spec has had to restate on contact (1, 3, now 4) — all three for the
same underlying reason: the plan was written before the shape of the receiver/emitter split
was understood.

## Step 3 notes — 2026-08-17 (the mark loop)

The mark loop landed, closing Step 3's remaining item 1. Shape used, exactly as the spec
directed: reuse `Matches` against `withMarks g k acc` (the source row with column `k`'s
marks truncated) so the fifteen-field bookkeeping is reused, not restated.

New source-row surgery (`withMarks g k ms := g.setIfInBounds k {g.at k with marks := ms}`),
with `at_withMarks_self` / `at_withMarks_ne` / `size_withMarks` / `withMarks_of_ge` /
`withMarks_keeps` and `rowOk_withMarks`. The last is the load-bearing one: the truncated
row is still `RowOk`, because column `k` is a *glyph* (`hwid ≠ 0`) so it is never the second
half of a pair, and the only content the pair rule constrains is a shadow — which `withMarks`
leaves untouched. `Cell.shadow` reads the pen only, so a base's shadow stays canonical.

Two `Matches` converters: `matches_below` (agreement below `k` only — the loop's *entry*,
swapping `g` for `withMarks g k []`) and `matches_row_congr` (full pointwise agreement — the
*exit*, swapping `withMarks g k (g.at k).marks` back for `g`, which reads back identically at
every column by structure-eta on `{g.at k with marks := (g.at k).marks}`).

`mark_step` is one mark: `Matches u Q (withMarks g k done) (k+1) → Matches (u.print (safeChar m))
Q (withMarks g k (done ++ [safeChar m])) (k+1)`. The single hypothesis that separates interior
from margin is `hdisj : (Q.x = k+1 ∧ ¬pending) ∨ (Q.x = k ∧ pending)`. That disjunction is
the whole reason `print_mark_pending_eq` / `cursor_print_mark_pending` had to be added to
`Theorems/Vt.lean`: at the final column the base print clamped the cursor to `cols-1 = k` and
armed wrap-pending, so the mark attaches *at* the cursor, not one left of it — the position
`printMark`'s `pending` branch names and no absolute move can address. Both branches write
column `k`, so the fifteen-field tail is shared.

`marks_fold` folds `mark_step` over the marks. `cols` is threaded as a fixed parameter with a
per-receiver `u.cols = cols` (kept across the fold by `cols_print`) — the earlier draft wrote
`RowOk w.cols g` with `w` unbound in the fold and did not compile; the `{cols}` + `hcols`
shape is the fix. `map_safeChar_id` closes the loop: the re-emitted marks are `safeChar`
images, equal to the stored marks because every mark is `Emittable`.

`step_narrow_marks` assembles it: `step_narrow` (mark-free, kept) paints the base against
`withMarks g k []`, then `marks_fold` walks the marks on. So `step_narrow` is now the
`marks = []` special case of `step_narrow_marks`.

`cha_places_cursor` generalized: dropped `hx : n - 1 < v.cols`, conclusion now
`min (n-1) (v.cols-1)`. The trailing `CHA` of a final-column marked-wide pair addresses past
the margin; the old in-range statement would have left that case unprovable, not false.

Gotchas this round, all AGENTS.md-relevant:
- `set` is Mathlib-only — banned. Rewrote `mark_step` inlining the cell/write terms instead
  of `set c := … / set W := …`. Cost: verbosity; benefit: it compiles.
- `List.mem_cons_self` / `List.not_mem_nil` take *no* explicit args in 4.32.0 (`... a l` / `... x`
  is "function expected"/"type mismatch"). Use bare `List.mem_cons_self`, and `by simp` for the
  empty-list vacuity.
- `subst hik'` on `hik' : i = k` eliminated `k` (the older var), leaving my `{g.at k with …}`
  literals dangling — "unknown identifier k". Use `rw [hik']` to fold `i → k` in the goal instead.
- `mend_keeps_prefix`'s receiver `u` is inferred from `hrow : RowOk u.cols _`. Stating `hrowW`
  as `RowOk w.cols _` made it infer `u := w` and reject `hgsW`/`hcellsW` (about the `putCell`).
  Pass `(u := w.putCell …)` explicitly, as `step_narrow`/`step_wide` already do.
- `rowSlot` extracted from `rowAnsi`'s inline lambda (so the row-replay theorem can name a
  def, not a lambda). It is temporarily unclaimed → `STATEMENT_CAP` 21 → 22, with a comment;
  it comes back down when `rowAnsi_writes_row` names it. The three `dsimp only` sites in
  `ends_rowAnsi`/`quiet_rowAnsi`/`smap_id_rowAnsi` each needed `unfold rowSlot` first.

Break-verify (mark loop), 2026-08-17: changed `Vt.printMark`'s write from
`{cell with marks := cell.marks ++ [ch]}` to `{cell with marks := cell.marks}` (drop the
mark). `Theorems/Vt.lean` fails at `print_mark_eq` (2774) and `print_mark_pending_eq`
(2799) with unsolved goals, cascading through `mark_step`/`step_narrow_marks`. Reverted;
`diff` confirms Core byte-identical; `./lake build Theorems Tests` green. So the mark chain
is load-bearing on the emulator actually storing the mark, not vacuous.

## Step 3 notes — 2026-08-17 (the wide-with-marks rung)

`step_wide_marks` closes spec item 2: `rowSlot`'s marked-wide branch
`glyph · CHA(k+2) · marks · CHA(k+3)`. Interior only (`k+2 < cols`); a width-2 base with no
room for its shadow is stored as a blank (`printPut` fix 11), so `RowOk` never presents a
wide base whose pair overruns — the "pair at the very margin" (shadow in the last column)
is the one wide case still needing a margin rung (see below).

The load-bearing new lemma is `cha_feed_eq : v.feed (csiNum n 0x47) = v.setCol (n-1)` (given
ground + u8need 0). `csiFinish` ends by forcing `pstate := .ground`, and `setCol` keeps the
ground pstate a `Matches` receiver already has, so the whole feed collapses to `setCol` and
every non-cursor field frames through `frame_setCol` at once — that is `cha_matches`. Far
cheaper than one preservation lemma per field. `cha_matches_lt` is the in-range corollary
(no clamp, cursor exactly `n-1`); `cha_cols` and `foldl_print_cols` keep the CHA bounds in
range across the sequence.

`hcb : k + 3 < 65535` is a real precondition, not bookkeeping: `CHA n` clamps its parameter
to 65535, so if the emitted column reached 65535 the repaint would mis-address. It is the
column analogue of `restore_sticky_any`'s `hfits` on rows; downstream (`restore_grid`) will
supply it from the ≤1000 dim clamp. `cha_matches_lt`'s `hin` (the addressed column is in
range) is what `k+2 < cols` buys — both jumps (`k+1` for the mark, `k+2` past the pair) land
inside the row.

`mark_step`/`marks_fold` were generalized to a write column `wcol < kf` (frontier) so the one
loop serves narrow (`wcol=k, kf=k+1`) and wide-marks (`wcol=k, kf=k+2`, cursor parked at
`k+1` by the first CHA). The frontier field is carried forward via `withMarks_keeps`'s
width-invariance rather than recomputed, since for the wide case `kf-1 = k+1 ≠ wcol`.

Break-verify: `Vt.setCol`'s `min x (cols-1)` → `min (x+1) (cols-1)`. Fails at
`cha_places_cursor` (5894) and `cha_matches` (6717, the `unfold; rfl` for cursor.x),
cascading to `step_wide_marks`. Reverted; Core byte-identical; green.

Remaining for `rowAnsi_writes_row`: margin rungs — `step_narrow_margin_marks` (a marked
narrow last cell), `step_wide_margin` and `step_wide_margin_marks` (a wide pair whose shadow
is the final column, where the base print clamps and the trailing CHA clamps too) — then the
fold over `rowSlot` itself, inducting on the byte accumulator.

## Step 3 notes — 2026-08-17 (the margin rungs)

The three last-cell rungs `rowAnsi_writes_row` needs, all built by adapting the interior
versions:
- `step_narrow_margin_marks` — a marked narrow last cell: `step_narrow_margin` base +
  `marks_fold`'s pending branch (`Or.inr`), exit `{P with pending := true}` (x unchanged).
- `step_wide_margin` — a wide pair whose shadow is the final column (`k+1 < cols ≤ k+2`, so
  `cols = k+2`): same base+shadow write as `step_wide`, only the advance clamps
  (`cursor_print_wide_margin`), exit `{P with x := cols-1, pending := true}`. The 13
  non-cursor fields are verbatim `step_wide`.
- `step_wide_margin_marks` — that pair, marked: CHA(k+2) still lands in range (`k+1 =
  cols-1`), but the trailing CHA(k+3) addresses `cols` and **clamps** to `cols-1`, so the
  final cursor is `cols-1` not `k+2` (used `cha_matches` with the clamp, not `cha_matches_lt`),
  and pending is false (the CHA cleared it). Exit `{P with x := cols-1, pending := false}`.

Design note for `rowAnsi_writes_row` (the remaining item): `rowSlot` advances its cell index
by 1 per cell, but a wide base paints TWO columns, so the receiver frontier runs one ahead of
`rowSlot`'s x between a base and its shadow. Matches's `frontier` field FORBIDS sitting there
(`g.at(k) width = 2` at frontier k+1 violates it) — spec constraint 2 as a type error. So the
fold must peel a wide pair (base+shadow) as a **unit** (two `rowSlot` steps, frontier +2, x
+2 together), i.e. a peel-1-or-2 induction well-founded on `cols - n`, not a plain
`invariant_foldl`. Pen threading interleaves via `step_pen` (rowSlot emits `penSgr` before a
cell whose pen differs from the fold's accumulator).

## Step 3 notes — 2026-08-17 (rowAnsi_writes_row — Step 3's exit)

`rowAnsi_writes_row` landed: feeding `rowAnsi g startPen` into any receiver matching `g` at
frontier 0 (with `startPen` in effect) paints the whole row — the receiver ends matching `g`
at every column, with `rowAnsi`'s returned pen in effect (threaded for the next row).
`pending` is existential (last-cell-shape dependent; the joining CR discards it).

Assembly, bottom-up:
- `rowSlot` extracted from `rowAnsi`'s lambda (so the theorem names a def) — `rowSlot_eq_narrow`
  / `_wide_nomarks` / `_wide_marks` / `_shadow` give its output as explicit tuples, folding
  from empty bytes.
- `rowSlot_split` / `rowSlot_fold_split`: rowSlot only appends to the byte accumulator and its
  (pen, index) ignore prior bytes, so the fold peels a cell at a time.
- `range_map_cons` + `foldl_rowSlot_range`: the array fold is the fold over `g`'s cells read
  positionally (`(range g.size).map (g.at ·)`), peelable from the front.
- `paint_range`: strong induction (`Nat.strongRecOn`) on the remaining-cell count, peeling a
  narrow cell (advance 1) or a wide pair base+shadow (advance 2). `Matches.frontier` makes a
  width-0 cell at a recursion point a contradiction (never land on a shadow) — spec constraint
  2 as a type error, not a runtime check. Pen threads via `pen_prefix_matches` (rowSlot's
  optional leading `penSgr`) + the eight cell rungs.
- cols bookkeeping: `penSgr_cols` / `pen_prefix_cols` / `cellText_cols` / `utf8s_cols` /
  `dance_cols` keep `w.cols = cols` across each cell's bytes, needed because the rungs are
  stated over `w.cols` (not a threaded `cols`).

Gotchas (AGENTS.md-relevant):
- `by_contra` is Mathlib-only — banned. Use `rcases Nat.lt_or_ge ...` + `exfalso`.
- `Nat.strong_induction_on` doesn't exist here; `Nat.strongRecOn` does (`| ind m ih =>`).
- `decide` refuses a goal with free variables even when the value is constant
  (`(Cell.shadow (g.at n)).width` is 0 regardless of `g.at n`, but `decide` still balks) —
  reduce the widths to literals with `rw [show … from rfl]` first, then `decide`.
- `rw [hmeq2] at hstep` (hmeq2 : n+2 = cols) clobbered `csiNum (n+2)` in the *bytes*, not just
  the frontier — rewrite the goal's frontier instead (`rw [← hmeq2, show n+2-1 = cols-1 …]`).
- `exact ih …` checks up to defeq, so `m-1-1` vs `m-2` and `n+1+1` vs `n+2` need no rewrite
  (both reduce to `pred (pred m)` / `succ (succ n)`). The spurious `rw [this] at hstep ⊢` I
  first wrote failed precisely because those terms weren't in `hstep`'s goal.

Break-verify: `rowSlot`'s narrow branch `cellText c` → `cellText c ++ [0x41]` (spurious 'A').
Fails at `rowSlot_eq_narrow`/`rowSlot_eq_wide_nomarks` and the fold invariants
`ends_rowAnsi`/`quiet_rowAnsi`/`smap_id_rowAnsi`. Reverted; Core byte-identical; green.
Complements the earlier emulator-side breaks (printMark, setCol): this pins the *emitter*.

**Step 3 is complete.** `STATEMENT_CAP` back to 21 (`rowSlot` now named by a theorem).
Remaining: Step 4 (`joinCRLF` row walk + no-scroll, alt switch, `restore_grid_any` /
`restore_grid_reachable` / `resume_grid`) and Step 5 (conformance profile, archive).

## Step 4 notes — 2026-08-18 (the grid, painted)

The grid-painting core is proved and committed (6 checkpoints):
- `OffRow` (a row's paint touches no other row — the half `Matches`, being about one row,
  could not carry; the cross-row scroll catastrophe `RowOk` guards against, stated
  positively) + per-rung companions `offRow_narrow`/`_wide`/`_mark`/`_marks_fold`/
  `_narrow_marks`/`_narrow_margin_marks`/`_wide_marks`/`_wide_margin`/`_wide_margin_marks`.
- `paint_range` and `rowAnsi_writes_row` now also conclude `OffRow`.
- `crlf_step`: the CRLF between rows is one clean cursor move — `lineFeed_interior` (below
  `bot` the LF moves down, does not scroll) + `carriageReturn`. The no-scroll argument.
- `rowsAnsi`/`gridFold_eq_rowsAnsi`/`gridAnsi_eq`: the array fold `gridAnsi` runs, as a
  peelable head-first list.
- `paint_rows` (`Walking` bundle + strong-ish structural induction): the grid row walk, no
  line feed scrolls (`joinCRLF` has no trailing separator, so the last row's LF never fires).
- `gridAnsi_writes_grid`: **the whole grid, painted into any client of matching dims with
  reproducible rows, reproduces `v.grid` exactly** — array for array (`grid_eq_of_cells`,
  `row_eq_of_paint`, `size_getRow_congr`, `getD_lt'`). Entry established via `SGR 0`
  (`penAfter _ [0] = {}`) then `home_feed_eq` (`CSI H = moveTo 0 0`).
- `prologue_sticky` / `prologue_modes`: the prologue's **canonical mid-stream** state
  (region whole, no alt, ASCII charsets; insert off / wrap on / origin off), lifted from
  `restore_sticky_any`'s chain and the `MMap` machinery. `rows ≥ 2` is `DECSTBM`'s constraint.

WHAT REMAINS for `restore_grid_any` (Def-of-done item 5), and the genuine subtlety found:
1. **The entry `u = w.feed (prologue ++ SGR0 ++ ED2)` needs `u.u8acc = 0`** —
   `utf8_feed`/`cellText_feed` require it (via `reset_u8`) for *multi-byte* glyphs, and it
   is carried through the whole row/grid walk as a `Matches`/`Walking` field. A CSI final
   byte forces `u8need = 0` (`u8_zero_after_csi`) but **not** `u8acc = 0`
   (`abortUtf8` only zeroes `u8acc` when `u8need > 0`). So the entry `u8acc = 0` needs the
   receiver's live invariant `w.u8need = 0 → w.u8acc = 0` (true for any client reached by
   feeding; not in `Good`/`Renderable`), threaded through the lead-in's abort and preserved
   across the CSIs (which never touch `u8acc` from a `u8need = 0` state). This is a real
   precondition and belongs in the statement — the same shape of hazard this spec exists to
   surface.
2. `paint_entry`: assemble `gridAnsi_writes_grid`'s ~14 entry facts about `u` — dims
   (`dims_feed`, needs `Good w`), `GridOk` (`renderable_feed`), sticky through `SGR0`/`ED2`
   (`smap_id_sgrNum`/`smap_id_ed`), modes through them (`mmap_id_sgr`; `mmap_id_ed` still to
   build), ground (`Ends`), and the `u8acc` of item 1.
3. no-alt `restore_grid_any` = `paint_entry` ∘ `gridAnsi_writes_grid` ∘ `restore_grid_of_paint`.
4. the `rows = 1` case (DECSTBM degenerate; a single row cannot scroll, so `Walking.bot`
   should weaken to `rows ≤ 1 ∨ bot = rows-1`).
5. the **alt-screen** case: `screensAnsi` paints main, parks, `?1049h` (enterAlt on the
   client blanks and resets region), then paints the alt — so `gridAnsi_writes_grid` applies
   to the post-`?1049h` state; the switch's state establishment is the new work.
6. `restore_grid_reachable` (supplies items 1/2's invariants from `LiveReachableVt`) and
   `resume_grid` (composes with checkpoint exactness).

## Step 4 notes — 2026-08-18 (the composition; DoD item 5 for the main screen)

`restore_grid_any_main` and `restore_grid_reachable` are **proved**: feeding `restore v` to any
live-reachable client of the session's dimensions leaves its grid equal to `v.grid`, array for
array. Non-vacuity checked by instantiating at a real 80×24 `Vt.init` (both the hypothesis
bundle and the conclusion).

The `u8acc` blocker from the previous round is **solved twice over**:
1. `uaz_feed` — an all-ASCII stream leaves the decoder quiesced. Built as the `u8acc` twin of
   the existing `un_*`/`uz_*` family (`ua_ctl` … `ua_stepStr`, `uaz_stepGround`, `uaz_step`).
   Restricting to `b < 0x80` (not `< 0xC0`) is what makes it easy: the UTF-8 continuation
   branch cannot arise, and every non-glyph restore byte is ASCII anyway. The `Ascii`
   predicate family (`Ascii.append/cons/nil`, `ascii_digits`, `ascii_csiNum`, `ascii_modeSet`,
   `ascii_penSgr`, …) discharges the side condition compositionally, the repo's own idiom.
2. `U8Ok v := v.u8need = 0 → v.u8acc = 0`, proved for **every live-reachable state**
   (`u8Ok_of_liveReachable`). So the precondition I flagged last round as "a real limit on any
   receiver" is a limit only on paper: no reachable client violates it. `Good` bounds `u8need`
   but says nothing about `u8acc`, which is why it needed its own invariant.
   `u8pair_stepEsc` is the honest shape for the `.esc` case: unchanged **or** both cleared —
   the backwards direction is *false*, because `RIS` rebuilds through `Vt.init` and reports
   zero whatever the receiver held. (I wrote the backwards lemma first; it does not hold.)

Other new machinery: `paint_entry` (the establishing prefix leaves the receiver ready — dims
via `dims_feed`+`Good`, rows via `renderable_feed`, region/charsets/alt via `prologue_sticky`,
modes via `prologue_modes`+`mmap_id_sgr`/`mmap_id_ed`, decoder via `uaz_feed`);
`modeSet_feed_eq` (a private mode set as a **state** equation, which `modeSet_modes` was not —
it saw only the `Modes` field, and `?1049h`'s real work is stashing the grid);
`setMode_pstate`; `csi_priv_open_eq`; `alt_switch_entry`; `modes_eraseScreen`; `grid_eq_of_cells`.

Gotchas: `set` and `by_contra` are Mathlib-only (banned) — hit both again. `dsimp only` after
`unfold Vt.csiFinish` eta-expands the record field-by-field, so a `rw` on the dispatch must go
through a **∀-quantified** equation (`show ∀ (u : Vt), u.csiDispatch … = …`), the trick
`cha_feed_eq` already used. `repeat' split; all_goals rfl` misaligns two sides that differ
only in `pstate` (the `enterAlt` branches split independently) — `setMode_pstate` with a
leading `dsimp only` is the fix.

Break-verify: `gridAnsi`'s home `CSI H` → `CSI 2;1 H` (a one-cell drift). Fails
`gridAnsi_eq` (8162) plus `ends_gridAnsi`/`quiet_gridAnsi`/`smap_id_gridAnsi`. Reverted; Core
byte-identical; green.

**STILL OPEN** (and now narrow): the **alt-screen** branch. `alt_switch_entry` +
`modeSet_feed_eq` are its hard half — the switch fires and hands the second paint a blank grid
of the right shape, region reset, cursor homed. What is missing is only the **modes** at the
switch (`insert`/`wrap`/`origin`), which sit between the prologue that sets them and the
switch that inherits them, across the main paint. Two routes, neither a one-liner, recorded in
a note above `restore_grid_reachable` in `Theorems/Render.lean`: `MMap id (gridAnsi …)` needs
`MMap` over `utf8s` and `MMap` carries no `u8acc`; or expose the modes from `paint_rows`
(`Walking` already carries `insert`/`wrap`) — which does not reach `origin`, since `Matches`
has no `origin` field. **The second is the better shape** and the recommended next step: add
`org` to `Matches` (one line per rung via `modes_print'` / `frame_setCol`, ten rungs), thread
it through `paint_range`/`paint_rows`/`gridAnsi_writes_grid`, then the alt branch is a
composition like the main one. Also still open: `rows = 1` (excluded by `h2 : 0 < v.rows - 1`,
`DECSTBM`'s own degenerate case — a one-row grid cannot scroll, so `Walking.bot` should weaken
to `rows ≤ 1 ∨ bot = rows - 1`), and `resume_grid` (compose with checkpoint exactness).

## Step 4 notes — 2026-08-18 (the alt screen; DoD item 5 now COMPLETE for both screens)

`restore_grid_any` (both screens) and `restore_grid_reachable` (no `altGrid` hypothesis) are
**proved**. The alt branch turned out much cheaper than the previous round's note projected:
the "add an `org` field to `Matches`, ten rungs" plan was **not needed**.

The realisation that unlocked it: the modes at the `?1049h` switch do not have to be threaded
through `Matches`. Two of them (`insert`, `wrap`) are already `Walking` invariants — I only had
to **expose** them in the output tuples of `paint_rows` and `gridAnsi_writes_grid` (two extra
conjuncts each, discharged by `hw.ins`/`hw.wrap` / `hM.ins`/`hM.wrap`, which were already in
hand). The third (`origin`) rides the **existing `Quiet` family**: `quiet_gridAnsi` already
proves the paint keeps `pstate = ground ∧ origin = false`, because `Quiet` crosses a multi-byte
glyph byte-by-byte through `ground_step` (UTF-8 state lives in `u8need`/`u8acc`, *not* `pstate`)
— which is exactly why it needs no `u8acc`, the thing that blocked the `MMap id (gridAnsi …)`
route. So `origin` after the paint is a one-liner: `(quiet_gridAnsi mg z hg horg).2`.

Machinery added:
* `gridAnsi_writes_grid'` — the paint theorem restated over a bare `tg : Array Row` + explicit
  `cols`/`rows` (the stashed main grid is not any `Vt`'s `.grid`). Trick: instantiate the
  original's target as `{u with grid := tg, cols := cols, rows := rows}` so **every** hypothesis
  lines up definitionally — no `by rw` conversions. Reused for the final alt paint too.
* `getRow_size_replicate` — every row of the freshly-blanked `enterAlt` grid is `cols` long,
  regardless of the default the `getRow` lookup falls back to. (Factored out after an inline
  version ballooned to ~30 lines of giant terms.)
* `alt_pre_switch` — the state just before the switch is fully re-established across the
  **discarded** main paint and the park (`penSgr ++ CUP`). The main paint's *cells* are thrown
  away by `enterAlt`, so only framed invariants matter: `insert`/`wrap` from
  `gridAnsi_writes_grid'`, `origin` from `Quiet`, the sticky fields (rows/top/bot/alt/g0/g1)
  from `SMap`, the dimensions from `dims_feed`; the park preserves all of them
  (`MMap id` = `mmap_id_penSgr`+`mmap_id_cup`; `SMap.append`; `uaz_feed` with `ascii_penSgr`+
  `ascii_csiNum2`). `MMap id` needs only `ground ∧ u8need = 0`; `SMap id` needs only `ground`.
* `restore_grid_any_alt` — composes the above with `alt_switch_entry` and the final
  `gridAnsi_writes_grid'`, then `restore_grid_of_paint`. The full alt `screensAnsi` is peeled
  with `feed_append × 4` after regrouping the park via `simp only [List.append_assoc]`.
* `restore_grid_any` — the one theorem, dispatching on `v.altGrid` (`match halt : v.altGrid`).

Gotchas: `set` is Mathlib-only (banned) — hit it again abbreviating `park`, replaced with a
helper lemma taking `park` as a bound term. `obtain ⟨…⟩ := by … exact ⟨…⟩` fails ("expected type
could not be determined" for `⟨…⟩`) — use a plain `have` and project. Parenthesis miscount on a
`show` (`.size` needs one wrapping paren the sibling `.cols`/`.getRow` haves don't).

Break-verify: `screensAnsi`'s alt branch final paint `gridAnsi v.grid` → `gridAnsi mainGrid`
(a plausible copy-paste slip — paint the stash twice). Fails `restore_grid_any_alt`'s `hscreens`
(9094) and the `SMap`/`Ends` stream predicate over `screensAnsi` (5397). Reverted; Core
byte-identical; `./lake build Theorems Tests` + `./tests/e2e.sh` green, `STATEMENT_CAP` 21.

**Still open** (both narrow, non-blocking): `rows = 1` (excluded by `h2 : 0 < v.rows - 1`,
`DECSTBM`'s degenerate case — weaken `Walking.bot` to `rows ≤ 1 ∨ bot = rows - 1`), and
`resume_grid` (compose `restore_grid_reachable` with checkpoint exactness). Then Step 5.

## Step 4 notes — 2026-08-18 (resume_grid — the end-to-end composition)

`resume_grid` closes the resume side of DoD item 5: a quiescent checkpoint round-trips
byte-identical (`Checkpoint.load_save_exact`) and replaying it into a fresh `Vt.init` of the
session's size reproduces the screen cell for cell, **either screen** (`restore_grid_any`).
Thin plumbing over already-break-verified lemmas — no new proof risk. The one wrinkle: the
receiver is `Vt.init c.vt.cols c.vt.rows`, whose dims are `clampDim`ed; `Good`'s `colsPos`/
`colsLe`/`rowsLe` make `clampDim = id` (`simp only [Vt.clampDim]; omega`). Non-vacuity pinned by
an `example` at a real 80×24 checkpoint.

## Step 4 notes — 2026-08-18 (rows = 1 — item 5 now truly "every v/w")

The `h2 : 0 < v.rows - 1` hypothesis is **gone** from the whole grid chain
(`prologue_sticky`, `paint_entry`, `restore_grid_any_main`/`_alt`/`_any`,
`restore_grid_reachable`, `resume_grid`). Item 5 now holds for *every* height, the one-row
screen included.

The corner was cheaper than the "weaken `Walking.bot`" note projected — `Walking.bot` never
needed touching, because `bot = rows - 1 = 0` already holds for one row. `h2` was load-bearing
in exactly one place: `prologue_sticky`'s DECSTBM step. For `rows ≥ 2`, `CSI 1;rows r` *resets*
the region whole regardless of the client (`stStbm_of`). For `rows = 1` the emitted `1;1r` is
degenerate (`stStbm 0 0 = ` no-op), so the region it leaves is whatever the lead-in left — and
that is already whole, because a **`Good`** one-row client has `bot < rows = 1 ⟹ bot = 0` and
`top ≤ bot ⟹ top = 0`. So `prologue_sticky` now takes `Good w` (which `paint_entry` already
had) and case-splits: `stStbm_of` for `rows ≥ 2`, the no-op + `Good (w.feed escSeq)`'s region
bounds (via `Good.feed` and `rows_st_lead`) for `rows = 1`. No region-across-lead lemma needed
— `Good.feed` on the ESC\ prefix supplies the bound directly, whichever way `?1049l` (`stAlt
false`) leaves the region (reset-to-whole if the client was on alt, unchanged otherwise, both
whole for one row).

The paint itself already worked for one row: `paint_rows` over a length-1 row list hits only
the last-row case, so `crlf_step` (the only place `bot < rows` / `cursor.y < bot` matters) is
never invoked — a single row cannot scroll, exactly as the design said.

Non-vacuity: `resume_grid` instantiated at `Vt.init 80 1` reproduces the 80×1 grid (an
`example` in `Theorems/Resume.lean`). Break-verify: `gridAnsi`'s home `CSI H → CSI 2;1 H`
fails `gridAnsi_eq` (8162) and the `Ends`/`Quiet`/`SMap` stream predicates (841/1722/5282); the
rows=1 example flows through this chain, so its claim is substantive, not vacuous. Reverted;
Core byte-identical; `./lake build Theorems Tests` + `./tests/e2e.sh` green, `STATEMENT_CAP` 21.

**Item 5 is now complete with no height caveat.** Remaining for the spec: Step 5 (conformance
profile into THEOREMS.md; archive `terminal-contract.md` + `grid-fidelity.md`).

## ledger-cleanup notes — 2026-08-18 (runtime items: resume dims, .err, ptyIn cap)

New spec `specs/ledger-cleanup.md` opened for the leftovers `restore-conformance.md` parked.
Three runtime (IO) items landed together — they share Daemon.lean/Client.lean and the pty test
harness, so one checkpoint.

**Resume dims (ledger item 4).** `Daemon.serve` spawned the pty at a hardcoded `spawnPty 80 24`
while the restored `Vt` kept the checkpoint's size — so `linger run`/`send`/`wait` on a
checkpointed-but-not-live session handed the child 80×24 against a differently-sized screen,
and (per the resume-dims recon) this also *defeated* the same-size-attach guard
(`onMsg_attach_same_size_vt`) for any non-80×24 session, since the reattach then saw a size
change and `Vt.resize` wiped the region/ruler — restore-conformance ledger item 1 re-entering
by the back door. Fixed: `spawnPty (UInt32.ofNat (clampDim vt0.cols)) (UInt32.ofNat (clampDim
vt0.rows))`. Clamp only the two syscall args, NOT `vt0` (a `Vt.resize` here is the very
ledger-item-1 regression); `clampDim` also guards a corrupt/foreign checkpoint whose unclamped
`cols ≥ 65536` would wrap to a 0-column tty in the shim's `(unsigned short)` cast
(`Checkpoint.load` is total on arbitrary bytes and does not clamp). Test: `resume_test.py`
resumes an 80×40→100×40 session with NO sizing attach (`run`, which never sends `.attach`) and
reads the pty's own `TIOCGWINSZ` from a probe *script file* — `run`/`send` space-join argv and
type it as keystrokes, so `sh -c '…'` loses its quoting (that cost me an hour: `echo HELLO`
came back as `\n` because `sh -c echo HELLO` runs `echo` with `HELLO` as `$0`); a script file
has nothing to lose. This host's `stty size` prints a mode dump and `tput` needs terminfo, so
`TIOCGWINSZ` is the honest oracle. Probe-verified: fixed → `100 40`; broken (the original
`spawnPty 80 24`) → `80 24`, which the `== ['100','40']` assertion rejects. The proof cannot
see this (`Daemon` is IO) — the pty test is the only guard, and reverting line ~304 keeps
`./lake build Theorems Tests` green while `resume_test.py` fails. That asymmetry is the point.

**.err on attach (ledger item 6).** `Client.attach` returned `Option UInt32` (status / none)
and its message loop dropped `.err` into the catch-all, so a `too many clients` refusal read as
a clean detach (`Cli` printed `detached from '<name>'`). Replaced the return with an `Outcome`
sum (`ended`/`detached`/`refused msg`) — the `Core.Listing.Row` idiom: each constructor carries
exactly its case's facts, so no caller can render one as another. `.err`'s payload is rendered
via `String.fromUTF8?` and **scrubbed** with `Remote.scrub` before hitting the raw terminal (our
daemon's message, but the socket is not a trusted channel), printed `\r\n`-prefixed to match the
raw-mode convention. Both call sites (`cmdAttach`, `watch`) updated to report the refusal
(exit 1). No test yet drives a 17th client — noted for the TUI step's e2e pass.

**ptyIn cap (ledger item 3).** `rt.ptyIn` was the one unbounded runtime buffer; a child that
stops reading (its pty input buffer fills → `flushPty` breaks at EAGAIN → every `.input` frame
appends forever). Added `ptyInCap := 4194304` (= `outbufCap`) and a named `queuePty` stage that
drops the newest frame past the cap and logs the transition once (`ptyInFull` edge flag).
Drop-newest, not disconnect: a `.writePty` carries no client id (produced by `.input` from any
client AND by the mediator's own query replies — pinned literally by `Theorems/Session.lean`'s
`step_ptyOut_effects`, so splitting the Effect vocabulary to attribute it is off the table), and
dropping the newest is what a tty does under `IMAXBEL` — it cuts at a frame boundary the client
already chose, so no UTF-8/escape is split. **Also fixed the twin latent bug the ptyIn recon
and I both found independently**: `flushPty` AND `flushConn` reclaimed memory only on a *full*
drain, so a partly-draining consumer grew the array without limit while `size - off` (what
`outbufCap` measures) stayed small — the cap never tripped. Both now `extract off …` on a
partial write, keeping `off = 0` outside the loop so pending and size agree. Test: `robust_test`
case 3 — `run stall sleep 600`, flood 16 MiB of 256 KiB `.input` frames over a raw control
socket, assert the log reports the cap once with `pending ≤ cap` (the bounded-buffer property
itself, deterministic — RSS-after-flood is dominated by transient decode garbage and is a noisy
oracle, so it is *not* asserted). Break-verified: reverting `queuePty` to the plain append makes
the log line vanish and the three log assertions fail (build stays green).

Constants live in `Daemon.lean` (Runtime), not Core — a Core constant would hit
`tests/coverage.py`'s 21/21 cap (nothing in Core reads `ptyIn`). `THEOREMS.md` §Bound paragraph
now names both caps and the compaction. No shim change (SHIM_CAP untouched).

## ledger-cleanup notes — 2026-08-18 (item 5: the human listing, safe and clean)

The `list` human output was a per-row `IO.println s!"{icon} {name}\t{detail}…"` with NO scrub,
against three sources that are not ours: a `cmd`/label from an older/foreign daemon on the
socket, a checkpoint filename (resumable rows), and a `-r` host. The recon confirmed our own
daemon already scrubs at the emit site (`infoText` via `utf8s`, proved by `infoText_framing`),
so the *current* leaks were exactly the two rows that bypassed it: the resumable row's raw
`("name", filename)` and the raw `@host`.

Fixed the repo's way — make the emitter total and provable, not audit the call site. New pure
core `Listing.humanRow`/`humanListing` (in `Zmx/Core/Listing.lean`) render the row as
`List UInt8` through `Render.utf8s`, which maps every C0/DEL to U+FFFD. `Theorems/Listing.lean`:
`humanRow_printable` (∀ b, 0x20 ≤ b ∧ b ≠ 0x7F — literally `utf8s_no_ctl _`, one line),
`humanRow_no_lf`, and `humanListing_printable` (every byte printable-or-`0x0A`, via
`List.mem_flatMap`). The CLI human branch is now one `writeAll (humanListing rows)`.

The claim is a **byte-range framing** theorem, not "printable ASCII": the status glyph is
U+28xx (braille) and `✓` is U+2713, so ASCII-only would be false — same shape as
`infoText_framing`/`history_framing`.

Data fixes in the same commit: the resumable row now goes through `rowFields` (→ `sanitize`, so
§Row's `rowFields_name` covers it and the shown name is the one `attach` accepts); local rows
are sorted (`qsort`) for deterministic order; the host leak is closed by `humanListing`'s scrub
(the display path — the ssh-argv host validation via `Remote.checkHosts` is a separate security
item, noted below, not needed for clean visuals). Visual bugs fixed for free: ragged columns
(name padded to the set's widest, computed in `humanListing` — sanitized names are ASCII so
length-padding aligns), `(busy)` on healthy remote rows (guarded on `status = unknown`), and
trailing whitespace (`dropTrailingBlanks`).

Elegance note (the user's steer): the first cut had `dispWidth`/`padTo`/`nameWidth` as three
top-level core defs, each of which the coverage gate (21/21) would demand a naming theorem for —
and `dispWidth` over `charWidth` needs a foldl-over-append lemma. That is proof weight for a
visual nicety. Inlined them as `let`s (length-based padding, correct for ASCII names), leaving
only `humanRow`/`humanListing` top-level, each named by the safety theorem. Cleaner code,
cleaner proofs, coverage stays at 21.

Break-verify: replace the final `utf8s (...)` in `humanRow` with a raw
`(...).map (UInt8.ofNat ·.toNat)` — `humanRow_printable` fails to typecheck
(`utf8s_no_ctl _` no longer applies, Theorems/Listing.lean:100) AND every `Tests/Listing.lean`
`native_decide` fixture (`count 0x1B = 0` etc.) is *refuted*. Reverted; green. `Tests/Listing`
also pins the *before*: the old `String`-interpolated row carried the ESC (`count 0x1B = 1`).
e2e: `overview_test` now touches a checkpoint named `ev\x1b[31mil\tfake.ckpt` and asserts no ESC
/TAB in the listing; `robust_test:57` updated from `? busy\t(busy)` to the space-aligned
`? busy (busy)`.

**Follow-up (security, not visuals):** the `-r` host string still flows into `ssh` argv
unvalidated (`resolveRemotes`); the display is now safe but a host with a control byte or shell
metacharacter is a separate concern for `Remote.checkHosts`. Parked, not done.

## ledger-cleanup notes — 2026-08-18 (restore_tabs_any — the tab ruler, proved)

`restore_tabs_any` / `restore_tabs_reachable` / `resume_tabs` are green: for any receiver of
the session's width, `(w.feed (restore v)).tabs = v.tabs`, array for array. The last restored
field on the fixtures-only list except the title and the DECSC slot.

**The elegance win, and it was the whole story.** `Keeps` (grid), `MMap id` (modes) and a tabs
family are the *same* predicate three times with a different field in the hole. Rather than
hand-roll a fourth copy (~25 lemmas, which is what the recon plan budgeted), I lifted the
plumbing once: `Fixes π bs` — "from ground, this stream returns to ground with nothing
half-decoded and leaves `π` alone" — with `nil`/`append`/`streamPred` and the generic CSI/OSC
walks (`fixes_csi_seq`, `fixes_csi_priv_seq`, `fixes_csiNum`, `fixes_csiNum2`, `fixes_csiPriv`,
`fixes_sgrOf`, `fixes_penSgr`, `fixes_osc`), each taking the π-fact for its own dispatch.
`csi_tail_proj` already did the hard walk generically, so `fixes_csi_seq` is six lines.
`keeps_eq_fixes : Keeps bs ↔ Fixes (·.grid) bs := Iff.rfl` records the duplication in the file;
collapsing `Keeps`/`MMap id` onto it is a mechanical re-point of ~30 call sites, deliberately
NOT done because those call sites carry the A1/A5 grid claims. The next field costs almost
nothing now.

Where I did NOT generalize, and why: `escSeq`/`escCharset`/`SO` are eight lines of case
analysis each whose only field-dependent step is one `rfl`, and **the byte sets differ per
field** — `ESC H` (HTS) writes the ruler but no cell, so `keeps_escSeq` admits `0x48` and
`fixes_tabs_escSeq` must not. Copying that byte list verbatim would have given a *false*
lemma; this is the §5 hazard the recon flagged and it is real. Generalizing there would have
meant three extra hypotheses per lemma to say "and this byte is safe for π".

**Two places the ruler's claim is genuinely simpler than the grid's**, both worth knowing:
1. `tabs_setMode` is **unconditional** for every mode number (`setMode`'s only non-`modes`
   arms are `enterAlt`/`leaveAlt`/`moveTo`/the DECSC slot, none of which writes `tabs`). So
   `fixes_tabs_modesAnsi` needs no allowlist and **no digit bridge** — contrast
   `keeps_modeSet`, which must exclude 47/1047/1049 because they swap the grid, and therefore
   needs `csi_digits_value` to identify the emitted number with the parsed one.
2. `tbc3_clears` asks only `pstate = .ground` of the receiver — **no `u8need = 0`**. The
   leading `ESC` of `CSI 3 g` aborts a half-decoded character itself
   (`step_esc_of_abort` + `feed_esc_of_abort` + `un_abortUtf8_esc`), and nothing about the
   ruler rides on the bytes it discards. That is the same argument `SMap` makes for the sticky
   bundle, and it is what keeps this claim free of the `paint_entry`/`U8Ok` apparatus the grid
   needs: the paint ends in glyph bytes, so `u8need = 0` right after it is expensive — and
   here it simply is not required.

The core: `tbc3_feed_eq` (TBC 3 as a state equation, `cha_feed_eq`'s shape with final `0x67`
and `arg 0 0 = 3`), `hts_feed_eq` (ESC H as a state equation), `hts_run` (the fold), and
`tabs_rebuilt` (clear-then-set reproduces the ruler, `Array.ext` size-and-pointwise, the
`grid_eq_of_cells` route). `hts_run`'s invariant carries `ground`, a quiesced decoder, `cols`
and the ruler — the **cursor is not carried**, because `CHA` establishes it and `HTS` consumes
it inside one iteration. That is why this is much simpler than `Matches`, which has to tie
cursor and grid *across* iterations.

Hypotheses, and why each: `Good w` (for `dims_feed` — the paint contains `0x63`, so
`dims_feed_ne_ris` does not apply), `w.cols = v.cols` (TBC 3 writes `replicate (receiver's
cols)`), `v.cols < 65535` (the largest emitted `CHA` parameter is `cols`, off the parser's
clamp — note **not** `< 65533`, which is `rowSlot`'s `x + 3` bound and irrelevant here), and
`v.tabs.size = v.cols`, which `Good`/`Renderable` do **not** carry: a longer ruler could hold a
stop no `range cols` walk emits. Proving `tabs.size = cols` a reachability invariant is a
`tabs_*` frame family of its own — worth doing, not needed here (recon's F2, deliberately not
attempted). Non-vacuity: instantiated at `Vt.init 80 24`, with `size_defaultTabs` as the
`hvtabs` witness — which also claims one more core def, so `STATEMENT_CAP` **tightens 21 → 20**.

Gotchas: `min (min 3 65535) 65535 = 3` with *literals* is already reduced, so `cha_feed_eq`'s
`rw [show … from by omega]` trick does not transfer — use `simp [hpar, hcur']`. A `match` on a
literal needs an explicit `rfl` after `rw [harg]` (`rw`'s auto-rfl does not fire). `Array.getD`
+ `dif_pos` leaves `getInternal`, so use `getD_lt'`. `Bool.eq_false_or_eq_true` yields
`= true ∨ = false` (that order). Destructuring `Fixes π` leaves a **beta-redex** where the goal
has the field applied — `dsimp only at h` lines them up; that friction is inherent to
parameterising by a function and is the same thing `MMap`'s users pay with `id_eq`.
`frame_moveTo`/`frame_enterAlt`/`frame_leaveAlt` are **looping** simp lemmas (they rewrite
`v.moveTo x y` into a record containing it), so `tabs_setMode` needs the *projection* lemmas
`tabs_moveTo`/`tabs_enterAlt`/`tabs_leaveAlt` first — exactly what `dims_setMode` does.

Break-verify, two of them, and the second is the one that matters:
* **Emitter-side, shape:** `csiNum (i+1) 0x47 → csiNum i 0x47` in `tabsAnsi` (the off-by-one),
  and separately dropping `escSeq 0x48` entirely. Both fail `restore_tabs_split` (9791) plus
  the four pre-existing stream lemmas over `tabsAnsi` (`ends_`/`quiet_`/`keeps_`/`smap_id_`).
  Legitimate, but these are *shape* catches — the split equation is syntactic.
* **Emulator-side, semantic (the sharp one):** `HTS` sets the stop at `cursor.x + 1` instead of
  `cursor.x` in `Zmx/Core/Vt.lean`. `tabsAnsi`'s shape is untouched, so `restore_tabs_split`
  still holds and **nothing pre-existing notices** — the single failure is `hts_feed_eq`
  (9731), i.e. the new ladder is the only thing in the repo that can catch a wrong tab column.
  That is the demonstration that the ruler claim does real work.
Reverted both; `Zmx/Core/*` byte-identical; `./lake build Theorems Tests` green and
warning-free, `./tests/e2e.sh` green, coverage 20/20.

## FINDINGS item 1 — 2026-08-18 (split Theorems/Render.lean; the heartbeat sweep refutes its own hypothesis)

`Theorems/Render.lean` (9,866 lines, 13 namespace open/close cycles) is now a 38-line façade
over ten parts in `Theorems/Render/`: Ends, Quiet, Pen, Keeps, Modes, Sticky, History, Row,
Grid, Tabs — cut at the boundaries the file's own `/-! ## …` headers already named, in a linear
import chain so declaration order is preserved exactly. Verbatim move, checked mechanically:
the 607-name declaration set diffs empty, and each part's body is byte-identical to its slice
of the original (a script reconstructs the original from the parts). No statement, proof or
docstring text changed.

Two things the split forced, both worth knowing before splitting any Lean file:
* **`private` does not cross a module boundary.** `u8_bounds` (used by the Quiet, Pen and Keeps
  rungs) and `print_quiet` (used by Row) were private only because everything lived in one
  file. They lost the modifier, with a comment saying why. Every other private helper turned
  out to be genuinely file-local — checked by grepping each one's usages across the new parts.
* **`tests/coverage.py` globbed `Theorems/*.lean` non-recursively**, so the moment the theorem
  statements moved into a subdirectory the gate read 58 core defs as unclaimed and failed.
  `rglob`, which is what it already did for `Zmx`. The e2e `git grep -- 'Theorems/*'` gates
  (sorry / native_decide) were fine — git pathspec globs match across `/`.

**The acceptance criterion was "bumps that survive are the record-width tax, the ones that
disappear were file size". The control refutes it.** 18 of the 20 `maxHeartbeats` raises turned
out deletable — but re-running the same deletions at the PRE-SPLIT commit (`1f68e42`, throwaway
worktree) shows all six representative ones were *already* deletable there. So the split earns
no credit: those raises were paying for neither file size nor record width. They were stale —
budget added when the proofs were in an earlier, rougher shape and never re-measured once the
surrounding lemmas got factored. **A `maxHeartbeats` raise is a measurement with an expiry
date, and nothing expires it.** The sweep is cheap (delete the line, build the module, restore)
and belongs after any large refactor.

Where the real cost is, measured by capping each file at half the default (100,000): exactly
three tight declarations — `Grid.paint_range` (the `Matches` strong induction), `Vt.csiDispatch`
and `Vt.renderable_csiDispatch` (dispatch-table case splits under `Good`/`Renderable`). All
three are invariant-over-wide-record work, so THEOREMS.md's record-width diagnosis survives as
a description of *where* cost concentrates — and note `Vt.csiDispatch` never had a raise at
all. `Row.lean` and `Modes.lean` pass at 50,000, a quarter of the default. Survivors kept:
`Checkpoint.load_save` needs its 2,000,000 (fails at 1,000,000); `Vt.renderable_stepGround`
needs 600k–1M, so its 2,000,000 is generous — left alone rather than tightened into fragility,
since a raise that is merely generous costs nothing and a tight one is a future surprise.

Item 2 (measured, not refactored): across the 12 invariant-discharging rungs, field bookkeeping
is ~22% of proof lines against ~78% argument, and the distribution is the tell — the *small*
rungs are discharge-heavy (`step_pen`, 34 lines, ~47%) while the *large* ones are argument
(`paint_range` 8%, `mark_step` 18%). Bad factoring would show cost growing with field count;
this grows with the difficulty of the step. Verdict: hard core. That also prices the deferred
"read-only fields into parameter position" refactor — it would attack the 204 bookkeeping lines
and none of the 742, i.e. legibility, not length.

## runtime-invariants step 2 — 2026-08-18 (Buf: the daemon's queues as a proved value)

`Zmx/Core/Buf.lean` + `Theorems/Buf.lean` + `Tests/Buf.lean` + a three-grep gate in
`tests/e2e.sh`. The runtime half of §Bound is now arithmetic with a proof and a source-tree
gate instead of a paragraph ending "not proved".

**The design diverged from the spec, and this is the interesting part.** The spec (and today's
daemon) shape a queue as `bytes` + an `off` the writer advances, with `bufCompact` reclaiming
the written prefix on every flush. Writing `bufOffer_owed` — "an accepted offer really is
appended" — needs `off ≤ bytes.size`, which no type enforced and every *content* proof would
have had to assume. That is the `design-for-provability` trigger, so the definition moved
rather than the theorem: since we compact on every flush, `off` is always 0 between rounds, so
the persistent state never needed it at all. `Buf` now holds exactly the bytes still owed; the
flush loop keeps its cursor as a local `Nat` and calls `bufAdvance` once when it stops.

Consequences worth knowing:
* The partial-drain leak is **unrepresentable**, not merely absent — there is no prefix to
  retain. `bufCompact` and its two theorems disappeared; `bufNoRetain : bufSize b = owedLen b`
  is `rfl` and *that is the claim*: memory equals debt structurally. Re-introducing the bug
  means changing the type, not deleting a line.
* Several proofs are one word (`rfl`) for the same reason. Short proofs here are the payoff of
  the representation, not a sign the claims are weak — `bufAdvance_owed` and `writeFrom_owed`
  are the same statement twice precisely because the queue *is* its debt.
* Nine theorems, each bound paired with a content twin so it cannot be satisfied by discarding
  data: `owedLen_eq` (the bridge — without it every bound is about an unrelated `Nat`),
  `bufNoRetain`, `bufAdvance_wf`/`bufAdvance_owed`, `bufOffer_bound`/`bufOffer_owed`,
  `bufEnqueue_bound`/`bufEnqueue_owed`, `writeFrom_owed`.
* `bufEnqueue_bound` stays **hypothesis-guarded** (`.2 = false → owedLen ≤ cap`). `.send`
  appends and *then* decides, so at the decision the frame that crossed the cap is queued and
  the honest unconditional bound is `cap` + one wire frame. Two enqueue functions, not one: the
  child path measures before appending (unconditional bound, no partial frame ever queued), the
  client path after. One shared function would force a theorem false of the shipped `.send`.

**A performance regression I introduced and caught.** The first flush loop called
`writeBuf fd (bufAdvance c.out wrote)`, which re-slices — O(n) *per iteration*, where the old
code passed an offset. Fixed by giving `Posix.writeBuf` a transient `sent` cursor: stored state
stays offset-free, the syscall gets the offset, one copy per flush as before. (`from` is a
reserved keyword in Lean 4; the parameter is `sent`.)

**Open-decision 1 (per-field `private`) — MEASURED, and the answer is no, for a reason worth
recording.** Lean 4.32 *does* block a cross-module read of a private structure field
("Field `bytes` from structure `Zmx.Core.Buf.Buf` is private"), and reading is what every
buffer arithmetic needs — so it would make the discipline compiler-enforced. Two findings kill
it for now: (a) `private` hides the field from `Theorems/` too, so the proofs would have to live
in `Zmx/Core/Buf.lean`, and `tests/coverage.py:100-113` scans `Theorems/**` *only* for theorem
statements — all seven new defs would become unclaimed surface and breach the 20/20 ratchet,
which must stay monotone; (b) it is only half a discipline anyway: structure-instance notation
and `{ b with … }` can still **write** a private field where they cannot read one (verified
both ways). Revisit the day `coverage.py` also counts theorems in `Zmx/Core` — that is the one
change that would make this adoptable.

**`Cli.queryInfo`'s accumulator was a live unbounded accumulation** and is now capped through
`bufOffer` at `infoReplyCap = 1 MiB`. Its loop's only exits are `.done`/`.err`/EOF/a 2000 ms
*silence* timeout, so a peer streaming `infoReply` frames steadily never ended it. Low severity
(`linger ls` is short-lived), but it is the same class as the `ptyIn` bug and the gate's first
act was to find it.

**The gate.** Three greps after the `SHIM_CAP` block: no `ByteArray` structure field, no
accumulating `mut … : ByteArray` local, no `.extract` in `Zmx/Runtime/*`. It is non-negotiable
because `Zmx/Runtime/*` is `IO`: no theorem can see that the daemon calls the proved functions,
so without it the theorems are arithmetic about a value nothing forces the runtime to use.
Zero false positives — `Client.encodeBA`'s *return* type and `splitDetach`'s *parameter* are
correctly permitted, which matters because a gate that cries wolf gets disabled.
**It measures something:** on `9ea62b0` it finds 5 hits (`Conn.out`, `Rt.ptyIn`,
`Cli.queryInfo`'s `mut acc`, and the two `.extract` compactions); after, 0.

Break-verify, four, two of them independent oracles for the same regression:
* `bufAdvance := fun b _ => b` (keep the prefix — the partial-drain regression): 5 errors,
  failing `bufAdvance_wf` (Theorems/Buf.lean:53) and `bufAdvance_owed` (:60).
* The same break also refutes **four `native_decide` fixtures** in `Tests/Buf.lean` (:28, :29,
  :35, :38) — the ones that assert `bufSize` tracks `owedLen` across a partial drain.
  **The contrast is the entire justification for this step:** the equivalent regression in the
  pre-`Buf` daemon (deleting the `extract` from `flushConn`/`flushPty`) left
  `./lake build Theorems Tests` completely green, and its only live oracle was the daemon's RSS
  under a 16 MiB flood — which the 2026-08-18 entry above records as measured and *rejected* as
  too noisy to assert. Same bug, previously invisible to the build, now two kernel-reducing
  oracles.
* Gate, twice: `dummy : ByteArray` added to `Conn` → G1 fires with the file and line;
  a stray `.extract` in `flushPty` → G3 fires. Both reverted.

Gates: `./lake build`, `./lake build Theorems Tests` green and warning-free; `coverage.py`
`20 (cap 20)`, `FAILURES: 0` (all seven new core defs named by a theorem statement — note
`bufSize`/`owedLen`/`owed`/`writeFrom` were chosen to dodge the namespace-stripping collision
the gate has with `Ring.push`/`Vt.size`); `./tests/e2e.sh` `E2E OK`; robust/attach/resume/
overview/status all `FAILURES: 0`, including robust case 3's exactly-once backpressure log and
its pending-within-cap assertion through the new `bufOffer` path. `SHIM_CAP` untouched at 27 —
`Posix.writeBuf` is a Lean-level wrapper over the existing `zmx_write` extern.

## ledger-cleanup close-out — 2026-08-19 (the parked host guard, and two ratchets)

**The last parked item is done.** `Remote.checkHosts` now rejects a host carrying a C0 control
or DEL, alongside the existing duplicate rejection: `hostClean`, `firstDirtyHost`, and
`checkHosts_ok_clean` (+ `firstDirtyHost_none` as the walk↔predicate bridge, which is what lets
the headline theorem be about the *bytes* rather than about the walk). Both new core defs are
named in theorem statements, so coverage stays 20/20.

Three design points, each a "why not the obvious thing":
* **Reject, don't scrub.** The host string goes into `ssh` argv, so rewriting it would connect
  somewhere the user did not name. Same argument the duplicate guard already made ("a
  configuration mistake with no valid meaning"). Contrast `humanListing`, which *scrubs*,
  because there the string is only displayed.
* **Not `Name.sanitize`.** `@` is not an `okChar`, so sanitizing would destroy a legitimate
  `user@host` target. Pinned by a fixture (`user@gpu2.example.com` must pass).
* **The refusal message scrubs the host it names.** The error is printed to a terminal, so
  echoing the raw bytes back would inject the escape through the *error* path — the listing was
  hardened yesterday and this was the remaining hole in the same class. Pinned by a fixture
  asserting the message carries no `0x1B`.

Break-verify: drop the rejection branch → `checkHosts_ok_nodup` and `checkHosts_ok_clean` both
fail to compile (their `split` no longer has a match to split) **and** four `native_decide`
fixtures are refuted, including the message-cleanliness one. Reverted; green.

**Two ratchets added to `tests/e2e.sh` §2, both break-verified**, turning yesterday's two
findings into gates rather than prose:
* `HEARTBEAT_CAP=2`. The factoring audit's real lesson was not the split: the control run showed
  six of the 18 deleted raises were **already deletable before it**, i.e. they were stale budget
  from when the proofs were rougher, and nothing expires such a measurement. Adding a third raise
  now fails with "a proof got harder — read that, or re-measure and delete a stale one".
  (Verified the naive break first: putting `set_option` above the `import` fails the *build*, not
  the ratchet — place it on a declaration to test the gate.)
* `RUNTIME_PARTIAL_CAP=2`. `pump` and `parseLs` are honest; the other five had the keyword by
  habit. Marking `flushPty` partial again fires the gate by name.
Both live next to `SHIM_CAP` and the `Buf` greps, and the reason is written at the gate.

`AGENTS.md` gained four rules from this stretch: the heartbeat-expiry rule, the
do-block-loops-don't-need-`partial` rule, "a proved pure value needs a grep gate to bite"
(generalising the `Buf` gate), and **one writer at a time on this tree** — two agents editing
concurrently raced the coverage ratchet (untracked files are invisible to `git diff -- Zmx/`, so
an out-of-band read caught a half-written state and reported 28 unclaimed defs), and both
compile the same tree so each sees the other's partial files as errors.

Also caught by running the gate myself rather than trusting a green report: `Zmx/Core/Buf.lean`'s
docstring contained the literal word `sorry` in prose, which trips the purity grep — the tree was
failing `e2e.sh` when it was reported green. Reworded. The gate is deliberately dumb; prose must
dodge the banned tokens.

## scrollback step 1 notes — 2026-08-19

`specs/scrollback-fidelity.md` Step 1: the ring reaches the receiver's own scrollback. The
capability, the oracle, the budget and the bridge; no new induction. Completion record is in the
spec. What follows is what only a worklog can carry.

### The oracle has a blind spot, and it is structural

`replayEq`'s new conjunct is `r.sb.toList == (sbRows v).toList` — the receiver's ring against the
**emitter's own view of the ring**. So it cannot see a single bug *inside* `sbRows`: reverse the
history and both sides reverse together. Found by break-verifying, not by design review, and it
invalidated three of the planned breaks as written. The fix is fixtures anchored on **literals**:

* `(sbRows scrolled).toList.map rowStr == ["aa", "bb", "cc"]` — the order;
* `(sbRows wideRing)` texts `["a漢b", "éx", "zz"]` and widths `[1, 2, 0]` — the fit;
* `hostileRing`, a ring row as only `Checkpoint.load` can make one — the sanitizer;
* the headline `history` string, which spans ring **and** screen against a literal.

Generalisation worth keeping: *a fixture that compares the code against the code is not an
oracle.* The tab-ruler bug hid behind a receiver that never differed; this one would have hidden
behind a comparison that always agreed.

### Breaks

Each was applied to the real tree, built, and reverted. "caught by" lists what went red.

* **B1 — delete the paint branch** (`else csiNum 3 0x4A` only). 15 fixtures, including the
  headline string, every `roundtripsFrom` on a scrolling session, the wide-glyph ring, the shrink
  case and all three byte-budget fixtures. **And both Python halves**: `attach_test` step 11's two
  "a line that scrolled off is replayed" assertions, and `resume_test`'s
  `survives-the-reboot-42` — which is the assertion the spec said "fails today", now that the
  marker is pushed off the screen before the detach. It does.
* **B2 — drop `ED 3`.** `roundtripsFrom (dirtySb 6 2) scrolled` fails while **`roundtrips
  scrolled` (fresh `Vt.init`) still passes**, and so does `roundtripsFrom (midOsc 6 2) scrolled`,
  because `midOsc`'s ring is empty. That is the exact blind spot that hid the ruler bug,
  reproduced on a new field. Also `Ends.lean:888` (the layer lemma) and the ED2/ED3 order fixture.
  Measured without `ED 3`: a second attach gives `["OLD1","OLD2","aa","bb","cc","aa","bb","cc"]`.
* **B3 — `ED 3` after the push.** Every ring fixture including the pristine `roundtrips scrolled`
  — our model wipes what it just filled. The three byte-length fixtures **pass**, since the bytes
  are the same ones reordered: lengths are not an oracle for order.
* **B4 — flush `rows ± 1`.** Measured `history` strings, plain and coloured:
  - `rows - 1` → `"aa\nbb\ndd\nee\n"` / `"AA\nBB\nDD\nEE\n"`: the **newest** history row is lost.
    It never leaves the screen, and the screen paint overwrites it.
  - `rows + 1` → `"aa\nbb\ncc\n\ndd\nee\n"` / `"AA\nBB\nCC\n\nDD\nEE\n"`: one spurious blank
    pushed **after** the newest history row, i.e. between history and screen — not leading it.
    Ring size 4 instead of 3, and on the coloured session the extra row's cell 0 carries
    `bg = Color.idx 196`: it is a coloured bar in the user's scrollback, not a blank line. That is
    `scrollUpIn` vacating with `blankRow cols v.pen`, with the pen the last painted row left.
  - At `rows + 1` the whole-stream bound fixture also fails (one extra CRLF), so the bound is
    sensitive to the flush count. Nothing else outside the `sb` oracle is: `replayEq` **minus**
    `sb` is true at `rows - 1`, `rows` and `rows + 1` alike, so the grid theorems staying green is
    zero evidence about the flush. `F = v.rows` was swept exhaustively over `rows, m ∈ 1…8` before
    the build: 64 of 64 cells admit exactly one `F`, always `rows`. No `min`, no `rows = 1` case,
    no `m < rows` case — for `m < rows` the surplus CRLFs are absorbed by the non-pushing descent
    and push **zero** blanks.
* **B5 — the double reverse, both halves.**
  - drop the outer `.reverse` → history reads backwards. Caught by the two literal anchors and
    the headline string; **not** by `replayEq` (see the blind spot above).
  - feed `v.sb.toList` instead of its reverse → the **oldest** N survive a tight budget. Pinned as
    a fact: a fitted 6-column row costs 12, so `sbTake 6 27` on the reverse gives `["bb","cc"]`
    (right) and on `toList` gives `["aa","bb"]` (wrong). Both variants keep all three rows
    whenever the ring fits whole, which is why every other fixture would have passed.
* **B6 — bare `Vt.resizeRow` for `fitRow`.** Caught by `rowOk_fitRow` and `fitRow_id_of_rowOk`,
  and — before the anchors were added — **by no fixture at all**. The spec predicted the shrink
  fixtures would fail; they do not, because `resizeRow` also mends and re-widths. The only
  difference is `cellFit`'s substitution/filter/width normalisation, which is unreachable from a
  live session (its ring rows are already `CellOk`) and reachable only from a decoded checkpoint.
  So `hostileRing` was added and now catches it. Recording the negative half deliberately: this
  break is a *proof* break by nature.
* **B7 — the budget.** `1 <<< 30` → the heavy-ring non-vacuity and both emitted-length fixtures
  fail. `0` → the `scrolled` fixtures fail **including the `(sbRows scrolled).size == 3`
  non-vacuity**, which is what proves the trim is not silently eating everything.
* **B8 — `cellFit` without the width-0 guard.** Caught by the wide-ring anchors (the text and the
  `[1,2,0]` widths) and by `fitRow_id_of_rowOk`. Note honestly: `cellOk_cellFit`'s *proof* also
  breaks, but only because it is written around the `if`; the **statement** stays true (`width :=
  charWidth base` satisfies the clause trivially). The spec's warning stands — `CellOk` does not
  measure the sanitizer's correctness, and it is the literal anchors that do.
* **The mode tail's kill criterion** (the one the spec said nobody would remember to check).
  Dropped `csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true` and repaired the three layer
  lemmas, then tried to close `scrollback_entry`'s conjuncts from what was left:
  - `origin = false` **still closes**, via `Quiet` (which carries origin and needs no `u8need`).
    Verified positively in `/tmp/killcrit.lean`, which compiles.
  - `insert = false` and `wrap = true` **do not**: the only layer that carries them is `MMap`
    (= `Fixes (·.modes)`), which demands `u8need = 0` going in, and the only instance that would
    cross the paint is `mmap_id_gridAnsi` — `Unknown identifier`. It does not exist because
    nothing in the repo proves the u8-quiescence of a glyph run (`Ends` is scoped to `pstate`;
    `gridAnsi_writes_grid'` wants `painted.size = receiver.rows`, which `sbRows` violates by
    design). So the bytes stay, and the reason is a **missing lemma, not a falsehood**.
  Anyone checking only `origin` would wrongly shed twelve load-bearing bytes.
* **`mmap_of_esc_lead` without its case split** (`h v hg rfl`): `Application type mismatch … rfl
  has type ?m = ?m but is expected to have type v.u8need = 0`. The split is the whole lemma.
* **`sbRowCost`'s `+ 6` → `+ 0`**: `rowAnsi_len_le_cost`'s `omega` fails. So the cost function is
  a claim now, and Definition-of-done item 3's "the proofs would survive changing `+ 6` to `+ 0`"
  is no longer true.

### Measured numbers worth not re-measuring

Ring shapes at 24 rows, `sbReplayBytes = 262144`, `outbufCap = 4194304`:

| ring | avail | kept | Σ sbRowCost | stage bytes | whole `restore` |
|---|---|---|---|---|---|
| empty, 80 cols | 0 | 0 | 0 | 14 | 2,207 |
| blank rows, 80 cols | 10,000 | 3,048 | 262,128 | 250,007 | 252,200 |
| realistic mixed, 80 cols | 10,000 | 2,383 | 262,130 | 252,669 | 254,862 |
| per-cell truecolour, 40 cols | 300 | 174 | 260,844 | 260,219 | 261,417 |
| 84 plain + 1 truecolour, 85 cols | 3,000 | 2,166 | 262,086 | **262,153** | 264,304 |

`(scrollbackAnsi v).length = Σ sbRowCost (sbRows v) + 2 * v.rows + 19` **exactly** on the last row
of that table — and on every one of sixteen column widths swept from 70 to 85, which is why the
bound is stated in that form and asserted as a fixture rather than left to Step 5. The 19 is
`ED 3` (4) + the paint's `SGR 0 CUP` (7) + the mode tail (14) − the per-row CRLF credit the
`joinCRLF` separators do not use (6). The last row also **exceeds** `sbReplayBytes` by 9 bytes:
the budget bounds the counted cost, not the stream.

Per-row: a blank 80-column row is 80 emitted / 86 counted; per-cell truecolour is 40 B/column, 57
with all seven attributes; `penSgr {}` is 4 bytes and the `+ 4` is attained (a blank row is 80
from the default pen and 84 from a truecolour one). A full `sbCap` ring is 32–46 MB at 80 columns
— 8–11× `outbufCap`, which *disconnects*. The spec's "~86 MB" is the 150-column figure.

Real pty bursts, 80×24: a 60-line plain reattach is **5,381** bytes; the same with 20 truecolour
cells per line is **54,287**. Both two orders under `outbufCap`.

**The unbudgeted term is the screen paint, not the ring.** With worst-case pens on both screens,
today's `restore` emits 219,276 bytes at 80×24, 1,140,617 at 200×50, 3,420,922 at 300×100 and
**4,561,018 at 400×100 — past `outbufCap` with no scrollback at all**. Pre-existing; Step 1 adds
~262 KB, moving the cliff from ~36,800 to ~34,500 cells of window area. Recorded in THEOREMS.md
§Restore so it is not rediscovered as a scrollback regression.

### Proof recipes

* **`mmap_of_esc_lead`** — the reusable trick. `MMap`/`Fixes` demand `u8need = 0` going in, which
  is unavailable after glyph bytes. For an **ESC-leading** chunk it is free: `by_cases` on
  `u8need = 0`; in the positive case apply the hypothesis, in the negative case `abortUtf8` on the
  leading ESC makes the state *literally equal* to `{ v with u8need := 0, u8acc := 0 }`, whose
  `modes` agree. Any future stage that must re-establish modes after a paint should end
  ESC-leading and reuse this.
* **`rw [feed_append]` chains are order-sensitive.** `++` is **left**-associative (the comment at
  `Keeps.lean:888` claiming otherwise is wrong), so `rw` peels the *outermost* append first. With
  the history stage in front of the alt branch's five chunks, the fourth peel reaches
  `penSgr mpen ++ csiNum2 …` — the cursor park — and splits it, after which nothing matches and
  the elaborator burns 2,000,000 heartbeats in `whnf` on `List.append`. Fix: one
  `have hpeel : w.feed (…) = (((…).feed …).feed …) := by rw [hscreens]; simp only [feed_append]`.
  `simp only [feed_append]` normalises **both** sides to the fully-peeled form, so it is
  confluent where a hand-counted `rw` chain is not. Cost: 0 extra heartbeat raises
  (`HEARTBEAT_CAP=2` untouched).
* **`penSgr_default_len`** needs `have hd : digits 0 = [0x30] := by rw [digits]; simp` first —
  `digits` is well-founded recursion and both `decide` and `rfl` get stuck on it.
* **Lemma placement bites in `Ends.lean`/`Quiet.lean`.** `ends_modeSet`, `quiet_modeSet` and
  `quiet_modeSet_decom_off` were defined *after* `ends_screensAnsi`/`quiet_screensAnsi`; the
  stage's layer lemma needs them and has to precede the screens lemma. Moved the three blocks up
  rather than duplicating them.
* `smap_id_modeSet_safe` was lifted out of `smap_id_modesAnsi`'s local `have hm`, unchanged, so
  the scrollback stage and the modes replay share one lemma instead of two copies.

### Environment facts

* `List.sum_reverse`, `List.map_reverse`, `List.toList_toArray`, `List.mem_of_mem_take`,
  `List.take_of_length_le`, `List.filter_eq_self`, `Array.ext`, `Array.getElem_range` all exist in
  4.32 core — the spec's worry about `List.sum_reverse` was unfounded.
* `Array.toList_toArray` does **not** exist; the name is `List.toList_toArray`.
* `Tests.Render` elaboration went from ~0.7s to ~17s with the byte-budget fixtures (two rings of
  3,000 and 10,000 rows through `native_decide`). Acceptable, but that is where the time is if it
  grows again.

## scrollback step 1 — audit follow-ups, 2026-08-19

Three independent audits ran against Step 1. Exit criteria: PASS (statements of
`restore_grid_any` / `restore_grid_reachable` / `resume_grid` byte-identical, gates green,
coverage 20/20). Break quality: PASS. Doc honesty: **FAIL**, and it was right — fixed here.

**The doc FAIL, because overclaiming is the one thing this repo cannot do.** Three live
overclaims in `THEOREMS.md`, all created by Step 1 shipping the emitter without the proof:
1. The `Render.restore` coverage row said "receiver-quantified for … every restored field but
   the screen cells". After Step 1 that sentence silently asserts receiver-quantification for
   **`sb`**, which has no theorem (`restore_sb_any` is Steps 2-4) — and its screen-cells
   exclusion was stale besides. Now names the cells and the ruler as proved and `sb` as
   fixture-carried.
2. The stage-budget paragraph read as though the **emitted** bytes were proved. They are not:
   `sbTake_budget`/`sbRows_budget` bound the *counted* cost `sbRowCost`, and the whole-stream
   emitted bound is fixtures (sharp at 262,153) until `scrollbackAnsi_le` in Step 5. The
   asymmetry is now stated where the claim is, per the spec's own DoD item 3 — the proofs would
   survive changing `sbRowCost`'s `+ 6` to `+ 0`, and a reader is entitled to know that.
3. The A5 row now lists scrollback as fixture-carried **and** records what this anchor's title
   now has an exception to: replaying the ring emits `ED 3`, so attaching to a session with
   history erases the borrowed terminal's saved lines. linger shares the user's scrollback (it
   never enters the alt screen), so that is the one thing it does to a terminal it cannot undo.
   Also deleted a stale sentence claiming the cursor claim is still `Vt.init`-only —
   `restore_cursor_any` has existed since the sticky round.

**The one real coverage gap the break audit found, now closed.** The two `sbTake` anchors spell
`.reverse` out *in the fixture*, so they document the trim rather than guard it: dropping
`sbRows`' own reverses left them passing. The break that describes — trim the oldest end with the
output order still right — was caught only incidentally, by `heavyRing`'s exact counts. Added a
fixture that asserts *which* rows survived **through `sbRows` itself**: `heavyRow i` encodes `i`
in its first cell's red channel, so the kept run is named as the newest 174 of 300
(`i = 126…299`; red 126,127 first and 43,42 last after the `% 256` wrap). Break-verified: the
audit's exact break (`sbTake … v.sb.toList` with no reverses) now fails it directly, alongside
two others. Reverted; green.

Two stale-citation fixes in `specs/scrollback-fidelity.md`, both of the kind that mis-plan a
resuming agent: it told a Step 3 agent that `paint_rows` "already needs `maxHeartbeats 1000000`,
`Grid.lean:792`" — there is **no** raise anywhere in `Theorems/Render/`, the tree's only two are
in `Checkpoint.lean` and `Vt.lean`, and `HEARTBEAT_CAP=2` has zero headroom, so a budgeted raise
would fail the gate. And the theorem is `Zmx.Core.resume_grid`; there is no `Resume` namespace.

Left as known-loose, deliberately: the two pty burst-length assertions have 12x and 77x headroom,
so they catch a catastrophic blowup rather than a 5x regression. Tightening them means
re-measuring on this host and pinning a number that will drift with the fixtures; the sharp
oracle is the `native_decide` bound at 262,153, which is exact.

## rename zmx → linger — 2026-08-19

Everything live is `linger` now: the Lean library and namespaces (`Linger.Core`,
`Linger.Posix`, `Linger.Runtime`), the `Linger/` tree, `Linger.lean`, the lake package and
`extern_lib`, the shim's 55 `linger_*` symbols, and the smoke exe (`ztest`/`ZTest.lean` →
`lingertest`/`LingerTest.lean`, with its `ZMXTEST` marker → `LINGERTEST`). 834 occurrences over
72 files; 63 files rewritten. The build is the oracle for the code half and it came up clean
first try, shim included — a `linger_*` symbol that failed to match its `@[extern]` would have
been a link error, so the C boundary is checked, not inspected.

**Three things deliberately NOT renamed**, each with a reason that is not branding:
1. **The checkpoint magic stays `"LZMX"`** (`Linger/Core/Checkpoint.lean:293`,
   `[0x4C,0x5A,0x4D,0x58,1]`). It is an on-disk **format identifier**: `load` accepts a payload
   only if `l.take 5 = magic`, so changing those bytes makes every existing checkpoint
   unreadable and a resumed session comes back blank. That is a format-version bump with a
   migration, not a search-and-replace. AGENTS.md already recorded it as frozen; the rename
   round did not get to overrule that by accident.
2. **`SCRATCHPAD.md` and `specs/archive/`** keep the old paths in historical entries — the
   worklog is append-only and the archived specs are closed records, so rewriting a path inside
   them would falsify what was true when written. Entries before today say `Zmx/…`.
3. **Citations of the upstream `zmx` project** ("verb surface mirrors zmx", "same resolution
   order as zmx", §Detach's "the zmx decoupling", PLAN.md's links). Those name someone else's
   project — prior art worth crediting, not stale branding.

**The real hazard was the gates going vacuous, not the code breaking.** Four of them are greps
over `Zmx/Core/*` / `Zmx/Runtime/*`, and `tests/coverage.py` globs `(ROOT/"Zmx").rglob`. Renaming
the directory without them would have left every one **passing while measuring nothing** — the
purity checks are `! git grep -n 'sorry' -- 'Zmx/Core/*'`, and a pathspec that matches no file
makes `grep` fail and therefore `!` succeed. Updated in lockstep and then *verified they still
measure*: coverage still reports the same `252 defs; 20 unclaimed (cap 20)` rather than a
vacuous `0`, the extern gate still resolves to exactly `Linger/Posix.lean`, `SHIM_CAP` still
counts 27, and the two new ratchets still count 2 and 2. Break-verified on the renamed path: a
`partial def` added to `Linger/Core/Name.lean` still trips `E2E FAIL: partial def in pure core`.
That check — "does the gate still fire after you move what it points at?" — is the one worth
repeating after any path change.

## checkpoint tag: LZMX -> LNGR with a legacy reader — 2026-08-19

`save` now writes `"LNGR"` v1; `load` accepts that or the pre-rename `"LZMX"` v1. The layout
after the tag never changed, so this is a **re-tag, not a format change** — which is what makes
"migrate completely without" achievable in one step: nothing to run, no flag, and a session's
next checkpoint is clean.

Two theorems, and only the pair means anything: `load_legacy_save` (an old file still resumes —
the rename orphaned nothing on disk) and `save_no_legacy` (a new file carries no trace of the old
tag — so the legacy reader is temporary rather than permanent). Plus `load_magic_agnostic`, which
says the tag is the *only* difference for any payload, garbage included.

**The interesting part was a proof getting harder, and what that meant.** Adding the second
branch inline to `load` made `load_save` time out at its existing 2,000,000 heartbeats. Per
AGENTS.md that is a signal to read rather than silence — and `HEARTBEAT_CAP` blocks silencing
anyway. Cause: with the tag decision inline, the round-trip proof carries it through the whole
parser chain. Fix was to name the stage (`stripMagic`, the `Vt.print*`/`rowSlot` idiom) and give
it two one-line lemmas. Consequences worth recording:
* `load_save`'s proof got **shorter** (four `List.take/drop` rewrites collapsed to one
  `stripMagic_magic`), and no longer needs its heartbeat raise at all — deleted. The tree is down
  to **one** raise (`Theorems/Vt.lean`), `HEARTBEAT_CAP` tightened 2 → 1.
* The legacy claims became two lines each instead of fighting the same chain.
* `magic` left `coverage.py`'s unclaimed list (the new theorems name it), and `stripMagic` /
  `legacyMagic` arrived already claimed, so the ratchet tightened 20 → 19 rather than needing a
  bump. That is the third time this round that naming a stage paid for itself twice.

Break-verified, both halves, each failing a theorem *and* a fixture:
* Remove the legacy branch from `stripMagic` → the old-file fixture is refuted and
  `stripMagic_legacy` / `load_magic_agnostic` stop compiling.
* Make `save` emit `legacyMagic` → `save_no_legacy` and its fixture fail (this is the break that
  proves "migrated" is a fact about the write side, not a hope).
Fixtures also pin the literal bytes of both tags, and that a *third* tag (`"LNGR"` v2, all-zero)
is still refused — the legacy branch widened what `load` accepts by exactly one tag, not by
"anything five bytes long".

**Verified end to end on real files**, not just in the kernel: created a session, detached (so the
daemon checkpointed), confirmed the file's tag is `[76,78,71,82,1] = "LNGR"`, hand-rewrote it to
`[76,90,77,88,1] = "LZMX"` to make a genuine pre-rename file, SIGKILLed the daemon and
reattached — `legacy-survives-42` came back — then detached again and the re-written checkpoint's
tag was `"LNGR"`. Migration observed, not inferred.

## drop the legacy checkpoint reader — 2026-08-19

`legacyMagic` and its read branch are gone; `load` accepts `"LNGR"` v1 and nothing else. The
reader lived one commit, which was the point of it: it existed to carry files written before the
rename, `save` had already been writing the new tag for a commit, and a check of
`$XDG_STATE_HOME/linger/<host>/` found **no `.ckpt` files at all**, so there was nothing on disk
to orphan. Verified before deleting rather than assumed — that check is the whole difference
between "removing dead code" and "removing someone's screen".

**The escape hatch, named so it is findable:** `e1ac562` has the reader plus
`load_legacy_save` / `save_no_legacy` / `load_magic_agnostic`, all green. Recorded in the
`save_tag` docstring, in AGENTS.md and in THEOREMS.md's §Restore row, because a deletion whose
recovery path is "search the log" is not really recoverable. Kept as a *fixture* too: `load` is
asserted to refuse `"LZMX"` v1 explicitly, so the old tag is now pinned as **rejected** rather
than merely absent — the difference matters if anyone reintroduces a tag check.

`stripMagic` stays a named stage even though it now tests a single tag. That is deliberate and
was measured in both directions: inlining the decision is what made `load_save` need
`maxHeartbeats 2000000`, and naming it is what let the raise be deleted. The tree still has
**one** raise (`HEARTBEAT_CAP=1`) after the deletion, so the benefit came from the naming and not
from the branch — worth knowing before someone "simplifies" a one-branch `if` back inline.

Ratchets: `coverage.py` holds at 19/19 (`magic` stays claimed through `save_tag` and
`stripMagic_magic`, so removing a claimed def did not push anything back into the unclaimed
list). Break-verified: reverting `magic` to the old four bytes refutes the byte-pinning fixture
and the refusal fixture (`Tests/Checkpoint.lean:71,87`).

Remote moved to `github.com/vincentqb/linger` (the old `lean-zmx` URL redirects). `git ls-remote`
resolves; its HEAD is `3ea04e5`, so local is **8 commits ahead** and nothing has been pushed —
that is the user's call, not mine.

## macOS port: four Linux assumptions the build hid, and one the gate hid — 2026-08-19

The tree moved to a darwin host (25.5, Apple clang, `/Users/quennv/lean-zmx`). `lake build` died
in the C backend on `SOCK_CLOEXEC`/`accept4`; fixing that exposed three more Linux assumptions,
two of which **compiled fine and were wrong at runtime** — the interesting kind.

* **`SOCK_CLOEXEC` / `accept4` (compile error, honest).** Both are Linux/FreeBSD extensions. Now
  `unix_socket_cloexec` / `accept_cloexec`, static helpers that take the atomic form where it
  exists and `fcntl(FD_CLOEXEC)` after the fact where it does not. The non-atomic window only
  leaks an fd if another thread forks inside it; the only fork here is `linger_spawn` from the
  same single-threaded Lean runtime, so the fallback is safe *here* without being safe in
  general — worth writing down, because that argument is what makes it acceptable. No new
  `LEAN_EXPORT`, so `SHIM_CAP` (27) is untouched.
* **`./lake`'s glibc workaround is Linux-only and *harmful* on macOS.** `LEAN_AR=/usr/bin/ar`
  points at Apple's ar, which cannot read the `@…rsp` response file lake hands it:
  `liblingershim.a: No such file or directory`. The mac toolchain's own clang and llvm-ar are
  fine. The wrapper now branches on `uname -s`, so `./lake build` stays the one command on both
  hosts (AGENTS.md's rule survives unchanged — the *reason* for it is just host-specific).
* **`linger_getcwd_of` read `/proc/<pid>/cwd` and silently returned `""` on macOS** — the failure
  mode was not a crash but a wrong session: `saveCkpt` falls back to `start_dir`, so
  reboot-resume reopened where the session was *created*, not where the user had `cd`'d.
  `resume_test`'s "fresh shell starts in the saved cwd" caught it. Replaced under `#ifdef
  __APPLE__` with libproc `proc_pidinfo(PROC_PIDVNODEPATHINFO)`, measured working for a
  same-uid process (the session shell is the daemon's child); it reports the resolved vnode path
  (`/private/tmp` for `/tmp`), which `chdir` accepts, so the caller is unaffected.
* **`Daemon.serve` tested `r == -111` for ECONNREFUSED.** That is glibc's number; macOS uses 61,
  so the stale-socket branch never fired and every daemon replacing a stale socket died on
  `bind: Address already in use (errno 48)` — eight of them at once in `robust_test`'s
  name-ownership race. Fixed by deleting the errno comparison rather than adding a platform
  table: we already hold the name lock at that point, so *any* failed connect means the path is
  ours to replace, and `ENOENT` makes the removal a no-op. Same reading `cmdList` already used.
  A raw errno constant in Lean is now a smell — the shim returns `-errno` and only the shim
  knows the numbers.

**The gate's own Linux assumption:** `resume_test` and `robust_test` found their daemon with
`pgrep -f '__daemon <name>'` filtered by `/proc/<pid>/environ` for `LINGER_DIR`. The filter is not
decoration — without it a test SIGKILLs whatever session of that name the developer has open.
macOS has no `/proc`, and `ps -Eww -p <pid>` prints the command with **no environment at all**
(measured, same uid), so there is nothing to read. New `tests/procs.py` keeps `/proc` where it
exists and otherwise asks about open files: the daemon holds the name flock on
`<ldir>/<name>.lock` and the bound `<ldir>/<name>.sock` for its whole life, so `lsof -nP -p`
names our dir iff the daemon is ours. Both spellings of the dir are accepted — lsof reports the
lock as `/private/tmp/…` while the socket says `/tmp/…`.
Break-verified the filter can say *no*: daemon in `LDIR` → `[pid]`, same call with a foreign dir →
`[]`. A fallback that always answered yes would pass every assertion in both tests and kill
strangers.

**Measured tty fact, and the one test payload that had to change.** `robust_test` part 3 needs a
child that stops reading to push back on the daemon. On macOS a nonblocking write of an
unterminated 256 KiB blob to a pty master whose slave never reads **succeeds forever** — 98 MB in
3 s — because the BSD tty layer *discards* an over-long canonical line instead of applying
backpressure. So `flushPty` always drained, `ptyIn` never grew, `ptyInCap` never tripped and the
"buffer full" line never logged: the test was asserting a condition it had failed to create. With
newline-terminated lines the same write gets `EAGAIN` after ~1022 B (canonical line queue), as on
Linux where either shape fills the 4 KB queue. Payload is now `(b'x'*63 + b'\n')*4096`, same
262144 B; the assertion then reports pending 4193282 B against cap 4194304. Nothing about the
property changed — the *stall* is now real on both hosts.

**What did not need touching**, checked rather than assumed: the `_Static_assert`s pinning the poll
bits pass on darwin (POLLIN/OUT/ERR/HUP/NVAL have the same values), and the pty path was already
`posix_openpt`/`grantpt`/`TIOCSCTTY` rather than glibc `forkpty`, so it ported for free — the
`a9f2e83` decision to avoid `-lutil` (taken for modern glibc) paid off on a host nobody had in
mind. All three builds and
`./tests/e2e.sh` (8 live suites) are green on darwin; ratchets unchanged (coverage 19/19,
`HEARTBEAT_CAP=1`, `SHIM_CAP=27`, `RUNTIME_PARTIAL_CAP` untouched). Not verified: that any of this
still builds on the AL2 box — the Linux branches are unchanged code, but nothing re-ran there.

**One repo hazard this surfaced, unrelated to any syscall:** the tree tracks *both* `Tests/`
(the Lean unit tests) and `tests/` (the shell/python e2e scripts). macOS's filesystem is
case-insensitive, so the two collapse into one on-disk directory (`Tests/`), and with
`core.ignorecase=true` git recorded a newly created `tests/procs.py` as **`Tests/procs.py`** —
which on a case-sensitive Linux checkout would put the helper in a different directory from the
tests that import it, so `from procs import daemon_pids` would fail there and nowhere else.
Staged deliberately instead: `git rm --cached Tests/procs.py` + `git update-index --add
--cacheinfo 100644,<blob>,tests/procs.py`, verified with `git ls-files --stage`. Anyone adding a
file to `tests/` from a mac must check the recorded path before committing.
||||||| parent of 8abdbcd (step 2: linger capture -- the screen one-shot, and a capture is a look)


## agent-cli steps 1–2 notes — 2026-08-19

Spec: `specs/agent-cli.md` (see its Decisions before touching any of this).

**Step 1 (info fields + `linger info`).** `infoFields` gained
`cols/rows/cursorx/cursory/alt/outseq`. `infoText_framing`/`infoText_records` needed zero
edits — they quantify over the field list, which was the design bet and it held. The new
verbs drain through `Client.drainBounded` (silence deadline, default 2000 ms): `oneShot`'s
`poll … (-1)` hangs forever against a daemon that never answers, and a **pre-upgrade daemon
answers a new verb with nothing at all** (§Frame drops unknown tags without a trace). That
is not hypothetical — linger daemons outlive binary upgrades by design. `wait` deliberately
stays on the untimed drain.

**Step 2 (`capture`).** Wire tag 16 (`.screen`, frozen-append), `Render.screenText` (the
grid only, `rowText` per row), `screenText_framing`/`screenText_lines` (proved, in
coverage.py's EMITTERS), the `onMsg` arm replying `outputMsgs (screenText) ++ [.done]` and
setting `lookSeq := s.outSeq` — **a capture is a look** (the user's call, spec Decision 1);
`.info` must never mark seen (`ls` polls every daemon) and `.history` stays an export.
`onMsg_screen` is `rfl`, so the reply shape and "the only state change is the read mark"
are one statement; `screen_marks_seen` is the user-facing half.

The `repeat' split; all_goals first | …` preservation proofs in `Theorems/Session.lean`
absorbed the new arm with **zero edits** — the order-robust-proof-script rule paying out
again. `decodeMsg_roundtrip` needed only `ne 16`; `decodeMsg_payload_le` one `by_cases`.

**Break-verified, four breaks, each caught by at least two oracles:**
* `infoFields` key renamed (`cols` → `width`) → `Tests/Session.lean:135` fixture refuted
  (and `tests/agent_test.py` would fail e2e). The porcelain keys are pinned.
* `screenText` painting `sb ++ grid` (the "obvious" transcript shape) →
  `screenText_lines` **type-mismatches** (the count is no longer the grid length), plus the
  grid-only fixtures in `Tests/Render.lean:797` and `Tests/Session.lean:174` refute. This is
  the break that guards capture staying positional (line k IS row k).
* `lookSeq` write dropped from the arm → `onMsg_screen` stops being `rfl`,
  `screen_marks_seen` unsolved, capture fixture refutes on `!unseen s2`.
* `.done` dropped from the reply → `onMsg_screen` fails, and **live**: `linger capture`
  printed the screen, hit the deadline at 2.01 s measured, said
  `no reply from 'b3' (daemon predates this command?)`, exit 1 — the no-hang contract
  demonstrated against a real daemon, which is the closest a test can get to "old daemon
  drops tag 16" without keeping an old binary around.

e2e gotcha for later steps: `linger send` does not press Enter (by design). A test that
`send`s commands and expects them to have *run* leaves them queued on the shell's input
line, and the junk corrupts the next `run` line — `tests/agent_test.py` floods via `run`
for exactly this reason. `capture` shows the *typed* line too (it is on the screen).


## agent-cli step 3 notes — 2026-08-19

`send <name> -`: stdin to the pty byte-exact, one `.input` frame per ≤ 64 KiB read,
poll-then-read (EOF = `read` → `none`; `some #[]` = would-block, looped past), no deadline on
purpose — a slow producer is legitimate and EOF is the only exit. Client-only: no protocol,
daemon or Core change, nothing accumulates (no `Buf` involvement, the e2e greps stay quiet).

**Break-verify found a worthless test and fixed it.** The break (drop the last byte of each
chunk) initially *passed* the e2e: the assertion looked for the marker in a capture, but the
tty echoes *typed* input onto the screen, so `echo STDIN-BOUND` appeared in the capture even
though the lost `\n` meant it never ran. The oracle now asserts on the shell *expansion*
(`echo "GOT-$((40+2))"` → `GOT-42`; typed line ≠ output line), and the break is caught.
Same trick for the ^C test (`INTER""RUPTED-OK` typed vs `INTERRUPTED-OK` executed) — though
under the dropLast break that one still passes as a **cascade artifact** (the corrupted
first line prevents `sleep` from ever starting), so the verbatim test is the load-bearing
delivery oracle and the ^C test is the control-byte semantics demo. Both recorded here so
nobody "simplifies" the markers back to plain text.


## agent-cli step 4 notes — 2026-08-19

`linger resize` — the control resize. The decision is a **named stage**
(`Session.controlResize`), not branches inline in the `.resize` arm, for the
`resizeEffects`/`stripMagic` reason: the theorems target the stage directly
(`controlResize_never_overrides` / `_applies` / `_same_size`, all `unfold` + `rw` proofs
with the guards as hypotheses) and `onMsg_resize_control` pins the routing, so no
setClient/sizeOwner-invariance lemma was ever needed — the statement shape dodged the
map/filter commuting proof entirely. The attached path is byte-identical to before (its
fixtures and `resizeEffects_owner_only` needed zero edits).

The seven message-generic preservation proofs (`onMsg_clients_length_le`, `_labels_le`,
`_decOk`, `_scan`, `_vt_good`, `_vt_live`, `_other`) absorbed both new arms (`.screen`
step 2, the restructured `.resize` here) with **only** `unfold onMsg` → `unfold onMsg
controlResize` — the `repeat' split; all_goals first | …` idiom paying out a third time.
No heartbeat raises anywhere in the spec's four steps (`HEARTBEAT_CAP=1` untouched); no
new syscalls (`SHIM_CAP=27`); `RUNTIME_PARTIAL_CAP=2` (the new CLI loops are `while` in
`do`); coverage tightened 19 → its cap held with `controlResize` and `screenText`
arriving claimed.

Break-verified (each caught by a theorem AND a fixture):
* sizer guard dropped (`if false then refuse…`) → `controlResize_never_overrides`'s
  `rw [if_pos h]` finds no `if` to rewrite (Theorems/Session.lean:819) and the
  refused-while-attached fixture (Tests/Session.lean:312) is refuted.
* same-size guard dropped → `controlResize_same_size` and `controlResize_applies`
  both fail (:831/:843) and the DECSTBM/tab-ruler preservation fixture (:336) is
  refuted — that fixture is the one that knows *why* the guard exists.

e2e closes the loop the pure fixtures cannot: `stty size` inside the session reports
`40 120` after `linger resize work 120 40` — the kernel's SIGWINCH path, the part no
theorem sees.

CLI validates 1..1000 (`clampDim`'s range) client-side: past 1000 the emulator would
clamp while the pty winsize did not, and the two must not be allowed to disagree from
this path (attach trusts a real terminal's report; an agent gets validated).


## agent-cli theorem hardening — 2026-08-19

Follow-up to the archived spec: three prose promises upgraded to statements, each chosen
because a fixture-passing wrong implementation exists for it.

**`screenText_records` / `history_records` / `history_screenText_suffix`** (+ the new
consumer-spec splitter `Render.linesLF` and its workhorse `linesLF_record`). Count +
framing say the right *number* of clean lines, not which bytes land on which line — the
"line k IS row k" promise in README/THEOREMS was implied, not stated. Now:
`linesLF (screenText v) = v.grid.toList.map rowText`, same for history over `sb ++ grid`,
and the capture is byte-for-byte the transcript's tail (`List.flatMap_append`, one line).
`linesLF` counts an unterminated trailing run as a record (a parser does not discard bytes
for a missing terminator) — pinned by fixtures, including `[0x0A,0x0A] → [[],[]]`.

**`onMsg_outSeq` + `onMsg_lookSeq_le` → `feedMsgs`/`step`/`run_lookSeq_le`** — the §Unread
honesty pair over whole traces, closing the increment the section header had parked
("the `.bytes` case makes it opaque to arithmetic"). The parked obstacle dissolved with
the same `unfold onMsg controlResize; repeat' split; all_goals first | …` script the
preservation theorems use; the one wrinkle was `step`'s ptyOut branch, where `omega` sees
`(⟨record, effects⟩).fst.lookSeq` as an opaque atom — a `dsimp only` before `omega` in the
alternative list reduces the pair/record projections and it closes. Landed now rather than
someday because `.screen` made `lookSeq` a two-writer field and `behind` an agent-facing
API (README tells agents to poll it).

**`controlResize_replies`** — guard-free totality on top of the three guarded shapes:
every control resize answers the requester (`.done` or `.err`), silence unrepresentable.
The pure half of the no-hang contract; `Client.drainBounded` owns the impure half.

Break-verified, three rounds:
* screenText emits `grid.reverse` → **`screenText_lines` (count) and `screenText_framing`
  stay green** — the wrong emitter passes both shipped step-2 theorems — while
  `screenText_records` and `history_screenText_suffix` refute (History.lean:161/:176; :124
  is the count theorem's *proof* needing a benign length-of-reverse rewrite, not a refuted
  statement). This is the measured content gap between "right number of clean lines" and
  "the right lines".
* `.screen` sets `lookSeq := s.outSeq + 1` → **`screen_marks_seen` AND `screen_behind_zero`
  stay green** (Nat subtraction clamps the lie to zero — `unseen` reads `outSeq+1 < outSeq`
  as false) — only `onMsg_lookSeq_le` (Session.lean:519) catches the overtake, plus
  `onMsg_screen`'s literal. The honesty chain is the ONLY oracle for this bug class;
  without it a future look-arm typo would ship a permanently-zero `behind`.
* same-size branch replies `(s, [])` → `controlResize_replies` (:942) and
  `controlResize_same_size` (:916) both refute — the totality claim catches the silent
  drop even where a shape theorem's guard doesn't reach.

Ratchets: coverage cap 19 holds (`linesLF` arrives claimed by four statements);
HEARTBEAT_CAP 1 (no raises — `linesLF_record`'s induction is light); nothing new in the
EMITTERS list beyond the strengthened descriptions (`linesLF` returns `List Bytes`, which
the stream regex correctly does not classify as an emitter).


## Lean module system on v4.32.0 — measured, before adopting — 2026-08-19

Probed in a scratch package (`/tmp/modprobe2`, same toolchain, same `./lake` wrapper) before
writing `specs/lean-modules.md`. Facts, each observed both ways where it matters:

* **Available, no experimental flag.** `module` + `public`/`private` + `@[expose]` +
  `public section` + `import all` all elaborate on the pinned `leanprover/lean4:v4.32.0`.
* **`private` structure fields now close BOTH holes** from the 2026-08-18 measurement that
  killed runtime-invariants Open decision 1: a plain importer cannot *read* (`Unknown constant
  _private…Buf.bytes`), cannot *write* (`{ b with off := 3 }` → "constructor for Buf is marked
  as private"), and cannot *forge* (`{ bytes := …, off := … }` → same). The old experiment's
  finding (b) — instance notation writes where it cannot read — is gone: field privacy makes
  the constructor private.
* **`import all` is the friend import the old experiment lacked** — finding (a) is gone too:
  a proof file outside Core sees private fields, module-private defs, and non-exposed bodies
  (`unfold`, `simp [f]`, `decide` all work), so proofs STAY in `Theorems/` and `coverage.py`'s
  Theorems-only statement scan keeps counting them. Grammar: `public import X` + `import all X`
  as two directives (`public import all` is rejected, with an error message saying exactly
  this). Statements that NAME private things must be module-private theorems (fine — theorems
  are leaves; being checked at build is their job); API-level statements can be `public`.
* **Proof bodies always get the private scope** — only statements are visibility-checked. A
  `public theorem` proved by `unfold`ing a non-exposed body compiles.
* **`@[expose]` refuses a body that touches private fields** ("constructor … is marked as
  private" on the exposed body). So sealed-type APIs are public-signature/hidden-body, and
  kernel-reduction consumers go through `import all`.
* **Interop is one-directional: legacy CAN import module, module CANNOT import legacy**
  ("cannot import non-`module` X from `module`"). Migration must walk the import DAG
  bottom-up. A legacy importer of a module file sees public bodies (its `decide`/
  `native_decide`/`unfold` keep working) **and privacy still binds it** (private field read
  and module-private def both refuse from a legacy file). So `Theorems/`/`Tests/` need no
  conversion except where they *state* things about sealed internals.
* **`public section` may run unclosed to EOF**, wrapping namespaces — so the
  semantics-preserving blanket posture is two inserted lines per file plus
  `import` → `public import`.
* **`@[extern] opaque` and `deriving Repr/Inhabited` over private fields work** under
  `module`; `partial def` unaffected.
* **Module files run at least one stricter lint** (`linter.unusedSimpArgs` surfaced as an
  error where legacy elaboration had been quiet) — expect small proof-hygiene fixes during
  migration, which is signal, not noise.
* **Gates:** the blanket posture leaves decl text as `def …`, so `coverage.py`'s
  `^(private )*def` scan and the e2e greps keep measuring unchanged; the regexes get
  hardened to also match `public def`/`@[expose] public def` anyway, with counts asserted
  identical, so a later per-decl tightening cannot silently blind check 1.


## lean-modules step 1 notes — 2026-08-19

The whole `Linger` lib plus the three roots are `module` files now (blanket `public
section`, imports as `public import`). Total migration friction on ~11k lines of Lean and
370 legacy lemmas: **two `@[expose]` annotations**, both of a kind worth knowing:

* `Checkpoint.R` — a **type-level def**. The compiler cannot agree on compiled
  representations across modules without seeing through it ("locally inferred compilation
  type differs from type that would be inferred in other modules", self-described as a
  current compiler limitation). Rule of thumb: a `def` that returns `Type` gets `@[expose]`
  on migration day; it has no implementation to hide.
* `Vt.applySgr` — its `let rec go` **compiler-generated auxiliary** (`Vt.applySgr.go`) is
  what `Theorems/Render/Pen.lean` inducts on by name, and auxiliaries stay module-private
  unless the parent's body is exposed. 101 `Unknown constant` errors from the legacy proof
  importer, one annotation to fix. Any future `where`/`let rec` whose auxiliary a proof
  names will need the same.

Everything else held with zero edits: every `unfold`/`simp [f]`/`decide`/`native_decide`
in legacy `Theorems/`/`Tests/` still sees the (public) bodies, exactly as the probe
predicted. `coverage.py`'s two census regexes and the statement scanner were hardened to
also match `@[expose]`/`public`/`private` prefixes — necessary already, since `applySgr`
had left the def census — and the exit criterion held: **every gate number is bit-identical
before/after** (coverage 256 defs/18 unclaimed, SHIM 27, runtime partial 2, heartbeats 1),
checked by diffing the captured before/after readings, not by eyeball.


## lean-modules step 2 notes — 2026-08-19

`Buf.bytes` is `private`. The 2026-08-18 open decision ("per-field private — MEASURED, and
the answer is no") is flipped, and both of its killing findings are individually dead:
(a) proofs stayed in `Theorems/Buf.lean` — now the tree's first friend module
(`public import Linger.Core.Buf` + `import all Linger.Core.Buf`) — so `coverage.py`'s
Theorems-only census kept counting (18 unclaimed, cap 19, unchanged); (b) the write hole is
closed, because field privacy makes the anonymous constructor private, so
structure-instance notation can no longer write or forge where it cannot read.

Shape of the seal: `Buf.empty` is the one public door in (`{}` sites in Daemon/Cli/Tests
became `.empty`), `writeFrom` stays the one window out (Posix calls it as API — no
`import all` needed there, the docstring's "one sanctioned read" is now literal). The
three e2e greps stay untouched: they ban a *parallel* runtime queue, which privacy cannot
see.

**Friend-module posture that worked:** no blanket `public section` in `Theorems/Buf.lean`.
Its lemmas are leaves (nothing imports them as terms — checked; every mention elsewhere is
prose), and module-private is ALSO what lets the `:= rfl` proofs elaborate: as `public
theorem`s their term-mode `rfl` was refused ("Not a definitional equality") because a
public statement's proof term elaborates against the exported (body-hidden) view, while the
probe's public-theorem-with-tactic-`by rfl` had sailed. Private theorems elaborate wholly
in the private scope. Rule of thumb: friend modules keep their theorems private unless
something downstream genuinely consumes one.

**A false-green break-verify, caught and worth remembering:** the three attacks (read /
`{ b with }` write / forge) appended to `Daemon.lean` "passed" `./lake build Linger` — but
`lean_lib Linger` builds the import closure of `Linger.lean`, which deliberately imports
Core+Posix only; `Linger/Runtime/**` is reached solely through the `linger` exe target. The
attack file was never compiled. Verified honestly against `./lake build linger` (and with
the attacks *inside* the namespace's `open` scope — parked after the final `end` they fail
on name resolution instead, which proves nothing): all three refuse, the read with
`Unknown constant _private…Buf.bytes`, write and forge with "constructor for `Buf` is
marked as private". **Break-verify against the target that compiles the attacked file.**

Ratchets: coverage 256 defs / 18 unclaimed (`Buf.empty` arrived claimed by
`owed_empty`/`owedLen_empty`); SHIM 27; heartbeats 1; runtime partials 2; e2e greps
unchanged and still green.


## lean-modules harvest — the theorems the seal newly makes TRUE — 2026-08-19

Compound-engineering pass over Step 2: what claims does a sealed `Buf` enable that were
not worth stating before? The test applied to each candidate was the poll-plan standard
(runtime-invariants' recorded kill): a claim whose canonical break is not caught by
anything is decoration.

**Landed: the whole-lifetime §Bound pair.** `ReachableIn cap`/`ReachableOut cap`
(Linger/Core/Buf.lean) are the least predicates containing `Buf.empty` and closed under the
queue's API — the `LiveReachableVt` idiom one layer down — and `reachableIn_bound` /
`reachableOut_bound` (Theorems/Buf.lean) prove any interleaving of capped offers (resp.
not-cut enqueues) and flush advances stays ≤ cap from boot, forever. Both proofs are
three-case inductions over the already-shipped step facts; no new arithmetic. The
constructor carrying `(bufEnqueue …).2 = false` IS the shipped append-then-cut discipline
(a cut client leaves the roster with its queue), so the guard is modeling, not weakening.
No content twins needed at this level: a trace bound composed of twinned steps inherits
the pairing.

**Why these were NOT written pre-seal, recorded so nobody backfills wrong reasons:** with
a public constructor, "reachable from empty" described a strict subset of what the runtime
could hold — any `{ bytes := … }` forge escaped it — so the predicate failed the
decoration test. The seal makes it exhaustive over what a plain importer can possess.
Break 1 demonstrates exactly this: re-admitting a `forge (b) : ReachableIn cap b`
constructor (the pre-seal world, as one line) makes `reachableIn_bound` unprovable
("Alternative `forge` has not been provided" — the induction demands a case no fact can
close). Break 2: dropping the not-cut guard from `ReachableOut.enqueue` refutes
`reachableOut_bound` (the proof's binder for the guard vanishes and `bufEnqueue_bound`
has nothing to eat).

**Cleanup in the same pass** (docs made true rather than aspirational): `Posix.writeBuf`'s
"the one place outside Core that reads a Buf's representation" was a convention — it now
*cannot* read the representation and calls the `writeFrom` window, so the docstring says
so; `Daemon.Conn.out` / `Rt.ptyIn` field docs point at their lifetime bounds; THEOREMS.md
§Bound gained the whole-life sentence.

**Candidates weighed and NOT built, with reasons:**
* A whole-trace FIFO/content characterization (owed = accepted frames minus advanced
  prefix) — real project, and the per-step twins already make each transition
  content-exact; a lifetime bound was the missing kind of claim, a lifetime content
  equation is not (nothing consumes it).
* `bufSize`/`owedLen` or `owed`/`writeFrom` collapse — the name pairs carry roles
  (footprint vs debt; spec vs syscall window), and `bufNoRetain`/`writeFrom_owed` are
  the equations; deleting a name to save a `rfl` is negative cleanup.
* Sealing `Session.State` the same way (boot + step as the only doors; would make
  `run_wf`'s WF hypothesis structural for the daemon) — genuinely attractive, but it is
  a new step, not a harvest: Daemon boots a literal `State`, Resume reads fields, and
  `Tests/Session.lean` forges rosters as test rigging, so it needs the friend-module
  treatment end to end. Noted in specs/lean-modules.md as the natural Step 5 for
  whenever the spec's turn comes back; scrollback-fidelity Step 2 is still queued ahead.


## lean-modules step 5 notes — 2026-08-19

`Session.State` is sealed: `boot` + `step` are the only doors. Field split: `vt`/`labels`/
`metaKv` stay public (exactly the checkpoint save-hook's reads, `Resume.saveCkpt`); the ten
bookkeeping fields WF protects go `private`, which makes the anonymous constructor private —
from the daemon, a field read, a `{ st with dirty := … }`, a `{ st with vt := … }` (public
field! the ctor is the gate) and a forge all refuse to compile, break-verified against the
`linger` exe target per the step-2 lesson. `boot_wf` + `run_boot_wf` land the A2 upgrade:
every state the daemon can possess is WF, given `Good vt` at the door.

**The Bounded-at-boot gap is real and is now closed at the door.** `.labelSet` enforces
`maxLabels` per message, but `Checkpoint.load` is deliberately total on arbitrary bytes and
the boot literal copied the restored label list verbatim — so `Bounded` was FALSE of a daemon
resumed from a forged >64-label checkpoint, and `run_wf`'s protection was vacuous for it.
`State.boot` takes `labels.take maxLabels` (oldest kept — `.labelSet` appends at the end).
Break: removing the `take` refutes the 70-label fixture (Tests/Session.lean:415) AND
`boot_wf`'s labels conjunct — two oracles.

**Module-system facts this step measured, beyond step 5a's:**
* `native_decide` inside a module needs `public meta import X` for every module whose
  compiled code the goal touches — names arrive via `public import`, but compiled code is a
  third scope (the error message says exactly which import to add). Tests/Session carries
  three.
* The friend posture generalizes: Theorems/Session (statements name sealed fields) and
  Tests/Session (fixtures rig rosters) both convert; NO public section in either, which also
  keeps every existing `:= rfl` term proof elaborating in the private scope — zero proof
  edits in the 1000-line theorem file beyond the header.
* The purity gate greps `Theorems/**` for the compiled-evaluation tactic's TOKEN, prose
  included — a docstring naming it fails the gate (correct behavior; a parsing gate would be
  evadable). Cost one fixup commit: pipefail when gating a chain, and don't name the tactic
  in Theorems/ comments.

Ratchets: coverage 257 defs (+`boot`, arriving claimed via `boot_wf`) / 18 unclaimed;
SHIM 27; heartbeats 1; runtime partials 2. Fifteen theorem files migrated in step 5a carry
the general recipe: `import all` every Core module whose bodies the proofs unfold, befriend
the previous rung (`import all Theorems.X` — the ladder is one proof split across files),
and term-`rfl`s under a blanket `public section` become `by rfl` (public statements
elaborate proofs against the exported view; tactic blocks get the private scope).


## pin-the-gaps — the coverage audit and its nine closures — 2026-08-29

`specs/pin-the-gaps.md`. An audit of the whole test+theorem surface, then the
nine gaps it found, closed in one round. Numbering is the audit's and is used in
the spec, the commits and below.

### What the audit measured, so nobody re-derives it

Baseline at `2f16167`: all three gates green; 1467 theorems and 1 lemma in
`Theorems/`, 262 `example`s in `Tests/`; `coverage.py` at 18 unclaimed (cap 19).
Structural checks that came back **clean** and are not worth re-running blind:

* Every `Theorems/*.lean` (13) and `Tests/*.lean` (10) is imported by its root.
* The Render ladder is one unbroken chain — Ends → Quiet → Pen → Keeps → Modes →
  Sticky → History → Row → Grid → Tabs → Scrollback — and the façade imports the
  last rung, so no rung is silently uncompiled.
* **THEOREMS.md cites 156 theorem-shaped names; 153 resolve.** The three that do
  not (`restore_sb_any`, `scrollbackAnsi_le`, and the `frame_print` /
  `frame_csiDispatch` pair) are each explicitly marked in the ledger as not yet
  existing or as recorded failures. No unbacked promises. Script: extract
  backticked snake_case identifiers, resolve against every declaration in
  `Theorems/` + `Linger/`; the false-positive class is env vars, tactic names and
  C constants (`LINGER_DIR`, `decreasing_by`, `O_EXCL`, `SHIM_CAP`).
* Ratchet headroom: `SHIM_CAP` 27/27, `HEARTBEAT_CAP` 1/1,
  `RUNTIME_PARTIAL_CAP` 2/2 — all exact. `STATEMENT_CAP` was the only loose one.

Two audit findings that are **not** defects and should not be "fixed":
`tests/remote_live_test.py` is documented in its own docstring as out of the gate
(it needs a real second host); `procs.py` is a helper, not a suite.

### The finding that redirected item 1: read-only is enforced daemon-side

`Client.attach`'s three `!readOnly` guards look like the mechanism for
`linger watch` and are not. The mechanism is `sizer := cols != 0 && rows != 0`
(`Session.lean` `.attach`) plus `onMsg .input`'s `if c.attached && !c.sizer`,
already proved by `onMsg_input_readonly`. Consequence, measured by break-verify:

| guard | what it does | observable? |
|---|---|---|
| A `sendMsg fd (.attach 0 0)` | the wire's only read-only bit | **yes, 3 ways** |
| B `if size != lastSize && !readOnly` | suppresses the observer's resize | **no** — `onMsg .resize` drops a non-sizer's anyway |
| C `if !out.isEmpty && !readOnly` | suppresses the observer's keys | **no** — `onMsg .input` drops them anyway |

So a pty test can only bite A, and B/C got grep gates in `e2e.sh` (the `SHIM_CAP`
species). **Do not write a pty assertion claiming to catch B or C.** Removing
guard A fails exactly three `watch_test.py` assertions (geometry at attach, the
mid-watch resize, and `linger resize` being refused because the watcher became
the size owner) — verified.

Also found and now pinned: **`linger watch` marks the session seen.**
`onMsg .attach` sets `lookSeq := s.outSeq` for *any* attach, `0×0` included, so
the read-only verb has one write effect. `status_test.py` only ever exercised
that through `attach`.

### Break-verify records (all eight intended breaks fired)

Theorem/fixture breaks, each reverted after:

1. `isWide` emoji clause `0x1F300`→`0x1F301` → `isWide_emoji` fails.
2. Drop the `c == 0x200C` singleton → `isZeroWidth_joiners` fails.
3. `isWide` Hangul-Jamo `lo` `0x1100`→`0x0100` → `isWide_low` fails (it is tight:
   `0x1100` *is* the table's minimum `lo`).
4. Overlap the tables at `0xFE2F` → `zeroWidth_not_wide` fails.
5. `.detachAll` drops its `.attached` filter → `onMsg_detachAll` fails.
6. `.labelUnset` clears the whole store → `onMsg_labelUnset` fails.
7. `.labelClear` becomes a no-op → `onMsg_labelClear` fails.

Gate breaks:

8. Guard A removed → 3 `watch_test.py` assertions fail. Guards B and C removed →
   the two new greps fire. One throwaway unclaimed def in `Linger/Core` →
   `coverage.py` fails (17 > cap 16), i.e. the cap now has zero headroom. One
   assertion in `status_test.py` wrapped in `if False:` → the check-count floor
   catches it (4 < 5) **while the suite still prints `FAILURES: 0`** — which is
   the whole reason item 7 exists, demonstrated rather than argued.

### NEGATIVE RESULT — `charWidth`'s branch order cannot be pinned by anything

Break 5 of the first batch was "swap `charWidth`'s two `if`s" and **nothing
caught it, correctly**: `zeroWidth_not_wide` proves the tables are disjoint, so at
most one branch can ever fire and the order cannot change any value. It is a
readability choice, not a decision. This kills a shape that looks attractive —
`charWidth c = 2 ↔ (isZeroWidth … = false ∧ isWide … = true)` — which appears to
pin the order and pins nothing; both such theorems were weighed and declined,
because landing them *instead of* the edge pins would drop the ratchet by 2 while
claiming no range content. Recorded in the `Theorems/Vt.lean` section docstring.

### Two more things no oracle can see (recorded, not pretended)

* **The wide table's two seams.** `0x3041-0x33FF ∪ 0x3400-0x4DBF` and
  `0x4E00-0x9FFF ∪ 0xA000-0xA4CF` are each one contiguous run written as two
  clauses. Moving a split point in *both* clauses changes no value. Pinned as
  `true` on both sides of each seam, which catches a one-sided shrink (it opens a
  gap) but never an overlap.
* **The `0x200B/0x200C/0x200D` cluster** is three mutually adjacent singletons, so
  no neighbour probe detects the loss of any one. Each is pinned individually;
  `0x200A` and `0x200E` are the cluster's only outside probes.

### Traps hit while doing this

* **The purity grep reads prose — again.** Writing "no `native_decide`" in a
  `Theorems/Vt.lean` docstring failed `e2e.sh` step 2 exactly as the step-5a fixup
  (`fb6a0e6`) recorded. The docstring now says "compiled evaluation" and warns the
  next writer inside the sentence itself. Cost: one full e2e run.
* **`^(PASS|FAIL)` also matches `FAILURES: 0`.** The first check-count measurement
  was uniformly one too high. The floors use `^(PASS|FAIL) ` with the space.
* **Structure-instance parsing.** `{ s with labels := s.labels.filter (·.1 != …) }`
  with the `·` lambda on a continuation line does not parse; an explicit
  `fun kv => …` does. Not a privacy or module problem, just layout.
* `List.of_mem_filter` does not exist on v4.32 — `List.mem_filter.mp/.mpr` plus
  `bne_iff_ne` is the idiom, and the `Bool`-vs-`Prop` gap at `!=` needs it in both
  directions.

### Compound-engineering pass (three duplications removed, one of them mine)

* **`Session.labelText`** — `.labelSet` and `.labelUnset` each open-coded
  `String.fromUTF8? (ByteArray.mk … .toArray) |>.getD ""`. Now one Core def, so
  the two arms cannot drift about what a key *is* (a `.labelSet` that decoded
  differently would leave a label no `unset` could reach). Census 258 → 259;
  unclaimed stayed 16 because the new theorems name it in their statements.
  `rfl` reduces through it unchanged.
* **`Tests/Vt.lean` `widthProbes`** — the 38 boundary codepoints were duplicated
  between the claim and its non-vacuity check. One `def`, two consumers; a
  corrected probe can no longer be fixed in one copy and not the other.
* **`tests/harness.py`** — writing `watch_test.py` meant copy-pasting a tenth set
  of `LINGER`/`ENV`/`drain`/`expect`/`linger`/`info`/`field`. Extracted instead
  (`procs.py` is the precedent for a shared test module), which also let `spawn`
  fix a race every copy had: `pty.fork()` then `ioctl(TIOCSWINSZ)` sets the size
  *after* the child may have read it, which is invisible until a test's subject IS
  the reported geometry. `watch_test.py` is 131 lines instead of ~200.
  **The nine older suites still carry their copies, deliberately** — porting them
  is a ten-file diff across a green gate and belongs in its own commit, not folded
  into this spec's step (AGENTS.md, one item in flight). It is now cheap *and*
  safe, because the check-count floors mean a port that silently drops an
  assertion fails the gate.

### `e2e.sh` shape change

Nine copy-pasted three-line suite invocations became one `suite <name> <floor>`
function and ten one-line calls — net fewer lines, and the floors live next to
`SHIM_CAP` where the other ratchets are read. Measured floors (live counts):
attach 35, resume 9, overview 7, remote 11, robust 14, graphics 9,
terminal_query 12, status 5, agent 24, watch 17.

### Where the numbers ended

`coverage.py`: `core defs 259; named by no theorem STATEMENT: 16 (cap 16)` —
zero headroom, matching every other ratchet. Remaining unclaimed, with the reason
each is still fine: `ckptIntervalMs` `maxClients` `maxLen` `csiCap` `dcsCap`
`oscCap` (constants a claim would restate), `clampDim` `feedBytes` `color256`
`decLine` `sgrParams` `knownTag` `writeU32` `firstDupHost` `parseRecord`
`records` (helpers whose composites are claimed). `clampDim` is the one worth a
future look: the runtime calls it on the `linger resize` path and no theorem
names it.
