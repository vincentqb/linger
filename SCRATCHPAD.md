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
