# runtime-invariants — the daemon's byte queues as data, proved, and gated

Status: active
Updated: 2026-08-18
Predecessor: `specs/ledger-cleanup.md` (complete; its item 2 landed the `ptyIn`
cap and the twin partial-drain compaction that this spec turns into theorems).

## Where this stands — read this first

**Next step:** nothing required. Steps 1 and 2 are done — the value increment has
landed, so if Steps 3-4 never happen this bet has delivered what it honestly could.
Two follow-ups are parked, both small: apply the `THEOREMS.md` §Bound/§Total
rewrites (drafted in `/tmp/theorems-bound.md` during step 2, held back only because
another agent held that file), and revisit per-field `private` on `Buf.bytes` if
`E2E/Coverage.lean` is ever taught to count theorems in `Linger/Core` — see the
measured negative result in SCRATCHPAD 2026-08-18.

**Done (2026-08-18):** Step 1 (five vestigial `partial def`s dropped; `pump` and
`parseLs` remain, each for a stated reason) and Step 2 (`Linger/Core/Buf.lean`,
`Theorems/Buf.lean`'s nine theorems with their content twins, `Tests/Buf.lean`'s
fixtures, the three-grep gate, and `Cli.queryInfo`'s live unbounded accumulator
closed). **Step 2 diverged from the design below**: `Buf` has no write cursor, because
`bufOffer_owed` needed an `off ≤ bytes.size` invariant no type enforced — so the
definition moved and the partial-drain leak became unrepresentable rather than fixed.
`bufCompact` and its two theorems therefore do not exist; `bufNoRetain` replaces them.
Details and the four break records in SCRATCHPAD 2026-08-18.

**What this spec deliberately does NOT build:** a pure poll plan / `revents`
classifier. See "## Settled non-goal for this spec" below. The negative result
goes in `SCRATCHPAD.md` in the same round as Step 1, so the next agent does not
re-propose it.

## Goal

`Session.step` is the session's brain and the daemon executes its effects. One
layer below that, the daemon still owns the **byte bookkeeping**: two long-lived
queues, their caps, their drop and cut policies, and the compaction that keeps
the cap measuring memory rather than a counter. Those are decisions dressed as
plumbing, and they are the runtime half of §Bound, which `THEOREMS.md:524-531`
currently ends with "These caps live in `Linger/Runtime/Daemon.lean` and are not
proved (the runtime is `IO`)."

Move the *value* into `Linger/Core/Buf.lean`, prove the caps and the compaction, and
gate — with a grep, because a source-tree property cannot be a theorem — that
`Linger/Runtime/*` declares no byte buffer of its own.

**Correct framing, because both drafts got this wrong in opposite directions.**
The partial-drain leak is **already fixed**: `flushConn` (`Linger/Runtime/Daemon.lean:79-88`)
and `flushPty` (`:90-101`) both compact on partial writes today, with the reason
in `flushConn`'s docstring, and `queuePty` (`:111-118`) caps at `ptyInCap`. So this
spec is not a bug fix. Its value is that the fix's **only live oracle was measured
and rejected as noisy** (`SCRATCHPAD.md`, 2026-08-18: RSS-after-flood is dominated
by transient decode garbage, so it is not asserted); the asserted property is a log
line about something else. `bufCompact_size`/`bufCompact_owed` are sharp oracles
for exactly that regression, and they reduce in the kernel. That is a strict
evidence upgrade, which is the one argument in the packet that survived
adversarial review.

## Definition of done

1. `Linger/Core/Buf.lean`: `Buf` = `bytes : ByteArray` + `off : Nat`, with the six
   named stages `owed` (spec-only, copies), `owedLen` (what the caps measure),
   `bufOffer` (drop the newest **whole** frame — the child-input discipline),
   `bufEnqueue` (append and report "cut this peer" — the client discipline),
   `bufAdvance` (`min`-clamped), `bufCompact` (on **every** flush). Two enqueue
   functions, not one: the shipped disciplines genuinely differ (`queuePty`
   measures before appending, `Daemon.lean:113`; `.send` appends then measures,
   `:129-130`), and one shared function forces a theorem that is *false* of the
   client path as shipped.
2. `Theorems/Buf.lean`, nine theorems, each with its **anti-vacuity twin in the
   same commit**: `owedLen_eq` (the bridge between the cheap number and the
   content — without it every bound below is about an unrelated `Nat`),
   `bufAdvance_wf`, `bufAdvance_owed`, `bufCompact_owed` (**the anti-vacuity
   theorem**: without it, `bufCompact b = {}` satisfies every size bound),
   `bufCompact_off`, `bufCompact_size`, `bufOffer_bound`, `bufOffer_owed`,
   `bufEnqueue_bound`. `bufEnqueue_bound`'s hypothesis-guarded form (`.2 = false →
   owedLen ≤ cap`) is deliberate: the honest bound for the shipped
   append-then-cut discipline is `≤ cap + one wire frame` (`outputChunk = 65536`).
3. **The gate** — three greps in `tests/e2e.sh` §2, after the `SHIM_CAP` block,
   asserting that `Linger/Runtime/*` declares no `ByteArray` structure field, no
   `mut … : ByteArray` local, and calls no `.extract`. This is the item the
   adversary's finding makes non-negotiable: `Linger/Runtime/*` is `IO`, so no
   theorem can see that it calls the proved functions, and without the gate the
   theorems are arithmetic about a value nothing forces the daemon to use. It is
   the same species of oracle as `SHIM_CAP` and `E2E/Coverage.lean`'s ratchet — evadeable
   by deliberately writing something new, not by reverting.
4. The gate **fails on `HEAD`** before the work and passes after. It currently
   has three hits: `Conn.out` (`Daemon.lean:41`), `Rt.ptyIn` (`:51`), and
   `Cli.queryInfo`'s `let mut acc : ByteArray := .empty` (`Linger/Runtime/Cli.lean:122`,
   appended at `:136`). A new gate that passes before the work measures nothing.
5. `Cli.queryInfo`'s accumulator is bounded. This is a **live unbounded
   accumulation**, verified: the loop's only exits are `.done`/`.err`/EOF/a 2000 ms
   *silence* timeout, so a peer that streams `infoReply` frames steadily never
   ends it. Same class as the `ptyIn` bug ledger item 3 closed, on the client
   side. Low severity (`linger ls` is short-lived) but the gate's first act is to
   close it, which is the shape you want in a new gate.
6. Five of the seven runtime `partial def`s removed: `pollRound`, `serve`
   (`Daemon.lean:178,250`), `drainReplies`, `attach` (`Client.lean:37,120`),
   `queryInfo` (`Cli.lean:116`). `while`/`for` in `do` does not force `partial`
   (`flushConn` at `:79` already proves it). Optionally a ratchet in `e2e.sh` so
   they cannot creep back. `parseLs` (`Cli.lean:245`) needs a `decreasing_by` the
   adversary did not land; `pump` (`Daemon.lean:164`) resists genuinely and stays
   `partial` unless Step 4 lands. **Do not add a fuel parameter** — it converts a
   hang into a silent drop.
7. `THEOREMS.md` §Bound rewritten to state exactly what is proved and what the
   grep carries, in that order, and no wider: "What is proved is the arithmetic,
   not the daemon; `Linger/Runtime/*` is `IO` and no theorem can see that it calls
   these functions; `tests/e2e.sh` gates that it declares no byte buffer of its
   own, which is a source-tree property and therefore a grep." Anyone who writes
   "the runtime is proved" — including in a commit message — is overclaiming.
8. `python3 E2E/Coverage.lean` still reports its two counts (the cap is 16 as of pin-the-gaps item 6, and is exact). Use the distinct base
   names above and **not** `push`/`size`/`pending`/`classify`: the gate strips
   namespaces (``E2E/Coverage.lean`'s base-name normalisation`), so a `Buf.push` would be silently auto-claimed
   by `Ring.push` and add surface with no claim. Consider fixing that hole, but in
   its own commit — it shakes a ratchet.
9. `./tests/e2e.sh` green and warning-free, including `E2E/Robust.lean`'s
   exactly-once backpressure-log assertion (`:138`) and the pending-within-cap
   assertion (`:136-137`, which parses the number out of the log string at `:129`
   — the format is a test oracle, keep it and print the **pre-push** pending).
   Every theorem and the gate break-verified, with the breaks in `SCRATCHPAD.md`.
10. `SHIM_CAP=27` unchanged (`grep -c LEAN_EXPORT c/shim.c` reads the same number
    before and after) — `writeBuf` is a Lean-level wrapper over the existing
    `linger_write` extern, and `e2e.sh:52` only requires `@[extern` to stay inside
    `Linger/Posix.lean`.

## Settled non-goal for this spec — the poll plan

A pure `pollPlan : Rt → Plan` plus `classify : Plan → Array UInt32 → List Intent`
buys `plan.fds.length = plan.masks.length` and "no out-of-range index". The
premise that made the desync a desync — *`revents[i]` is the readiness of
`fds[i]`* — is established by the C loop in `c/shim.c` (length mismatch is an `IO`
error, `lean_alloc_array(n, n)`, `out[i] = pfds[i].revents`) and is not a
Lean-visible fact. Break-verify the alignment theorem and you find it: **permute
the slot order in `pollPlan` and the length equation still holds.** A claim whose
canonical break does not catch its canonical bug is decoration.

Three further reasons: the bug class is already retired structurally by the
`polled` snapshot (`Daemon.lean:181`, with `AGENTS.md`'s "any poll loop must
freeze its fd set"); the residual failure is already caught loudly in C; and the
hard part refuses to leave `IO` — `pollRound`'s client loop is a *state-dependent
reaction sequence*, not a classification (`:226` skips a conn an earlier
iteration's close dropped, and `:236` re-checks after a POLLOUT-triggered close),
so a pure `List Intent` must be re-validated against live state between every
intent, which is the code you already have. The daemon's defect history supports
this: `git log -- Linger/Runtime/Daemon.lean` is 6 commits, 2 of them fixes, and the
desync happened **once**, pre-release.

Record this in `SCRATCHPAD.md` as a negative result, with the permutation break
spelled out. Re-opening it needs a new reason, not a fresh pair of eyes.

## Steps

### Step 1 — the vestigial `partial def`s

Status: **done** (2026-08-18).

Delete `partial` from the five functions in Definition-of-done item 6.
`lakefile.lean` states the reason for banning `partial def` ("it hides a
termination argument we would rather be forced to write down") and the runtime is
currently violating it for no reason in five of seven places. The adversary
verified these compile in a full copy at `/tmp/lzb`; **re-verify in this tree
before committing** — I did not run it here.

**Exit:** `./lake build` and `./tests/e2e.sh` green and warning-free; the
`partial def` count in `Linger/Runtime/*` is 2 (`pump`, `parseLs`) with the reason
for each in a comment; `THEOREMS.md:520-523` amended to say which loops remain
and why.

### Step 2 — `Buf`, its theorems, and the gate

Status: **done** (2026-08-18), with the no-write-cursor divergence recorded above.
**The value increment: if everything after this slips, the bet has delivered what it
honestly could.**

`Linger/Core/Buf.lean` (~70 lines), `Theorems/Buf.lean` (~150), `Tests/Buf.lean`
(~20, `native_decide` allowed), `Linger/Posix.lean` +4 (`writeBuf fd b := write fd
b.bytes (USize.ofNat b.off)` — the only place outside Core that reads a `Buf`'s
representation), `Daemon.lean` ~45 lines changed (`Conn.off` disappears into the
`Buf`; `Rt` loses `ptyIn`/`ptyInOff`), `Cli.lean` ~10, `e2e.sh` +8, plus the
`THEOREMS.md` §Bound rewrite and a `SCRATCHPAD.md` entry with six break records.

`ByteArray` in `Linger/Core/` is house-legal (`e2e.sh:41-50` bans `sorry`,
`sorryAx`, `partial def` and `: IO ` only) and has precedent (`Vt.feedBytes`,
`Linger/Core/Vt.lean:946`). Lean 4.32 core carries a usable lemma set in
`Init/Data/ByteArray/Lemmas.lean` (`size_append`, `size_extract`,
`extract_zero_size`, `extract_extract`, `extract_eq_empty_iff`, most `@[simp]`).
Do **not** state anything through `ByteArray.toList` — it is a `get!` + `reverse`
loop. If a reviewer asks for `List UInt8` uniformity with the rest of Core,
refuse: a 4 MiB `List UInt8` is ~48 bytes per byte and `++` is O(left), so every
`.send` becomes a multi-megabyte cons walk. Put that in the module header so it is
not re-litigated.

Preserve, exactly: `flushConn`'s two-branch reaction (`n < 0` → peer gone → close
+ `.closed` back into the machine; `n == 0` → EAGAIN → `break`, POLLOUT resumes)
versus `flushPty`'s collapse of both to `break` (a dead child surfaces as `read`
returning `none` → `.childExited`, and there is nothing to disconnect). Share the
bookkeeping, **not** the loop — a shared `flushInto` invites "fixing" that
asymmetry, which would either drop the pty queue on a transient or leave a dead
client's frames queued. Compact exactly **once**, after the loop, in both.
`bufAdvance` must not clear the `full` flag on a partial drain: ``E2E/Robust.lean`'s exactly-once backpressure assertion`
asserts the backpressure line appears exactly once, and re-arming the log fails it.

**Exit:** three build gates green and warning-free; `E2E/Coverage.lean` at 20/20 with
the distinct base names; the gate fails on `HEAD` and passes after; the gate
break-verified twice (add `dummy : ByteArray` to `Conn`; re-add an `.extract` in
`Linger/Runtime/`); `bufCompact := id` fails `bufCompact_size`/`_off` and the
`native_decide` fixture **while `./lake build Theorems Tests` would have stayed
green today** — record that contrast, it is the entire justification for the bet;
`bufCompact := fun _ => {}` passes every bound and fails only `bufCompact_owed`;
`owedLen b := b.bytes.size` fails `owedLen_eq`; deleting `bufOffer`'s guard fails
both the theorem and `robust_test`'s three log assertions (two independent
oracles, one pre-existing). Record that `bufEnqueue_bound`'s *first* candidate
break (measure-before, report-after) **fails to catch** — the note is worth more
than the theorem.

### Step 3 — optional: the roster as pure data

Status: pending, off critical path.

`Linger/Core/Loop.lean` part A only: `Conn`/`Loop` (fds as `Nat`, matching
`Session.Event.connected`), `conn?`/`setConn`/`dropConn`/`addConn`, the two cap
policies, `Op`/`step`/`run`, `WF`, `run_wf` and `loop_run_bounded` — the exact
shape of `Session.run_wf` (`Theorems/Session.lean:645-656`), one level down. Value:
§Bound over a whole *trace* (any interleaving of queues, partial writes, accepts
and cuts), plus `setConn_other` as §Isolate at the transport layer.

**Kill criterion for this step specifically:** if `Rt` ends up holding both `lp`
and shadow copies of anything in it, stop and revert — a second copy of the
roster is the drift hazard this was meant to remove. Also do **not** drag
`childPid`/`sockPath`/`exiting`/`saveCkpt`/`dropCkpt` into Core: they carry no
claim and would each cost a naming theorem for nothing.

**Exit:** gates green; `queueSend` returning `some (setConn …)` unconditionally
must fail `wf_queueSend`; dropping `setConn`'s `if c'.fd == c.fd` guard must fail
`setConn_other`.

### Step 4 — optional: `pump` without `partial`

Status: pending, off critical path. Judge with Steps 1-3 in front of you; be
willing to drop it.

Two fixed drain passes, which is **byte-for-byte today's schedule**: `runEffect`
returns a non-empty event list only from `.send`, twice, both immediately after
`rt.dropConn` (`Daemon.lean:133,137`), always `.closed`; `Theorems/Session.lean:43-46`
`step_closed` already proves a `.closed` step emits only `.checkpoint`; and
`runEffect .checkpoint` returns `(rt, [])` (`:153-155`). Follow-ups were already
appended at the **tail** of the queue (`:174`), so the order is unchanged. Add
`Effect.feedbackFree` in `Linger/Core/Session.lean` and
`step_closed_feedbackFree` so the runtime's comment cites a theorem instead of a
reading of an `IO` file, and keep an `IO.eprintln "BUG —"` alarm for the day a
future effect gains a feedback event.

**Exit:** gates green; the alarm's absence asserted in a live suite (`resume_test`
guarantees a checkpoint at the detach save point) — an alarm nobody hears is not a
mitigation. Break both halves: make `step`'s `.closed` branch emit `.send id
.done` (an already-shipped theorem catches it) and make `runEffect .checkpoint`
return an event (the log assertion catches it).

## Open decisions

1. **Can the gate become a type discipline?** If Lean 4.32 supports per-field
   `private` on a structure, making `Buf.bytes` unreachable outside
   `Linger.Core.Buf` (with `Posix.writeBuf` taking the whole `Buf`) upgrades the gate
   from grep to compiler-enforced and demotes the three greps to belt-and-braces.
   **Test this first — it is a ten-minute experiment that could change the
   design's strength materially.** Unverified.
2. **The `.send` cap discipline.** Keeping append-then-cut forces the honest bound
   `≤ outbufCap + 65536 + header`; switching to refuse-then-cut gives the clean
   `≤ outbufCap` but changes *when* a slow client is disconnected. My
   recommendation is to keep today's behaviour and state the bound in its
   hypothesis-guarded form. Decide **before** writing `bufEnqueue_bound`. If the
   clean bound is preferred, it is a behaviour change and belongs in the
   Definition of done, not smuggled in as a proof convenience.
3. **Append cost is unchanged, and someone will claim otherwise.** A `Buf` reached
   from `rt.conns` has refcount ≥ 2, so `bytes ++ more` copies — exactly as
   `{ c with out := c.out ++ bytes }` does today. This bet is performance-neutral.
   If `robust_test`'s 16 MiB flood looks slow, that copy was there before and
   after; do not "fix" it inside this bet.
4. **`POLLNVAL` is decoded by nobody, today or here.** No path appears to reach it
   (every `close` is paired with a `dropConn`). If anyone adds it: do **not** map
   it to a read — `linger_read` on `EBADF` raises, which would kill `serve`.
5. **`parseLs` is pure argument-parsing logic living in `Linger/Runtime/`** with no
   theorem. If someone wants a genuinely misplaced decision moved into Core, that
   is a better candidate than the poll plan.

## Kill criteria and fallback (from the design review)

**Bet A — kill criteria.**

*Step 1 (the emitter).* Kill if **either**: (a) `restore_grid_any` /
`restore_grid_reachable` / `resume_grid` cannot be made green without adding a
hypothesis or weakening a statement — the temptation will be to add something
about `v.sb`, and `fitRow`'s unconditional `rowOk_fitRow` exists precisely so that
is never necessary; if it still is, the definition is wrong, not the theorem; or
(b) the `MMap`-across-glyphs obstacle turns out to be unavoidable *and* the twelve
bytes of mode re-establishment do not clear it — i.e. `scrollback_entry`'s modes
conjunct will not close. Run the experiment either way: drop
`csiNum 4 0x6C ++ modeSet 6 false ++ modeSet 7 true` from `scrollbackAnsi` and
confirm the modes obligation fails. **If it still closes, `mmap_id_gridAnsi` is
reachable after all and the stage should shed those bytes.**
*Fallback that still ships:* `linger scrollback` / `linger history --color` — wire
up `Render.history`'s existing-but-dead `withAnsi` branch
(`Linger/Core/Render.lean:548-558`; the only call site is `Session.lean:250` at
`false`, and `history_framing`/`history_lines` are both stated at `false`) behind
a CLI flag with its own framing theorem. The user gets coloured history on demand,
no `ED 3`, no destruction of their own scrollback, no touch to `restore`. Strictly
smaller than the goal, but it is a shipped capability and it deletes unproved dead
code either way.

*Steps 2-4 (the ladder).* Kill Step 3 if `push_walk` blows past ~4,000,000
heartbeats, **or** if its scroll branch needs a hypothesis the bundle does not
carry — per house doctrine that means the *bundle* is wrong, so try the flat
structure once before declaring. Do **not** buy a `rows ≥ 2` restriction to make it
go: commit `8dc61a4` fought to remove exactly that, and re-introducing it for a
new claim would make two neighbouring theorems disagree about which heights they
cover.
*Fallback that still ships:* Step 1 and Step 2 already stand. Step 1 leaves the
capability shipped with a decidable oracle — `replayEq` on `sb`, the `dirtySb`
receiver, the byte fixtures, two pty assertions, a strengthened `resume_test` —
which fails the build the moment any of it regresses. That is the same posture
`Tests/Render.lean`'s header documents for the grid before stage 3d landed, and it
is a defensible place to stop. Step 2 stands entirely alone as §Replay's positive
scroll specification, closing the gap `THEOREMS.md:358-361` names. Then A5's
inbound list reads "history: repainted and fixture-carried; the receiver-quantified
claim is future work with the scroll spec already in hand", and
`specs/scrollback-fidelity.md` records `push_walk` as the single blocking rung with
the *measured* reason it stalled.

*The kill criterion nobody will remember to check:* if the product decision on
`ED 3` goes the other way — the user decides discarding their own terminal
scrollback on every attach is unacceptable — Step 1's emitter is dead as designed,
because without `ED 3` a second attach stacks a second copy of the ring. The
fallback is the same `linger scrollback` command. Get that decision before writing
`scrollbackAnsi`, not after the pty test.

**Bet B — kill criteria.**

*Step 1.* Cannot fail; the compile was already demonstrated. If a function turns
out to need `partial` after all, leave it and put the reason in a comment — that is
the outcome `lakefile.lean` asks for.

*Step 2 (`Buf` + the gate).* Kill if the gate cannot be made to pass without
hollowing it out — specifically, if bounding `Cli.queryInfo` through `Buf` turns
into a rewrite of the reply loop, or if the whole-`Linger/Runtime` scope turns up a
fourth long-lived buffer that does not fit the `Buf` shape. Do **not** narrow the
gate's scope to `Daemon.lean` to make it pass: that leaves `Cli.lean:122`'s
unbounded accumulator alive and puts the next buffer in `Client.lean` where the
gate is not looking, which is a gate measuring nothing.
Also kill if the answer to "does this theorem bite the shipped code?" comes out
honestly *no* — i.e. if the grep turns out to be evadeable by ordinary refactoring
rather than by deliberately writing something novel. The `SHIM_CAP` and
`E2E/Coverage.lean` precedents say it is not, and ``E2E/Coverage.lean`'s runtime-emitter scan` already scans
`Linger/**`, so there is precedent for a Runtime-side gate — but check, don't assume.
*Fallback that still ships:* Step 1, plus `Buf` and `Theorems/Buf.lean` **without**
the runtime rewiring — a proved, claimed, unreferenced Core module is not much, so
prefer instead: keep the two `Daemon.lean` buffers on `Buf` (the rewiring is 45
lines and closes the sharp-oracle gap for the compaction fix) and drop only the
`Cli.lean` conversion and the `.extract` grep, shipping the two *structural* greps
(no `ByteArray` field, no `mut ByteArray` local) with `Cli.lean`'s accumulator
tracked as a separate one-line item. That keeps the ratchet real and the diff
honest.

*Steps 3-4 (roster, two-pass `pump`).* Both are already optional. Kill Step 3 the
moment `Rt` holds a shadow copy of anything in `Loop`; kill Step 4 if the
`IO.eprintln "BUG —"` alarm cannot be asserted-absent in a live suite, because an
alarm nobody hears is not a mitigation and the two-pass schedule then rests
entirely on a reading of an `IO` file with no gate.
*Fallback:* leave `pump` `partial` with a comment citing `step_closed`. That is the
honest state and it costs nothing.
