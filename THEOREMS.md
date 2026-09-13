# Theorems — the tension ledger

Read this file at whichever depth you need:

* **The anchor set** (below) — four theorems that carry the product's
  promises. If you only ever read four statements, read these.
* **The rungs** (the § table) — the port's tensions and the
  invariant that resolves each. These are what the anchors are built
  from; a section is listed before its first proof so an open tension is
  on the record.
* The prose sections after that — what the theorems *don't* settle, where
  the model stops, and the two places a guarantee rests on the kernel
  rather than on a proof.

## The anchor set

| Anchor | Statement | Theorem |
|---|---|---|
| **A1. A session survives a crash** | a checkpoint round-trips exactly, and the byte stream rebuilt from it leaves the terminal quiesced — parser in `ground`, no half-decoded character — for **any** receiver, not just a fresh one. Any session state, no hypotheses. The **cursor** lands where the session had it (given the §Bound invariant and DECOM off) | `Resume.resume_quiesced_any` (§Restore ∘ §Replay; `resume_quiesced` is the fresh-`Vt.init` form), `Resume.resume_cursor` |
| **A2. The daemon cannot be broken by traffic** | no event trace of any length — adversarial clients, hostile pty bytes, any interleaving — breaks a buffer cap, the screen invariant, or one client's isolation from another. **Structural since the `State` seal** (specs/archive/lean-modules.md Step 5): the constructor is private and `State.boot` caps restored labels, so `run_boot_wf` covers every state the daemon can *possess*, not just the traces it politely runs — the runtime cannot read, poke or forge the bookkeeping (break-verified from inside the daemon, a public-field `{ st with … }` included), and a forged checkpoint's label list can no longer boot past `maxLabels` (the Bounded-at-boot gap, found by sizing the seal and closed at the door) | `Session.run_wf`, `Session.run_bytes_isolates` (§Bound ∘ §Total ∘ §Isolate), `Session.boot_wf` / `Session.run_boot_wf` (the door) |
| **A3. The transport is invisible** | any re-chunking of any well-formed encoded stream decodes to exactly that stream: same messages, same order, nothing retained, no error | `Wire.decode_encode_chunked` (§Stream = §Frame ∘ §Chunk) |
| **A4. A session name has one owner** | given the kernel grants at most one `flock` holder, at most one daemon ever unlinks or binds a given name | `Claim.at_most_one_owner` (§Claim) |
| **A5. linger is invisible to the terminal it borrows** | whatever state a client's terminal is in, the restore stream establishes what the repaint needs; whatever state the session's program left, the hand-back returns the terminal to a state the next program can use. Both quantified over the receiver, with no hypothesis on it | **inbound (modes): `Render.restore_modes_any` ✓** — for any `v`, `w`, `(w.feed (restore v)).modes = v.modes` (given `v.modes.mouse` in the emulator's allowlist, which `setMode` guarantees); parser half `restore_grounds` ✓. **outbound: `Render.leave_canonical_all` ✓** — for any receiver at least two rows tall, `w.feed leaveAnsi` leaves the parser `ground`, the modes at the default record, the scroll region whole, both charsets ASCII with G0 shifted in, the main screen current and the pen reset (`leave_canonical` is the parser+modes half, kept as the hypothesis-free statement). **inbound pen ✓** — `restore_pen_any`, via `penSgr_feed` + the pen-projection CSI walk. **inbound sticky fields ✓** — `Render.restore_sticky_any` installs the session's scroll region, both charset designations, the shift state and the screen selection into any receiver of the same height (`restore_region_any`, `restore_charset_any`, `restore_alt_any` are its projections); the two hypotheses are `Good v` and `v.top < v.bot`, the region `DECSTBM` accepts. **inbound screen cells ✓** (2026-08-18) — `Render.restore_grid_any` (dispatching on `v.altGrid`), `Render.restore_grid_reachable` and `Resume.resume_grid` — both screens, **every height** (the one-row corner included, via `Good w` in `prologue_sticky`; no `rows ≥ 2` hypothesis): feeding `restore v` to any **live-reachable** client of the session's dimensions leaves its grid equal to `v.grid`, array for array and cell for cell. Main screen via the row painter (`rowAnsi_writes_row`), the grid walk (`paint_rows`, whose no-scroll argument is `crlf_step` plus `joinCRLF`'s missing trailing separator), `gridAnsi_writes_grid` and `paint_entry`; alt screen (`restore_grid_any_alt`) via `alt_pre_switch` (the entry state survives the discarded main paint and the park), `alt_switch_entry` and a second `gridAnsi_writes_grid'`. The receiver's `Good`/`Renderable`/decoder invariants are discharged from reachability, not assumed — including `U8Ok` (`u8need = 0 → u8acc = 0`), which `Good` does not carry and which the multi-byte-glyph decode needs. A receiver **mid-character** is covered too (2026-09-11): `u8need = 0` used to be a hypothesis and is not one, because `restore` opens with `ESC` and `abortUtf8` discards the pending sequence (`restore_cons`, `abort_esc`, `feed_restore_zeroed`) — reachability could not have supplied it, since `((Vt.init 80 24).feed [0xC3]).u8need = 1`. **inbound tab ruler ✓** (2026-08-18) — `Render.restore_tabs_any` / `restore_tabs_reachable` / `Resume.resume_tabs`: for any receiver of the session's width, `(w.feed (restore v)).tabs = v.tabs`, array for array. The clear (`tbc3_clears`, `TBC 3`) asks only `pstate = ground` of the receiver — the leading `ESC` aborts a half-decoded character itself, so unlike the grid this claim needs no `U8Ok` apparatus at all (the grid's `u8need` hypothesis is gone as of 2026-09-11 for the same reason, but its `U8Ok` remains — `abortUtf8` leaves a stale `u8acc`, which the ruler never reads) — the stops are one `setIfInBounds` fold (`hts_run`, whose `CHA`+`HTS` pair establishes and consumes the cursor inside a single iteration), and the fold reproduces the ruler by `tabs_rebuilt`. The tail after it is `Fixes (·.tabs)` (`fixes_tabs_tail`), needing no allowlist and no digit bridge because `tabs_setMode` holds for every mode number. Two hypotheses beyond matching width: `Good w` (for `dims_feed`) and `v.tabs.size = v.cols`, which `Good`/`Renderable` do not carry. **This is the field that was worse than unproved**: `tabsAnsi` used to skip the ruler when the session's was the default, so the claim would have been *false* until that set-only leak was fixed — the one place a fix had to precede its theorem. **Still on the round-trip fixtures alone**, and named so the list is not "just the cells": the window **title** and the **DECSC slot**. **inbound scrollback ✓** (2026-09-11) — `Render.restore_sb_any` / `restore_sb_reachable` / `Linger.Core.resume_sb`: feeding `restore v` to any live-reachable client of the session's dimensions leaves `(w.feed (restore v)).sb.toList = (sbRows v).toList` — the session's history, oldest first, each row fitted to the session's width and trimmed from the oldest end to the byte budget. `.toList` and not `.sb` is deliberate and not a weakening: a ring that has wrapped and a ring built from index 0 are the same *history* in different *records*. `restore_sb_exact` closes the gap to `v.sb.toList` when the budget kept everything and the rows are already the session's width (`sbRows_toList_eq`, `fitRow_id_of_rowOk`) — which is every ring a live session built, since `scrollUpIn` pushes `v.getRow 0`. The ladder: `push_walk` (the walk, with the flush count `v.rows` shown unique), `ed3_empties`/`ed3_entry` (the `ED 3` empties the receiver's ring and carries `paint_entry`'s conjuncts across it — `Good` bounds `sb.size` and says *nothing* about `sb.start`, so nothing else in the repo could supply what the walk needs), `sbRows_size_le` + `Good.sbLe` **at the session** for the room, and `restore_sb_of_stage` for the other half — that none of the one-or-two screen paints, the alt switch, the region, the ruler, the DECSC slot, the title, the modes, the charsets, the pen or the final cursor address touches what the stage built. `gridAnsi` gets no `Fixes (·.sb)` lemma and cannot: it ends in `joinCRLF` and a `CRLF` at the region bottom pushes, so its invariance is conditional on the row count and rides `paint_rows`' ninth conjunct instead — `Renderable v` is the load-bearing hypothesis, and a target taller than the receiver pushes exactly `v.grid.size - v.rows` rows. **The guard makes this two branches, not one**: `restore_sb_keeps_of_empty` says a session with *no* history leaves the client's own scrollback alone, and that asymmetry is a user-facing decision rather than an optimization. **And one place this anchor's own title has an exception, recorded rather than buried:** replaying the ring means emitting `ED 3`, so attaching to a session that has history *erases the borrowed terminal's saved lines* in that window — linger never enters the alt screen, so the session shares the user's scrollback. That is the one thing linger does to a terminal it cannot undo; conformance-profile entry 11 records the divergence (ours clears the screen too) and README §Notes tells the user |

Each anchor is a *composition* of rungs, which is why the rung table is
still worth having: A1 is §Restore plus §Replay, A2 lifts three §s from
one event to a whole process lifetime, A3 subsumes §Frame and §Chunk as
special cases. A5 exists because linger is not a window manager (windows,
tabs and splits are settled non-goals), so it *borrows* a terminal you
already had — and a borrow has two ends. The outbound end was missing
entirely until 2026-08-15; both ends are now proved at the value level for
the modes, the pen and the sticky bundle (region, charsets, shift state,
screen selection). The cells and the tab ruler are proved too; the title and the DECSC slot
are still fixture-carried — see the A5 row.

A1's screen half is **closed** as of 2026-08-18: the replayed *cells* equalling
the saved cells is `Resume.resume_grid` (via `Render.restore_grid_any`), on both
screens and at every height, and the tab ruler followed the same day
(`Resume.resume_tabs`). `Tests/Render.lean`'s round-trip fixtures are now
regression tests rather than the fidelity oracle — which is exactly the handoff
`specs/archive/grid-fidelity.md` described. A1's cursor half was proved earlier
(`resume_cursor`), as was the whole byte layer beneath (`utf8_feed` and friends
reduce a repaint to a chain of `Vt.print`s). What remains fixture-carried on the
inbound side is the window **title** and the **DECSC slot** — and no longer the
*scrollback*: as of `specs/scrollback-fidelity.md` Step 4 a client's ring
**becomes** `sbRows v`, proved receiver-quantified (`restore_sb_any`,
`restore_sb_reachable`, `Linger.Core.resume_sb`) and end to end from a checkpoint.
The ladder is the emitter's row half (`rowOk_fitRow` unconditionally,
`sbRows_budget`, `rowAnsi_len_le_cost`), the bridge that keeps the ring out of the
screen theorems' statements (`scrollback_entry`), the walk (`push_walk`), the
`ED 3` that empties the receiver first (`ed3_empties`, `ed3_entry`) and the proof
that nothing `restore` emits afterwards touches it (`restore_sb_of_stage`). The
fixtures stay as the oracle for the *fit and the order* — `replayEq`'s `sb`
conjunct compares against the emitter's own view and is blind to bugs inside
`sbRows`, which is what the literal-anchored ring fixtures, the `dirtySb`
receiver and the two pty assertions exist for.

A5 adds no new idea to the rung table, only a
direction: §Handback is §Replay's question — *what does this stream
assume about, or leave behind in, the thing it writes to?* — asked about
the terminal linger gives back rather than the one it paints into.

## Coverage ledger — every README promise is backed or bounded

The hand-back bug shipped because a real product promise ("detaching leaves
your terminal usable") had no anchor — nothing proved it, no test pinned it,
no limitation bounded it. That is the one coverage failure that matters, so it
is the one we enforce: **every user-facing promise in README.md maps to a
theorem (anchor/rung), a live test suite, a stated limitation, or a settled
non-goal — never to nothing.**

A fanned-out audit (2026-08-16) classified all **72** README promises (the
mechanically enforced part of this is below, and it found the audit's own ledger
understating the gap by 2.7×):
**22 proved** by an anchor/rung, **41 test-pinned** (runtime `IO`, which
`Linger/Runtime/*` puts on `tests/` by design — see "§Total covers the emulator,
not the runtime" below), **6 bounded** by a stated limitation or non-goal,
and **2 gaps** — both now closed:

* *"no external Lean dependencies"* — was true but unguarded; now a fail-closed
  `lakefile.lean`/`lake-manifest.json` check in `tests/gates.sh`.
* *"`LINGER_NO_DETACH_KEY=1` disables the detach key"* — was unexercised; now a
  case in `E2E/Attach.lean` (the mirror of the ctrl-\ detach test).

Maintenance rule (the discipline, not a script): a new README promise, or a new
`§`/anchor, must land with its mapping — the anchor table above, the `§` "Where"
column, a named test, or a one-line limitation here. A promise with none of
those is the shape that let the hand-back through; treat an unmapped promise as a
bug, not a doc lapse. The README-promise mapping is re-derivable by re-running the
audit; it is a review gate, not an automated one, because "does this sentence have
backing" is a judgement a grep cannot make.

### …and the part that *is* automated, because the review gate was being fooled

Two things a grep **can** judge, so `E2E/Coverage.lean` judges them on every
`./tests/e2e.sh` run and the review gate no longer has to be trusted for either.

**1. Theorem-*statement* coverage of the pure core, as a ratchet.** The previous gate
grepped all of `Theorems/*.lean` for each core definition's name. That cannot tell a
claim from a word, and it was being fooled in the most embarrassing possible place:
`Render.history` — a byte stream the binary writes to the user's terminal — counted as
claimed because the word "history" appears in a **doc comment** in
`Theorems/Session.lean`. Nine of the ten definitions it *did* flag had zero mentions
anywhere, so what it actually measured was "is this name absent entirely".

The replacement strips Lean comments and looks only between `theorem <name>` and the
`:=`/`by` that opens the proof. The honest number is **27 of 229 core definitions
named by no theorem statement**, where the old gate reported 10 — so the real
uncovered surface was 2.7× what the ledger claimed. Most of the 27 are bounds
constants and predicates (`csiCap`, `oscCap`, `isWide`, `clampDim`), but some are
runtime-facing and worth naming as the queue they are — as of 2026-08-17 the head of
it is the checkpoint codec's `parseRecord`/`records`/`knownTag`/`magic`/`writeU32`.

The measure paid for itself immediately. `infoText` was top of that queue, and it was
top for a reason: Step 0 ledger item 2 was an **unfixed injection bug in exactly that
framing** — a label value carrying a newline forged an extra listing record, including
a `status`/`state` pair. Fixed at the emit site and proved (`infoText_framing`,
`infoText_records`), which dropped the ratchet from 27 to 26. The restructure that made
it provable — building `List UInt8` instead of interpolating a `String` — is the same
one recorded as the route for `history`.

Next on the queue was `chunksOf`/`outputMsgs`/`outputChunk`, the session's own framing
of what a client receives. `chunksOf` had appeared in `Theorems/` exactly once, in a
comment — the same blindness. Now `outputMsgs_faithful` and `outputMsgs_bounded`
(§Chunk row above), which took the ratchet to **23**. The break-verify there is worth
recording as a lesson about statement *shape*: the bound was first stated on
`chunksOf outputChunk bs`, and doubling `outputMsgs`' chunk size left it green. Restated
via `outputMsgs_payloads`, which pins the frames' payloads to the chunker, both claims
now fail. A theorem next to the code is not a theorem about it.

**2. Every byte stream the runtime emits is classified.** This is the check that
answers "are we proving things about the code that actually runs". The runtime's
emitter surface is small and enumerable — five functions — and each must be listed
with a theorem that constrains it or a stated limitation:

| stream | where the runtime writes it | backing |
|---|---|---|
| `Render.restore` | `Session.onMsg .attach` | **proved**: `restore_grounds`, `restore_u8_zero`, `restore_modes_any`, `restore_pen_any`, `restore_sticky_any`, `restore_cursor_any`, `restore_grid_any`, `restore_tabs_any`, `restore_sb_any` — receiver-quantified for the parser, the decoder, the screen cells, the tab ruler and the **scrollback** (2026-09-11, `specs/scrollback-fidelity.md` Step 4; `restore_sb_keeps_of_empty` is the guard's other branch). **Not** the window title or the DECSC slot |
| `Render.leaveAnsi` | `Client.attach`'s `finally` | **proved**: `leave_canonical`, `leave_canonical_all` |
| `Render.history` | `Session.onMsg` (`linger history`) | **proved**: `history_framing`, `history_lines`, `history_records` — every byte is a line terminator or printable content, the newline count *is* the row count, and `linesLF` splits the stream into exactly the rows' texts in order, so a cell cannot forge a line however the session's program filled the grid |
| `Render.screenText` | `Session.onMsg .screen` (`linger capture`) | **proved**: `screenText_framing`, `screenText_lines`, `screenText_records` — the same anti-forgery pair as `history` but grid-only, plus the parse contract (line *k* is `rowText` of row *k*) and `history_screenText_suffix`, which ties the capture byte-for-byte to the transcript's tail. Discussed at length under §Row; it was missing from **this table** until pin-the-gaps item 8, while `E2E/Coverage.lean` had been enforcing it all along |
| `Render.utf8s` | reached from outside `Render` by `Session.infoText`, which frames listing records with it | **proved**: `utf8s_no_ctl`, `utf8s_no_esc`, `utf8s_no_esc_bel`, `Session.utf8s_no_frame` — no scrubbed text can carry an escape, a BEL, or a framing byte |

A new emitter wired into the runtime fails the gate until it is classified, and an
entry for a stream the runtime *no longer* emits fails too, so the list cannot drift
into being a description of the past. All three failure modes are break-verified.

**There are now no stated limitations in that table**, and getting there is the
clearest thing the measure bought. `Render.history` was the last emitter assembled
through `String` (`rowText` → `String.intercalate` → `String.toUTF8`) — precisely the
shape `Linger/Core/Render.lean`'s own header says makes output unprovable, since a `String`
does not reduce in the kernel. It was classified as *bounded*, with the route recorded in
the entry: restructure it to build `List UInt8`. That route then got walked twice — first
for `Session.infoText`, where it also fixed a live injection bug, and then for `history`
itself. The limitation entry existed for about as long as it took to act on it, which is
the argument for writing a limitation down in a form that names its fix.

A5 is now proved at the value level in both directions, not just the
parser level. Both quantify over the receiver with no hypothesis on it —
the shape `specs/archive/restore-conformance.md` exists to reach — and rest on a
reusable layer: `modeSet_modes` exposes a private mode set as its
`setMode` (the dispatch-exposing bridge the spec named, for any mode
number, alt-screen modes included — where `keeps_modeSet` excludes them
because they touch the grid, but the parser and the modes projection do
not), and `MMap` is the modes-from-ground analog of `Keeps` that composes
per-chunk transforms. `leave_modes` folds the hand-back to the default
record; `restore_modes_any` folds `modesAnsi` to the session's record.
The inbound proof needed no repaint-modes ladder: because every
`modesAnsi` chunk is `ESC`-initiated (and `ESC` clears `u8need`), the
prefix through the title only has to reach `ground` — the already-proven
`Ends` ladder — so the paint is never dragged into a modes proof. Its one
hypothesis, `v.modes.mouse` in `{0,1000,1002,1003}`, is the emulator's own
mouse allowlist (`setMode` only ever stores those), and is exactly why
`modesAnsi` normalizes a foreign checkpoint's garbage mouse value to off
rather than replaying it.

**The sticky fields close A5's inbound half** (2026-08-16). The scroll region,
both charset designations, the shift state and the screen selection are the
group whose emitters are *not* all in the tail — `regionAnsi` runs before the
title, and `screensAnsi` switches screens in the middle of the repaint — so
unlike the modes and the pen these claims cannot step over `gridAnsi`; they have
to prove the repaint leaves them alone. Three things made that affordable:

* **One bundled projection, not four layers.** `Vt.stick` is `(rows, top, bot,
  g0, g1, so, alt)`. The frames pass retired the four single-field invariance
  layers for every operation whose result is a syntactic record update, and
  named the two it could not — `print` (a five-stage chain) and `csiDispatch` (a
  thirty-arm match) — so a fifth *layer* would have cost those two ~40 lemmas
  and a *bundle* costs them ~10. The frames note rejected bundling for fixing
  "only the fields we happened to need"; the answer is that this bundle is
  **closed**: `rows` is in it because `DECSTBM`'s clamp and the alt switch's
  region reset both read it.
* **The CSI walk, generalized.** `csi_tail_proj` takes the projection as a
  parameter (its one requirement, `PsBlind`, is that a bare `pstate` update
  cannot move it — `rfl` for every field accessor *but* `pstate` itself, which is
  the one projection this walk cannot serve and does not need to)
* **`SMap` needed no `u8need`, and neither did Step 2's second half.** The same
  observation closes both: a CSI's *final* byte cannot leave a character
  half-decoded, and `restore` ends with one (`cursorAnsi`). So
  `restore_u8_zero (v w)` holds for any receiver in fifteen lines — the entire stream
  in front of it is irrelevant — where `restore_quiesced` had to assume a fresh
  `Vt.init`. With `restore_grounds` (the `ESC \` lead-in, the other end) that is
  `restore_quiesced_any`, and A1 now reads over any receiver. `csi_tail_modes` and
  `csi_tail_pen` are now its instances, and `stick` a third; likewise
  `smap_csi_one_arg` does the digit-run-and-dispatch walk once for both markers,
  where `mmap_irm` and `modeSet_tail` each did it by hand.
* **No `u8need` in the stream predicate.** `SMap` is the `Quiet` shape — ground
  in, ground out, projection transformed — because every CSI/ESC chunk clears a
  half-decoded character at its own leading `ESC`, and a text run cannot move a
  sticky field whatever is pending. That is what lets the repaint be a chunk
  here at all.

The same machinery then closed A5's **outbound** non-modes fields
(`leave_canonical_all`), which Definition-of-done item 2b had asked for and which
`leave_canonical` alone did not cover: leaving the outbound half at "modes only"
while the inbound half was complete is exactly the asymmetry that let the
hand-back ship. `CSI r` — `DECSTBM` with no parameters, which is how the hand-back
names "the whole screen" without knowing the receiver's height — needed its own
short walk (`smap_stbm_plain`), and the trailing `SGR 0` turns out to *be*
`penSgr {}`, so `penSgr_feed` gives the pen directly.

Two long-range dependencies became visible rather than staying inspection-only.
`charsetAnsi` is set-only for the shift state (it sends `SO` when the session has
G1 shifted in and *nothing* when it does not), and `regionAnsi` emits nothing for
a whole-screen region — so both claims run back through the entire repaint to the
prologue's `SI` and `CSI 1 ; rows r`. They hold; the transform in
`smap_charsetAnsi` now says out loud that they *rest on* the prologue, which is
the same set-only shape `87f64b3` fixed in `modesAnsi` and worth watching. The
excluded case is a one-row region (`v.top = v.bot`): `CSI t ; t r` is refused
here and on every real terminal, so there is nothing to install.

### What the proof effort caught that the tests did not

Twelve infidelities have been found in `Render.restore`. Seven came from
reading the emitter against the parser. The eighth came from *proving*:
setting up the pen round trip required counting the parameters an SGR
carries, and a pen with all seven attributes plus truecolour foreground
and background needed 18 — two over the parser's cap, which drops the
whole sequence. Such a pen replayed **entirely default**: every attribute
and both colours lost. The state is reachable (an application sets
attributes and colours in separate SGRs), and sixteen fixtures had missed
it. `penSgr` now emits at most 8 parameters per sequence, and
`penSgr_under_cap` states the bound so the failure cannot come back
silently. The tenth was found while *designing* the grid induction rather than writing it: a combining mark on a wide char's own cell replayed onto its shadow, because the emitter put the marks after a 2-column advance. Reachable by moving the cursor back into a CJK line. Fixed by carrying the column in \`rowAnsi\` and parking the cursor with an absolute \`CHA\`.

The twelfth came out of an adversarial review of the sticky-field claims, and it
is the *same* set-only shape as `87f64b3`: **`tabsAnsi` is set-only for the tab
ruler.** It emits nothing when the session's ruler is the default, and neither the
prologue nor `ED 2` clears tab stops (no `TBC`, no `RIS` anywhere in linger's
output), so a client whose previous occupant ran `CSI 3 g` plus its own `HTS`es
keeps that ruler and the session's tabs come back wrong. Reproduced against the
project's own decidable oracle: with a receiver whose ruler was re-set every four
columns, `replayEq` failed on `.tabs` — it had passed only because no fixture moved
the *receiver's* ruler. **Fixed in the same session**: `tabsAnsi` now emits the
ruler unconditionally, pinned by the `dirtyTabs` fixtures and break-verified by
restoring the guard. It is the one field where the fix had to come before the
theorem, since `restore_tabs_any` would have been *false*; it is now provable and
unproved, and it is why the A5 row above names the uncovered fields instead of
saying "only the cells".

The eleventh was found by neither proving nor testing but by taking the
*diagnosis* seriously. Once the pattern was named — an emitter correct
only under an unstated precondition on the stateful thing it writes to —
the same question asked in the other direction found that nothing at all
cleaned up the user's terminal on detach (§Handback). No proof was
involved and no test existed; the audit that a proof plan scheduled is
what found it, which is worth remembering the next time the plan says
"audit first, it is cheap".

## The rungs

| § | Tension | Invariant | Where |
|---|---------|-----------|-------|
| §Frame | evolvable protocol vs simple daemon | `decode (encode m) = ([m], ∅)`; unknown tag skips exactly its frame | Theorems/Wire.lean |
| §Chunk | TCP/pty chunking is arbitrary vs stateful parsers | decode/feed invariant under concatenation: `feed (a ++ b) = feed b ∘ feed a`. And the session's *own* framing on top of the transport: `outputMsgs_faithful` (the payloads of the ≤ 64 KiB `output` frames concatenate back to exactly the bytes handed in, so a reattaching client gets the whole repaint, not a prefix) and `outputMsgs_bounded` | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Stream | transport fragmentation vs one parsed conversation | any re-chunking of any well-formed encoded stream feeds back to exactly that stream — nothing retained, no error (`decode_encode_chunked`; §Frame and §Chunk are its special cases) | Theorems/Wire.lean |
| §Bound | zellij crashes under cpu/mem load (unbounded actor queues) | every buffer has a structural cap preserved by `step`; nothing to fill | Theorems/Wire.lean, Theorems/Vt.lean, Theorems/Session.lean |
| §Total | emulator fed adversarial bytes vs no crashes ever | `Vt.step`/`feed` total (no `partial`, grep-checked); `Good` invariant preserved for any byte: cursor + saved + alt-stashed cursors strictly in bounds, top ≤ bot < rows. Grid dimensions are preserved by every operation too (`dims_feed`; `RIS` re-clamps, which `Good` makes the identity) | Theorems/Vt.lean |
| §Detach | sessions outlive clients (the zmx decoupling) | zero-client session still advances; detach/detach-all don't touch the screen (only permitted effect: a checkpoint) | Theorems/Session.lean |
| §Restore | reboot-resume vs corrupt/stale state files | `load (save s) = some s` (parser state quiesced); `load` total on arbitrary bytes; the on-disk tag is pinned (`save_tag`: `"LNGR"` v1, and `load` refuses every other tag, the pre-rename one included — its reader lived for one commit and is available at `e1ac562` if a v1 `"LZMX"` file ever turns up) | Theorems/Checkpoint.lean |
| §Name | user-chosen names vs filesystem paths | sanitized names can't escape the socket dir (no `/`, `..`-prefix, NUL, empty); `@` reserved for `name@host` | Theorems/Name.lean |
| §Remote | trusting `ssh host linger ls` output vs local listing safety | parser total, garbage-tolerant; §Name carries through; display fields scrubbed of control bytes | Theorems/Remote.lean |
| §Isolate | many clients on one session vs per-client framing | `.bytes id` leaves every *other* client's record (and decoder) bit-identical | Theorems/Session.lean |
| §Row | a list row's identity vs an unreliable `info` reply | a row's name is the sanitized socket filename alone; the reply can neither change it nor smuggle a second one in | Theorems/Listing.lean |
| §Claim | one session name vs many daemons racing for it | *given* the kernel grants ≤1 `flock` holder, ≤1 daemon ever unlinks or binds that name | Theorems/Claim.lean |
| §Replay | one saved byte stream must recreate the live screen on a fresh terminal | **parser half proved**: a fresh emulator fed a whole restore stream is quiesced — parser in `ground`, no half-decoded character (`restore_quiesced`), for any `Vt` and with no hypotheses. So a reattach can never wedge a client mid-sequence. **Cursor proved end to end** (`restore_cursor`): the replayed cursor equals the session's, given `Good` (§Bound) and DECOM off — resting on `Quiet`, which says a restore body leaves the parser ground *and* DECOM off, so the final `CUP` is read as an absolute address. **Byte layer proved**: feeding the bytes of a glyph *is* printing it (`utf8_feed`, `cellText_feed`, `crlf_feed`), so nothing below the emulator-operation level is left to trust. **Pen proved** (`penSgr_feed`): the emitted SGRs set the pen to exactly the saved one, from any starting pen — the parser's accumulator delivers the numbers `penSgr` chose (`csi_joinSemi_feed`) and `applySgr` inverts them (`pen_codes_recover`); every sequence stays under the parser's 16-parameter cap (`penSgr_under_cap`), the invariant that replaced a real bug. Remaining: the *cells* — that the replayed grid equals the saved grid, pinned meanwhile by the decidable `replayEq` fixtures and the `Tests/Fuzz.lean` corpus (both failure lists empty, no held-out mutations). The emulator side of that claim is now closed by §Renderable — the shapes the row painter cannot express are no longer reachable — so what is left is the row/grid replay induction itself, not side conditions on it | Theorems/Render.lean, Tests/Render.lean |
| §Handback | the session's program owns the terminal's state while attached vs. the user's shell gets that terminal back | a detaching client hands back a terminal the next program can use, and what it hands back does not depend on what the session was doing: `Render.leaveAnsi` is a **constant**, written in `Client.attach`'s `finally` so every exit path — detach key, session exit, EOF, decoder error, exception — goes through it. It leads with `ESC \` for the same reason the restore prologue does (a program that died mid-OSC/DCS would swallow the whole stream), then leaves the alt screen, clears IRM/DECOM/mouse×3/SGR-mouse/focus/bracketed-paste/DECCKM/DECKPNM, restores autowrap, the full scroll region and the ASCII charsets, parks the cursor bottom-left (`?6l` and `CSI r` both home it, so it is placed rather than preserved — and DECSC/DECRC cannot help, since the bundle a real DECRC restores is exactly the state being reset) and ends with `SGR 0`. **Proved as `Render.leave_canonical_all`** — for every receiver at least two rows tall, the parser ends `ground`, the modes are the default record, the scroll region is whole, both charsets are ASCII with G0 shifted in, the main screen is current and the pen is reset. (`leave_canonical` is the parser+modes half and needs no hypothesis at all; the two-row one is `DECSTBM`'s own, here and on every real terminal.) What no theorem covers is the **cursor position** — `CSI 999 ; 1 H` is clamped by the receiver, so where it lands is the receiver's business — and pinned by `E2E/Attach.lean` step 9's thirteen assertions. Termios is not terminal state — `termRestore` was the whole of the cleanup before this, and detaching out of a full-screen program left the shell on the alt screen with mouse reporting on, no cursor, autowrap off, a stale scroll region and DEC line drawing selected. Still leaked outbound: the **window title**, which `titleAnsi` sets on attach and we cannot put back because we never read it (xterm's title stack would; it is not universal) | Linger/Core/Render.lean, Linger/Runtime/Client.lean, E2E/Attach.lean |
| §Terminal | a child needs a terminal that answers, but linger has no terminal of its own and may have no client attached | one bounded pure transducer owns a documented query profile: for a fixed starting `Vt`, scanner and child byte stream, the VT projection, the scanner and the **ordered reply stream are independent of the client roster** (`Terminal.feed_vt`, `Session.ptyOut_reply_roster_independent`); a complete owned query is removed from presentation output and answered exactly once, everything else is byte-for-byte passthrough — proved for arbitrary APC and sixel payloads that do not carry their own terminator (`apc_passthrough`, `sixel_passthrough`, both under `StFree`), and pinned for ordinary ANSI, over-cap candidates and unknown/vendor queries by `Tests/Terminal.lean` at every byte split rather than by a theorem; the general conservation lemma is not yet stated; the scanner is capped at 128/256/2048 bytes for CSI/OSC/DCS and an over-cap candidate becomes passthrough rather than growth (`feed_bounded`); an incomplete trailing prefix is released once at EOF, broadcast before the exit notifications, and never re-fed to the VT (`Session.step_childExited_effects`, which is `rfl` against the literal effect list; `finish_exact` only says what `finish` returns). Chunking-invariant end to end (`feed_append`). No input to the mediator names the child. **No reply linger writes to the child can commit a line**: replies are routed into the child's own pty input (`.writePty`), and a request is untrusted child output, so an echoed reply carrying a `CR`/`LF` was a terminal-reply command injection — `cat`ing a crafted file could run a command. `feed_replies_noNl` proves the reply stream contains no `0x0D`/`0x0A` for any child bytes and any scanner state; the one echoing reply, XTGETTCAP, filters its payload to the hex+`;` alphabet a conforming request uses (`capByte`), identity on a real query and terminator-free on a malformed one. Found by the Step 0 audit, not by a test; pinned by the proof, `Tests/Terminal.lean` and a live pty case in `E2E/Terminal.lean` | Theorems/Terminal.lean, Theorems/Session.lean |
| §Renderable | the painter can express only some grids, and the emulator can reach more of them | the emulator does not store a shape a repaint cannot reproduce. A cell holds a printable base of the width it claims and at most eight zero-width marks (`printableChar` substitutes controls **on store**, `printMark` caps marks and parks them on a base, never a shadow); a wide glyph keeps its shadow and that shadow carries nothing of its own. Every row mutation ends in `Row.mend`, and `mend_pairOk` discharges the pair rule for **any** input row, so the invariant costs no per-operation index reasoning. `mend_keeps_narrow`/`mend_keeps_wide` say the repair is the identity on a well-formed write, which is what lets a repaint read back what it just painted. `renderable_step` carries it for **any byte** and `renderable_feed` for any stream, so with `renderable_init` it holds of every state the emulator can reach; `renderable_resize` and `renderable_quiesce` cover the other two things a live session does to a terminal. `LiveReachableVt` is the least predicate closed under those three, and `renderable_of_liveReachable` discharges the shape hypothesis a replay theorem would otherwise have to assume — so it cannot be satisfied vacuously by excluding awkward states. Lifted to the daemon by `Session.run_vt_renderable`, for any event trace. The base clause is stated concretely (`Emittable`) rather than as `printableChar c = c`, which would be a tautology against the function that establishes it | Linger/Core/Vt.lean, Theorems/Vt.lean |
| §Status | one glyph per listing row vs seven distinguishable conditions | the seven states **partition** the observation space: \`cover\` (every row is in some state), \`disjoint\` (none is in two), \`classify_sound\` + \`classify_unique\` (the priority cascade computes the legend, and is the only function that does), \`reachable\` (no glyph is a state the program cannot report), \`icon_injective\` / \`name_injective\` (distinct states, distinct symbols -- so a merge must delete a state rather than overload a glyph), \`name_clean\` (porcelain names carry no tab or newline, which is what makes tab-separated rows unambiguous without escaping) | Theorems/Status.lean |
| §Resume | the product's own promise: crash, reboot, reattach | §Restore ∘ §Replay composed — `load (save c)` succeeds, its replay leaves the terminal quiesced (anchor A1), and the cursor lands where the session had it (`resume_cursor`) | Theorems/Resume.lean |


## Reading a row

Each § is proved for *all* inputs, not sampled: the state machines are
`List`/`Nat`-shaped precisely so the inductions go through. Proofs use
`native_decide` nowhere; the unit tests in `Tests/` do, because they
pin concrete behavior (golden bytes, screen contents) where evaluation
is the point.

Each row was **break-verified**: the code was deliberately broken once
to watch the theorem catch it, and the break is recorded in
`SCRATCHPAD.md`. A theorem that survives a wrong definition is worth
nothing.

The machine-layer rows also hold over whole event *traces*, not just
single steps: `run` (Linger/Core/Session.lean) names the fold the
runtime's poll loop performs, `run_eq_foldl` pins it to that fold
exactly (state threading and effect order), and `run_wf` /
`run_bytes_isolates` (Theorems/Session.lean) lift §Bound + §Total and
§Isolate to the daemon's whole life — no trace of any length breaks
the caps, the screen invariant, or client isolation.

## Why the rungs carry hundreds of lemmas, and how much of it frames retire

Four of the invariance layers — `pstate`, `u8need`, `dims`, `origin`
(`Theorems/Vt.lean`) — are the same ~28 lemmas written four times: for
every emulator operation, "this field is unchanged". About 110 lemmas,
one idea.

The generalization, **now in force for the leaf operations**, is to state
each operation's *frame* — its footprint — once:

```lean
theorem frame_putCell : v.putCell x y c = { v with grid := (v.putCell x y c).grid }
```

Read: *`putCell` writes only `grid`*. Every field invariance is then one
rewrite away, for **any** field — including `top` and `saved`, which no
layer ever covered. There are 30 frames, placed before the four layers so
those can cite them, and 28 layer proofs are now a single `rw [frame_X]`
(86 proof lines removed). A fifth field costs nothing for these
operations.

**How far it goes, measured rather than assumed.** A frame is provable by
`rfl` exactly when the operation's result is a *syntactic record update*.
That holds for the leaf operations — the thirty that are converted — and
it **fails** for two classes, both spiked before this claim was written:

* *Compositions.* `frame_print` (the full stage chain) times out: the
  monolithic unfold is too large for a per-branch `rfl`. Gluing staged
  frames instead needs frame *composition*, which needs footprints as
  first-class data (a field-set type, a `WritesWithin` predicate,
  monotonicity) — a small effect system, larger than the sprawl it
  removes.
* *Folds.* `frame_csiDispatch` fails on arms like
  `List.foldl (fun a _ => a.tab) v (range n)`: a fold's result is not a
  record update, so the arm needs an induction and manual gluing — about
  what the current per-field sweep costs.

So `print`, `csiDispatch` and the fold-based operations (`eraseScreen`,
`insertLines`, `deleteLines`) keep their per-field lemmas, which is also
where the conditional cases (`RIS`, `setMode`) live. Frames retired the
mechanical majority; the residue is the part that was never mechanical.

Two weaker ideas, recorded because they look attractive and are not:

* *Bundling* the four fields into one conjunction is a 4× win but fixes
  only the fields we happened to need; a frame is complete.
* *Splitting* `Vt` into `{screen, parser, meta}` and typing the printing
  operations `Screen → Screen` does not capture the invariance at all,
  because the read/write distinction is **per-operation**: `print` reads
  `cols`/`rows` to clamp and reads `modes` for wrap/insert while writing
  neither, so any partition that groups `dims` with the cells still
  permits a resize. The refactor that would capture it moves read-only
  data into *parameter* position (`print : Dims → Modes → …`) — far
  larger, and mostly subsumed by frames.

The honest limit of all of them: a frame says what an operation leaves
alone, never what the written fields *become*. Grid fidelity (§Replay
stage 3d) needs the positive specification, which is real content rather
than bookkeeping. Frames retire sprawl; they do not shorten that road.

**That limit is now closed for `scrollUpIn`**, the one operation the
scrollback story rests on (`specs/scrollback-fidelity.md` Step 2).
`scrollUpIn_rows` says what a scroll *writes* — row `y'` inside the region
becomes the row below it, and the vacated bottom row is blank **in the pen
in effect**, so a coloured session scrolls up a coloured blank rather than
a default one. `scrollUpIn_sb_push` says what it pushes (the evicted top
row, once, only when the region is the whole screen and the alt screen is
down); `scrollUpIn_sb_of_false` says the branch that may not push does not,
which no frame can state because `sb` is inside the footprint a frame
declares. `lineFeed_scroll` is `lineFeed_interior`'s twin at the region
bottom. `top ≤ bot` is a stated hypothesis of `scrollUpIn_rows` and not
decoration: with an inverted region the vacated-row write lands *outside*
`[top, bot]`, which makes "outside the region is untouched" false at
`y' = bot`. Every caller has it from `Good.topLe`.

The row walk carries the ring across the screen paint: `Render.OffRow`
gained an `sb` field and `paint_rows` an `sb` conclusion. `OffRow.cells`
cannot supply it — at one row a scroll rewrites the only row there is, so
`cells` is vacuous exactly where the ring grows, which `Tests/Vt.lean`
pins as a fixture rather than an argument.

## Concurrency: what the model rules out, and what the theorems cover

There are **no data races to reason about**, by construction rather
than by proof: the daemon is one process with one `poll` loop, there
are no threads, no `IO.Ref`/`Task`/shared mutable state anywhere, and no
signal handler that touches state (every `signal()` in `c/shim.c` is
`SIG_IGN`/`SIG_DFL`; the client polls `winsizeGet` instead of taking
`SIGWINCH`, which removes async-signal reentrancy as a category). So
"concurrency" here means **interleaving of events from many clients**,
plus **two processes meeting at a file**. Three theorems carry it:

* **§Chunk** — the per-connection half. `poll` hands us whatever bytes
  happen to have arrived, so chunk boundaries are nondeterministic;
  `Decoder.feed_append` says any split of one client's stream yields
  the same messages in the same order. Interleaving cannot desync a
  frame.
* **§Isolate** — the cross-client half. `.bytes id` provably leaves
  every other client's record, including its decoder mid-frame,
  bit-identical. One client cannot corrupt another's framing, and
  §Bound's `decOk` holds for *all* clients simultaneously.
* **§Restore** — the file half. Checkpoints are written tmp+`rename`
  (atomic), and `load` is total on arbitrary bytes, so a reader racing
  a writer sees either the old file or the new one and never dies on a
  torn one.

Two clients typing at once still interleave into the pty — inherent to
a shared terminal, not a defect, and no theorem should claim otherwise.
What *is* deliberately ordered: the pty size is owned by the newest
attached real terminal (`Session.sizeOwner`), so concurrent resizes
converge instead of fighting. `resizeEffects_owner_only` states it for
attached clients, and the control path (`linger resize`, below) extends
it rather than bending it.

## The agent verbs (specs/archive/agent-cli.md) — what they promise, and the two deliberate semantics

One-shot verbs so another program can see and drive a session. Three claims
carry them, plus two decisions that are semantics, not accidents:

* **A capture cannot be forged and is positionally parseable.**
  `Render.screenText` (the `linger capture` stream) emits the grid alone,
  `rowText` per row: every byte is a line terminator or printable content
  (`screenText_framing`) and the newline count is exactly the grid's row count
  (`screenText_lines`) — a cell the session's program filled cannot inject a
  line break. The parse contract itself is a theorem, not a consequence the
  reader has to trust: `screenText_records` says splitting the stream on LF
  (`Render.linesLF`, the consumer's splitter as a specification) yields the
  grid **row for row** — line k IS `rowText` of row k, which count + framing
  alone do not give (a reversed-row emitter passes both; the break record
  shows only `screenText_records` catching it). `history_records` is the same
  contract for the transcript, and `history_screenText_suffix` ties the two
  byte-for-byte: a capture is exactly the transcript's tail, so an agent may
  mix the verbs without normalizing. Same anti-forgery species as
  `infoText_records` (§Row's discipline applied to every line-oriented stream
  a caller parses).
* **A capture is a look — deliberately.** The `.screen` arm's only state
  change is the read mark catching up (`onMsg_screen`, which is `rfl`, so any
  smuggled side effect breaks it; `screen_marks_seen` and `screen_behind_zero`
  are the user-facing halves): after a capture, `unseen` is false and `behind`
  counts output since *your* capture, which is the change cursor an agent
  polls. The line is drawn at verbs that deliver the current screen: `.info`
  never marks seen (`ls` polls every live daemon; a listing that marked
  everything read would destroy the status column) and `history` stays an
  export.
* **…and `behind` is honest over the daemon's whole life.** Capture made the
  read mark a two-writer field and an agent-facing API, so the general claims
  landed with it: no client message moves the output counter (`onMsg_outSeq` —
  traffic cannot *forge* activity; only `.ptyOut` advances `outSeq`), and no
  event trace of any length lets the read mark overtake it (`run_lookSeq_le`,
  via `onMsg_lookSeq_le`/`step_lookSeq_le`), so `behind = outSeq - lookSeq` is
  a real count and never a Nat-subtraction lie. The break record is the reason
  this pair exists: a `.screen` arm that sets `lookSeq := outSeq + 1` leaves
  `screen_marks_seen` and `screen_behind_zero` **green** — Nat clamps the lie
  to zero — and only `onMsg_lookSeq_le` catches it.
* **A control resize never overrides an attached sizer.** `linger resize`
  reaches `Session.controlResize` only from non-attached connections
  (`onMsg_resize_control`); while an attached sizer exists it changes nothing
  and refuses loudly (`controlResize_never_overrides` — an agent must not
  believe a size it never got), with nobody attached a genuine new size is
  exactly one `resizePty` plus the emulator resize (`controlResize_applies`),
  and the same-size branch is inert (`controlResize_same_size`) for the
  attach guard's reason: `Vt.resize` wipes the scroll region and tab ruler,
  and no SIGWINCH fires at an unchanged winsize to make the child re-establish
  them. On top of the three guarded shapes, `controlResize_replies` is the
  guard-free totality: every control resize answers the requester — `.done`
  or `.err`, silence unrepresentable — the pure half of the no-hang contract
  (`Client.drainBounded` owns the impure half, against daemons that predate
  the verb).

The runtime half — one `.input` frame per ≤ 64 KiB stdin read in
`send <name> -`, and the bounded drain that keeps a new verb from hanging
against a pre-upgrade daemon (§Frame drops an unknown tag *silently*, and
linger daemons outlive binary upgrades by design) — is `IO`, so it is pinned
by `E2E/Agent.lean` (suite 12) rather than proved; the break records are
in SCRATCHPAD 2026-08-19, including the live 2-second no-reply demonstration.

### Session identity at the socket path: closed by the kernel, not by a proof

`Daemon.serve` used to claim a name as probe → unlink-if-refused →
`bind`, and that middle step was a window: with a *stale* socket
present, two starting daemons could both pass the probe, the first
bind, and the second unlink the first's live socket before binding its
own — leaving a daemon alive holding a shell nobody could reach by name.

It now takes an exclusive `flock` on `<name>.lock` **before** the probe
and holds it for the process's whole life, so only the owner may unlink
or bind. `flock` rather than an `O_EXCL`/`mkdir` lock file on purpose:
those are atomic to create but have *no automatic release*, so a
SIGKILLed or power-cut holder leaves a lock nobody can clear, which is
why such designs need a staleness timeout — and any timeout is wrong
(too short steals a live lock, too long makes sessions unstartable
after a reboot). The kernel drops an `flock` when the holder dies, so
there is no timeout in this codebase at all. The lock file is
deliberately never unlinked: unlinking it would let a newcomer lock a
fresh inode while the owner still held the old one.

§Claim states the mutual exclusion this buys, and states it the only
way an OS primitive admits: **conditionally**. `Exclusive` (at most one
`flock` holder) is a hypothesis naming exactly what the kernel is
trusted for; `Guarded` (only the holder unlinks or binds) is ours and is
proved. So the theorem is "≤1 owner per name, given ≤1 lock holder",
and the assumption is one reviewable line rather than an unstated hope.
An advisory lock is still a theorem-grade guarantee over the population
that cooperates — every process claiming a session name is an `linger`
daemon — and §Claim says so precisely, including what it does not
cover.

This is a kernel guarantee plus a proof, not a proof alone.
`E2E/Robust.lean` pins the correspondence between §Claim's model
and `serve`: stale socket plus eight concurrent starts yields exactly
one daemon and one shell, and the name is re-claimable immediately
after the owner exits.

## Network filesystems: where the guarantees stop

Three parts of the design assume local storage, in decreasing severity.

**Socket directory (only reachable by setting `LINGER_DIR`).** Unix
sockets are host-local rendezvous names; `bind` on NFS commonly fails
outright, and on a *shared* directory the failure is worse than an
error: sockets belonging to other hosts appear in `list`, no local
listener answers them, and the stale-socket cleanup would delete
another machine's live socket. The defaults avoid this —
`$XDG_RUNTIME_DIR` (tmpfs) or `/tmp/linger-$UID`. Pointing `LINGER_DIR` at
a network mount is unsupported.

**The name lock.** `flock` is unreliable over NFS, so `Exclusive` — and
therefore §Claim — does not hold there. Moot in practice, since the
same shared-directory scenario is already broken by the point above.

**State directory (checkpoints).** This one can arrive by accident: the
default sits under `$HOME`, which is network-mounted on many setups.
Writes are safe (`tmp` + `rename` is atomic, and §Restore's totality
covers a torn or foreign file), but two hosts sharing `$HOME` and each
running a session called `work` would clobber one another's checkpoint.
The default state directory is therefore namespaced by hostname, which
is also the correct semantics: replaying machine B's terminal on
machine A would restore a screen describing a working tree and a
process world that are not there. An explicit `LINGER_DIR` is taken
verbatim — an override is an instruction, not an accident.

Not affected: `readDir` staleness under attribute caching is cosmetic
(a session may appear a beat late), and the daemon's log file has a
single writer. Worth knowing rather than fixing: the `0700` mode on the
socket directory is only as strong as the filesystem enforcing it,
which on NFSv3 with `auth_sys` is not very.

`list` cleaning up stale sockets is *not* part of that hazard: it
unlinks only when `connect` itself fails, which the kernel answers from
the socket's bind state, so a daemon that is merely slow (or SIGSTOPed)
keeps its socket — and §Row keeps it correctly named in the listing.
Verified.

## The conformance profile — what `restore`/`leave` assume of the receiver

These are emitter/parser self-consistency theorems: the model receiver is our own `Vt`, so a
green proof says the stream `restore` emits is read back by *that* parser as the state it
encodes. Each entry below is a behaviour the stream depends on, and so a place a nonconforming
terminal would diverge from the proof — the honest boundary of the claim, and linger's stated
compatibility requirement. (The pty and e2e suites remain the only evidence about real
terminals; see the note under `## What these theorems do not settle`.)

1. **Absolute cursor addressing with origin mode off.** After `CSI ? 6 l` (DECOM off), `CSI H`
   homes to (0,0) and `CSI r ; c H` / `CHA` address from the screen origin, not the scroll
   region. The paint homes with `CSI H` and places a wide glyph's marks with `CHA`; a terminal
   that kept origin mode after `?6l`, or made `CHA` region-relative, would misplace cells.
   (`prologueAnsi`'s `?6l`, `home_places_cursor`, `cha_matches`.)
2. **Deferred wrap at the right margin, with autowrap on.** A glyph in the last column arms a
   wrap-pending rather than moving the cursor, and a following combining mark attaches to that
   cell. `CSI ? 7 h` sets it; the row induction models `cursor.pending`. A terminal that
   wrapped eagerly would push a margin cell's mark to the next line. (`?7h`,
   `step_narrow_margin`, `Vt.printMark`; two fuzz seeds in SCRATCHPAD 2026-08-15.)
3. **The SGR parameter cap: at most sixteen parameters, the seventeenth sets `ignore` and drops
   the sequence.** `penSgr` splits a pen into ≤3 sequences of ≤8 parameters so none is dropped.
   A terminal with a smaller cap would lose attributes or colours. (`penSgr`,
   `penSgr_under_cap`, `pen_codes_recover`.)
4. **`ED 2` clears the screen and touches nothing else** — not the modes, pen, cursor or
   dimensions. It is the clean slate before the paint. (`eraseScreen_two_frame`, `mmap_id_ed`.)
5. **Charset designations are honoured (`ESC ( B`, `ESC ) B`, `SI`).** The stream re-designates
   ASCII and shifts G0 in; a terminal left in DEC line-drawing would render the paint's ASCII as
   box glyphs. (`charsetAnsi`, `prologueAnsi`.)
6. **DECSTBM sets the scroll region, and refuses a region of fewer than two lines.** `CSI 1 ;
   rows r` resets the region whole for `rows ≥ 2`; for one row it is a no-op and a conforming
   (`Good`) one-row screen already has the whole region. A terminal that accepted a one-row
   region, or ignored DECSTBM, could scroll the paint. (`prologue_sticky`, `smap_stbm`,
   `stStbm`.)
7. **The alt-screen switch stashes and blanks.** `CSI ? 1049 h` replaces the grid with a blank
   of the current size, saves the cursor and pen, and resets the region; `?1049l` restores. A
   terminal that switched without blanking or without resetting the region would corrupt the
   alt-screen paint. (`alt_switch_entry`, `modeSet_feed_eq`, `Vt.enterAlt`.)
8. **The final cursor address is clamped to the receiver's size.** `CSI 999 ; 1 H` parks the
   cursor bottom-left (region-relative under DECOM), clamped by the receiver — which is why the
   stream carries no dimensions for it, and why *where* it lands is the receiver's business.
   (`cursorAnsi`, `restore_cursor`, `leave_canonical_all`'s note.)
9. **A leading `ST` (`ESC \`) resynchronises a receiver caught in a string state.** It closes an
   in-progress OSC/DCS so the rest of the stream is parsed as commands rather than swallowed
   into a title. (`prologueAnsi`'s lead-in, `restore_grounds`, `st_grounds`.)
10. **UTF-8 decoding returns to a clean state after each complete glyph**, and the stream ends
    ESC-initiated so nothing is left half-decoded. (`utf8_feed`, `restore_u8_zero`, `U8Ok`.)
11. **`CSI 3 J` — a divergence, not an assumption.** xterm's `ED 3` is Erase-Saved-Lines: it
    discards the saved lines and leaves the screen alone. Ours clears the screen as well
    (`Vt.eraseScreen`, `Vt.eraseScreen`'s mode-3 branch), which is stricter than the sequence's
    meaning and unobservable where we emit it — the stream's `ED 2` is four bytes earlier, so
    the surplus erase is idempotent, and every field but `sb` is identical with it, without it,
    and on either side of `ED 2`, under a default pen or a BCE one. `E3=\E[3J` is declared by
    xterm, tmux, alacritty, foot, vte and the linux console, and ncurses' `clear(1)` sends
    `CSI H CSI 2 J CSI 3 J` — our order. A terminal that does not implement it ignores it, and
    the failure mode is benign: the previous occupant's history survives above ours and repeated
    attaches stack copies. We emit it **only when there is history to put there**, because that
    window's scrollback is the user's and shared with their shell — linger never enters the alt
    screen. (`scrollbackAnsi`; `E2E/Attach.lean` step 11 pins the order, and
    `Tests/Render.lean`'s guard fixtures pin both branches.)
12. **A printed line that scrolls off the top of a whole-screen region enters the terminal's own
    scrollback.** That is the only way to put a line there, and it is what the history stage
    does: paint the ring, then `rows` CR+LFs. A terminal with no scrollback, or one that
    discards the region's evicted rows, shows the screen correctly and keeps no history — the
    same benign failure as 11. (`scrollbackAnsi`, `Vt.scrollUpIn`'s push guard.)

## What these theorems do not settle

* **§Total covers the emulator, not the runtime.** `Linger/Runtime/*` is `IO`, and two
  of its loops are still `partial def` — `pump` (its recursion is genuinely
  unbounded without a two-pass argument) and `parseLs` (wants a `decreasing_by`);
  the other five shed the keyword on 2026-08-18, since `while`/`for` in a `do`
  block never needed it. Its correctness rests on the live suites in `E2E/`, not
  on proof. The pure/impure line is the `Linger/Core` boundary, enforced by
  `tests/gates.sh`.
* **§Bound bounds our buffers, not the OS's.** A peer that never reads eventually
  fills the kernel socket buffer; the runtime caps *both* of its own byte queues at
  4 MiB rather than grow — the per-client output backlog (`outbufCap`, disconnect the
  slow client) and the pty input backlog (`ptyInCap`, drop the newest whole frame, as
  a tty's own input buffer does when the child stops reading). Those queues are
  `Linger.Core.Buf`, and `Theorems/Buf.lean` proves the arithmetic: each cap bounds what
  is *owed* (`bufOffer_bound`, and `bufEnqueue_bound` guarded by "the peer was not
  cut", because `.send` appends before it decides), memory equals the debt so nothing
  written is retained (`bufNoRetain`), and each bound is paired with a content claim
  through `owed` so it cannot be met by discarding data (`bufOffer_owed`,
  `bufEnqueue_owed`, `bufAdvance_owed`). `Buf` holds only the bytes still owed, so the
  partial-drain leak — reclaim on empty, and a peer draining a little each round grows
  the array while the debt stays small — is unrepresentable rather than merely fixed.
  **What is proved is the arithmetic, not the daemon.** `Linger/Runtime/*` is `IO`, and no
  theorem can see that it calls these functions rather than open-coding the same sums.
  Two enforcement layers carry that gap (2026-08-19, the module system —
  specs/archive/lean-modules.md Step 2): `Buf.bytes` is `private`, so the runtime cannot read,
  write (`{ b with … }`), or forge a `Buf`'s representation — all three refuse at
  compile time, break-verified from inside the daemon; `Buf.empty` is the one door in,
  `writeFrom` the one window out, and `Theorems/Buf.lean` sees inside via `import all`,
  the friend import. And `tests/gates.sh` still gates that the runtime declares no byte
  buffer *of its own* — privacy seals `Buf`, but only the grep bans a parallel
  `ByteArray` queue, which is a source-tree property and therefore a grep, in the same
  spirit as `SHIM_CAP`. **The seal is also what upgraded the per-step bounds to
  whole-lifetime ones**: `ReachableIn`/`ReachableOut` (Linger/Core/Buf.lean) are
  exhaustive over what a plain importer can possess — pre-seal a forged `Buf` escaped
  any such predicate, which is why they were not worth stating — and
  `reachableIn_bound`/`reachableOut_bound` say any interleaving of capped offers (or
  not-cut enqueues) and flush advances, from boot, stays within the cap: §Bound over
  the queue's whole life, the same lift `run_wf` gives the machine one layer up.
* **Grid dimensions are invariant by theorem now** (`dims_feed`,
  Theorems/Vt.lean): no byte stream changes `cols`/`rows`. `RIS`
  re-derives them through `clampDim`, which is the identity exactly when
  they are already in range — so that one case is conditional on `Good`.
  The runtime still re-reads dimensions after every feed.
* **§Restore says the codec round-trips, not that the shell's world
  is restored.** A resumed session gets its screen, scrollback, modes,
  labels and cwd back — not its process tree. That is the deliberate
  continuum-shape trade: the work resumes, the programs do not.
  The scrollback comes back **to the byte budget**, which is the limit worth
  naming: `sbReplayBytes = 262144` bounds Σ `sbRowCost` over the replayed rows, so
  a ring of plain 80-column lines replays about three thousand of them and a ring
  of per-cell truecolour rows replays a few dozen. The budget is not prudence —
  `outbufCap` *disconnects* a client, and an unbudgeted full ring is 32–46 MB at 80
  columns. The emitted stage is bounded by `sbReplayBytes + 2 * rows + 19`, not by
  the budget itself; the extra is `ED 3`, the paint's `SGR 0`/`CUP` and the mode
  tail, and it is attained (measured: 262153 bytes for a ring whose rows each end
  in a truecolour cell). **Who carries which half, stated rather than blurred:**
  `sbTake_budget`/`sbRows_budget` prove a bound on the *counted* cost `sbRowCost`;
  the *emitted* whole-stream bound is fixtures (five ring shapes, sharp at 262,153)
  until `scrollbackAnsi_le` lands in Step 5. The **row** half of that asymmetry is
  closed, not deferred: `rowAnsi_len_seed` + `rowAnsi_len_le_cost` say a row's
  emitted paint from *any* incoming pen is within its counted cost, so an earlier
  version of this paragraph — "the proofs would survive changing `sbRowCost`'s
  `+ 6` to `+ 0`" — is false, and was corrected under pin-the-gaps item 9.
  Break-verified: `+ 0` makes `rowAnsi_len_le_cost`'s `omega` fail. What the
  fixtures still carry alone is the *whole-stream* step.
  `Vt.eraseScreen 3` clears `sb` as well as the screen
  (`Vt.eraseScreen`'s mode-3 branch), which is the receiver-ring-empty premise the
  receiver-quantified claim will cite.
* **The screen paint, not the history, is the unbudgeted term.** Measured while
  sizing the ring budget: with worst-case pens on both screens `restore` alone
  emits 4,561,018 bytes at 400×100 — already past `outbufCap` before any
  scrollback. The cliff is around 34,500 cells of window area at worst-case pens,
  and the history stage moved it there from ~36,800 by consuming ~6% of the
  headroom. Pre-existing, not introduced here, and not yet closed: it wants a
  budget on the paint, which is a bigger change than this step.
* **Images are passed through, not modelled.** Kitty graphics, sixel and
  iTerm2 sequences reach attached clients byte for byte, and the emulator
  ignores their payloads — parked in the string state until the
  terminator, accumulating nothing, so §Bound holds for a program
  streaming megabytes of base64 exactly as it does for any other output.
  Nothing is stored, so `restore` cannot replay them: a cell carries a
  character, marks, a width and a pen, and image placements are overlays
  anchored to cells rather than cell content. What brings an image back is
  the application redrawing, which a reattach triggers only when the
  terminal size changed (the kernel suppresses `SIGWINCH` otherwise). Both
  halves of that rule, and the passthrough itself, are pinned by
  `E2E/Graphics.lean` — rendering from the grid instead of forwarding
  raw chunks would break images with no other test noticing. Storing them
  is a scope decision rather than a missing proof, and README "Graphics"
  gives the four reasons.
