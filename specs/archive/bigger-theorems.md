# bigger-theorems — composed statements over the existing ledger

**Status: CLOSED 2026-08-12.** All four steps landed. The successor spec
for the one thing left open is `specs/grid-fidelity.md`.

**Goal.** Consolidate the theorem ledger: state the composed claims that
make the product's promises checkable in one place, and stop paying for
the same lemma four times.

**Definition of done.** Each step's statement is a green theorem in
`Theorems/` (no `sorry`, no `native_decide`), break-verified with the
break recorded in `SCRATCHPAD.md`, its row in `THEOREMS.md`, and
`./tests/e2e.sh` green. — **met for all four steps.**

## Completion record

| Step | Landed |
|---|---|
| 1 §Stream | `Wire.decode_encode_chunked` — any re-chunking of any well-formed encoded stream decodes to exactly that stream. §Frame and §Chunk became special cases |
| 2 trace lift | `Session.run`, `run_eq_foldl`, `run_wf`, `run_bytes_isolates` — the per-step machine theorems over a whole daemon lifetime |
| 3 §Replay | parser half complete (`restore_quiesced`, hypothesis-free); digit round trip (`accDigits_digits`); cursor end to end (`restore_cursor` → `Resume.resume_cursor`); `Quiet` (parser-ground ∧ DECOM-off, composable); byte layer reduced to `Vt.print` chains (`utf8_feed`, `utf8s_feed`, `cellText_feed`, `crlf_feed`); `penSgr_under_cap` |
| 4 frames | 30 `frame_*` for the leaf operations, 28 layer proofs collapsed to one `rw`, 86 proof lines removed |
| anchors | `THEOREMS.md` restructured as anchor set A1–A4 over 15 rungs |

Nine real emitter bugs were fixed along the way — seven from reading the
emitter against the parser during stage 3a, one (`§Replay` fix 5, the
region-relative cursor) from stating the cursor claim, and one (the SGR
parameter cap, which replayed a heavily-styled pen as **blank**) from
counting parameters while setting up the pen round trip. That last one is
the argument for proving rather than testing: sixteen fixtures had missed
it.

**What is NOT closed** — the *values*: that the replayed cells and pens
equal the saved ones. That is anchor A1's last gap and it now has its own
spec, `specs/grid-fidelity.md`, because it is a different kind of work
(positive specification of what gets written, not consolidation of what
does not).

**Decided — do not relitigate.**

* No single theorem spans the trust boundaries; the factored ledger *is*
  the design. The anchor set in `THEOREMS.md` is the readable summary.
* Cross-client commutativity is **false** (attach order decides
  `sizeOwner`; input interleaves into one pty). §Isolate is the honest
  maximum at the machine layer.
* `Render` is byte-native: a `String` literal does not reduce in the
  kernel, so a String-assembled emitter is unprovable in principle.
* `safeChar` and `utf8`'s codepoint clamp are hypothesis-free emit
  guards, not defensive noise — they are what make the proofs need no
  `Vt` invariant.
* Under DECOM the cursor can sit outside the scroll region (`VPA` ignores
  origin mode); that stays a **hypothesis**, not an emitter fix — setting
  DECOM homes the cursor, so emitting absolute first does not work.
* Frames do not extend to compositions or folds (measured, not assumed).
  The footprint-as-data effect system that would fix it is larger than
  the sprawl it removes — rejected.
* `ParamBytes` **excludes** the `<=>?` private markers (it is 0x30–0x3B,
  not 0x30–0x3F). One predicate then serves both invariance layers: the
  marker is what decides whether a sequence can be DECOM, so it is
  structure, handled at the one construct that has it
  (`ends_csi_priv_seq`), not a parameter byte. This is what avoided
  duplicating the whole SGR parameter chain for `Quiet`.
* The mouse-mode emit is **guarded** (`mouse != 6`) rather than backed by
  a reachability invariant on `Vt`. `setMode` only ever stores
  1000/1002/1003 there, so the guard is unreachable in practice — but a
  `Good`-style field would have to be maintained by every constructor,
  and one guarded emit is cheaper. Same trade as `safeChar`.

**Open questions.**

* Grid/pen value fidelity (step 3d) — needs the positive specification of
  what written fields become; frames buy nothing toward it.
* CI on a modern-glibc box: the durable guard for the portability class
  that bit on gpu2. Repo-level, outside this spec.Outcome of the "is there a bigger theorem?" review (2026-08-12): no
single theorem can span the trust boundaries (that factoring is the
design), but three composed statements are worth having. Cross-client
commutativity was considered and rejected as FALSE (attach order
decides `sizeOwner`; input interleaves into one pty) — §Isolate is the
honest maximum at the machine layer.

## Step 1 — §Stream: chunking is invisible (wire)

The composed §Frame ∘ §Chunk statement:

> For ANY well-formed message sequence and ANY re-chunking of its
> encoded bytes (per-byte, per-frame, arbitrary TCP segmentation),
> feeding the chunks yields exactly that sequence, in order, nothing
> retained, no error.

Reads: Zmx/Core/Wire.lean, Theorems/Wire.lean.
Writes: `Decoder.feedAll` (Core spec of the runtime read loop),
`takeFrames_leftover_stable`, `Decoder.feedAll_flatten`,
`decode_encode_chunked` (Theorems), one per-byte-chunking test
(Tests/Wire.lean). `decode_encode` / `decode_encode_stream` become
special cases.

Verify: build green; break-verify by making `feedAll` drop a chunk's
messages.

## Step 2 — trace lift: the per-step theorems over the daemon's life

`run : State → List Event → State × List Effect` (the fold the runtime
loop performs), plus:
- `run_eq_foldl` — `run` is exactly the effect-accumulating fold (pins
  the definition; state and effect threading both).
- `WF s := Bounded s ∧ Good s.vt`; `step_wf`; `run_wf` — no event
  trace of any length can break the daemon's bounds or the screen
  invariant.
- `run_bytes_isolates` — a client's whole byte stream, however
  chunked, leaves every other client's record untouched.

Reads: Zmx/Core/Session.lean, Theorems/Session.lean.
Writes: `run` (Core), the four theorems above, a concrete trace test
(Tests/Session.lean).

Verify: build green; break-verify by making `run` drop effects
(caught by `run_eq_foldl`). Note honestly: `run_wf`'s discriminating
power rests on `step_bounded`/`step_vt_good` (their breaks are the
recorded ones); the lift itself is pinned by `run_eq_foldl`.

## Step 3 — §Replay: restore fidelity (opened, staged)

The target theorem (the biggest unproved pure surface — Render has no
theorems today):

> `(Vt.init v.cols v.rows).feed (Render.restore v) ≃ v` — same grid,
> cursor position, pen, scroll region, modes, title, tabs, charset,
> saved cursor; composed with §Restore (`load ∘ save = id`) this makes
> reboot-resume exact end to end.

`≃` deliberately excludes: `sb` (restore repaints the screen, not the
scrollback — by design), `bell` (runtime signal), wrap-`pending` flags
(unrepresentable: cursor addressing clears them on any terminal),
parser fields (target is quiesced; the replay itself must END ground —
that IS compared).

Emitter/parser alignment review found these infidelities in
`Render.restore` (each = state the emitter never replays, or bytes the
parser reads differently than the emitter meant). Fix in Render, pin
each with a Tests/Render.lean round-trip that fails before the fix:

1. combining marks on a wide char live on its width-0 continuation
   cell; `rowAnsi` skips width-0 cells entirely → marks lost.
2. charset state (`g0Line`/`g1Line`/`shiftOut`) never replayed → box
   drawing breaks after reattach.
3. `saved` (DECSC) never replayed → DECRC after reattach goes to 0,0.
4. `modes.origin` (DECOM) and `modes.insert` (IRM) not in `modesAnsi`.
5. final cursor CUP is absolute; under DECOM it must be region-relative.
6. custom tab stops never replayed.
7. in alt screen, the stashed main cursor/pen can't be reproduced by
   paint-then-switch → emit CUP+SGR of the stash before `?1049h`
   (also corrects `saved` clobbering: replay `saved` AFTER the screen
   switch).

Stage 3a (done): fix the emitter, land the decidable comparator +
native_decide round-trip suite over vts exercising every feature
(colors incl. 256/rgb, wide+marks, region+scroll, alt screen, modes,
title, tabs, charset, saved). The suite IS the fidelity oracle until
the proofs land.

Stage 3b (DONE — the parser half, complete). `Render` is byte-native
(`List UInt8`, not `String` — a `String` literal does not reduce in the
kernel, so the old emitter's output was unprovable *in principle*).
Byte facts proved: `digits_range`, `utf8_no_ctl`/`utf8s_no_ctl` (via a
`min` clamp and `safeChar`, so no `Vt` invariant is needed). Two
invariance layers in `Theorems/Vt.lean`: `pstate` (~18 lemmas) and
`u8need` (~30, equation-form so they work as guided rewrites). On top,
the `Ends` combinator and one lemma per emitted construct:
`ends_csi_seq` (the workhorse — CSI `<params> <final>` returns to
ground), `ends_penSgr`, `ends_escSeq`, `ends_escCharset`, `ends_osc`,
`ends_rowAnsi`/`ends_joinCRLF`/`ends_gridAnsi` (via a generic
`invariant_foldl`), then every restore stage and finally:

  **`restore_quiesced`** — a fresh emulator fed a whole restore stream
  is in `.ground` with `u8need = 0`, for ANY `Vt`, no hypotheses.

The `u8need` half needed no reasoning about the repaint's multi-byte
encodings: `restore` *ends* with the cursor's `CSI … H`, whose leading
ESC clears any pending sequence, and every later byte is < 0xC0 so none
can re-arm one (`u8_zero_after_csi`). Break-verified twice: dropping a
CSI final byte (breaks `ends_csiNum` + 2 fixtures) and removing the
`safeChar` guard (makes `safeChar_ge` unprovable, cascading through the
grid chain). Emitter stages named for provability along the way:
`penSgrBody`, `sgrAttr`, `sgrColor`, `escSeq`, `escCharset`,
`screensAnsi`, `regionAnsi`, `tabsAnsi`, `savedAnsi`, `charsetAnsi`,
`titleAnsi`, `cursorAnsi`, `restoreBody`.

Stage 3c (STARTED — numbers round-trip). `accDigits` models the CSI
parameter accumulator exactly as `stepCsi` runs it, and
**`accDigits_digits : accDigits 0 (digits n) = min n 65535`** proves the
emitter and the parser are inverse on numbers, up to the parser's
documented clamp. Lifted to the emulator by `csi_digit_step` /
`csi_digits_feed` / `csi_digits_value` (feeding `digits n` from a CSI
with `cur = 0` leaves `cur = min n 65535`, `haveCur`, params untouched).
Break-verified: emitting least-significant-digit-first breaks the
theorem and 10 fixtures. This is the foundation for every numeric
fidelity claim (cursor, region, mode numbers, colour components).

Stage 3c-rest (rungs done; composition open). Both rungs the cursor
claim was waiting on are proved:

1. *Full-sequence cursor* — **`cup_places_cursor`**: feeding the whole
   `CSI row ; col H` that `cursorAnsi` emits places the cursor at exactly
   (`col-1`,`row-1`). The lift needed only that the prefix leaves the
   fields CUP reads alone, carried by a `Frame` bundle (cols, rows,
   modes) with one lemma per step kind.
2. *Origin layer* — `org_*` in Theorems/Vt.lean (~30 lemmas), resting on
   the structural fact that `modes` is written only by `setMode`;
   `org_setMode` is the single conditional rung (only **private** mode 6
   writes `origin`), lifted by `org_csiDispatch`/`org_csiFinish`/
   `org_stepCsi`, plus `org_step_of_{ground,esc,csi}` and
   `org_feed_ground` at the stream level.

What remains is the *composition* over `restoreBody`, and the shape it
wants is now clear. `KeepsOriginOff` on its own is the wrong abstraction:
without a `pstate` premise it is false for a bare text run (fed in the
middle of a CSI, an `h` byte could complete a mode set). The right
predicate bundles the two claims —

```lean
def Quiet (bs : Bytes) : Prop :=
  ∀ v, v.pstate = .ground → v.modes.origin = false →
    ((v.feed bs).pstate = .ground ∧ (v.feed bs).modes.origin = false)
```

— which composes over `++` exactly like `Ends`, and whose `pstate` half
is already discharged construct-by-construct by the `ends_*` family. The
per-construct origin halves are then one chain each; the only interesting
one is `csiPriv n`, whose *own* bytes set `priv = 0x3F`, so it needs the
state tracked to the final byte to show the pushed parameter is
`min n 65535 ≠ 6` (`csi_digits_value` now returns `priv` for exactly
this). With `Quiet (restoreBody v)` in hand, `restore_cursor` is
`cup_places_cursor` applied to the mid-state, with `dims_feed` and
`Vt.init`'s clamp (identity under `Good`) supplying the bounds.

Documented gap that stays a hypothesis: under DECOM the cursor can sit
outside the scroll region (`VPA` ignores origin mode) and a
region-relative `CUP` cannot express that; emitting absolute first does
not help, since setting DECOM homes the cursor.

Stage 3c-rest (DONE — the cursor claim closed). `Quiet` is the bundled
predicate the notes above predicted, and it went in as designed:

```lean
def Quiet (bs : Bytes) : Prop :=
  ∀ v, v.pstate = .ground → v.modes.origin = false →
    ((v.feed bs).pstate = .ground ∧ (v.feed bs).modes.origin = false)
```

closed under `++`/`ite`/`flatten`/`flatMap` exactly like `Ends`, with the
`pstate` half of each construct discharged by the existing `ends_*` family
and one origin argument added per construct. Two things fell out that the
plan had only guessed at:

* **`ParamBytes` was the wrong shape**, and fixing it removed the
  duplication rather than adding to it. It admitted the `<=>?` private
  markers (0x30–0x3F); tightened to 0x30–0x3B it means *plain parameter
  byte*, which is what makes "a marker-free CSI cannot be DECOM" a
  one-line consequence — and lets `Quiet` reuse `paramBytes_penSgrBody`
  and the whole SGR chain verbatim instead of cloning it. The marker
  became explicit structure at the one construct that has it
  (`ends_csi_priv_seq`).
* **The private-mode replay needed a second rung in the `org_*` layer.**
  `org_stepCsi` assumes the marker is absent, which excludes every mode
  replay. `org_csiFinish_pending` decides the question instead: with no
  pushed parameter and a pending accumulator that is not 6, no `h`/`l`
  final can be DECOM. The digit run that *builds* that accumulator is
  covered by the frame layer (`frame_csi_digits_feed`) — the first place
  frames paid for themselves in a proof they were not written for.

`restore_cursor` then composes: `quiet_restoreBody` (parser ground, DECOM
off after ~a kilobyte of repaint) + `cup_places_cursor` (the final CUP
delivers its parameters) + `dims_feed` (the repaint cannot have resized
the emulator) + `clampDim` as the identity under `Good`. Lifted to
`Resume.resume_cursor`, which replaces the `resume_cursor_shape`
placeholder: A1's cursor half is now proof, not fixtures.

The emitter guard the plan called for landed as
`if v.modes.mouse != 0 && v.modes.mouse != 6`.

Break-verified three times, and the first two attempts are worth
recording because they were *weak*:

1. Deleting the guard outright → caught, but as a `Type mismatch` on the
   `ite` shape. That only proves the proof mentions the guard.
2. Appending `csiPriv 6 0x68` to `regionAnsi` → same shape-level catch.
3. Changing `set 2004 true` to `set 6 true` in `modesAnsi` and updating
   the proof to follow (as a maintainer would) → `decide proved that the
   proposition 6 ≠ 6 is false`. *That* is the semantic catch: a restore
   stream that turns DECOM on is rejected. Also changing the guard from
   `!= 6` to `!= 7` gives `¬mouse = 7 but expected mouse ≠ 6` — the guard
   is load-bearing for exactly DECOM and nothing else.

Lesson for future break-verification: a break that changes a *term's
shape* is not a test of the theorem, only of the proof script. Change a
value, keep the shape, and update the proof the way a maintainer would.

Also deleted: the `KeepsOriginOff` scaffolding at the end of
Theorems/Render.lean (~85 lines), including three `org_step_of_*` lemmas
that *shadowed* the more general ones now in Theorems/Vt.lean. Its own doc
comment had already said the bundled predicate was what was wanted. No
external users, so it was dead weight pointing the reader at a rejected
abstraction.

Deliberately NOT done: abstracting the ~13 stage lemmas over a
`StreamPred` bundle so `Ends` and `Quiet` share one skeleton. Sketched it;
the blocker is that `modesAnsi`'s DECOM branch is hypothesis-free for
`Ends` and hypothesis-bearing for `Quiet`, so a shared stage lemma would
have to carry `v.modes.origin = true → P (csiPriv 6 0x68)` and would
weaken `restore_quiesced` from "no hypotheses" to "one vacuous
hypothesis". Preserving a hypothesis-free flagship theorem is worth more
than deduplicating thirteen 3-line proofs. Revisit only if a *third*
layer wants the same skeleton.

Stage 3d (open): grid fidelity — per-cell print round-trip induction
(wide, marks, IRM off, wrap-pending at row ends), then §Replay itself.

Verify (3a): every new test fails against unfixed Render (recorded),
passes after; `./tests/e2e.sh` green (restore byte stream changes are
behavior-compatible: resume/attach suites must stay green).


## Step 4 — retire the invariance sprawl with frames (DONE for the leaves)

The four layers (`pstate`, `u8need`, `dims`, `origin`) were ~110 lemmas
that are ~28 written four times. Each *leaf* operation now has ONE frame
equation naming its footprint:

```lean
theorem frame_putCell : v.putCell x y c = { v with grid := (v.putCell x y c).grid }
```

**Landed**: 30 frames, placed *before* the four layers so they can be
cited by them; 28 layer proofs collapsed to a single `rw [frame_X]` (86
proof lines removed); every field invariance — including fields no layer
covers, like `top` and `saved` — is now one rewrite away, so a fifth field
costs nothing for these operations. Full gate green.

**Deliberately not converted, measured rather than assumed:** `print`,
`csiDispatch`, and the fold-based operations (`eraseScreen`,
`insertLines`, `deleteLines`). A frame proves by `rfl` only when the
result is a *syntactic* record update: `frame_print` times out (the
composed stage chain is too large for a per-branch `rfl`) and
`frame_csiDispatch` fails on `List.foldl` arms. Gluing staged frames would
need footprints as first-class data — a field-set type, a `WritesWithin`
predicate, monotonicity lemmas — i.e. a small effect system, larger than
the sprawl it removes. Those operations keep their per-field lemmas, which
is also where the conditional cases (`RIS`, `setMode`) live.

Not addressed by frames, deliberately: the *positive* specification of
what written fields become. That is stage 3d (grid fidelity) and it is
content, not bookkeeping.
