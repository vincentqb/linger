# bigger-theorems — composed statements over the existing ledger

Status: in progress

Outcome of the "is there a bigger theorem?" review (2026-08-12): no
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
