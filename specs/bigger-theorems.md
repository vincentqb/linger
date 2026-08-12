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

Stage 3b (done, scoped): `Render` is byte-native (`List UInt8`, not
`String` — a `String` literal does not reduce in the kernel, so the old
emitter's output was unprovable *in principle*). Byte facts proved:
`digits_range`, `utf8_no_ctl`/`utf8s_no_ctl` (via a `min` clamp and
`safeChar`, so no `Vt` invariant is needed), plus a `pstate`-invariance
layer in `Theorems/Vt.lean` (~18 lemmas: every print/cursor/erase/scroll
op, `ctl`, `acceptChar`, `stepGround`). On top: the `Ends` combinator
(`nil`/`append`/`ite`/`flatten`/`flatMap`/`text`) and **`ends_csi_seq`** —
`CSI <params> <final>` provably returns the parser to ground — with
`ends_csiNum`, `ends_csiNum2`, `ends_csiPriv` as instances. Break-verified
by dropping a CSI final byte (breaks the theorem *and* the fixtures).
Scope note: `Ends` covers `pstate` only; the companion `u8need = 0` needs
per-op `u8need` lemmas through `csiDispatch` and buys much less (a
trailing partial UTF-8 mis-renders one glyph; a stuck `.csi` swallows
everything). `replayEq` checks it.

Stage 3b-rest (open, mechanical): `ends_penSgr` (needs `penSgr`'s
parameter body as a named stage so the chunk is syntactically
separable), the OSC-title construct (`ESC ] 2 ; text BEL` — needs
`stepOsc`/`oscFinish` lemmas), the `ESC`-single constructs (`ESC 7`,
`ESC =`, `ESC ( 0`), then `Ends (restore v)` as their composition.

Stage 3c (open): value fidelity — digit round-trip (CSI param
accumulator vs `toString`; may need a bespoke digit emitter in Render
for provability), then pen/cursor/region/modes equality theorems.

Stage 3d (open): grid fidelity — per-cell print round-trip induction
(wide, marks, IRM off, wrap-pending at row ends), then §Replay itself.

Verify (3a): every new test fails against unfixed Render (recorded),
passes after; `./tests/e2e.sh` green (restore byte stream changes are
behavior-compatible: resume/attach suites must stay green).
