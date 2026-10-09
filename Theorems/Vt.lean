module

public import Theorems.Vt.Parser
public import Theorems.Vt.Renderable
import all Theorems.Vt.Parser
import all Theorems.Vt.Renderable

/-! # VT reachability and stream boundaries

State bounds and frame lemmas support the independent parser and renderable-grid
invariants. This umbrella combines them into reachability and boundary guarantees;
`import all Theorems.Vt` continues to expose the sealed-field theorem interface.
-/

namespace Linger.Core.Vt

/-! ### §LiveReachable — the states a running session can actually hold

The predicate a replay theorem may assume: the least set containing a fresh
emulator and closed under the things a live session does to one — feed pty
bytes, resize on attach, forget partial parser state (what a checkpoint
save/load does), **and come off disk through the decoder's door**.

**The fifth rung arrived after finding R2** (SCRATCHPAD.md), and the earlier prose
here — "fidelity is claimed for these and not for an arbitrary decoded checkpoint,
which no theorem can vouch for" — was true when the door only decided `Good`. It is
not any more: `Vt.ofDecoded` now decides `Renderable` and the ruler as well, so
`ofDecoded_good`/`ofDecoded_renderable`/`ofDecoded_tabsOk` vouch for exactly the
three components the relation supplies, and `ofDecoded_u8Ok` for the fourth because
the door *fixes* `u8need := 0` and `u8acc := 0`.

The premise is the door's own conclusion (`Vt.ofDecoded … = some v`) and that is
load-bearing rather than stylistic. Step 3 measured a rung premised on `Good v`
**unsound**: `Good` implies neither the grid's shape nor a zeroed UTF-8
accumulator, so that rung broke `renderable_of_liveReachable` and
`u8Ok_of_liveReachable` — the two lemmas the relation exists to supply. Do not
re-derive that; the error texts are in the Step 3 record.

What the rung widens, deliberately: all four `*_of_liveReachable` lemmas now speak
of decoded states too, so every `Render.restore_*_reachable` theorem — whose
statements are unchanged — covers a receiver or a subject that came off disk, and
`Session.LiveVt` becomes provable for a **resumed** daemon
(`Session.liveVt_boot_of_load`, via `Checkpoint.load_live`). That last one is why
the rung was added at all: without it the resumed session's shape invariant travels
through `renderable_feed`/`renderable_resize` one operation at a time instead of
through one daemon-level theorem.

What it does **not** widen: nothing here says a ring row is the screen's width.
`Vt.resize` leaves the scrollback at its old width by design, so
`Render.restore_sb_exact`'s `hrok` is immovable by any amount of reachability — Step
3's measurement, and the reason the decoder deliberately does not validate the ring
either. -/

inductive LiveReachableVt : Vt → Prop where
  | init (cols rows : Nat) : LiveReachableVt (Vt.init cols rows)
  | feed {v : Vt} (h : LiveReachableVt v) (bytes : List UInt8) : LiveReachableVt (v.feed bytes)
  | resize {v : Vt} (h : LiveReachableVt v) (cols rows : Nat) : LiveReachableVt (v.resize cols rows)
  | quiesce {v : Vt} (h : LiveReachableVt v) : LiveReachableVt v.quiesce
  /-- **The resume rung.** A `Vt` the decoder's door accepted is one a live session can
  hold — not because the record on disk was trustworthy, but because the door refuses
  every record that does not describe such a state. The premise is `Vt.ofDecoded`'s own
  `some`, never `Good v`; see this section's docstring for why that distinction is the
  difference between sound and unsound. -/
  |
  ofDecoded {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen} {modes : Modes}
    {top bot : Nat} {tabs : Array Bool} {sb : Ring} {altGrid : Option (Array Row × Cursor × Pen)}
    {saved : Saved} {title : String} {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    LiveReachableVt v

/-- **The shape hypothesis, discharged.** Every state a live session can hold is
one the row painter can express — so the replay theorem needs no side condition
on the grid, and cannot be satisfied vacuously by excluding awkward states.

The `ofDecoded` arm is what widens this from "every state a fresh boot reaches" to
"every state the daemon can hold, resumed sessions included", and it is the arm a
`Good`-premised rung could not have closed (§LiveReachable's docstring). -/
theorem renderable_of_liveReachable {v : Vt} (h : LiveReachableVt v) : Renderable v := by
  induction h with
  | init c r => exact renderable_init c r
  | feed _ bytes ih => exact renderable_feed ih bytes
  | resize _ c r ih => exact renderable_resize ih c r
  | quiesce _ ih => exact renderable_quiesce ih
  | ofDecoded hd => exact ofDecoded_renderable hd

/-- …and `Good` likewise, so the two invariants travel together. -/
theorem good_of_liveReachable {v : Vt} (h : LiveReachableVt v) : Good v := by
  induction h with
  | init c r => exact good_init c r
  | feed _ bytes ih => exact Good.feed bytes ih
  | resize _ c r ih => exact Good.resize c r ih
  | quiesce _ ih => exact Good.set_ground (Good.set_u8 0 0 (by omega) ih)
  | ofDecoded hd => exact ofDecoded_good hd

/-- **The decoder invariant a live state carries.** Whenever no UTF-8 sequence is pending the
accumulator is zero — `stepGround` zeroes it on the byte that *completes* a sequence, and
`abortUtf8` zeroes it on the byte that abandons one. This is the precondition the grid claim
needs on its receiver and could not get from `Good` or `Renderable`: `Good` bounds `u8need`
but says nothing about `u8acc`. -/
def U8Ok (v : Vt) : Prop := v.u8need = 0 → v.u8acc = 0

theorem u8Ok_init (cols rows : Nat) : U8Ok (Vt.init cols rows) := fun _ => rfl

theorem u8Ok_stepGround {v : Vt} (b : UInt8) (h : U8Ok v) : U8Ok (v.stepGround b) := by
  intro hz
  unfold Vt.stepGround at hz ⊢
  by_cases h1 : (b == 0x1B) = true
  · rw [ite_eq_left h1] at hz ⊢; exact h hz
  rw [ite_eq_right h1] at hz ⊢
  by_cases h2 : b < 0x20
  · rw [ite_eq_left h2] at hz ⊢
    rw [ua_ctl]; rw [un_ctl] at hz; exact h hz
  rw [ite_eq_right h2] at hz ⊢
  by_cases hdel : (b == 0x7F) = true
  · rw [ite_eq_left hdel] at hz ⊢; exact h hz
  rw [ite_eq_right hdel] at hz ⊢
  by_cases h3 : b < 0x80
  · rw [ite_eq_left h3] at hz ⊢
    rw [ua_acceptChar]; rw [un_acceptChar] at hz; exact h hz
  rw [ite_eq_right h3] at hz ⊢
  by_cases h4 : b < 0xC0
  · rw [ite_eq_left h4] at hz ⊢
    dsimp only at hz ⊢
    by_cases h5 : (v.u8need == 0) = true
    · rw [ite_eq_left h5] at hz ⊢; exact h hz
    rw [ite_eq_right h5] at hz ⊢
    by_cases h6 : (v.u8need == 1) = true
    · rw [ite_eq_left h6] at hz ⊢
      rw [ua_acceptChar]
    · rw [ite_eq_right h6] at hz ⊢
      exfalso
      simp only [beq_iff_eq] at h5 h6
      simp only [] at hz
      omega
  rw [ite_eq_right h4] at hz ⊢
  by_cases h7 : b < 0xE0
  · rw [ite_eq_left h7] at hz ⊢; exact absurd hz (by simp)
  rw [ite_eq_right h7] at hz ⊢
  by_cases h8 : b < 0xF0
  · rw [ite_eq_left h8] at hz ⊢; exact absurd hz (by simp)
  rw [ite_eq_right h8] at hz ⊢
  by_cases h9 : b < 0xF8
  · rw [ite_eq_left h9] at hz ⊢; exact absurd hz (by simp)
  rw [ite_eq_right h9] at hz ⊢
  exact h hz

theorem u8Ok_step {v : Vt} (b : UInt8) (h : U8Ok v) : U8Ok (v.step b) := by
  have hab : U8Ok (v.abortUtf8 b) := by
    unfold Vt.abortUtf8
    split
    · intro _; rfl
    · exact h
  unfold Vt.step
  dsimp only
  split
  · exact u8Ok_stepGround _ hab
  all_goals
    ( intro hz
      first
      | (rw [ua_stepEscInter]; rw [un_stepEscInter] at hz; exact hab hz)
      | (rw [ua_stepCsi]; rw [un_stepCsi] at hz; exact hab hz)
      | (rw [ua_stepOsc]; rw [un_stepOsc] at hz; exact hab hz)
      | (rw [ua_stepStr]; rw [un_stepStr] at hz; exact hab hz)
      | ( rcases u8pair_stepEsc (v.abortUtf8 b) b with ⟨hn, ha⟩ | ⟨-, ha⟩
          · rw [ha];
            exact
              hab
                (by
                  rw [← hn]; exact hz)
          · exact ha))

theorem u8Ok_feed : ∀ (bs : List UInt8) {v : Vt}, U8Ok v → U8Ok (v.feed bs) := fun bs {v} h =>
  invariant_foldl U8Ok Vt.step (fun _ b hw => u8Ok_step b hw) bs v h

/-- **The fourth component the resume rung needs, and the only one the door does not
already claim.** `Vt.ofDecoded` *fixes* `u8need := 0` and `u8acc := 0` rather than
validating them — parser state is deliberately not persisted (`Checkpoint.wVt`), so there
is nothing on disk to check — which makes `U8Ok` immediate at the door.

This is also the component that makes the premise's shape matter. `Good` bounds `u8need`
and says nothing whatever about `u8acc`, so a rung premised on `Good v` cannot reach this
claim; Step 3 measured exactly that failure (`invalid ▸ notation, argument hg.u8Le has type
v.u8need ≤ 3, equality expected`). -/
theorem ofDecoded_u8Ok {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    U8Ok v := by
  unfold Vt.ofDecoded at h
  split at h
  · cases h
    intro _
    rfl
  · exact absurd h (by simp)

theorem u8Ok_of_liveReachable {v : Vt} (h : LiveReachableVt v) : U8Ok v := by
  induction h with
  | init c r => exact u8Ok_init c r
  | feed _ bytes ih => exact u8Ok_feed bytes ih
  | resize _ c r ih =>
    intro hz; rw [show (Vt.resize _ c r).u8acc = _ from rfl] at *; exact ih hz
  | quiesce _ _ =>
    intro _; rfl
  | ofDecoded hd => exact ofDecoded_u8Ok hd

/-- **…and the ruler, which is `specs/archive/vt-toolkit.md` Step 3's harvest.** The ruler
premise of `Render.restore_tabs_any` — `v.tabs.size = v.cols` — is a fact about every
state a live session can hold, so a caller with reachability discharges it here. Neither `Good` nor
`Renderable` implies it (the first bounds the dimensions, the second speaks of the
grid), which is why it needed the §Ruler layer of its own rather than a clause on
one of them.

Note the two rungs that could have broken it and do not: `resize` reinstalls
`defaultTabs` at the new width, and the `feed` rung covers `TBC 3`, which replaces
the whole array — the invariant is *re-established* there rather than preserved,
which is the shape `tabsOk_csiDispatch` records. The `ofDecoded` rung is a third
that could have: before finding R2 the door accepted a ruler of any length at all,
and `ofDecoded_tabsOk` is exactly the claim that closed it. -/
theorem tabsOk_of_liveReachable {v : Vt} (h : LiveReachableVt v) : TabsOk v := by
  induction h with
  | init c r => exact tabsOk_init c r
  | feed _ bytes ih => exact tabsOk_feed bytes ih
  | resize _ c r ih => exact tabsOk_resize _ c r
  | quiesce _ ih => exact tabsOk_quiesce ih
  | ofDecoded hd => exact ofDecoded_tabsOk hd

/-! ## Absolute vertical motion

VPA shares CUP's origin and clamp. Screen bounds alone would not catch a cursor
below `top` under DECOM; the exact result and region bounds below do. -/

theorem csiDispatch_vpa (v : Vt) (s : CsiState) :
    v.csiDispatch s 0x64 = if s.ignore then v else v.moveTo v.cursor.x (s.arg 0 1 - 1) := by rfl

/-- Only the cursor changes: its column is preserved, the row uses the current
origin, and pending wrap is cleared. No premise constrains the requested row. -/
theorem csiDispatch_vpa_exact {v : Vt} (h : Good v) (s : CsiState) (hi : s.ignore = false) :
    v.csiDispatch s 0x64 =
      { v with
        cursor :=
          { x := v.cursor.x,
            y :=
              min ((if v.modes.origin then v.top else 0) + (s.arg 0 1 - 1))
                (if v.modes.origin then v.bot else v.rows - 1),
            pending := false } } := by
  rw [csiDispatch_vpa]
  have hx : min v.cursor.x (v.cols - 1) = v.cursor.x :=
    Nat.min_eq_left
      (by
        have hc := h.curX
        omega)
  simp [hi, Vt.moveTo, hx]

/-- Even a source cursor outside the region is placed inside it by VPA under
DECOM. Requiring the source cursor to be inside would conceal the original bug. -/
theorem csiDispatch_vpa_in_region {v : Vt} (h : Good v) (s : CsiState) (hi : s.ignore = false)
    (ho : v.modes.origin = true) :
    v.top ≤ (v.csiDispatch s 0x64).cursor.y ∧ (v.csiDispatch s 0x64).cursor.y ≤ v.bot := by
  rw [csiDispatch_vpa_exact h s hi]
  simp only [ho, ↓reduceIte]
  have ht := h.topLe
  constructor <;> omega

/-! ## CSI collection — bounds and omitted parameters

`Good.csiLe` bounds the parameter count. Numeric bounds and the empty accumulator
need their own invariant: without the latter, treating an omitted field as zero
would only be an assumption about the parser's caller. The private parser stages
and the reachability proof below establish it for every byte stream, including
after a decoded checkpoint. The exact collection contracts also distinguish a
missing parameter from a dropped one; a frame alone would not catch that bug. -/

/-- Closing a field below the cap appends exactly one slot, including when no
digits preceded the separator, and resets the accumulator for the next field. -/
theorem csiPush_of_lt (s : CsiState) (sub : Bool) (h : s.params.size < 16) :
    csiPush s sub =
      { s with
        params := s.params.push (min s.cur 65535, s.curSub), cur := 0, curSub := sub,
        haveCur := false } := by
  unfold csiPush
  rw [ite_eq_right (by omega)]

/-- Overflow retains the collected fields but ignores the entire sequence. -/
theorem csiPush_of_ge (s : CsiState) (sub : Bool) (h : 16 ≤ s.params.size) :
    csiPush s sub =
      { s with
        ignore := true, cur := 0, haveCur := false } := by
  unfold csiPush
  rw [ite_eq_left h]

/-- A trailing separator creates an omitted final field; it cannot silently
disappear at dispatch. This matters for SGR, whose omitted field is a reset. -/
theorem csiFinish_omitted (v : Vt) (s : CsiState) (final : UInt8) (hh : s.haveCur = false)
    (hp : 0 < s.params.size) :
    v.csiFinish s final = { v.csiDispatch (csiPush s false) final with pstate := .ground } := by
  unfold Vt.csiFinish
  rw [ite_eq_right (by simp [hh])]
  split
  · rename_i he
    simp [Array.toList_eq_nil_iff.mp he] at hp
  · rfl

/-- Sixteen closed fields leave no room for the final field, whether explicit
or omitted. Dispatching the overflowing sequence changes only the parser state. -/
theorem csiFinish_overflow (v : Vt) (s : CsiState) (final : UInt8) (hp : 16 ≤ s.params.size) :
    v.csiFinish s final = { v with pstate := .ground } := by
  unfold Vt.csiFinish
  split
  · simp [Vt.csiDispatch]
  · split
    · rename_i he
      simp [Array.toList_eq_nil_iff.mp he] at hp
    · simp [csiPush_of_ge s false hp, Vt.csiDispatch]

/-- Numeric and omitted-value invariants; `Good.csiLe` separately bounds the count. -/
structure CsiValuesOk (s : CsiState) : Prop where
  curLe : s.cur ≤ 65535
  paramsLe : ∀ p ∈ s.params.toList, p.1 ≤ 65535
  emptyCur : s.haveCur = false → s.cur = 0

theorem csiValuesOk_empty : CsiValuesOk {} := by
  constructor
  · simp
  · simp
  · intro _; rfl

theorem csiValuesOk_push {s : CsiState} (h : CsiValuesOk s) (sub : Bool) :
    CsiValuesOk (csiPush s sub) := by
  by_cases hp : s.params.size < 16
  · rw [csiPush_of_lt s sub hp]
    constructor
    · simp
    · intro p hm
      simp only [Array.toList_push, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hm
      rcases hm with hm | rfl
      · exact h.paramsLe p hm
      · exact Nat.min_le_right _ _
    · intro _; rfl
  · rw [csiPush_of_ge s sub (by omega)]
    exact ⟨by simp, h.paramsLe, fun _ => rfl⟩

def CsiOk (v : Vt) : Prop := ∀ s, v.pstate = .csi s → CsiValuesOk s

theorem csiOk_of_pstate_eq {v w : Vt} (hp : v.pstate = w.pstate) (h : CsiOk w) : CsiOk v :=
  fun s hs => h s (hp.symm.trans hs)

theorem csiOk_set {v : Vt} {s : CsiState} (h : CsiValuesOk s) :
    CsiOk { v with pstate := .csi s } := by
  intro t ht
  cases ht
  exact h

theorem csiOk_init (cols rows : Nat) : CsiOk (Vt.init cols rows) := by simp [CsiOk, Vt.init]

theorem csiOk_stepGround {v : Vt} (h : CsiOk v) (b : UInt8) : CsiOk (v.stepGround b) := by
  by_cases hb : b = 0x1B
  · simp [CsiOk, Vt.stepGround, hb]
  · exact csiOk_of_pstate_eq (ps_stepGround v b hb) h

theorem csiOk_stepEsc {v : Vt} (h : CsiOk v) (b : UInt8) : CsiOk (v.stepEsc b) := by
  unfold Vt.stepEsc
  repeat' split
  all_goals
    with_reducible
      first
      | exact h
      | exact csiOk_set csiValuesOk_empty
      | simp [CsiOk, Vt.init]

theorem csiOk_stepEscInter (v : Vt) (i b : UInt8) : CsiOk (v.stepEscInter i b) := by
  unfold Vt.stepEscInter
  repeat' split
  all_goals simp [CsiOk]

theorem csiOk_stepCsi {v : Vt} {s : CsiState} (h : CsiOk v) (hs : CsiValuesOk s) (b : UInt8) :
    CsiOk (v.stepCsi s b) := by
  fun_cases Vt.stepCsi v s b
  · exact csiOk_set ⟨Nat.min_le_right _ _, hs.paramsLe, by simp⟩
  · exact csiOk_set (csiValuesOk_push hs false)
  · exact csiOk_set (csiValuesOk_push hs true)
  · exact csiOk_set ⟨hs.curLe, hs.paramsLe, hs.emptyCur⟩
  · exact csiOk_set ⟨hs.curLe, hs.paramsLe, hs.emptyCur⟩
  · simp [CsiOk]
  · simp [CsiOk, Vt.csiFinish]
  · simp [CsiOk]
  · exact h
  · exact csiOk_of_pstate_eq (ps_ctl v b) h
  · simp [CsiOk]

theorem csiOk_stepOsc (v : Vt) (acc : Array UInt8) (esc : Bool) (b : UInt8) :
    CsiOk (v.stepOsc acc esc b) := by
  unfold Vt.stepOsc
  repeat' split
  all_goals try (unfold Vt.oscFinish; dsimp only; repeat' split)
  all_goals simp [CsiOk]

theorem csiOk_stepStr (v : Vt) (esc : Bool) (b : UInt8) : CsiOk (v.stepStr esc b) := by
  unfold Vt.stepStr
  repeat' split
  all_goals simp [CsiOk]

theorem csiOk_step {v : Vt} (h : CsiOk v) (b : UInt8) : CsiOk (v.step b) := by
  have hab : CsiOk (v.abortUtf8 b) := csiOk_of_pstate_eq (ps_abortUtf8 v b) h
  unfold Vt.step
  dsimp only
  split
  · exact csiOk_stepGround hab b
  · exact csiOk_stepEsc hab b
  · exact csiOk_stepEscInter _ _ _
  · rename_i s hp
    exact csiOk_stepCsi hab (hab s hp) b
  · exact csiOk_stepOsc _ _ _ _
  · exact csiOk_stepStr _ _ _

theorem csiOk_feed : ∀ (bs : List UInt8) {v : Vt}, CsiOk v → CsiOk (v.feed bs) := fun bs {v} h =>
  invariant_foldl CsiOk Vt.step (fun _ b hw => csiOk_step hw b) bs v h

/-- The decoder starts in ground state, so it needs no new acceptance condition. -/
theorem ofDecoded_csiOk {cols rows : Nat} {grid : Array Row} {cursor : Cursor} {pen : Pen}
    {modes : Modes} {top bot : Nat} {tabs : Array Bool} {sb : Ring}
    {altGrid : Option (Array Row × Cursor × Pen)} {saved : Saved} {title : String}
    {g0Line g1Line shiftOut bell : Bool} {v : Vt}
    (h :
      Vt.ofDecoded cols rows grid cursor pen modes top bot tabs sb altGrid saved title g0Line g1Line
          shiftOut bell =
        some v) :
    CsiOk v := by
  unfold Vt.ofDecoded at h
  split at h
  · cases h
    simp [CsiOk]
  · exact absurd h (by simp)

/-- Every reachable CSI state has bounded values and a zero accumulator whenever
the current field is omitted. Arbitrary feeds, resize, quiesce and resume are covered. -/
theorem csiOk_of_liveReachable {v : Vt} (h : LiveReachableVt v) : CsiOk v := by
  induction h with
  | init c r => exact csiOk_init c r
  | feed _ bytes ih => exact csiOk_feed bytes ih
  | resize _ _ _ ih => exact ih
  | quiesce _ _ => simp [CsiOk, Vt.quiesce]
  | ofDecoded hd => exact ofDecoded_csiOk hd

/-- Omitted fields in a live parser contribute zero, rather than losing their
position or reusing the previous field's digits. -/
theorem csiPush_omitted_of_liveReachable {v : Vt} (h : LiveReachableVt v) {s : CsiState}
    (hp : v.pstate = .csi s) (hh : s.haveCur = false) (hs : s.params.size < 16) (sub : Bool) :
    (csiPush s sub).params = s.params.push (0, s.curSub) := by
  rw [csiPush_of_lt s sub hs]
  simp only [(csiOk_of_liveReachable h s hp).emptyCur hh, Nat.zero_min]

/-! ## §Restore — the sticky receiver state, as one bundled projection

This layer supplies `Render.restore`'s receiver-quantified value
claims: the state the stream **establishes and must then leave alone** outside
the grid, cursor, pen, modes and parser — the scroll region, the two charset
designations, the shift state, and which screen is current. Its preservation
claims use the frames and `off_print` above.

Bundling was the idea the frames note rejected ("fixes only the fields we
happened to need"), and the objection is answered rather than ignored: this
bundle is not a chosen subset but a *closed* one. `rows` rides along because two
of the transforms read it — `DECSTBM` clamps against it, and the alt switch
resets the region to it — so a bundle without `rows` would not be closed under
its own transforms. Everything else the stream writes already has a layer.

The transforms are named (`stAlt`, `stStbm`, `stCharset`, `stSetMode`) so the
`Render` ladder composes them the way `MMap` composes `Modes` transforms. -/

/-- The receiver fields `restore` establishes and then must not disturb. -/
structure Sticky where
  rows : Nat
  top : Nat
  bot : Nat
  g0 : Bool
  g1 : Bool
  so : Bool
  alt : Bool

def stick (v : Vt) : Sticky :=
  { rows := v.rows, top := v.top, bot := v.bot, g0 := v.g0Line, g1 := v.g1Line, so := v.shiftOut,
    alt := v.altGrid.isSome }

/-! The projections, as rewrite rules. `rfl` for a *variable* receiver, which is
what keeps the field corollaries in `Render` from asking the elaborator to whnf a
whole restore stream. -/

theorem stick_rows (u : Vt) : (stick u).rows = u.rows := by rfl

theorem stick_top (u : Vt) : (stick u).top = u.top := by rfl

theorem stick_bot (u : Vt) : (stick u).bot = u.bot := by rfl

theorem stick_g0 (u : Vt) : (stick u).g0 = u.g0Line := by rfl

theorem stick_g1 (u : Vt) : (stick u).g1 = u.g1Line := by rfl

theorem stick_so (u : Vt) : (stick u).so = u.shiftOut := by rfl

theorem stick_alt (u : Vt) : (stick u).alt = u.altGrid.isSome := by rfl

/-! ### The framed operations: one `rw` each, every field at once -/

theorem stick_moveTo (v : Vt) (x y : Nat) : stick (v.moveTo x y) = stick v := by
  rw [frame_moveTo]; rfl

theorem stick_setCol (v : Vt) (x : Nat) : stick (v.setCol x) = stick v := by
  rw [frame_setCol]; rfl

theorem stick_backspace (v : Vt) : stick v.backspace = stick v := by
  rw [frame_backspace]; rfl

theorem stick_lineFeed (v : Vt) : stick v.lineFeed = stick v := by
  rw [frame_lineFeed]; rfl

/-- **A line feed below the region bottom just moves the cursor down.** Its only scrolling
consumer is the `cursor.y == bot` branch, and `y < bot` rules that out — the grid, and every
row, is left exactly as it was. This is the no-scroll fact the grid walk turns each `CRLF`
on. -/
theorem lineFeed_interior (v : Vt) (hy : v.cursor.y < v.bot) (hlt : v.bot < v.rows) :
    v.lineFeed =
      { v with
        cursor :=
          { v.cursor with
            y := v.cursor.y + 1, pending := false } } := by
  unfold Vt.lineFeed Vt.clearPending
  dsimp only
  rw [ite_eq_right
      (show ¬(v.cursor.y == v.bot) = true from by
        simp; omega),
    ite_eq_left (show v.cursor.y + 1 < v.rows from by omega)]

/-! ### The positive scroll specification

The frames above say what `scrollUpIn` leaves **alone**. These say what it **writes** —
the gap §Total names in its own words ("a frame says what an operation leaves alone,
never what the written fields *become*"), closed for the one operation the scrollback
story rests on.

The fold is tractable for exactly one reason: it reads `v.getRow`, never the accumulator
it is building (`Linger/Core/Vt.lean`, `Vt.scrollUpIn`), so the writes are independent and
one pointwise characterization covers all of them. `getD_foldl_setRange` is that
characterization, stated over an arbitrary source function so nothing in it depends on the
values being rows. Same shape as `foldl_setTab_mem`/`_not_mem` over the tab ruler. -/

theorem size_foldl_setRange {α} [Inhabited α] (f : Nat → α) (top : Nat) :
    ∀ (n : Nat) (a : Array α),
      ((List.range n).foldl (fun b i => b.setIfInBounds (top + i) (f i)) a).size = a.size
  | 0, _ => rfl
  | n + 1, a => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [Array.size_setIfInBounds, size_foldl_setRange f top n a]

/-- **The write lands**: index `top + i` holds the `i`-th source value. The later writes
are at strictly larger indices, so they cannot disturb it. -/
theorem getD_foldl_setRange {α} [Inhabited α] (f : Nat → α) (top : Nat) (d : α) :
    ∀ (n : Nat) (a : Array α) (i : Nat),
      i < n →
        top + i < a.size →
        ((List.range n).foldl (fun b k => b.setIfInBounds (top + k) (f k)) a).getD (top + i) d = f i
  | 0, _, _, hi, _ => absurd hi (by omega)
  | n + 1, a, i, hi, hlt => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rcases Nat.lt_or_ge i n with h | h
    · rw [getD_set_ne _ (top + n) (top + i) (f n) d (by omega)]
      exact getD_foldl_setRange f top d n a i h hlt
    · have hin : i = n := by omega
      subst hin
      exact
        getD_set_self _ (top + i) (f i) d
          (by
            rw [size_foldl_setRange]; exact hlt)

/-- …and every index the fold never writes keeps what it had. -/
theorem getD_foldl_setRange_of_ne {α} [Inhabited α] (f : Nat → α) (top : Nat) (d : α) :
    ∀ (n : Nat) (a : Array α) (j : Nat),
      (∀ i, i < n → j ≠ top + i) →
        ((List.range n).foldl (fun b k => b.setIfInBounds (top + k) (f k)) a).getD j d = a.getD j d
  | 0, _, _, _ => rfl
  | n + 1, a, j, h => by
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [getD_set_ne _ (top + n) j (f n) d (h n (by omega))]
    exact getD_foldl_setRange_of_ne f top d n a j fun i hi => h i (by omega)

/-- The two branches of `scrollUpIn` differ only in `sb`, so its grid is one term. -/
theorem grid_scrollUpIn (v : Vt) (top bot : Nat) (a : Bool) :
    (v.scrollUpIn top bot a).grid =
      ((List.range (bot - top)).foldl
            (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1))) v.grid).setIfInBounds
        bot (blankRow v.cols v.pen) := by
  unfold Vt.scrollUpIn
  dsimp only
  split <;> rfl

/-- **What a scroll writes.** Row `y'` inside the region becomes the row below it, the
vacated bottom row is blank **in the pen currently in effect** (stated, not hidden — a
coloured session scrolls up a coloured blank), and everything outside the region is
untouched.

`top ≤ bot` is load-bearing for the third conjunct and nothing else: with an inverted
region `bot - top` is `0`, so the fold is empty and the blank write at `bot` is the only
one — and it lands *outside* `[top, bot]`, which would make "outside is untouched" false
at `y' = bot`. `Good.topLe` is where every caller gets it. -/
theorem scrollUpIn_rows (v : Vt) (top bot : Nat) (a : Bool) (htb : top ≤ bot)
    (hbot : bot < v.grid.size) :
    (∀ y', top ≤ y' → y' < bot → (v.scrollUpIn top bot a).getRow y' = v.getRow (y' + 1)) ∧
      (v.scrollUpIn top bot a).getRow bot = blankRow v.cols v.pen ∧
      ∀ y', (y' < top ∨ bot < y') → (v.scrollUpIn top bot a).getRow y' = v.getRow y' := by
  have hrow :
    ∀ y',
      (v.scrollUpIn top bot a).getRow y' =
        (((List.range (bot - top)).foldl
                  (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1)))
                  v.grid).setIfInBounds
              bot (blankRow v.cols v.pen)).getD
          y' (blankRow v.cols v.pen) := by
    intro y'
    show
      (v.scrollUpIn top bot a).grid.getD y'
          (blankRow (v.scrollUpIn top bot a).cols (v.scrollUpIn top bot a).pen) =
        _
    rw [show (v.scrollUpIn top bot a).cols = v.cols from by rw [frame_scrollUpIn],
      show (v.scrollUpIn top bot a).pen = v.pen from by rw [frame_scrollUpIn], grid_scrollUpIn]
  refine ⟨fun y' hle hlt => ?_, ?_, fun y' hne => ?_⟩
  · rw [hrow y', getD_set_ne _ bot y' _ _ (by omega)]
    rw [show y' = top + (y' - top) from by omega]
    exact
      getD_foldl_setRange _ top _ (bot - top) v.grid (y' - top) (by omega)
        (by
          rw [show top + (y' - top) = y' from by omega]; omega)
  · rw [hrow bot,
      getD_set_self _ bot _ _
        (by
          rw [size_foldl_setRange]; exact hbot)]
  · rw [hrow y', getD_set_ne _ bot y' _ _ (by rcases hne with h | h <;> omega),
      getD_foldl_setRange_of_ne _ top _ (bot - top) v.grid y'
        (fun i hi => by rcases hne with h | h <;> omega)]
    unfold Vt.getRow
    rfl

/-- **What a scroll pushes**: the evicted top row, once, when the region is the whole
screen and the alt screen is not up. The `getRow 0` is the row the guard's `top = 0`
makes it. -/
theorem scrollUpIn_sb_push (v : Vt) (bot : Nat) (hbot : bot = v.rows - 1)
    (halt : v.altGrid = none) : (v.scrollUpIn 0 bot true).sb = v.sb.push (v.getRow 0) := by
  unfold Vt.scrollUpIn
  dsimp only
  rw [ite_eq_left
      (show (true && (0 : Nat) == 0 && bot == v.rows - 1 && v.altGrid.isNone) = true from by
        simp [hbot, halt])]

/-- **A line feed at the region bottom scrolls**: `lineFeed_interior`'s twin, and the
bridge Step 3's `crlf_scroll_step` composes with the two theorems above. -/
theorem lineFeed_scroll (v : Vt) (hy : v.cursor.y = v.bot) :
    v.lineFeed = v.clearPending.scrollUp := by
  unfold Vt.lineFeed
  dsimp only
  rw [ite_eq_left
      (show (v.clearPending.cursor.y == v.clearPending.bot) = true from by
        simp [Vt.clearPending, hy])]

/-! ### The ring, below the cap

The receiver's ring is empty when `restore` starts pushing (`ED 3`) and the pushed run is
capped by `sbTake`, so the wrap branch is unreachable on the replay path. These are the
three facts that let a push be read as an append. -/

/-- Below the cap a push is an append, and the oldest index does not move. -/
theorem ring_push_data {r : Ring} (row : Row) (h : r.data.size < sbCap) :
    (r.push row).data = r.data.push row ∧ (r.push row).start = r.start := by
  unfold Ring.push
  rw [ite_eq_left h]
  exact ⟨rfl, rfl⟩

/-- A ring that never wrapped reads back as its own array, oldest first. -/
theorem ring_toList_of_start_zero {r : Ring} (h : r.start = 0) : r.toList = r.data.toList := by
  unfold Ring.toList
  rw [h]
  simp

/-- One `take` step, which is how the walk grows the expected history by a row. -/
theorem take_succ_getD {α} [Inhabited α] (l : List α) (n : Nat) (h : n < l.length) :
    l.take (n + 1) = l.take n ++ [l.getD n default] := by
  rw [List.take_add_one, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

theorem stick_reverseIndex (v : Vt) : stick v.reverseIndex = stick v := by
  rw [frame_reverseIndex]; rfl

theorem stick_applySgr (v : Vt) (ps : List (Nat × Bool)) : stick (v.applySgr ps) = stick v := by
  rw [frame_applySgr]; rfl

theorem stick_oscFinish (v : Vt) (acc : Array UInt8) : stick (v.oscFinish acc) = stick v := by
  rw [frame_oscFinish]; rfl

theorem stick_abortUtf8 (v : Vt) (b : UInt8) : stick (v.abortUtf8 b) = stick v := by
  unfold Vt.abortUtf8; split <;> rfl

theorem stick_eraseScreen (v : Vt) (m : Nat) : stick (v.eraseScreen m) = stick v := by
  rw [frame_eraseScreen]
  rfl

/-- With both charsets ASCII, `printChar` is the identity on anything the painter
emits — `safeChar` and `printableChar` agree on a non-control codepoint. -/
theorem printChar_id_of_ascii {v : Vt} (hg0 : v.g0Line = false) (hg1 : v.g1Line = false) {c : Char}
    (h20 : 0x20 ≤ c.toNat) (h7 : c.toNat ≠ 0x7F) : v.printChar c = c := by
  unfold Vt.printChar printableChar
  rw [show ((v.shiftOut && v.g1Line) || (!v.shiftOut && v.g0Line)) = false from by
      rw [hg0, hg1]; cases v.shiftOut <;> rfl]
  rw [show (if (false : Bool) = true then decLine c else c) = c from rfl]
  rw [ite_eq_right
      (by
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
        omega)]

/-! #### Where the cursor goes

`print_narrow_eq` and its siblings say what a print *writes*; the row induction also
needs where it leaves the cursor, because `hpend : cursor.pending = false` is a
hypothesis of all three and has to be re-established for column `k+1`. The margin
case is the interesting one and it is why `pending` is in the invariant at all: at
the right margin `printAdvance` clamps the column and arms wrap-pending, so the last
cell of a row leaves a state no absolute cursor move can express. -/

theorem off_putCell (v : Vt) (x y : Nat) (c : Cell) :
    offScreen (v.putCell x y c) = offScreen v := by
  rw [frame_putCell]; rfl

theorem off_mendRow (v : Vt) (y : Nat) : offScreen (v.mendRow y) = offScreen v := by
  rw [frame_mendRow]; rfl

theorem cursor_putCell (v : Vt) (x y : Nat) (c : Cell) : (v.putCell x y c).cursor = v.cursor := by
  rw [frame_putCell]

theorem cursor_mendRow (v : Vt) (y : Nat) : (v.mendRow y).cursor = v.cursor := by rw [frame_mendRow]

theorem cursor_printAdvance_lt (v : Vt) (n : Nat) (h : v.cursor.x + n < v.cols) :
    (v.printAdvance n).cursor =
      { v.cursor with
        x := v.cursor.x + n, pending := false } := by
  unfold Vt.printAdvance
  rw [ite_eq_right (by omega)]

theorem cursor_printAdvance_ge (v : Vt) (n : Nat) (h : v.cols ≤ v.cursor.x + n) :
    (v.printAdvance n).cursor =
      { v.cursor with
        x := v.cols - 1, pending := v.modes.wrap } := by
  unfold Vt.printAdvance
  rw [ite_eq_left (by omega)]

/-- The three facts `printAdvance` needs about the state a cell write leaves, as one
lemma: a write touches only the grid, so the cursor is the `clearPending` one and the
columns and modes are `v`'s. -/
private theorem write_frame (v : Vt) (f : Vt → Vt)
    (hf : ∀ u : Vt, offScreen (f u) = offScreen u ∧ (f u).cursor = u.cursor) :
    (f v.clearPending).cursor = { v.cursor with pending := false } ∧
      (f v.clearPending).cols = v.cols ∧ (f v.clearPending).modes = v.modes := by
  obtain ⟨ho, hc⟩ := hf v.clearPending
  exact
    ⟨by
      rw [hc]; rfl, congrArg OffScreen.cols ho, congrArg OffScreen.modes ho⟩

theorem cursor_print_narrow_fits {v : Vt} {ch : Char} (hpc : v.printChar ch = ch)
    (hw : charWidth ch = 1) (hins : v.modes.insert = false) (hpend : v.cursor.pending = false)
    (hfit : v.cursor.x + 1 < v.cols) :
    (v.print ch).cursor =
      { v.cursor with
        x := v.cursor.x + 1, pending := false } := by
  rw [print_narrow_eq hpc hw hins hpend]
  obtain ⟨hcur, hcol, -⟩ :=
    write_frame v
      (fun u =>
        (u.putCell v.cursor.x v.cursor.y
              { base := ch, marks := [], width := 1, pen := v.pen }).mendRow
          v.cursor.y)
      (fun u =>
        ⟨(off_mendRow _ _).trans (off_putCell _ _ _ _),
          (cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_lt _ 1
      (by
        rw [hcur, hcol]; exact hfit),
    hcur]

theorem cursor_print_narrow_margin {v : Vt} {ch : Char} (hpc : v.printChar ch = ch)
    (hw : charWidth ch = 1) (hins : v.modes.insert = false) (hpend : v.cursor.pending = false)
    (hmar : v.cols ≤ v.cursor.x + 1) :
    (v.print ch).cursor =
      { v.cursor with
        x := v.cols - 1, pending := v.modes.wrap } := by
  rw [print_narrow_eq hpc hw hins hpend]
  obtain ⟨hcur, hcol, hmod⟩ :=
    write_frame v
      (fun u =>
        (u.putCell v.cursor.x v.cursor.y
              { base := ch, marks := [], width := 1, pen := v.pen }).mendRow
          v.cursor.y)
      (fun u =>
        ⟨(off_mendRow _ _).trans (off_putCell _ _ _ _),
          (cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_ge _ 1
      (by
        rw [hcur, hcol]; exact hmar),
    hcur, hcol, hmod]

theorem cursor_print_wide_fits {v : Vt} {ch : Char} (hpc : v.printChar ch = ch)
    (hw : charWidth ch = 2) (hins : v.modes.insert = false) (hpend : v.cursor.pending = false)
    (hfit : v.cursor.x + 1 < v.cols) (hfit2 : v.cursor.x + 2 < v.cols) :
    (v.print ch).cursor =
      { v.cursor with
        x := v.cursor.x + 2, pending := false } := by
  rw [print_wide_eq hpc hw hins hpend hfit]
  obtain ⟨hcur, hcol, -⟩ :=
    write_frame v
      (fun u =>
        ((u.putCell v.cursor.x v.cursor.y
                  { base := ch, marks := [], width := 2, pen := v.pen }).putCell
              (v.cursor.x + 1) v.cursor.y
              (Cell.shadow { base := ch, marks := [], width := 2, pen := v.pen })).mendRow
          v.cursor.y)
      (fun u =>
        ⟨((off_mendRow _ _).trans (off_putCell _ _ _ _)).trans (off_putCell _ _ _ _),
          ((cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_lt _ 2
      (by
        rw [hcur, hcol]; exact hfit2),
    hcur]

/-- The pair that ends exactly at the margin: the shadow occupies the last column, so
the advance clamps and arms wrap-pending — the state the spec's negative result says
is load-bearing. -/
theorem cursor_print_wide_margin {v : Vt} {ch : Char} (hpc : v.printChar ch = ch)
    (hw : charWidth ch = 2) (hins : v.modes.insert = false) (hpend : v.cursor.pending = false)
    (hfit : v.cursor.x + 1 < v.cols) (hmar : v.cols ≤ v.cursor.x + 2) :
    (v.print ch).cursor =
      { v.cursor with
        x := v.cols - 1, pending := v.modes.wrap } := by
  rw [print_wide_eq hpc hw hins hpend hfit]
  obtain ⟨hcur, hcol, hmod⟩ :=
    write_frame v
      (fun u =>
        ((u.putCell v.cursor.x v.cursor.y
                  { base := ch, marks := [], width := 2, pen := v.pen }).putCell
              (v.cursor.x + 1) v.cursor.y
              (Cell.shadow { base := ch, marks := [], width := 2, pen := v.pen })).mendRow
          v.cursor.y)
      (fun u =>
        ⟨((off_mendRow _ _).trans (off_putCell _ _ _ _)).trans (off_putCell _ _ _ _),
          ((cursor_mendRow _ _).trans (cursor_putCell _ _ _ _)).trans (cursor_putCell _ _ _ _)⟩)
  rw [cursor_printAdvance_ge _ 2
      (by
        rw [hcur, hcol]; exact hmar),
    hcur, hcol, hmod]

/-- A combining mark moves nothing: `print_mark_eq` is a write and a mend. -/
theorem cursor_print_mark {v : Vt} {m : Char} (hpc : v.printChar m = m) (hw : charWidth m = 0)
    (hpend : v.cursor.pending = false) (hnw : (v.getCell (v.cursor.x - 1) v.cursor.y).width ≠ 0)
    (hcap : (v.getCell (v.cursor.x - 1) v.cursor.y).marks.length < 8) :
    (v.print m).cursor = v.cursor := by
  rw [print_mark_eq hpc hw hpend hnw hcap, cursor_mendRow, cursor_putCell]

/-- …and it does not *disarm* wrap-pending either, which is what lets a run of marks on
a final-column glyph all land on the same cell. -/
theorem cursor_print_mark_pending {v : Vt} {m : Char} (hpc : v.printChar m = m)
    (hw : charWidth m = 0) (hpend : v.cursor.pending = true)
    (hnw : (v.getCell v.cursor.x v.cursor.y).width ≠ 0)
    (hcap : (v.getCell v.cursor.x v.cursor.y).marks.length < 8) :
    (v.print m).cursor = v.cursor := by
  rw [print_mark_pending_eq hpc hw hpend hnw hcap, cursor_mendRow, cursor_putCell]

/-! ### Sticky projections of a print

The complete print projects `off_print`. -/

/-- Printing a glyph cannot move the region, the charsets, the shift state or the
screen selection — it *reads* the charsets (`printChar` translates) and reads the
screen selection (a full-screen scroll goes to scrollback only on main), and
writes neither. -/
theorem stick_print (v : Vt) (ch : Char) : stick (v.print ch) = stick v :=
  congrArg (fun s => Sticky.mk s.rows s.top s.bot s.g0 s.g1 s.so s.alt.isSome) (off_print v ch)

theorem stick_acceptChar (v : Vt) (n : Nat) : stick (v.acceptChar n) = stick v := by
  unfold Vt.acceptChar; split <;> exact stick_print _ _

/-- `SO`/`SI` are the two C0 bytes that write a sticky field, so they are the two
excluded here — the reason `Render.charsetAnsi`'s shift state needs a claim of
its own and the rest of the stream can be transparent to it. -/
theorem stick_ctl (v : Vt) (b : UInt8) (h1 : b ≠ 0x0E) (h2 : b ≠ 0x0F) :
    stick (v.ctl b) = stick v := by
  unfold Vt.ctl
  split
  all_goals
    first
    | rfl
    | exact stick_backspace _
    | exact stick_lineFeed _
    | exact absurd rfl h1
    | exact absurd rfl h2

theorem stick_stepGround (v : Vt) (b : UInt8) (h1 : b ≠ 0x0E) (h2 : b ≠ 0x0F) :
    stick (v.stepGround b) = stick v := by
  fun_cases Vt.stepGround v b
  all_goals
    first
    | exact stick_acceptChar _ _
    | exact stick_ctl _ _ h1 h2
    | rfl

/-! ### The transforms — the four things in a restore stream that DO write a
sticky field. Named, so the `Render` ladder composes them the way `MMap`
composes `Modes` transforms, and so "what can move this field" is a list. -/

/-- `?1049 h`/`l` (also `?47`, `?1047`): the screen switch, which resets the
region as a side effect. Mirrors `enterAlt`/`leaveAlt` including their
idempotence — which is why `alt` has to be *in* the bundle and not just an
output of it. -/
def stAlt (on : Bool) (s : Sticky) : Sticky :=
  match on with
  | true =>
    if s.alt then s
    else
      { s with
        alt := true, top := 0, bot := s.rows - 1 }
  | false =>
    if s.alt then
      { s with
        alt := false, top := 0, bot := s.rows - 1 }
    else s

/-- `CSI t ; b r` (DECSTBM), on the arguments after defaults and the 1-based
decrement — including the receiver-side refusal of a region of fewer than two
lines or one that does not fit, which is why `rows` is in the bundle. -/
def stStbm (t bo : Nat) (s : Sticky) : Sticky :=
  if t < bo && bo < s.rows then
    { s with
      top := t, bot := bo }
  else s

/-- `ESC ( x` / `ESC ) x`: a charset designation. -/
def stCharset (i x : UInt8) (s : Sticky) : Sticky :=
  if i == 0x28 then { s with g0 := x == 0x30 }
  else if i == 0x29 then { s with g1 := x == 0x30 } else s

/-- `SM`/`RM`: of the fourteen modes `setMode` knows, only the three
screen-switch numbers reach a sticky field. -/
def stSetMode (n : Nat) (on : Bool) (s : Sticky) : Sticky :=
  if n == 47 || n == 1047 || n == 1049 then stAlt on s else s

/-! The transforms' own arithmetic, so the value chain in `Render` can be a
sequence of rewrites rather than one giant `rfl`. -/

theorem stAlt_rows (on : Bool) (s : Sticky) : (stAlt on s).rows = s.rows := by
  unfold stAlt; cases on <;> (dsimp only; split <;> rfl)

theorem stAlt_alt (on : Bool) (s : Sticky) : (stAlt on s).alt = on := by
  unfold stAlt
  cases on
  · dsimp only
    split
    · rfl
    · rename_i h; simpa using h
  · dsimp only
    split
    · rename_i h; exact h
    · rfl

/-- `DECSTBM` accepted: the receiver-side guard is exactly "at least two rows and
it fits". -/
theorem stStbm_of {t bo : Nat} {s : Sticky} (h1 : t < bo) (h2 : bo < s.rows) :
    stStbm t bo s =
      { s with
        top := t, bot := bo } := by
  unfold stStbm; rw [ite_eq_left (by simp [h1, h2])]

theorem stick_enterAlt (v : Vt) (b : Bool) : stick (v.enterAlt b) = stAlt true (stick v) := by
  unfold Vt.enterAlt stAlt
  dsimp only
  by_cases h : v.altGrid.isSome = true
  · rw [ite_eq_left h, ite_eq_left (show (stick v).alt = true from h)]
  · rw [ite_eq_right h, ite_eq_right (show ¬((stick v).alt = true) from h)]
    rfl

theorem stick_leaveAlt (v : Vt) (b : Bool) : stick (v.leaveAlt b) = stAlt false (stick v) := by
  unfold Vt.leaveAlt stAlt
  dsimp only
  rcases hv : v.altGrid with - | x
  · rw [ite_eq_right
        (show ¬((stick v).alt = true) from by
          show ¬(v.altGrid.isSome = true); rw [hv]; simp)]
  · rw [ite_eq_left
        (show (stick v).alt = true from by
          show v.altGrid.isSome = true; rw [hv]; simp)]
    rfl

theorem stick_stepEscInter (v : Vt) (i x : UInt8) (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) :
    stick (v.stepEscInter i x) = stCharset i x (stick v) := by
  rw [stepEscInter_final v i x hlo hhi]
  unfold stCharset
  by_cases h28 : (i == 0x28) = true
  · rw [ite_eq_left h28, ite_eq_left h28]; rfl
  · rw [ite_eq_right h28, ite_eq_right h28]
    by_cases h29 : (i == 0x29) = true
    · rw [ite_eq_left h29, ite_eq_left h29]; rfl
    · rw [ite_eq_right h29, ite_eq_right h29]
      rfl

theorem stick_setMode (v : Vt) (n : Nat) (on : Bool) :
    stick (v.setMode true n on) = stSetMode n on (stick v) := by
  unfold stSetMode
  by_cases h : (n == 47 || n == 1047 || n == 1049) = true
  · rw [ite_eq_left h]
    simp only [Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (rfl | rfl) | rfl <;> cases on <;>
      first
      | exact stick_leaveAlt v _
      | exact stick_enterAlt v _
  · -- every remaining arm writes `modes`, the cursor or the saved slot only
    rw [ite_eq_right h]
    fun_cases Vt.setMode v true n on
    all_goals
      first
      | rfl
      | exact stick_moveTo _ _ _
      | (split <;> rfl)
      | (exfalso; simp_all)

/-- IRM is the only non-private mode we parse, and it is `modes`-only. -/
theorem stick_setMode_plain (v : Vt) (n : Nat) (on : Bool) :
    stick (v.setMode false n on) = stick v := by
  unfold Vt.setMode
  split <;> rename_i hpv
  · exact absurd hpv (by decide)
  · split <;> rfl

/-! ### Conditional sticky preservation through `csiDispatch`

One case-bash over every final byte, so that a new sequence in the emitter cannot
quietly acquire a sticky effect: the three finals that *can* have one are
hypotheses, not omissions. -/

/-- `SM` applies all parameters in order, as a state equation including every
mode's side effects. A first-parameter equation would discard requested modes. -/
theorem csiDispatch_sm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    v.csiDispatch s 0x68 = v.setModes (s.priv == 0x3F) s.params.toList true := by
  unfold Vt.csiDispatch;
  rw [ite_eq_right
      (by
        rw [hi]; simp)];
  rfl

theorem csiDispatch_rm (v : Vt) (s : CsiState) (hi : s.ignore = false) :
    v.csiDispatch s 0x6C = v.setModes (s.priv == 0x3F) s.params.toList false := by
  unfold Vt.csiDispatch;
  rw [ite_eq_right
      (by
        rw [hi]; simp)];
  rfl

/-- Single-mode emitters recover their exact old state equation from the full
parameter list, not just from a fact about its first element. -/
theorem csiDispatch_sm_one (v : Vt) (s : CsiState) (n : Nat) (sub : Bool) (hi : s.ignore = false)
    (hp : s.params = #[(n, sub)]) : v.csiDispatch s 0x68 = v.setMode (s.priv == 0x3F) n true := by
  rw [csiDispatch_sm v s hi, hp]
  exact setModes_one v _ n sub true

theorem csiDispatch_rm_one (v : Vt) (s : CsiState) (n : Nat) (sub : Bool) (hi : s.ignore = false)
    (hp : s.params = #[(n, sub)]) : v.csiDispatch s 0x6C = v.setMode (s.priv == 0x3F) n false := by
  rw [csiDispatch_rm v s hi, hp]
  exact setModes_one v _ n sub false

/-- `DECSTBM`, likewise as a state equation. -/
theorem csiDispatch_stbm (v : Vt) (s : CsiState) (hi : s.ignore = false) (hp : s.priv = 0) :
    v.csiDispatch s 0x72 =
      (if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows then
        ({ v with
              top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 }).moveTo
          0 0
      else v) := by
  unfold Vt.csiDispatch
  rw [ite_eq_right
      (by
        rw [hi]; simp)]
  show
    (if s.priv != 0 then v
      else
        if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows then
          ({ v with
                top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 }).moveTo
            0 0
        else v) =
      _
  rw [ite_eq_right
      (by
        rw [hp]; simp)]

theorem stick_csiDispatch_stbm (v : Vt) (s : CsiState) (hi : s.ignore = false) (hp : s.priv = 0) :
    stick (v.csiDispatch s 0x72) = stStbm (s.arg 0 1 - 1) (s.arg 1 v.rows - 1) (stick v) := by
  have hst :
    stStbm (s.arg 0 1 - 1) (s.arg 1 v.rows - 1) (stick v) =
      (if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows then
        { stick v with
          top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 }
      else stick v) := by
    rfl
  rw [csiDispatch_stbm v s hi hp, hst]
  split
  · exact stick_moveTo _ 0 0
  · rfl

/-! #### The preservers, one per final byte the emitters use

Per-final rather than one bash over all thirty: the tail walk
(`Render.csi_tail_proj`) takes the dispatch fact as a *hypothesis*, and every
sequence linger emits has a concrete final byte, so a 30-way case split with a
variable scrutinee would be work nobody needs. The same shape as
`modes_csiDispatch_{cup,sgr,stbm}`. -/

theorem stick_csiDispatch_cup (v : Vt) (s : CsiState) : stick (v.csiDispatch s 0x48) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact stick_moveTo _ _ _

theorem stick_csiDispatch_cha (v : Vt) (s : CsiState) : stick (v.csiDispatch s 0x47) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact stick_setCol _ _

theorem stick_csiDispatch_sgr (v : Vt) (s : CsiState) : stick (v.csiDispatch s 0x6D) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right (by simp [hi])]
    show stick (if s.priv == 0 then v.applySgr s.params.toList else v) = _
    split
    · exact stick_applySgr _ _
    · rfl

theorem stick_csiDispatch_ed (v : Vt) (s : CsiState) : stick (v.csiDispatch s 0x4A) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch; rw [ite_eq_right (by simp [hi])]; exact stick_eraseScreen _ _

theorem stick_csiDispatch_tbc (v : Vt) (s : CsiState) : stick (v.csiDispatch s 0x67) = stick v := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right (by simp [hi])]
    show
      stick
          (match s.arg 0 0 with
          | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
          | 3 => { v with tabs := Array.replicate v.cols false }
          | _ => v) =
        _
    split <;> rfl

/-! ### The remaining parser states -/

theorem stick_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    stick (v.stepOsc acc e b) = stick v := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    first
    | exact stick_oscFinish _ _
    | rfl

/-- `RIS` (`ESC c`) is the one escape that resets everything, and no linger
stream emits it. -/
theorem stick_stepEsc (v : Vt) (b : UInt8) (h : b ≠ 0x63) : stick (v.stepEsc b) = stick v := by
  unfold Vt.stepEsc
  split
  all_goals
    first
    | rfl
    | exact stick_lineFeed _
    | exact stick_reverseIndex _
    | exact absurd rfl h
    | ( repeat' split
        all_goals rfl)

/-! ### `step`, one lemma per incoming parser state

Each is the `stick` analog of `ground_step` / `org_step_of_*`: `abortUtf8` cannot
move a sticky field (it drops pending UTF-8 and nothing else), so the incoming
state selects the arm and the arm's lemma finishes it. -/

theorem stick_step_of_ground {v : Vt} (b : UInt8) (hg : v.pstate = .ground) (h1 : b ≠ 0x0E)
    (h2 : b ≠ 0x0F) : stick (v.step b) = stick v := by
  rw [step_of_ground b hg]
  exact (stick_stepGround _ b h1 h2).trans (stick_abortUtf8 v b)

theorem stick_step_of_esc {v : Vt} (b : UInt8) (hg : v.pstate = .esc) (h : b ≠ 0x63) :
    stick (v.step b) = stick v := by
  rw [step_of_esc b hg]
  exact (stick_stepEsc _ b h).trans (stick_abortUtf8 v b)

theorem stick_step_of_osc {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) : stick (v.step b) = stick v := by
  rw [step_of_osc b hg]
  exact (stick_stepOsc _ acc e b).trans (stick_abortUtf8 v b)

theorem stick_step_of_escInter {v : Vt} {i : UInt8} (x : UInt8) (hg : v.pstate = .escInter i)
    (hlo : 0x30 ≤ x) (hhi : x ≤ 0x7E) : stick (v.step x) = stCharset i x (stick v) := by
  rw [step_of_escInter x hg, stick_stepEscInter _ i x hlo hhi, stick_abortUtf8]

/-- `SO` and `SI` from ground, the two bytes `stick_ctl` excludes. -/
theorem stick_step_si {v : Vt} (hg : v.pstate = .ground) :
    stick (v.step 0x0F) = { stick v with so := false } := by
  rw [step_of_ground 0x0F hg]
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  rw [show (v.abortUtf8 0x0F).ctl 0x0F = { (v.abortUtf8 0x0F) with shiftOut := false } from rfl,
    show
      stick { (v.abortUtf8 0x0F) with shiftOut := false } =
        { stick (v.abortUtf8 0x0F) with so := false }
      from rfl,
    stick_abortUtf8]

theorem stick_step_so {v : Vt} (hg : v.pstate = .ground) :
    stick (v.step 0x0E) = { stick v with so := true } := by
  rw [step_of_ground 0x0E hg]
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  rw [show (v.abortUtf8 0x0E).ctl 0x0E = { (v.abortUtf8 0x0E) with shiftOut := true } from rfl,
    show
      stick { (v.abortUtf8 0x0E) with shiftOut := true } =
        { stick (v.abortUtf8 0x0E) with so := true }
      from rfl,
    stick_abortUtf8]

/-! ## The clamp and the two tables, said out loud

Three pure-core values the tree *used* everywhere and *stated* nowhere: every proof that
needed them re-derived them inline, which is why the old source scanner counted
them as unclaimed. `Theorems/Coverage.lean` now checks exact constants in theorem
types. The clamp's own range (`clampDim_range`, `clampDim_eq_self_iff`) is stated beside
`Good` in `Theorems/Vt/State.lean`; each theorem below is the postcondition its callers
were already assuming. -/

/-- **`Vt.init` applies the clamp, and the grid it builds is the clamped height.** -/
theorem init_shape (cols rows : Nat) :
    (Vt.init cols rows).cols = clampDim cols ∧
      (Vt.init cols rows).rows = clampDim rows ∧
      (Vt.init cols rows).grid.size = clampDim rows := ⟨rfl, rfl, by simp [Vt.init]⟩

/-- A resize clears deferred wrap in every cursor slot, including the main
screen cursor stashed while the alternate screen is active. -/
theorem resize_clears_pending (v : Vt) (cols rows : Nat) :
    (v.resize cols rows).cursor.pending = false ∧
      (v.resize cols rows).saved.cur.pending = false ∧
      ∀ g cur pen, (v.resize cols rows).altGrid = some (g, cur, pen) → cur.pending = false := by
  refine ⟨rfl, rfl, ?_⟩
  intro g cur pen h
  cases hAlt : v.altGrid with
  | none => simp [Vt.resize, hAlt] at h
  | some value =>
    obtain ⟨oldGrid, oldCur, oldPen⟩ := value
    simp only [Vt.resize, hAlt, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨_, hcur, _⟩
    rw [← hcur]

/-- **A 256-colour parameter saturates rather than wraps**, which is why `color256` takes a
`min`: `UInt8.ofNat 256` is `0`, so without it `SGR 38;5;256` would silently select colour 0
instead of 255. -/
theorem color256_saturates : color256 256 = color256 255 := by rfl

/-- **Line drawing is geometry-neutral.** Every source is a one-column ASCII glyph and so
is every box character it maps to, so a charset designation cannot change a row's column
accounting — the thing `CellOk.width` ties stored cells to. A mapping added into the wide
or zero-width tables falsifies this. -/
theorem charWidth_decLine (c : Char) : charWidth (decLine c) = charWidth c := by
  unfold decLine
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | (subst_vars; decide)
      | decide

/-- **The `ByteArray` convenience is the same machine.** `feedBytes` is the adapter the
`Tests/` and `E2E/` fixtures call (the daemon feeds `List UInt8` through `Terminal.feed`), and
this says it adds nothing — so every theorem stated over `feed` covers those fixtures. -/
theorem feedBytes_eq (v : Vt) (bytes : ByteArray) : v.feedBytes bytes = v.feed bytes.toList := by
  rfl

/-! ## Boundaries for injected titles

An ESC intermediate is pending until a final byte, even for sequences the emulator
does not interpret. DEL cannot publish a boundary in CSI, ESC or an intermediate
sequence. These claims allow any receiver title, screen, CSI parameters and UTF-8
state; only the parser state and the byte class select the transition.
-/

/-- Every byte in the full ESC intermediate range opens a pending sequence. -/
theorem stepEsc_intermediate (v : Vt) (b : UInt8) (hlo : 0x20 ≤ b) (hhi : b ≤ 0x2F) :
    v.stepEsc b = { v with pstate := .escInter b } := by
  unfold Vt.stepEsc
  split
  all_goals
    first
    | exact False.elim ((of_decide_eq_false rfl) hhi)
    | exact False.elim ((of_decide_eq_false rfl) hlo)
    | simp [hlo, hhi]

/-- The shared parser uses that transition even with a pending UTF-8 decoder. -/
theorem step_esc_intermediate {v : Vt} (b : UInt8) (hp : v.pstate = .esc) (hlo : 0x20 ≤ b)
    (hhi : b ≤ 0x2F) : v.step b = { (v.abortUtf8 b) with pstate := .escInter b } := by
  simp only [Vt.step, ps_abortUtf8, hp]
  exact stepEsc_intermediate _ b hlo hhi

/-- Further intermediates and ignored nonfinal bytes retain a pending parser
and the receiver's title. A new ESC has its own restart transition below. -/
theorem step_escInter_pending {v : Vt} {i : UInt8} (b : UInt8) (hp : v.pstate = .escInter i)
    (hf : ¬(0x30 ≤ b ∧ b ≤ 0x7E)) (he : b ≠ 0x1B) :
    (∃ j, (v.step b).pstate = .escInter j) ∧ (v.step b).windowTitle = v.windowTitle := by
  simp only [Vt.step, ps_abortUtf8, hp]
  simp only [Vt.stepEscInter, Bool.and_eq_true, decide_eq_true_eq, hf, ite_false,
    beq_eq_false_iff_ne.mpr he, Bool.false_eq_true]
  split
  all_goals refine ⟨⟨_, rfl⟩, ?_⟩
  all_goals unfold Vt.windowTitle Vt.abortUtf8
  all_goals split <;> rfl

/-- An arbitrarily long unfinished sequence stays closed to injected output.
There is no length bound or assumption on the stored title. -/
theorem feed_escInter_pending (bytes : List UInt8) {v : Vt} {i : UInt8}
    (hp : v.pstate = .escInter i) (hb : ∀ b ∈ bytes, ¬(0x30 ≤ b ∧ b ≤ 0x7E) ∧ b ≠ 0x1B) :
    (∃ j, (v.feed bytes).pstate = .escInter j) ∧
      (v.feed bytes).atBoundary = false ∧ (v.feed bytes).windowTitle = v.windowTitle := by
  induction bytes generalizing v i with
  | nil => exact ⟨⟨i, hp⟩, by simp [Vt.feed, Vt.atBoundary, hp], rfl⟩
  | cons b bs
    ih =>
    obtain ⟨⟨j, hj⟩, ht⟩ := step_escInter_pending b hp (hb b (by simp)).1 (hb b (by simp)).2
    have hi := ih hj (fun c hc => hb c (by simp [hc]))
    exact ⟨hi.1, hi.2.1, hi.2.2.trans ht⟩

/-- Discarding scrollback after each byte cannot introduce a false boundary.
The observer waits through the whole unfinished sequence, preserving its title. -/
theorem observe_escInter_pending (bytes : List UInt8) {v : Vt} {i : UInt8}
    (hp : v.pstate = .escInter i) (hb : ∀ b ∈ bytes, ¬(0x30 ≤ b ∧ b ≤ 0x7E) ∧ b ≠ 0x1B) :
    (∃ j, (v.observe bytes).pstate = .escInter j) ∧
      (v.observe bytes).atBoundary = false ∧ (v.observe bytes).windowTitle = v.windowTitle := by
  induction bytes generalizing v i with
  | nil => exact ⟨⟨i, hp⟩, by simp [Vt.observe, Vt.atBoundary, hp], rfl⟩
  | cons b bs
    ih =>
    obtain ⟨⟨j, hj⟩, ht⟩ := step_escInter_pending b hp (hb b (by simp)).1 (hb b (by simp)).2
    have hi := ih (v := { (v.step b) with sb := {} }) hj (fun c hc => hb c (by simp [hc]))
    exact ⟨hi.1, hi.2.1, hi.2.2.trans ht⟩

/-- Starting after ESC, any intermediate followed by any unfinished suffix
keeps the public title observer away from a write boundary. -/
theorem observe_esc_intermediates (i : UInt8) (bytes : List UInt8) {v : Vt} (hp : v.pstate = .esc)
    (hlo : 0x20 ≤ i) (hhi : i ≤ 0x2F) (hb : ∀ b ∈ bytes, ¬(0x30 ≤ b ∧ b ≤ 0x7E) ∧ b ≠ 0x1B) :
    (v.observe (i :: bytes)).atBoundary = false ∧
      (v.observe (i :: bytes)).windowTitle = v.windowTitle := by
  change
    ({ (v.step i) with sb := {} }.observe bytes).atBoundary = false ∧
      ({ (v.step i) with sb := {} }.observe bytes).windowTitle = _
  rw [step_esc_intermediate i hp hlo hhi]
  have h :=
    observe_escInter_pending bytes (v :=
      { (v.abortUtf8 i) with
        pstate := .escInter i, sb := {} })
      rfl hb
  refine ⟨h.2.1, h.2.2.trans ?_⟩
  unfold Vt.windowTitle Vt.abortUtf8
  split <;> rfl

/-- A final completes both the control sequence and any stray partial UTF-8
decoder, so waiting for an intermediate sequence does not block forever. -/
theorem step_escInter_final_boundary {v : Vt} {i : UInt8} (b : UInt8) (hp : v.pstate = .escInter i)
    (hlo : 0x30 ≤ b) (hhi : b ≤ 0x7E) :
    (v.step b).atBoundary = true ∧ (v.step b).windowTitle = v.windowTitle := by
  have ha : b < 0x80 := by
    rw [UInt8.lt_iff_toNat_lt]
    rw [UInt8.le_iff_toNat_le] at hhi
    change b.toNat ≤ 126 at hhi
    change b.toNat < 128
    omega
  have hu : (v.abortUtf8 b).u8need = 0 := by
    unfold Vt.abortUtf8
    split
    · rfl
    · rename_i h
      simp [ha] at h
      omega
  simp only [Vt.step, ps_abortUtf8, hp]
  rw [stepEscInter_final _ i b hlo hhi]
  repeat' split
  all_goals constructor
  all_goals
    with_reducible
      first
      | simpa [Vt.atBoundary] using hu
      | ( unfold Vt.windowTitle Vt.abortUtf8
          split <;> rfl)

/-- ESC abandons an intermediate sequence by starting a new ESC sequence,
never by briefly reporting a boundary where an OSC title could be injected. -/
theorem step_escInter_restart {v : Vt} {i : UInt8} (hp : v.pstate = .escInter i) :
    (v.step 0x1B).pstate = .esc ∧
      (v.step 0x1B).atBoundary = false ∧ (v.step 0x1B).windowTitle = v.windowTitle := by
  simp only [Vt.step, ps_abortUtf8, hp]
  refine ⟨rfl, rfl, ?_⟩
  change (v.abortUtf8 0x1B).title = v.title
  unfold Vt.abortUtf8
  split <;> rfl

/-- DEL leaves the entire parser state intact, including every CSI parameter
and the selected charset bank; in ground state it stores nothing and moves no
cursor. Its only possible effect is UTF-8 neutralization. -/
theorem step_del_preserves_parser {v : Vt}
    (hp :
      v.pstate = .ground ∨
        v.pstate = .esc ∨ (∃ i, v.pstate = .escInter i) ∨ (∃ s, v.pstate = .csi s)) :
    v.step 0x7F = v.abortUtf8 0x7F := by
  rcases hp with hp | hp | ⟨i, hp⟩ | ⟨s, hp⟩
  · rw [step_of_ground 0x7F hp]
    unfold Vt.stepGround
    rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left (by decide)]
  · simp only [Vt.step, ps_abortUtf8, hp]
    rfl
  · simp only [Vt.step, ps_abortUtf8, hp]
    change { (v.abortUtf8 0x7F) with pstate := .escInter i } = _
    rw [← hp, ← ps_abortUtf8 v 0x7F]
  · simp only [Vt.step, ps_abortUtf8, hp]
    rfl

/-- The public observer cannot permit title output after DEL in an incomplete
CSI, ESC or intermediate sequence; the application title remains unchanged. -/
theorem observe_del_boundary {v : Vt}
    (hp : v.pstate = .esc ∨ (∃ i, v.pstate = .escInter i) ∨ (∃ s, v.pstate = .csi s)) :
    (v.observe [0x7F]).pstate = v.pstate ∧
      (v.observe [0x7F]).atBoundary = false ∧ (v.observe [0x7F]).windowTitle = v.windowTitle := by
  change (v.step 0x7F).pstate = _ ∧ (v.step 0x7F).atBoundary = false ∧ (v.step 0x7F).windowTitle = _
  rw [step_del_preserves_parser (Or.inr hp)]
  refine ⟨ps_abortUtf8 _ _, ?_, ?_⟩
  · rcases hp with hp | ⟨i, hp⟩ | ⟨s, hp⟩ <;> simp [Vt.atBoundary, ps_abortUtf8, hp]
  · unfold Vt.windowTitle Vt.abortUtf8
    split <;> rfl

theorem atBoundary_iff (v : Vt) : v.atBoundary = true ↔ v.pstate = .ground ∧ v.u8need = 0 := by
  simp [Vt.atBoundary]

/-- Observing a concatenation is observing each part in turn. -/
public theorem observe_append (v : Vt) (a b : List UInt8) :
    v.observe (a ++ b) = (v.observe a).observe b := by simp [Vt.observe, List.foldl_append]

/-- Every observer byte is the existing parser step, changing only discarded
history. In particular its title, parser state and partial UTF-8 agree exactly. -/
theorem observe_singleton (v : Vt) (b : UInt8) : v.observe [b] = { (v.step b) with sb := {} } := rfl

theorem observe_no_history (v : Vt) (bytes : List UInt8) (h : v.sb = {}) :
    (v.observe bytes).sb = {} := invariant_foldl (·.sb = {}) _ (fun _ _ _ => rfl) bytes v h

theorem observe_good (v : Vt) (bytes : List UInt8) (h : Good v) : Good (v.observe bytes) :=
  invariant_foldl Good (fun w b => { (w.step b) with sb := {} })
    (fun _ b hw => { Good.step b hw with sbLe := by simp [Ring.size, sbCap] }) bytes v h

/-- Discarding history preserves every invariant required of a public VT
transformer; screen shape and parser state still come from the usual step. -/
theorem observe_invariants (v : Vt) (bytes : List UInt8) (hr : Renderable v) (hu : U8Ok v)
    (ht : TabsOk v) (hc : CsiOk v) :
    Renderable (v.observe bytes) ∧
      U8Ok (v.observe bytes) ∧ TabsOk (v.observe bytes) ∧ CsiOk (v.observe bytes) :=
  invariant_foldl (fun w => Renderable w ∧ U8Ok w ∧ TabsOk w ∧ CsiOk w)
    (fun w b => { (w.step b) with sb := {} })
    (fun _ b hw =>
      ⟨renderable_congr (renderable_step hw.1 b) rfl rfl rfl rfl, u8Ok_step b hw.2.1,
        tabsOk_step b hw.2.2.1, csiOk_step hw.2.2.2 b⟩)
    bytes v ⟨hr, hu, ht, hc⟩

theorem observe_dims (v : Vt) (bytes : List UInt8) (h : Good v) :
    (v.observe bytes).colCount = v.colCount ∧ (v.observe bytes).rowCount = v.rowCount := by
  have hi :=
    invariant_foldl (fun w => Good w ∧ dims w = dims v) (fun w b => { (w.step b) with sb := {} })
      (fun w b hw =>
        ⟨{ Good.step b hw.1 with sbLe := by simp [Ring.size, sbCap] },
          (dims_step b hw.1).trans hw.2⟩)
      bytes v ⟨h, rfl⟩
  exact Prod.mk.inj hi.2

end Linger.Core.Vt
