module

public import Theorems.Render.Grid
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Grid

-- No `public section`: a **public** declaration's type may not mention a private
-- field, and `Vt`'s are private now (the seal, `specs/archive/vt-toolkit.md` Step 1).
-- Module-private is the default, so consumers reach in with `import all`. See the
-- longer note in `Theorems/Vt.lean`.

/-! # §Replay, the tab ruler

The tab-ruler ladder, built on the projection-preservation support in
`Theorems.Render.Keeps`: `restore_tabs_any`.
Split out of `Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## §Replay, the tab ruler — `restore_tabs_any`

The last restored field whose claim was carried by fixtures alone (with the window
title and the DECSC slot). The *fix* landed earlier — `tabsAnsi` emits the ruler
unconditionally, because a client is not a reset terminal and nothing else in a
restore stream clears a tab stop — and this is the theorem that fix made provable:
as the code stood before it, `restore_tabs_any` would have been **false**.

`tabs` is an `Array Bool` of size `cols`, not a scalar, so it does not fold into
`stick`; the shape is therefore array equality via size-and-pointwise (`Array.ext`,
the same route `grid_eq_of_cells` takes) rather than a transform algebra. And it
needs no transform algebra: the only transform in the stream is inside `tabsAnsi`
itself, so a *preservation* predicate (`Fixes (·.tabs)`) plus one fold lemma is the
whole story. -/

theorem psBlind_tabs : PsBlind (fun v : Vt => v.tabs) := fun _ _ => rfl

/-! ### The ruler is untouched by everything the tail emits

`Vt.tabs` moves only under `TBC` (a CSI `g`), `HTS` (an **ESC** `H`), `RIS` and
`Vt.resize`. The tail after `tabsAnsi` emits none of them — note that `0x48` is
`HTS` only as an *ESC* final; as a CSI final it is `CUP`, which is why `savedAnsi`
and `cursorAnsi` are safe. That distinction is load-bearing: the existing
`keeps_escSeq` admits `0x48` (HTS writes no *cell*), and copying its byte list
verbatim here would give a **false** lemma. -/

theorem tabs_csiDispatch_cup (v : Vt) (s : CsiState) : (v.csiDispatch s 0x48).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.moveTo (s.arg 1 1 - 1) (s.arg 0 1 - 1)).tabs = v.tabs
    rw [frame_moveTo]

theorem tabs_csiDispatch_sgr (v : Vt) (s : CsiState) : (v.csiDispatch s 0x6D).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (if s.priv == 0 then v.applySgr s.sgrParams else v).tabs = v.tabs
    split
    · rw [frame_applySgr]
    · rfl

/-- **A mode set never touches the ruler** — unconditionally, for any mode number.
`setMode`'s only non-`modes` arms are `enterAlt`/`leaveAlt`/`moveTo`/the DECSC slot,
and none of them writes `tabs`. This is where the ruler's claim is *simpler* than
the grid's: `keeps_modeSet` has to exclude `47`/`1047`/`1049` (they swap the grid)
and therefore needs the digit bridge to identify the emitted number with the parsed
one, and `restore_modes_any` needs the mouse allowlist. The ruler needs neither. -/
theorem tabs_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).tabs = v.tabs := by rw [frame_moveTo]

theorem tabs_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).tabs = v.tabs := by rw [frame_enterAlt]

theorem tabs_leaveAlt (v : Vt) (s : Bool) : (v.leaveAlt s).tabs = v.tabs := by rw [frame_leaveAlt]

theorem tabs_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    (v.setMode priv n on).tabs = v.tabs := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [tabs_moveTo, tabs_enterAlt, tabs_leaveAlt]
  all_goals rfl

theorem tabs_setModes (v : Vt) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    (v.setModes priv ps on).tabs = v.tabs :=
  setModes_invariant (fun w => w.tabs = v.tabs) priv on ps
    (fun w p _ h => (tabs_setMode w priv p.1 on).trans h) v rfl

theorem tabs_csiDispatch_sm (v : Vt) (s : CsiState) : (v.csiDispatch s 0x68).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    exact tabs_setModes v _ _ true

theorem tabs_csiDispatch_rm (v : Vt) (s : CsiState) : (v.csiDispatch s 0x6C).tabs = v.tabs := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    exact tabs_setModes v _ _ false

theorem tabs_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).tabs = v.tabs := by
  rw [frame_oscFinish]

/-- `ESC x` for the singles the tail emits. **`0x48` is deliberately absent**: as an
ESC final it is `HTS`, which sets a stop at the cursor — the one escape in this
family that moves the ruler. `0x63` (`RIS`) is absent for the same reason, and no
linger stream emits it anyway. -/
theorem fixes_tabs_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x3E ∨ b = 0x5C) :
    Fixes (fun v : Vt => v.tabs) (escSeq b) := by
  intro v hg hu
  rw [show escSeq b = [0x1B] ++ [b] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [b]) = (w.step 0x1B).step b from fun w => by
      simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet b rfl (by simpa using hu)]
  rcases hb with h | h | h | h <;> subst h <;> show _ ∧ _ ∧ _ <;> unfold Vt.stepEsc <;>
    exact ⟨rfl, by simpa using hu, rfl⟩

theorem fixes_tabs_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) (hlo : 0x30 ≤ x)
    (hhi : x ≤ 0x7E) : Fixes (fun v : Vt => v.tabs) (escCharset i x) := by
  intro v hg hu
  rw [show escCharset i x = [0x1B] ++ [i, x] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [i, x]) = ((w.step 0x1B).step i).step x from fun w => by
      simp [Vt.feed]]
  rw [esc_step_eq hg hu]
  have hinter : ({ v with pstate := .esc } : Vt).step i = { v with pstate := .escInter i } := by
    rw [step_of_esc_quiet i rfl (by simpa using hu)]
    unfold Vt.stepEsc
    rcases hi with h | h
    · subst h; rfl
    · subst h; rfl
  rw [hinter, step_of_escInter_quiet x rfl (by simpa using hu)]
  show _ ∧ _ ∧ _
  rw [stepEscInter_final _ i x hlo hhi]
  repeat' split
  all_goals exact ⟨rfl, by simpa using hu, rfl⟩

theorem fixes_tabs_shiftOut : Fixes (fun v : Vt => v.tabs) [0x0E] := by
  intro v hg hu
  rw [show ∀ (w : Vt), w.feed [(0x0E : UInt8)] = w.step 0x0E from fun _ => rfl]
  rw [step_of_ground_quiet (0x0E : UInt8) hg hu]
  show _ ∧ _ ∧ _
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  unfold Vt.ctl
  exact ⟨hg, by simpa using hu, rfl⟩

theorem fixes_tabs_shiftIn : Fixes (fun v : Vt => v.tabs) [0x0F] := by
  intro v hg hu
  rw [show ∀ (w : Vt), w.feed [(0x0F : UInt8)] = w.step 0x0F from fun _ => rfl]
  rw [step_of_ground_quiet (0x0F : UInt8) hg hu]
  show _ ∧ _ ∧ _
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  unfold Vt.ctl
  exact ⟨hg, by simpa using hu, rfl⟩

/-- A mode set (`CSI ? n h/l`) leaves the ruler alone for **any** `n`. Contrast
`keeps_modeSet`, which needs the digit bridge to know `n ∉ {47, 1047, 1049}`. -/
theorem fixes_tabs_modeSet (n : Nat) (on : Bool) : Fixes (fun v : Vt => v.tabs) (modeSet n on) := by
  unfold modeSet
  cases on
  · exact fixes_csiPriv psBlind_tabs n 0x6C (by decide) (by decide) tabs_csiDispatch_rm
  · exact fixes_csiPriv psBlind_tabs n 0x68 (by decide) (by decide) tabs_csiDispatch_sm

theorem fixes_tabs_irm (on : Bool) :
    Fixes (fun v : Vt => v.tabs) (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact fixes_csiNum psBlind_tabs 4 0x6C (by decide) (by decide) tabs_csiDispatch_rm
  · exact fixes_csiNum psBlind_tabs 4 0x68 (by decide) (by decide) tabs_csiDispatch_sm

/-- **The mode replay leaves the ruler alone**, with no allowlist and no digit
bridge — `tabs_setMode` holds for every mode number, so every branch is the same
one-liner. -/
theorem fixes_tabs_modesAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (modesAnsi v) := by
  unfold modesAnsi
  refine Fixes.append ?_ (fixes_tabs_irm v.modes.insert)
  refine Fixes.append ?_ (fixes_tabs_modeSet 6 _)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1004 _)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1006 _)
  refine
    Fixes.append ?_
      ((Fixes.streamPred _).ite (fun _ => fixes_tabs_modeSet v.modes.mouse true)
        (fun _ => Fixes.nil _))
  refine Fixes.append ?_ (fixes_tabs_modeSet 1003 false)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1002 false)
  refine Fixes.append ?_ (fixes_tabs_modeSet 1000 false)
  refine Fixes.append ?_ (fixes_tabs_modeSet 2004 _)
  refine Fixes.append ?_ (fixes_tabs_modeSet 25 _)
  refine
    Fixes.append ?_
      ((Fixes.streamPred _).ite (fun _ => fixes_tabs_escSeq 0x3D (by decide))
        (fun _ => fixes_tabs_escSeq 0x3E (by decide)))
  exact (fixes_tabs_modeSet 7 _).append (fixes_tabs_modeSet 1 _)

theorem fixes_tabs_savedAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (savedAnsi v) := by
  unfold savedAnsi
  exact
    ((fixes_penSgr psBlind_tabs _ tabs_csiDispatch_sgr).append
          (fixes_csiNum2 psBlind_tabs _ _ 0x48 (by decide) (by decide) tabs_csiDispatch_cup)).append
      (fixes_tabs_escSeq 0x37 (by decide))

theorem fixes_tabs_titleAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (titleAnsi v) := by
  unfold titleAnsi
  exact fixes_osc psBlind_tabs _ tabs_oscFinish

theorem fixes_tabs_charsetAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (charsetAnsi v) := by
  unfold charsetAnsi
  refine
    (((Fixes.streamPred _).ite
              (fun _ => fixes_tabs_escCharset 0x28 0x30 (by decide) (by decide) (by decide))
              (fun _ => fixes_tabs_escCharset 0x28 0x42 (by decide) (by decide) (by decide))).append
          ((Fixes.streamPred _).ite
            (fun _ => fixes_tabs_escCharset 0x29 0x30 (by decide) (by decide) (by decide))
            (fun _ => fixes_tabs_escCharset 0x29 0x42 (by decide) (by decide) (by decide)))).append
      ?_
  exact (Fixes.streamPred _).ite (fun _ => fixes_tabs_shiftOut) (fun _ => Fixes.nil _)

theorem fixes_tabs_cursorAnsi (v : Vt) : Fixes (fun v : Vt => v.tabs) (cursorAnsi v) := by
  unfold cursorAnsi
  exact
    (Fixes.streamPred _).ite
      (fun _ => fixes_csiNum2 psBlind_tabs _ _ 0x48 (by decide) (by decide) tabs_csiDispatch_cup)
      (fun _ => fixes_csiNum2 psBlind_tabs _ _ 0x48 (by decide) (by decide) tabs_csiDispatch_cup)

/-- The six original tail stages preserve the ruler: the DECSC slot, title, modes,
charsets, pen and cursor address. `fixes_tabs_pending_tail` includes the pending-wrap
repairs interleaved with these stages. -/
theorem fixes_tabs_tail (v : Vt) :
    Fixes (fun v : Vt => v.tabs)
      (savedAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen ++
        cursorAnsi v) :=
  (((((fixes_tabs_savedAnsi v).append (fixes_tabs_titleAnsi v)).append
                (fixes_tabs_modesAnsi v)).append
            (fixes_tabs_charsetAnsi v)).append
        (fixes_penSgr psBlind_tabs v.pen tabs_csiDispatch_sgr)).append
    (fixes_tabs_cursorAnsi v)

/-! ### The ruler, rebuilt from a cleared one

`tabsAnsi` clears every stop (`TBC 3`) and then sets the ones the session holds, one
`CHA`+`HTS` pair each. On the array side that is a fold of `setIfInBounds` over the
filtered index list, and this says the fold reproduces the session's ruler exactly.
Array equality is size-and-pointwise (`Array.ext`), the route `grid_eq_of_cells`
takes — the size half is needed internally anyway, since the cleared ruler is an
`Array.replicate`, so a pointwise-only claim would be weaker for no saving. -/

/-- A stop that reads back `true` is in range: out of range `getD` returns the
default, which is `false`. This is what lets the monotonicity step below avoid a
size side condition. -/
theorem getD_true_lt {a : Array Bool} {j : Nat} (h : a.getD j false = true) : j < a.size := by
  rcases Nat.lt_or_ge j a.size with hlt | hge
  · exact hlt
  · exfalso
    rw [Array.getD, dite_eq_right (by omega)] at h
    exact absurd h (by decide)

theorem size_foldl_setTab :
    ∀ (l : List Nat) (a : Array Bool), (l.foldl (fun b i => b.setIfInBounds i true) a).size = a.size
  | [], _ => rfl
  | i :: is, a => by rw [List.foldl_cons, size_foldl_setTab is, Array.size_setIfInBounds]

/-- Setting stops never clears one: a stop already set survives the rest of the fold.
Needed because the head write of `foldl_setTab_mem` has to outlive the tail. -/
theorem foldl_setTab_mono :
    ∀ (l : List Nat) (a : Array Bool) (j : Nat),
      a.getD j false = true → (l.foldl (fun b i => b.setIfInBounds i true) a).getD j false = true
  | [], _, _, h => h
  | i :: is, a, j, h => by
    rw [List.foldl_cons]
    refine foldl_setTab_mono is _ j ?_
    by_cases hij : j = i
    · rw [hij,
        getD_set_self a i true false
          (by
            rw [← hij]; exact getD_true_lt h)]
    · rw [getD_set_ne a i j true false hij]; exact h

theorem foldl_setTab_mem :
    ∀ (l : List Nat) (a : Array Bool) (j : Nat),
      j ∈ l → j < a.size → (l.foldl (fun b i => b.setIfInBounds i true) a).getD j false = true
  | [], _, _, h, _ => absurd h (by simp)
  | i :: is, a, j, hmem, hsz => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with h | h
    · rw [h]
      exact
        foldl_setTab_mono is _ i
          (getD_set_self a i true false
            (by
              rw [← h]; exact hsz))
    · exact
        foldl_setTab_mem is _ j h
          (by
            rw [Array.size_setIfInBounds]; exact hsz)

theorem foldl_setTab_not_mem :
    ∀ (l : List Nat) (a : Array Bool) (j : Nat),
      j ∉ l → (l.foldl (fun b i => b.setIfInBounds i true) a).getD j false = a.getD j false
  | [], _, _, _ => rfl
  | i :: is, a, j, h => by
    rw [List.foldl_cons, foldl_setTab_not_mem is _ j (fun hm => h (List.mem_cons.mpr (Or.inr hm)))]
    exact getD_set_ne a i j true false (fun he => h (List.mem_cons.mpr (Or.inl he)))

/-- **The ruler is rebuilt exactly.** Clearing every stop and then setting the ones
the session holds gives back the session's ruler — provided it is `cols` long, which
is what makes a stop at an index outside `range cols` impossible. -/
theorem tabs_rebuilt {t : Array Bool} {cols : Nat} (hsz : t.size = cols) :
    ((List.range cols).filter (fun i => t.getD i false)).foldl
        (fun (a : Array Bool) i => a.setIfInBounds i true) (Array.replicate cols false) =
      t := by
  apply Array.ext
  · rw [size_foldl_setTab, Array.size_replicate, hsz]
  · intro j hj _
    have hjc : j < cols := by
      rw [size_foldl_setTab, Array.size_replicate] at hj; exact hj
    have hjt : j < t.size := by
      rw [hsz]; exact hjc
    -- both sides through `getD`, where the fold lemmas live
    rw [← getD_lt' _ j false hj, ← getD_lt' t j false hjt]
    by_cases hstop : t.getD j false = true
    · exact
        (foldl_setTab_mem _ _ j (List.mem_filter.mpr ⟨List.mem_range.mpr hjc, hstop⟩)
              (by
                rw [Array.size_replicate]; exact hjc)).trans
          hstop.symm
    · have hf : t.getD j false = false := by
        rcases Bool.eq_false_or_eq_true (t.getD j false) with h | h
        · exact absurd h hstop
        · exact h
      rw [foldl_setTab_not_mem _ _ j (fun hm => hstop (List.mem_filter.mp hm).2), hf,
        getD_lt' _ j false
          (by
            rw [Array.size_replicate]; exact hjc),
        Array.getElem_replicate]

/-! ### The clear, the stops, and the fold

`tabsAnsi` is `TBC 3` followed by one `CHA`+`HTS` pair per stop. Both halves get a
**state equation**, because what they do to the ruler is the claim rather than a
frame around it.

The clear asks only `pstate = .ground` of the receiver — no `u8need = 0`. The
leading `ESC` of `CSI 3 g` aborts a half-decoded character by itself
(`un_abortUtf8_esc`), and nothing about the ruler rides on the bytes it discards.
That is the same argument `SMap` makes for the sticky bundle, and it is what keeps
the ruler's claim free of the `paint_entry`/`U8Ok` apparatus the grid's needs: the
paint ends in glyph bytes, so `u8need = 0` right after it is expensive, and here it
is simply not required. -/

theorem tabs_abortUtf8 (v : Vt) (b : UInt8) : (v.abortUtf8 b).tabs = v.tabs := by
  unfold Vt.abortUtf8; split <;> rfl

theorem cols_abortUtf8 (v : Vt) (b : UInt8) : (v.abortUtf8 b).cols = v.cols := by
  unfold Vt.abortUtf8; split <;> rfl

theorem abortUtf8_of_uz {v : Vt} (b : UInt8) (h : v.u8need = 0) : v.abortUtf8 b = v := by
  unfold Vt.abortUtf8; rw [ite_eq_right (by simp [h])]

/-- Feeding `ESC` is the same as discarding a half-decoded character first: `step`
aborts before it dispatches, and a second abort at `0x1B` is the identity. -/
theorem step_esc_of_abort (u : Vt) : u.step 0x1B = (u.abortUtf8 0x1B).step 0x1B := by
  unfold Vt.step
  rw [abortUtf8_of_uz 0x1B (un_abortUtf8_esc u)]

/-- …so a stream that opens with `ESC` may as well be fed to the aborted state. -/
theorem feed_esc_of_abort (u : Vt) (rest : Bytes) :
    u.feed (0x1B :: rest) = (u.abortUtf8 0x1B).feed (0x1B :: rest) := by
  simp only [feed_cons]
  rw [step_esc_of_abort u]

/-- Glyph bytes preserve tabs regardless of the decoder's pending count or accumulator. -/
theorem tabs_glyph_step {v : Vt} (b : UInt8) (hg : v.pstate = .ground) (hb : 0x20 ≤ b) :
    (v.step b).tabs = v.tabs := by
  have hac (w : Vt) (n : Nat) : (w.acceptChar n).tabs = w.tabs := by
    unfold Vt.acceptChar
    split <;> exact congrArg OffScreen.tabs (off_print _ _)
  have hs (w : Vt) : (w.stepGround b).tabs = w.tabs := by
    unfold Vt.stepGround
    split
    · rfl
    rw [ite_eq_right
        (show ¬b < (0x20 : UInt8) from by
          simp only [UInt8.lt_iff_toNat_lt]
          have := UInt8.le_iff_toNat_le.mp hb
          omega)]
    split
    · exact hac _ _
    split
    · split
      · rfl
      split
      · exact hac _ _
      · rfl
    repeat' split
    all_goals rfl
  have hp : (v.abortUtf8 b).pstate = .ground := (ps_abortUtf8 _ _).trans hg
  unfold Vt.step
  dsimp only
  rw [hp, hs, tabs_abortUtf8]

theorem tabs_glyph_run :
    ∀ (bs : Bytes) (v : Vt), v.pstate = .ground → (∀ b ∈ bs, 0x20 ≤ b) → (v.feed bs).tabs = v.tabs
  | [], _, _, _ => rfl
  | b :: bs, v, hg, hb => by
    have h := hb b (by simp)
    rw [feed_cons]
    exact
      (tabs_glyph_run bs _
            (ground_step b hg
              (by
                intro he
                subst b
                exact (by decide : ¬(0x20 : UInt8) ≤ 0x1B) h))
            (fun c hc => hb c (by simp [hc]))).trans
        (tabs_glyph_step b hg h)

theorem tabs_cellText (c : Cell) {v : Vt} (hg : v.pstate = .ground) :
    (v.feed (cellText c)).tabs = v.tabs := by
  apply tabs_glyph_run _ _ hg
  intro b hb
  rcases List.mem_append.mp hb with hb | hb
  · exact (utf8_no_ctl _ (safeChar_ge c.base).1 (safeChar_ge c.base).2 b hb).1
  · exact (utf8s_no_ctl _ b hb).1

/-- The leading ESC aborts any partial glyph before the pen replay preserves tabs. -/
theorem tabs_penSgr_of_ground (p : Pen) {v : Vt} (hg : v.pstate = .ground) :
    (v.feed (penSgr p)).pstate = .ground ∧
      (v.feed (penSgr p)).u8need = 0 ∧ (v.feed (penSgr p)).tabs = v.tabs := by
  have he : penSgr p = 0x1B :: (penSgr p).drop 1 := by simp [penSgr, sgrOf, csiB]
  have hf : v.feed (penSgr p) = (v.abortUtf8 0x1B).feed (penSgr p) := by
    rw [he]
    exact feed_esc_of_abort v _
  rw [hf]
  have h :=
    fixes_penSgr psBlind_tabs p tabs_csiDispatch_sgr (v.abortUtf8 0x1B)
      ((ps_abortUtf8 _ _).trans hg) (un_abortUtf8_esc v)
  exact ⟨h.1, h.2.1, h.2.2.trans (tabs_abortUtf8 _ _)⟩

/-- Reprinting the pending glyph preserves tabs without a grid or decoder invariant. -/
theorem fixes_tabs_pendingAnsi (cols : Nat) (grid : Array Row) (cur : Cursor) (row : Nat)
    (pen : Pen) : Fixes (fun v : Vt => v.tabs) (pendingAnsi cols grid cur row pen) := by
  let cells := grid.getD cur.y #[]
  let x := if (cells.at cur.x).width == 0 then cur.x - 1 else cur.x
  let cell := cellFit (cells.at x)
  change
    Fixes (fun v : Vt => v.tabs)
      (if
          cur.pending && cur.y < grid.size && cur.x < cells.size && cur.x + 1 == cols &&
            charWidth cell.base != 0 &&
            x + charWidth cell.base == cols then
        csiNum2 row (x + 1) 0x48 ++ penSgr cell.pen ++ cellText cell ++ penSgr pen
      else [])
  split
  · intro v hg hu
    rw [feed_append, feed_append, feed_append]
    have hc :=
      fixes_csiNum2 psBlind_tabs row (x + 1) 0x48 (by decide) (by decide) tabs_csiDispatch_cup v hg
        hu
    have hp := fixes_penSgr psBlind_tabs cell.pen tabs_csiDispatch_sgr _ hc.1 hc.2.1
    have ht := tabs_cellText cell hp.1
    have hq := tabs_penSgr_of_ground pen (ends_cellText cell _ hp.1)
    exact ⟨hq.1, hq.2.1, hq.2.2.trans (ht.trans (hp.2.2.trans hc.2.2))⟩
  · exact Fixes.nil _

theorem fixes_tabs_savedPendingAnsi (v : Vt) :
    Fixes (fun v : Vt => v.tabs) (savedPendingAnsi v) := by
  unfold savedPendingAnsi
  exact
    (Fixes.streamPred _).ite
      (fun _ => (fixes_tabs_pendingAnsi _ _ _ _ _).append (fixes_tabs_escSeq 0x37 (by decide)))
      (fun _ => Fixes.nil _)

theorem fixes_tabs_cursorPendingAnsi (v : Vt) :
    Fixes (fun v : Vt => v.tabs) (cursorPendingAnsi v) := by
  unfold cursorPendingAnsi
  split
  · refine Fixes.append ?_ (fixes_penSgr psBlind_tabs _ tabs_csiDispatch_sgr)
    refine Fixes.append ?_ (fixes_tabs_charsetAnsi v)
    refine Fixes.append ?_ (fixes_tabs_irm _)
    refine Fixes.append ?_ (fixes_tabs_modeSet 7 _)
    refine Fixes.append ?_ (fixes_tabs_pendingAnsi _ _ _ _ _)
    refine Fixes.append ?_ fixes_tabs_shiftIn
    refine Fixes.append ?_ (fixes_tabs_escCharset 0x29 0x42 (by decide) (by decide) (by decide))
    refine Fixes.append ?_ (fixes_tabs_escCharset 0x28 0x42 (by decide) (by decide) (by decide))
    exact (fixes_tabs_modeSet 7 true).append (fixes_tabs_irm false)
  · exact Fixes.nil _

/-- Every stage after the tab ruler, including both pending-wrap repairs, preserves it. -/
theorem fixes_tabs_pending_tail (v : Vt) :
    Fixes (fun v : Vt => v.tabs)
      (savedAnsi v ++ savedPendingAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
        penSgr v.pen ++
        cursorAnsi v ++
        cursorPendingAnsi v) := by
  refine Fixes.append ?_ (fixes_tabs_cursorPendingAnsi v)
  refine Fixes.append ?_ (fixes_tabs_cursorAnsi v)
  refine Fixes.append ?_ (fixes_penSgr psBlind_tabs v.pen tabs_csiDispatch_sgr)
  refine Fixes.append ?_ (fixes_tabs_charsetAnsi v)
  refine Fixes.append ?_ (fixes_tabs_modesAnsi v)
  refine Fixes.append ?_ (fixes_tabs_titleAnsi v)
  exact (fixes_tabs_savedAnsi v).append (fixes_tabs_savedPendingAnsi v)

/-- `CSI 3 g` (TBC 3) as a state equation: it clears every stop and touches nothing
else. -/
theorem tbc3_feed_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (csiNum 3 0x67) = { v with tabs := Array.replicate v.cols false } := by
  rw [show csiNum 3 0x67 = [0x1B, 0x5B] ++ (digits 3 ++ [(0x67 : UInt8)]) from by
      simp [csiNum, csiB]]
  rw [feed_append, keeps_csi_open hg hu]
  obtain ⟨s', heq, hcur', hhave, hpar, hint, hsub⟩ :=
    csi_digits_run_eq 3 (v := { v with pstate := .csi ({} : CsiState) }) (s := ({} : CsiState)) rfl
      (by simpa using hu) rfl
  rw [show
      ∀ (u : Vt), u.feed (digits 3 ++ [(0x67 : UInt8)]) = (u.feed (digits 3)).feed [(0x67 : UInt8)]
      from fun u => by simp [Vt.feed, List.foldl_append]]
  rw [heq, show ∀ (u : Vt), u.feed [(0x67 : UInt8)] = u.step 0x67 from fun _ => rfl]
  rw [csi_final_step_eq 0x67 rfl (by simpa using hu) (by rw [hint]) (by decide) (by decide)]
  unfold Vt.csiFinish
  rw [ite_eq_left (by simpa using hhave),
    ite_eq_right
      (by
        rw [hpar]; decide)]
  dsimp only
  have harg :
    ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState).arg 0 0 =
      3 := by
    rw [arg_of_one_of 0
        (show
          ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState).params =
            (#[] : Array (Nat × Bool)).push (3, s'.curSub)
          from by simp [hpar, hcur'])]
    simp
  rw [show
      ∀ (u : Vt),
        u.csiDispatch
            ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState) 0x67 =
          { u with tabs := Array.replicate u.cols false }
      from by
      intro u
      unfold Vt.csiDispatch
      rw [ite_eq_right
          (show
            ¬(({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } :
                    CsiState)).ignore =
                true
            from by
            show ¬(s'.ignore = true)
            rw [show s'.ignore = ({} : CsiState).ignore from by
                obtain ⟨s2, hps2, -, -, -, -, hign2, -, -⟩ :=
                  csi_digits_value 3 (v := { v with pstate := .csi ({} : CsiState) }) (s :=
                    ({} : CsiState)) rfl rfl
                have : s' = s2 :=
                  PState.csi.inj
                    ((by rw [heq] :
                          ((({ v with pstate := .csi ({} : CsiState) } : Vt)).feed
                                (digits 3)).pstate =
                            PState.csi s').symm.trans
                      hps2)
                rw [this]; exact hign2]
            simp)]
      show
        (match
            ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState).arg 0
              0 with
          | 0 => { u with tabs := u.tabs.setIfInBounds u.cursor.x false }
          | 3 => { u with tabs := Array.replicate u.cols false }
          | _ => u) =
          { u with tabs := Array.replicate u.cols false }
      rw [harg]
      rfl]
  show
    ({ ({ v with pstate := .csi s' } : Vt) with
          tabs := Array.replicate ({ v with pstate := .csi s' } : Vt).cols false,
          pstate := .ground } :
        Vt) =
      { v with tabs := Array.replicate v.cols false }
  rw [hg]

/-- **The clear grounds the ruler from any receiver**, whatever its decoder was
holding. -/
theorem tbc3_clears {u : Vt} (hg : u.pstate = .ground) :
    (u.feed (csiNum 3 0x67)).tabs = Array.replicate u.cols false ∧
      (u.feed (csiNum 3 0x67)).cols = u.cols ∧
      (u.feed (csiNum 3 0x67)).pstate = .ground ∧ (u.feed (csiNum 3 0x67)).u8need = 0 := by
  have hshape : u.feed (csiNum 3 0x67) = (u.abortUtf8 0x1B).feed (csiNum 3 0x67) := by
    rw [show csiNum 3 0x67 = 0x1B :: (0x5B :: (digits 3 ++ [(0x67 : UInt8)])) from by
        simp [csiNum, csiB]]
    exact feed_esc_of_abort u _
  rw [hshape,
    tbc3_feed_eq
      (by
        rw [ps_abortUtf8]; exact hg)
      (un_abortUtf8_esc u)]
  exact
    ⟨by rw [cols_abortUtf8], cols_abortUtf8 u 0x1B, by
      rw [ps_abortUtf8]; exact hg, un_abortUtf8_esc u⟩

/-- `ESC H` (HTS) as a state equation: it sets a stop at the cursor. -/
theorem hts_feed_eq {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0) :
    v.feed (escSeq 0x48) = { v with tabs := v.tabs.setIfInBounds v.cursor.x true } := by
  rw [show escSeq 0x48 = [0x1B] ++ [(0x48 : UInt8)] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [(0x48 : UInt8)]) = (w.step 0x1B).step 0x48 from fun w =>
      by simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet (0x48 : UInt8) rfl (by simpa using hu)]
  show
    ({ ({ v with pstate := .esc } : Vt) with
          tabs :=
            ({ v with pstate := .esc } : Vt).tabs.setIfInBounds
              ({ v with pstate := .esc } : Vt).cursor.x true,
          pstate := .ground } :
        Vt) =
      { v with tabs := v.tabs.setIfInBounds v.cursor.x true }
  rw [hg]

/-- **The stops, as one array fold.** Each `CHA` parks the cursor on its column and
the `HTS` after it sets the stop there, so the whole run *is* `setIfInBounds` folded
over the stop list.

The cursor is deliberately **not** part of the carried invariant: `CHA` establishes
it and `HTS` consumes it inside a single iteration, so the loop carries only
`ground`, a quiesced decoder, `cols` and the ruler. That is what makes this simpler
than `Matches`, which has to tie the cursor to the grid *across* iterations. -/
theorem hts_run :
    ∀ (ss : List Nat) (u : Vt),
      u.pstate = .ground →
        u.u8need = 0 →
        u.cols < 65535 →
        (∀ i ∈ ss, i < u.cols) →
        (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).tabs =
            ss.foldl (fun (t : Array Bool) i => t.setIfInBounds i true) u.tabs ∧
          (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).cols = u.cols ∧
          (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).pstate = .ground ∧
          (u.feed (ss.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))).u8need = 0
  | [], u, hg, hu, _, _ => ⟨rfl, rfl, hg, hu⟩
  | i :: is, u, hg, hu, hlt, hmem => by
    have hi : i < u.cols := hmem i (by simp)
    -- `CHA (i+1)` parks the cursor on column `i`; only the cursor moves
    have hcha : u.feed (csiNum (i + 1) 0x47) = u.setCol i := by
      rw [cha_feed_eq (i + 1) hg hu (by omega) (by omega), show i + 1 - 1 = i from by omega]
    have hx : (u.setCol i).cursor.x = i := by
      show min i (u.cols - 1) = i
      omega
    -- …then `HTS` sets the stop the cursor is on
    have hhts :
      (u.setCol i).feed (escSeq 0x48) =
        { u.setCol i with tabs := u.tabs.setIfInBounds i true } := by
      rw [hts_feed_eq
          (by
            rw [frame_setCol]; exact hg)
          (by
            rw [frame_setCol]; exact hu),
        hx, show (u.setCol i).tabs = u.tabs from by rw [frame_setCol]]
    rw [List.flatMap_cons, feed_append, feed_append, hcha, hhts, List.foldl_cons]
    obtain ⟨h1, h2, h3, h4⟩ :=
      hts_run is { u.setCol i with tabs := u.tabs.setIfInBounds i true }
        (by
          show (u.setCol i).pstate = _; rw [frame_setCol]; exact hg)
        (by
          show (u.setCol i).u8need = _; rw [frame_setCol]; exact hu)
        (by
          show (u.setCol i).cols < _; rw [frame_setCol]; exact hlt)
        (fun j hj => by
          show j < (u.setCol i).cols
          rw [frame_setCol]
          exact hmem j (by simp [hj]))
    refine ⟨h1, ?_, h3, h4⟩
    rw [h2]
    show (u.setCol i).cols = u.cols
    rw [frame_setCol]

/-- `restore`, split at the tab ruler: the head that grounds the receiver, the clear,
the stops, and the tail that leaves the ruler alone. -/
theorem restore_tabs_split (v : Vt) :
    restore v =
      (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v) ++
        (csiNum 3 0x67 ++
          ((((List.range v.cols).filter (fun i => v.tabs.getD i false)).flatMap
              (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48)) ++
            (savedAnsi v ++ savedPendingAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
              penSgr v.pen ++
              cursorAnsi v ++
              cursorPendingAnsi v))) := by
  unfold restore restoreBody tabsAnsi
  simp only [List.append_assoc]

/-- **A5 inbound, the tab ruler.** For any receiver of the session's width, `restore`
installs the session's tab ruler — the field that was, until the emitter was fixed,
worse than unproved: `tabsAnsi` used to skip the whole thing when the session's ruler
was the default, so a client whose previous occupant had set its own stops kept them
and a `\t` landed on the wrong column. As the code stood then this theorem would have
been **false**, which is why the fix had to precede it.

`Good w` is what `dims_feed` needs of the receiver (the paint contains the byte
`0x63`, so the cheaper `dims_feed_ne_ris` does not apply), and it is also where the
`CHA` bound comes from: the largest emitted parameter — one more than the last column
— must stay off the parser's 65535 clamp, and `Good.colsLe` caps `w.cols` at 1000,
which `hcols` transports to `v.cols`. That bound used to be a stated binder and was a
small lie about what the claim needs. `hvtabs` is the one hypothesis on the session
that `Good`/`Renderable` do not already give: a ruler longer than `cols` could hold a
stop no `range cols` walk would ever emit, and `Checkpoint.load` is total on arbitrary
bytes, so it is asked for rather than assumed. -/
theorem restore_tabs_any (v w : Vt) (hgood : Good w) (hcols : w.cols = v.cols)
    (hvtabs : v.tabs.size = v.cols) : (w.feed (restore v)).tabs = v.tabs := by
  have hub : v.cols < 65535 := by
    have := hgood.colsLe; rw [hcols] at this; omega
  rw [restore_tabs_split, feed_append, feed_append, feed_append]
  -- the head grounds any receiver and cannot change its width
  have hhg :
    (w.feed
          (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++
            regionAnsi v)).pstate =
      .ground := by
    rw [show
        prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++ regionAnsi v =
          (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) ++ regionAnsi v
        from rfl,
      feed_append]
    exact ends_regionAnsi v _ (paint_grounds v w)
  have hhc :
    (w.feed
          (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v ++
            regionAnsi v)).cols =
      v.cols := by
    rw [← dims_fst, dims_feed _ hgood, dims_fst]; exact hcols
  -- the clear, then the stops
  obtain ⟨hct, hcc, hcg, hcu⟩ := tbc3_clears hhg
  obtain ⟨hrt, -, hrg, hru⟩ :=
    hts_run ((List.range v.cols).filter (fun i => v.tabs.getD i false)) _ hcg hcu
      (by
        rw [hcc, hhc]; exact hub)
      (fun i hi => by
        rw [hcc, hhc]
        exact List.mem_range.mp (List.mem_filter.mp hi).1)
  -- the tail leaves the ruler alone, so the fold's value is the answer
  obtain ⟨-, -, htl⟩ := fixes_tabs_pending_tail v _ hrg hru
  -- `Fixes` is parameterised by the projection, so destructuring it leaves a
  -- beta-redex where the goal has the field applied; `dsimp` lines them up.
  dsimp only at htl
  rw [htl, hrt, hct, hhc]
  exact tabs_rebuilt hvtabs

/-- The pointwise form: every column's stop is the session's. -/
theorem restore_tabs_stop_any (v w : Vt) (hgood : Good w) (hcols : w.cols = v.cols)
    (hvtabs : v.tabs.size = v.cols) (i : Nat) :
    (w.feed (restore v)).tabs.getD i false = v.tabs.getD i false := by
  rw [restore_tabs_any v w hgood hcols hvtabs]

/-- The ruler claim with the receiver's invariant discharged from reachability, the
shape `restore_grid_reachable` has — minus the hypothesis on the *session*, which the
ruler claim turns out not to need at all: the only thing `LiveReachableVt v` supplied
was `v.cols < 65535`, and `Good w` plus `hcols` already give it.

`hvtabs` stays **here** on purpose, and it is now a choice rather than a gap: `Good`
and `Renderable` still say nothing about the ruler's length, but `Vt.tabsOk_of_liveReachable`
(`specs/archive/vt-toolkit.md` Step 3) proves it of every reachable state, so a caller with
reachability discharges it and `restore_tabs_live` below is that caller. Keeping this
form is what makes the two claims different rather than redundant: a session whose ruler
is the right length gets the ruler restored **whether or not it is reachable**, which
covers a decoded checkpoint — and `Checkpoint.load` is total on arbitrary bytes, so that
case is real. Weakening this signature to `LiveReachableVt v` would trade a hypothesis
for a strictly stronger one and lose exactly that. -/
theorem restore_tabs_reachable (v w : Vt) (hw : LiveReachableVt w) (hcols : w.cols = v.cols)
    (hvtabs : v.tabs.size = v.cols) : (w.feed (restore v)).tabs = v.tabs :=
  restore_tabs_any v w (good_of_liveReachable hw) hcols hvtabs

/-- **The ruler claim with every invariant discharged**, the exact twin of
`restore_grid_reachable`: between two states a live session can hold, matching width is
the whole of what is left to say. `Good w` comes from the receiver's reachability and the
ruler length from the session's (`Vt.tabsOk_of_liveReachable`) — the `tabs_*` frame family
this file used to name as future work and `Theorems/Vt.lean`'s §Ruler section now is.

This is an addition to `restore_tabs_reachable` rather than a replacement for it; see that
theorem's docstring for why the weaker-hypothesis form is the one a decoded checkpoint
needs. -/
theorem restore_tabs_live (v w : Vt) (hw : LiveReachableVt w) (hv : LiveReachableVt v)
    (hcols : w.cols = v.cols) : (w.feed (restore v)).tabs = v.tabs :=
  restore_tabs_reachable v w hw hcols (tabsOk_of_liveReachable hv)

/-- Non-vacuity: a real 80×24 session satisfies every hypothesis, so the ruler claim
is not vacuously true. -/
example : ((Vt.init 80 24).feed (restore (Vt.init 80 24))).tabs = (Vt.init 80 24).tabs :=
  restore_tabs_any _ _ (good_init 80 24) rfl (size_defaultTabs _)

end Linger.Core.Render
