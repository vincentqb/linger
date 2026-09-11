module

public import Theorems.Render.Tabs
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Tabs

public section

/-! # §Replay — the scrollback stage

What `Render.scrollbackAnsi` sends is built from three pieces, and this file
proves the two that are about *rows* rather than about the receiver's state: the
fit (`cellFit`/`fitRow` produce rows a repaint can reproduce, with **no**
hypothesis, which is what keeps the ring out of the screen theorems' statements)
and the budget (`sbTake`/`sbRows` never count past `sbReplayBytes`, and what they
keep is a contiguous newest run).

The receiver-state piece — `scrollback_entry`, that feeding the stage preserves
every conjunct the screen paint needs — is in `Theorems/Render/Grid.lean` beside
`paint_entry`, because it re-establishes exactly `paint_entry`'s outputs.

**The asymmetry to keep in view.** `sbTake_budget`/`sbRows_budget` bound the
*counted* cost `sbRowCost`, not the emitted bytes. `rowAnsi_len_le_cost` closes
that gap one row at a time — the emitted paint of a row from **any** incoming pen
is within its counted cost — which is what makes `sbRowCost`'s `+ 6` a claim
rather than a convention. The whole-stream form
`(scrollbackAnsi v).length ≤ Σ sbRowCost (sbRows v) + 2 * v.rows + 19` is a
fixture in `Tests/Render.lean` and a Step-5 theorem; it is *sharp*, attained with
zero slack by a ring whose rows each end in a truecolour cell. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## The cost of a row, from any incoming pen

`sbRowCost` counts a row's paint seeded with the **default** pen, but the stage
paints each row seeded with whatever pen the row above left in effect. The gap is
at most one `SGR`, and exactly four bytes: `rowSlot`'s width-0 branch returns the
pen accumulator untouched, so the two folds diverge only at the first non-shadow
cell and agree from that cell on. -/

/-- `rowSlot`'s non-shadow branch, as an explicit triple. The shadow branch is
`rowSlot_eq_shadow`; this is its complement, generic in the width (the
`rowSlot_eq_*` family in `Theorems/Render/Row.lean` splits it further by shape,
which a length argument does not need). -/
theorem rowSlot_eq_nonzero (B : Bytes) (p : Pen) (x : Nat) (c : Cell) (hw : ¬c.width = 0) :
    rowSlot (B, p, x) c =
      ((if c.pen == p then B else B ++ penSgr c.pen) ++
          (if c.width == 2 && !c.marks.isEmpty then
            utf8 (safeChar c.base) ++ csiNum (x + 2) 0x47 ++ utf8s c.marks ++ csiNum (x + 3) 0x47
          else cellText c),
        c.pen, x + 1) := by
  unfold rowSlot
  dsimp only
  rw [ite_eq_right (by simp [hw] : ¬(c.width == 0))]

/-- **The seed lemma.** Painting a row from pen `p` instead of pen `q` costs at
most one `penSgr q` more, however long the row is: the excess is one optional
`SGR` at the first non-shadow cell and never accumulates. The disjunction is the
induction's invariant — either the two folds have converged (same pen, bounded
byte excess) or they have not yet diverged (`p2` is still the seed `q`, equal
lengths). -/
theorem foldl_rowSlot_seed (q : Pen) :
    ∀ (cs : List Cell) (B1 B2 : Bytes) (p1 p2 : Pen) (x : Nat),
      ((p1 = p2 ∧ B1.length ≤ B2.length + (penSgr q).length) ∨ (p2 = q ∧ B1.length = B2.length)) →
        (cs.foldl rowSlot (B1, p1, x)).1.length ≤
          (cs.foldl rowSlot (B2, p2, x)).1.length + (penSgr q).length
  | [], B1, B2, p1, p2, x, h => by
    simp only [List.foldl_nil]
    rcases h with ⟨_, hle⟩ | ⟨_, he⟩
    · exact hle
    · omega
  | c :: cs, B1, B2, p1, p2, x, h => by
    rw [List.foldl_cons, List.foldl_cons]
    by_cases hw : c.width = 0
    · rw [rowSlot_eq_shadow c B1 p1 x hw, rowSlot_eq_shadow c B2 p2 x hw]
      refine foldl_rowSlot_seed q cs _ _ _ _ _ ?_
      rcases h with ⟨hp, hle⟩ | ⟨hp, he⟩
      · exact
          Or.inl
            ⟨hp, by
              simp only [List.length_append]; omega⟩
      · exact
          Or.inr
            ⟨hp, by
              simp only [List.length_append]; omega⟩
    · rw [rowSlot_eq_nonzero B1 p1 x c hw, rowSlot_eq_nonzero B2 p2 x c hw]
      refine foldl_rowSlot_seed q cs _ _ _ _ _ (Or.inl ⟨rfl, ?_⟩)
      have key :
        (if c.pen == p1 then B1 else B1 ++ penSgr c.pen).length ≤
          (if c.pen == p2 then B2 else B2 ++ penSgr c.pen).length + (penSgr q).length := by
        rcases h with ⟨hp, hle⟩ | ⟨hp, he⟩
        · rw [hp]
          by_cases hq : c.pen == p2
          · rw [ite_eq_left hq, ite_eq_left hq]; omega
          · rw [ite_eq_right hq, ite_eq_right hq]; simp only [List.length_append]; omega
        · by_cases hq : c.pen == p2
          · rw [ite_eq_left hq]
            have hcq : penSgr c.pen = penSgr q := by rw [show c.pen = p2 from by simpa using hq, hp]
            by_cases hq1 : c.pen == p1
            · rw [ite_eq_left hq1]; omega
            · rw [ite_eq_right hq1]; simp only [List.length_append, hcq]; omega
          · rw [ite_eq_right hq]
            by_cases hq1 : c.pen == p1
            · rw [ite_eq_left hq1]; simp only [List.length_append]; omega
            · rw [ite_eq_right hq1]; simp only [List.length_append]; omega
      simp only [List.length_append]
      omega

/-- The array-level form of the seed lemma. -/
theorem rowAnsi_len_seed (row : Row) (p q : Pen) :
    (rowAnsi row p).1.length ≤ (rowAnsi row q).1.length + (penSgr q).length := by
  unfold rowAnsi
  dsimp only
  rw [foldl_rowSlot_range row ([], p, 0), foldl_rowSlot_range row ([], q, 0)]
  exact foldl_rowSlot_seed q _ [] [] p q 0 (Or.inr ⟨rfl, rfl⟩)

/-- `penSgr {}` is four bytes — the `+ 4` inside `sbRowCost`. `digits` recurses on
well-founded recursion, so its `0` case has to be unfolded by hand; `decide` and
`rfl` both get stuck on it. -/
theorem penSgr_default_len : (penSgr ({} : Pen)).length = 4 := by
  have hd : digits 0 = [0x30] := by
    rw [digits]; simp
  simp [penSgr, sgrColorSeq, colorCodes, penAttrCodes, sgrOf, joinSemi, csiB, hd]

/-- **The `+ 6` made a claim.** Whatever pen is in effect when a replayed row is
painted, its emitted bytes are within that row's counted `sbRowCost` — so the
budget's arithmetic is about the same rows the stage emits.

The bound is tight at the row level: `penSgr {}` = 4 is attained (a blank
80-column row is 80 bytes from the default pen and 84 from a truecolour one), so
the slack is not trimmable, and the remaining `+ 2` is the pushing CRLF the
emitted paint does not contain. -/
theorem rowAnsi_len_le_cost (row : Row) (p : Pen) : (rowAnsi row p).1.length ≤ sbRowCost row := by
  have h := rowAnsi_len_seed row p ({} : Pen)
  rw [penSgr_default_len] at h
  unfold sbRowCost
  omega

/-! ## The fit — reproducible rows with no hypothesis

This is what buys Definition-of-done item 4: because `rowOk_fitRow` is
unconditional, no theorem about the *screen* ever needs a hypothesis about
`v.sb`. A bare `Vt.resizeRow` here would have carried
`∀ x, CellOk (row.at x)` — a hypothesis the ring is exactly the place that cannot
supply it (`Vt.resize` re-fits the grid and leaves the ring alone, and a decoded
checkpoint's ring is arbitrary). -/

/-- A codepoint a repaint may emit is stored as itself. -/
theorem printableChar_id_of_emittable {c : Char} (h : Emittable c) : printableChar c = c := by
  unfold printableChar
  rw [ite_eq_right
      (by
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, Nat.not_lt]
        exact ⟨h.1, h.2⟩)]

/-- Every clause of `CellOk`, by construction and with **no** hypothesis on the
cell: the base is `printableChar`'d, a non-shadow's width is `charWidth` of that
base, the marks are filtered to zero-width printables and capped at eight. -/
theorem cellOk_cellFit (c : Cell) : CellOk (cellFit c) := by
  refine ⟨printableChar_emittable _, fun hw => ?_, ?_, fun m hm => ?_⟩
  · show
      charWidth (printableChar c.base) =
        if c.width == 0 then 0 else charWidth (printableChar c.base)
    by_cases hz : c.width = 0
    · exact
        absurd
          (by
            show (if c.width == 0 then 0 else charWidth (printableChar c.base)) = 0
            rw [ite_eq_left (by simp [hz])])
          hw
    · rw [ite_eq_right (by simp [hz])]
  · show ((c.marks.filter _).take 8).length ≤ 8
    rw [List.length_take]
    omega
  · have hm' := List.mem_of_mem_take hm
    have hp := (List.mem_filter.mp hm').2
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact
      ⟨hp.1, by
        rw [← hp.2]; exact printableChar_emittable m⟩

/-- **Unconditional.** `Row.mend` supplies the pairs, `cells_map_range` the cells,
and the `Array.range` the exact width. -/
theorem rowOk_fitRow (row : Row) (cols : Nat) : RowOk cols (fitRow row cols) := by
  unfold fitRow
  exact rowOk_mend (by simp) (cells_map_range _ _ (fun i => cellOk_cellFit _))

/-- The fit is the **identity** on a cell a repaint could already reproduce. -/
theorem cellFit_id {c : Cell} (h : CellOk c) : cellFit c = c := by
  have hbase : printableChar c.base = c.base := printableChar_id_of_emittable h.base
  have hmarks :
    (c.marks.filter (fun m => charWidth m == 0 && printableChar m == m)).take 8 = c.marks := by
    rw [List.filter_eq_self.mpr (fun a ha => ?_)]
    · exact List.take_of_length_le h.marksLe
    · obtain ⟨hw, hem⟩ := h.marks a ha
      simp [hw, printableChar_id_of_emittable hem]
  have hwidth : (if c.width == 0 then 0 else charWidth c.base) = c.width := by
    by_cases hz : c.width = 0
    · rw [ite_eq_left (by simp [hz]), hz]
    · rw [ite_eq_right (by simp [hz])]; exact h.width hz
  show
    ({ base := printableChar c.base,
       width := if c.width == 0 then 0 else charWidth (printableChar c.base),
       marks := (c.marks.filter (fun m => charWidth m == 0 && printableChar m == m)).take 8,
       pen := c.pen } :
        Cell) =
      c
  rw [hbase, hmarks, hwidth]

/-- **The anti-vacuity receipt.** On the rows a live session actually stores the
fit changes nothing, so comparing a receiver's replayed ring against `sbRows v`
is not a weakened target dressed up as a claim — it is the session's own history.
(`Vt.scrollUpIn` pushes `v.getRow 0`, and `rowOk_getRow` holds of every
`Renderable` state; a *decoded checkpoint's* ring is the case where the fit has
work to do.) -/
theorem fitRow_id_of_rowOk {cols : Nat} {row : Row} (h : RowOk cols row) :
    fitRow row cols = row := by
  have hcells : (Array.range cols).map (fun i => cellFit (row.at i)) = row := by
    refine Array.ext (by simp [h.size]) (fun i hi1 hi2 => ?_)
    have hlt : i < (Array.range cols).size := by simpa using (by simpa using hi1 : i < cols)
    rw [Array.getElem_map _ hi1, Array.getElem_range hlt]
    show cellFit (row.at i) = row[i]
    rw [cellFit_id (h.cells i)]
    show row.getD i default = row[i]
    rw [Array.getD, dite_eq_left hi2]
    rfl
  unfold fitRow
  rw [hcells]
  exact mend_of_pairOk h.pairs

/-! ## The budget

`sbTake` stops at the first row that does not fit rather than skipping it, which
is what makes the two claims below both true: the kept rows never exceed the
budget, and they are the **newest** contiguous run. -/

/-- The counted cost of what a budget admits never exceeds that budget. -/
theorem sbTake_budget (cols : Nat) :
    ∀ (budget : Nat) (l : List Row), ((sbTake cols budget l).map sbRowCost).sum ≤ budget
  | _, [] => by simp [sbTake]
  | budget, r :: rs => by
    rw [sbTake]
    split
    · rename_i hfits
      have hrec := sbTake_budget cols (budget - sbRowCost (fitRow r cols)) rs
      simp only [List.map_cons, List.sum_cons]
      omega
    · simp

/-- **The kept rows are a prefix of the walk**, i.e. a contiguous run of the
newest history rows, each fitted — never a subsequence with holes. This is what
licenses "the oldest lines are dropped first" in the docs, and it is the shape
the receiver-side claim consumes. -/
theorem sbTake_prefix (cols : Nat) :
    ∀ (budget : Nat) (l : List Row),
      sbTake cols budget l = (l.take (sbTake cols budget l).length).map (fun r => fitRow r cols)
  | _, [] => by simp [sbTake]
  | budget, r :: rs => by
    rw [sbTake]
    split
    · have hrec := sbTake_prefix cols (budget - sbRowCost (fitRow r cols)) rs
      simp only [List.length_cons, List.take_succ_cons, List.map_cons]
      exact congrArg _ hrec
    · simp

/-- What a reattaching client is sent stays inside `sbReplayBytes` of counted
cost, for **every** `Vt` — including one whose ring was decoded from a
checkpoint. The double reverse is invisible to a sum, which is exactly why it
needs the order fixtures rather than this theorem. -/
theorem sbRows_budget (v : Vt) : ((sbRows v).toList.map sbRowCost).sum ≤ sbReplayBytes := by
  unfold sbRows
  rw [List.toList_toArray, List.map_reverse, List.sum_reverse]
  exact sbTake_budget v.cols sbReplayBytes v.sb.toList.reverse

/-! ## Step 3 — the ring is untouched by everything `restore` emits after the stage

The mirror of `Theorems/Render/Tabs.lean`'s ruler tail, at `π := (·.sb)`. The `Fixes`/
`PsBlind` layer there is already field-generic, so most of this is a projection rename
over scripts whose every leaf is `rfl` on a record update that omits `sb`.

Two places it is **not** a rename, and both matter.

* **`ESC H` is admitted here and excluded there.** `0x48` as an ESC final is `HTS`, which
  sets a tab stop — so the ruler's own tail must refuse it, and `Tabs.lean` says so. It
  writes no scrollback, so this family admits it, which is what lets `tabsAnsi` be covered
  below. The exclusions that stay are `0x63` (`RIS`, which clears the ring outright) and
  `0x44`/`0x45`/`0x4D` (`IND`/`NEL`/`RI`, which run `lineFeed` and may scroll).
* **There is no total `sb_csiDispatch_any`, and there cannot be.** `0x4A` reaches `ED 3`,
  which wipes the ring, and `0x53` (`SU`) scrolls with `allowSb := true` and pushes. The
  per-final family is therefore mandatory rather than tidiness — which is also why
  `gridAnsi` gets no `Fixes` lemma at all: a `CRLF` at the region bottom pushes, so its
  invariance is conditional and lives in the paint ladder as `OffRow.sb`. -/

theorem psBlind_sb : PsBlind (fun v : Vt => v.sb) := fun _ _ => rfl

theorem sb_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).sb = v.sb := by rw [frame_moveTo]

theorem sb_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).sb = v.sb := by rw [frame_enterAlt]

theorem sb_leaveAlt (v : Vt) (s : Bool) : (v.leaveAlt s).sb = v.sb := by rw [frame_leaveAlt]

/-- **A mode set never touches the ring**, for any mode number — including `47`/`1047`/
`1049`, which swap the *grid*: `enterAlt`/`leaveAlt` stash and restore cells, never
history, which is why a session's scrollback survives a full-screen program. -/
theorem sb_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    (v.setMode priv n on).sb = v.sb := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [sb_moveTo, sb_enterAlt, sb_leaveAlt]
  all_goals rfl

theorem sb_csiDispatch_cup (v : Vt) (s : CsiState) : (v.csiDispatch s 0x48).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.moveTo (s.arg 1 1 - 1) (s.arg 0 1 - 1)).sb = v.sb
    rw [frame_moveTo]

theorem sb_csiDispatch_sgr (v : Vt) (s : CsiState) : (v.csiDispatch s 0x6D).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (if s.priv == 0 then v.applySgr s.sgrParams else v).sb = v.sb
    split
    · rw [frame_applySgr]
    · rfl

theorem sb_csiDispatch_sm (v : Vt) (s : CsiState) : (v.csiDispatch s 0x68).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setMode (s.priv == 0x3F) (s.arg 0 0) true).sb = v.sb
    rw [sb_setMode]

theorem sb_csiDispatch_rm (v : Vt) (s : CsiState) : (v.csiDispatch s 0x6C).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setMode (s.priv == 0x3F) (s.arg 0 0) false).sb = v.sb
    rw [sb_setMode]

theorem sb_oscFinish (v : Vt) (acc : Array UInt8) : (v.oscFinish acc).sb = v.sb := by
  rw [frame_oscFinish]

theorem sb_csiDispatch_cha (v : Vt) (s : CsiState) : (v.csiDispatch s 0x47).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.setCol (s.arg 0 1 - 1)).sb = v.sb
    rw [frame_setCol]

theorem sb_csiDispatch_tbc (v : Vt) (s : CsiState) : (v.csiDispatch s 0x67).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show
      (match s.arg 0 0 with
          | 0 => { v with tabs := v.tabs.setIfInBounds v.cursor.x false }
          | 3 => { v with tabs := Array.replicate v.cols false }
          | _ => v).sb =
        v.sb
    repeat' split
    all_goals rfl

theorem sb_csiDispatch_stbm (v : Vt) (s : CsiState) : (v.csiDispatch s 0x72).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show
      (if s.priv != 0 then v
          else
            if s.arg 0 1 - 1 < s.arg 1 v.rows - 1 && s.arg 1 v.rows - 1 < v.rows then
              ({ v with
                    top := s.arg 0 1 - 1, bot := s.arg 1 v.rows - 1 }).moveTo
                0 0
            else v).sb =
        v.sb
    repeat' split
    all_goals
      first
      | rfl
      | rw [frame_moveTo]

/-- `ESC x` for the singles `restore` emits, plus `0x48` (`HTS`) — see the header for why
this family is broader than the ruler's and which bytes stay out of it. -/
theorem fixes_sb_escSeq (b : UInt8) (hb : b = 0x37 ∨ b = 0x3D ∨ b = 0x3E ∨ b = 0x5C ∨ b = 0x48) :
    Fixes (fun v : Vt => v.sb) (escSeq b) := by
  intro v hg hu
  rw [show escSeq b = [0x1B] ++ [b] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [b]) = (w.step 0x1B).step b from fun w => by
      simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet b rfl (by simpa using hu)]
  rcases hb with h | h | h | h | h <;> subst h <;> show _ ∧ _ ∧ _ <;> unfold Vt.stepEsc <;>
    exact ⟨rfl, by simpa using hu, rfl⟩

theorem fixes_sb_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) :
    Fixes (fun v : Vt => v.sb) (escCharset i x) := by
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
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, by simpa using hu, rfl⟩

theorem fixes_sb_shiftOut : Fixes (fun v : Vt => v.sb) [0x0E] := by
  intro v hg hu
  rw [show ∀ (w : Vt), w.feed [(0x0E : UInt8)] = w.step 0x0E from fun _ => rfl]
  rw [step_of_ground_quiet (0x0E : UInt8) hg hu]
  show _ ∧ _ ∧ _
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  unfold Vt.ctl
  exact ⟨hg, by simpa using hu, rfl⟩

theorem fixes_sb_modeSet (n : Nat) (on : Bool) : Fixes (fun v : Vt => v.sb) (modeSet n on) := by
  unfold modeSet
  cases on
  · exact fixes_csiPriv psBlind_sb n 0x6C (by decide) (by decide) sb_csiDispatch_rm
  · exact fixes_csiPriv psBlind_sb n 0x68 (by decide) (by decide) sb_csiDispatch_sm

theorem fixes_sb_irm (on : Bool) :
    Fixes (fun v : Vt => v.sb) (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact fixes_csiNum psBlind_sb 4 0x6C (by decide) (by decide) sb_csiDispatch_rm
  · exact fixes_csiNum psBlind_sb 4 0x68 (by decide) (by decide) sb_csiDispatch_sm

theorem fixes_sb_modesAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (modesAnsi v) := by
  unfold modesAnsi
  refine Fixes.append ?_ (fixes_sb_irm v.modes.insert)
  refine Fixes.append ?_ (fixes_sb_modeSet 6 _)
  refine Fixes.append ?_ (fixes_sb_modeSet 1004 _)
  refine Fixes.append ?_ (fixes_sb_modeSet 1006 _)
  refine
    Fixes.append ?_
      ((Fixes.streamPred _).ite (fun _ => fixes_sb_modeSet v.modes.mouse true)
        (fun _ => Fixes.nil _))
  refine Fixes.append ?_ (fixes_sb_modeSet 1003 false)
  refine Fixes.append ?_ (fixes_sb_modeSet 1002 false)
  refine Fixes.append ?_ (fixes_sb_modeSet 1000 false)
  refine Fixes.append ?_ (fixes_sb_modeSet 2004 _)
  refine Fixes.append ?_ (fixes_sb_modeSet 25 _)
  refine
    Fixes.append ?_
      ((Fixes.streamPred _).ite (fun _ => fixes_sb_escSeq 0x3D (by decide))
        (fun _ => fixes_sb_escSeq 0x3E (by decide)))
  exact (fixes_sb_modeSet 7 _).append (fixes_sb_modeSet 1 _)

theorem fixes_sb_savedAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (savedAnsi v) := by
  unfold savedAnsi
  exact
    ((fixes_penSgr psBlind_sb _ sb_csiDispatch_sgr).append
          (fixes_csiNum2 psBlind_sb _ _ 0x48 (by decide) (by decide) sb_csiDispatch_cup)).append
      (fixes_sb_escSeq 0x37 (by decide))

theorem fixes_sb_titleAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (titleAnsi v) := by
  unfold titleAnsi
  exact fixes_osc psBlind_sb _ sb_oscFinish

theorem fixes_sb_charsetAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (charsetAnsi v) := by
  unfold charsetAnsi
  refine
    (((Fixes.streamPred _).ite (fun _ => fixes_sb_escCharset 0x28 0x30 (by decide))
              (fun _ => fixes_sb_escCharset 0x28 0x42 (by decide))).append
          ((Fixes.streamPred _).ite (fun _ => fixes_sb_escCharset 0x29 0x30 (by decide))
            (fun _ => fixes_sb_escCharset 0x29 0x42 (by decide)))).append
      ?_
  exact (Fixes.streamPred _).ite (fun _ => fixes_sb_shiftOut) (fun _ => Fixes.nil _)

theorem fixes_sb_cursorAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (cursorAnsi v) := by
  unfold cursorAnsi
  exact
    (Fixes.streamPred _).ite
      (fun _ => fixes_csiNum2 psBlind_sb _ _ 0x48 (by decide) (by decide) sb_csiDispatch_cup)
      (fun _ => fixes_csiNum2 psBlind_sb _ _ 0x48 (by decide) (by decide) sb_csiDispatch_cup)

/-- **The scroll region replay leaves the ring alone.** `DECSTBM` writes `top`/`bot` and
homes the cursor. -/
theorem fixes_sb_regionAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (regionAnsi v) := by
  unfold regionAnsi
  exact
    (Fixes.streamPred _).ite (fun _ => Fixes.nil _)
      (fun _ => fixes_csiNum2 psBlind_sb _ _ 0x72 (by decide) (by decide) sb_csiDispatch_stbm)

/-- **The ruler replay leaves the ring alone**: `TBC 3` writes `tabs`, and each stop is a
`CHA` (cursor column) plus an `HTS` (`ESC H`, one stop). This is the stage whose bytes the
ruler's own tail had to refuse, which is why `fixes_sb_escSeq` admits `0x48`. -/
theorem fixes_sb_tabsAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (tabsAnsi v) := by
  unfold tabsAnsi
  refine (fixes_csiNum psBlind_sb 3 0x67 (by decide) (by decide) sb_csiDispatch_tbc).append ?_
  refine (Fixes.streamPred _).flatMap (fun i => ?_)
  exact
    (fixes_csiNum psBlind_sb (i + 1) 0x47 (by decide) (by decide) sb_csiDispatch_cha).append
      (fixes_sb_escSeq 0x48 (by decide))

/-- **The ring survives everything `restore` emits after `tabsAnsi`**: the DECSC slot, the
title, the mode replay, the charset designations, the trailing pen and the final cursor
address. The ruler's twin, and the reason the two files' byte lists differ is recorded in
the header. -/
theorem fixes_sb_tail (v : Vt) :
    Fixes (fun v : Vt => v.sb)
      (savedAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen ++
        cursorAnsi v) :=
  (((((fixes_sb_savedAnsi v).append (fixes_sb_titleAnsi v)).append (fixes_sb_modesAnsi v)).append
            (fixes_sb_charsetAnsi v)).append
        (fixes_penSgr psBlind_sb v.pen sb_csiDispatch_sgr)).append
    (fixes_sb_cursorAnsi v)

/-! ### `CRLF` at the region bottom — the step the history walk runs once per row

`Theorems/Render/Grid.lean`'s `crlf_step` is the *interior* case, where the line feed moves
the cursor down and the grid is untouched; that is what makes the screen paint scroll-free.
The history push is the other case on purpose: each `CRLF` at `bot` scrolls the region and
pushes the row that was on top into the receiver's ring, which is the only way to put a line
into a terminal's own scrollback. -/

/-- **`CRLF` at the region bottom scrolls**, as a full state equation. `crlf_step`'s twin. -/
theorem crlf_scroll_step {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hy : v.cursor.y = v.bot) : v.feed [0x0D, 0x0A] = v.carriageReturn.scrollUp := by
  rw [crlf_feed hg hu,
    lineFeed_scroll v.carriageReturn
      (by
        rw [show v.carriageReturn.cursor.y = v.cursor.y from rfl,
          show v.carriageReturn.bot = v.bot from rfl, hy])]
  rfl

/-- **…and what it pushes: the row that was on top of the screen, exactly once.** The
hypotheses are the entry state `paint_entry`/`scrollback_entry` establish — full-screen
region, main screen — so a caller in the walk has them already. -/
theorem crlf_scroll_sb {v : Vt} (hg : v.pstate = .ground) (hu : v.u8need = 0)
    (hy : v.cursor.y = v.bot) (htop : v.top = 0) (hbot : v.bot = v.rows - 1)
    (halt : v.altGrid = none) : (v.feed [0x0D, 0x0A]).sb = v.sb.push (v.getRow 0) := by
  rw [crlf_scroll_step hg hu hy]
  unfold Vt.scrollUp
  rw [show v.carriageReturn.top = 0 from by
      rw [frame_carriageReturn]; exact htop,
    scrollUpIn_sb_push v.carriageReturn v.carriageReturn.bot
      (by
        rw [frame_carriageReturn]; exact hbot)
      (by
        rw [frame_carriageReturn]; exact halt)]
  rw [show v.carriageReturn.sb = v.sb from by rw [frame_carriageReturn],
    show v.carriageReturn.getRow 0 = v.getRow 0 from by
      unfold Vt.getRow; rw [frame_carriageReturn]]

end Linger.Core.Render
