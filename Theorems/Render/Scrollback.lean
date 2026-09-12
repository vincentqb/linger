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

/-! ## `ED 2` keeps the ring — and why the generic CSI walk cannot say so

`fixes_csiNum`'s dispatch obligation is quantified over **every** `CsiState`, and at
`final = 0x4A` that obligation is false: `eraseScreen 3` sets `sb := {}`. So `ED 2` needs the
emitted parameter identified with the parsed one — the repo's "digit bridge", which existed
only at `π := (·.grid)` (`keeps_csi_digits_tail`). It is generalized over `π` below, the same
move `csi_tail_proj` makes for the unconditional walk.

`fixes_csiNum` is **not** made redundant by the bridge form: it takes an unconditional
obligation and admits `n = 0`, which the bridge cannot (`arg_of_one` needs `0 < n`). -/

namespace Linger.Core.Vt

theorem sb_eraseRowSpan (v : Vt) (y f t : Nat) : (v.eraseRowSpan y f t).sb = v.sb := by
  unfold Vt.eraseRowSpan
  dsimp only

theorem foldl_eraseRowSpan_sb :
    ∀ (l : List Nat) (v : Vt), (l.foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) v).sb = v.sb
  | [], _ => rfl
  | i :: is, v => by
    rw [List.foldl_cons, foldl_eraseRowSpan_sb is (v.eraseRowSpan i 0 v.cols), sb_eraseRowSpan]

/-- **`ED 2` clears cells and keeps history**, which is the whole difference between it and
`ED 3` and the reason `restore` can start with a clean slate without discarding the ring it
is about to replay. -/
theorem sb_eraseScreen_two (v : Vt) : (v.eraseScreen 2).sb = v.sb := by
  rw [eraseScreen_two_eq]
  exact foldl_eraseRowSpan_sb _ v

end Linger.Core.Vt

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ### The digit bridge, for any projection -/

theorem fixes_csi_digits_tail {α : Type} {π : Vt → α} (hb : PsBlind π) (n : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) (hn : 0 < n) (hlt : n < 65535)
    (hπ : ∀ (w : Vt) (t : CsiState), t.arg 0 0 = n → π (w.csiDispatch t final) = π w) {v : Vt}
    {s : CsiState} (hg : v.pstate = .csi s) (hu : v.u8need = 0) (hi : s.inter = 0)
    (hcur : s.cur = 0) (hpar : s.params = #[]) :
    (v.feed (digits n ++ [final])).pstate = .ground ∧
      (v.feed (digits n ++ [final])).u8need = 0 ∧ π (v.feed (digits n ++ [final])) = π v := by
  obtain ⟨s', heq, hcur', hhave, hpar', hint, -⟩ := csi_digits_run_eq n hg hu hcur
  rw [show ∀ (w : Vt), w.feed (digits n ++ [final]) = (w.feed (digits n)).feed [final] from fun w =>
      by simp [Vt.feed, List.foldl_append]]
  rw [heq, show ∀ (w : Vt), w.feed [final] = w.step final from fun _ => rfl]
  rw [csi_final_step_eq final rfl (by simpa using hu)
      (by
        rw [hint]; exact hi)
      h1 h2]
  unfold Vt.csiFinish
  rw [ite_eq_left (by simpa using hhave),
    ite_eq_right
      (by
        rw [hpar', hpar]; simp)]
  dsimp only
  refine
    ⟨rfl, by
      rw [un_csiDispatch]; simpa using hu, ?_⟩
  have harg :
    ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState).arg 0 0 =
      n := by
    rw [show
        ({ s' with params := s'.params.push (min s'.cur 65535, s'.curSub) } : CsiState) =
          { s' with params := #[(n, s'.curSub)] }
        from by
        rw [hpar', hpar, hcur']
        rw [show min (min n 65535) 65535 = n from by omega]
        rfl]
    rw [arg_of_one, ite_eq_right (by omega)]
  rw [hb _ PState.ground, hπ _ _ harg, hb v (PState.csi s')]

theorem fixes_csiNum_arg {α : Type} {π : Vt → α} (hb : PsBlind π) (n : Nat) (final : UInt8)
    (h1 : 0x40 ≤ final) (h2 : final ≤ 0x7E) (hn : 0 < n) (hlt : n < 65535)
    (hπ : ∀ (w : Vt) (t : CsiState), t.arg 0 0 = n → π (w.csiDispatch t final) = π w) :
    Fixes π (csiNum n final) := by
  intro v hg hu
  rw [show csiNum n final = [0x1B, 0x5B] ++ (digits n ++ [final]) from by
      unfold csiNum csiB; simp]
  rw [show
      ∀ (w : Vt),
        w.feed ([0x1B, 0x5B] ++ (digits n ++ [final])) =
          (w.feed [0x1B, 0x5B]).feed (digits n ++ [final])
      from fun w => by simp [Vt.feed, List.foldl_append]]
  rw [keeps_csi_open hg hu]
  obtain ⟨hp', hu', hπ'⟩ :=
    fixes_csi_digits_tail hb n final h1 h2 hn hlt hπ (v := { v with pstate := .csi {} }) rfl
      (by simpa using hu) rfl rfl rfl
  exact ⟨hp', hu', by rw [hπ', hb v (PState.csi {})]⟩

theorem sb_csiDispatch_ed2 (v : Vt) (s : CsiState) (ha : s.arg 0 0 = 2) :
    (v.csiDispatch s 0x4A).sb = v.sb := by
  by_cases hi : s.ignore = true
  · simp [Vt.csiDispatch, hi]
  · unfold Vt.csiDispatch
    rw [ite_eq_right hi]
    show (v.eraseScreen (s.arg 0 0)).sb = v.sb
    rw [ha, sb_eraseScreen_two]

theorem fixes_sb_ed2 : Fixes (fun v : Vt => v.sb) (csiNum 2 0x4A) :=
  fixes_csiNum_arg psBlind_sb 2 0x4A (by decide) (by decide) (by omega) (by omega)
    (fun w t ha => sb_csiDispatch_ed2 w t ha)

/-- `SI` (shift in). `fixes_sb_shiftOut` is `SO` (`0x0E`), which `charsetAnsi` emits; the
prologue emits this one, and the near-miss is a real gap rather than a rename. -/
theorem fixes_sb_shiftIn : Fixes (fun v : Vt => v.sb) [0x0F] := by
  intro v hg hu
  rw [show ∀ (w : Vt), w.feed [(0x0F : UInt8)] = w.step 0x0F from fun _ => rfl]
  rw [step_of_ground_quiet (0x0F : UInt8) hg hu]
  show _ ∧ _ ∧ _
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  unfold Vt.ctl
  exact ⟨hg, by simpa using hu, rfl⟩

/-- **The prologue keeps the ring.** Nine stages, and every byte is inside the family: no
`J`, no `RIS` (`0x63`, which clears the ring), no `IND`/`NEL`/`RI` (`0x44`/`0x45`/`0x4D`,
which scroll). -/
theorem fixes_sb_prologueAnsi (v : Vt) : Fixes (fun v : Vt => v.sb) (prologueAnsi v) := by
  unfold prologueAnsi
  refine Fixes.append ?_ fixes_sb_shiftIn
  refine Fixes.append ?_ (fixes_sb_escCharset 0x29 0x42 (by decide))
  refine Fixes.append ?_ (fixes_sb_escCharset 0x28 0x42 (by decide))
  refine
    Fixes.append ?_
      (fixes_csiNum2 psBlind_sb 1 v.rows 0x72 (by decide) (by decide) sb_csiDispatch_stbm)
  refine Fixes.append ?_ (fixes_sb_modeSet 7 true)
  refine Fixes.append ?_ (fixes_sb_modeSet 6 false)
  refine Fixes.append ?_ (fixes_csiNum psBlind_sb 4 0x6C (by decide) (by decide) sb_csiDispatch_rm)
  exact (fixes_sb_escSeq 0x5C (by decide)).append (fixes_sb_modeSet 1049 false)

/-- **The whole clear-and-paint prefix keeps the ring** — the prefix `ascii_paint_prefix`
quotes, which is what lets Step 4 walk past it in one rewrite. -/
theorem fixes_sb_paint_prefix (v : Vt) :
    Fixes (fun v : Vt => v.sb) (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A) :=
  ((fixes_sb_prologueAnsi v).append
        (fixes_csiNum psBlind_sb 0 0x6D (by decide) (by decide) sb_csiDispatch_sgr)).append
    fixes_sb_ed2

/-- The history walk's byte stream, one unit per row: paint the row, then a `CRLF`. -/
def pushBytes : List Row → Pen → Bytes
  | [], _ => []
  | r :: rs, p => (rowAnsi r p).1 ++ crlfB ++ pushBytes rs (rowAnsi r p).2

theorem joinCRLF_cons2 (b c : Bytes) (bs : List Bytes) :
    joinCRLF (b :: c :: bs) = b ++ crlfB ++ joinCRLF (c :: bs) := by rfl

/-- **The flush's first `CRLF` completes the walk.** `joinCRLF` omits the trailing separator,
so the first of the `v.rows` flushing `CRLF`s is the last row's own pushing one — which is
what makes the walk uniform and `rows = 1` need no special case. -/
theorem pushBytes_eq :
    ∀ (rs : List Row) (p : Pen), rs ≠ [] → pushBytes rs p = joinCRLF (rowsAnsi rs p) ++ crlfB
  | [], _, h => absurd rfl h
  | [r], p, _ => by
    show
      (rowAnsi r p).1 ++ crlfB ++ pushBytes [] (rowAnsi r p).2 = joinCRLF [(rowAnsi r p).1] ++ crlfB
    show (rowAnsi r p).1 ++ crlfB ++ [] = (rowAnsi r p).1 ++ crlfB
    simp
  | r :: r' :: rs, p, _ => by
    show
      (rowAnsi r p).1 ++ crlfB ++ pushBytes (r' :: rs) (rowAnsi r p).2 =
        joinCRLF (rowsAnsi (r :: r' :: rs) p) ++ crlfB
    rw [pushBytes_eq (r' :: rs) (rowAnsi r p).2 (by simp),
      show rowsAnsi (r :: r' :: rs) p = (rowAnsi r p).1 :: rowsAnsi (r' :: rs) (rowAnsi r p).2 from
        rfl,
      show
        rowsAnsi (r' :: rs) (rowAnsi r p).2 =
          (rowAnsi r' (rowAnsi r p).2).1 :: rowsAnsi rs (rowAnsi r' (rowAnsi r p).2).2
        from rfl,
      joinCRLF_cons2]
    simp only [List.append_assoc]

theorem flatten_replicate_crlfB_add (a b : Nat) :
    (List.replicate (a + b) crlfB).flatten =
      (List.replicate a crlfB).flatten ++ (List.replicate b crlfB).flatten := by
  induction a with
  | zero => simp
  | succ n ih =>
    simp only [Nat.succ_add, List.replicate_succ, List.flatten_cons, ih, List.append_assoc]

structure Painted (cols rows : Nat) (L B : List Row) (off D Y : Nat) (p : Pen) (u : Vt) : Prop where
  colsEq : u.cols = cols
  rowsEq : u.rows = rows
  top : u.top = 0
  bot : u.bot = rows - 1
  alt : u.altGrid = none
  ground : u.pstate = .ground
  u8need : u.u8need = 0
  u8acc : u.u8acc = 0
  ins : u.modes.insert = false
  wrap : u.modes.wrap = true
  g0 : u.g0Line = false
  g1 : u.g1Line = false
  cury : u.cursor.y = Y
  pen : u.pen = p
  gsz : u.grid.size = rows
  rlens : ∀ y', (u.getRow y').size = cols
  known : ∀ y', y' < D → u.getRow y' = L.getD (off + y') default
  dle : D ≤ rows
  ylt : Y < rows
  sbStart : u.sb.start = 0
  sbData : u.sb.data.toList = B ++ L.take off
  sum : off + D ≤ L.length

structure Pushing (cols rows : Nat) (L B : List Row) (off D Y : Nat) (p : Pen) (u : Vt) :
    Prop extends Painted cols rows L B off D Y p u where
  curx : u.cursor.x = 0
  cpend : u.cursor.pending = false

/-- Rows a paint left alone are the same rows. -/
theorem row_eq_of_offRow {y y' : Nat} {u u' : Vt} (hO : OffRow y u u') (hne : y' ≠ y)
    (hlt : y' < u.grid.size) : u'.getRow y' = u.getRow y' := by
  apply Array.ext
  · exact hO.sizes y'
  · intro i hi1 hi2
    show (u'.getRow y')[i] = (u.getRow y')[i]
    rw [show (u'.getRow y')[i] = u'.getCell i y' from (getD_lt' _ i default hi1).symm,
      show (u.getRow y')[i] = u.getCell i y' from (getD_lt' _ i default hi2).symm]
    exact hO.cells i y' hne hlt

/-- **The paint of one history row.** At the frontier (`D = Y`) the receiver paints row `Y`
with `L[off + Y]`; the row walk's `OffRow`/`SMap` layers carry every other field, the ring
included (`OffRow.sb`). -/
theorem pushing_paint {cols rows : Nat} {L B : List Row} {off Y : Nat} {p : Pen} {u : Vt} {r : Row}
    (hcb : cols < 65533) (hpos : 0 < cols) (hP : Pushing cols rows L B off Y Y p u)
    (hrok : RowOk cols r) (hval : r = L.getD (off + Y) default) (hsum : off + (Y + 1) ≤ L.length) :
    Painted cols rows L B off (Y + 1) Y (rowAnsi r p).2 (u.feed (rowAnsi r p).1) := by
  have hrow_u : RowOk u.cols r := by
    rw [hP.colsEq]; exact hrok
  have hgsY : Y < u.grid.size := by
    rw [hP.gsz]; exact hP.ylt
  have hm0 : Matches u { x := 0, y := Y, pen := p, pending := false } r 0 :=
    matches_zero hP.curx hP.cury hP.cpend hP.pen hP.ground hP.u8need hP.u8acc hP.ins hP.wrap hP.g0
      hP.g1 (by rw [hP.rlens Y, hP.colsEq]) hgsY
  obtain ⟨pd, hM, hO⟩ :=
    rowAnsi_writes_row hrow_u
      (by
        rw [hP.colsEq]; exact hcb)
      (by
        rw [hP.colsEq]; exact hpos)
      hm0
  have hrowY : (u.feed (rowAnsi r p).1).getRow Y = r :=
    row_eq_of_paint (cols := u.cols) hO.cols hrow_u hM
  have hstick : stick (u.feed (rowAnsi r p).1) = stick u := (smap_id_rowAnsi r p u hP.ground).2
  have hylt := hP.ylt
  refine
    ⟨?_, ?_, ?_, ?_, ?_, hM.ground, hM.u8need, hM.u8acc, hM.ins, hM.wrap, ?_, ?_, hM.curY, hM.pen,
      ?_, ?_, ?_, by omega, hylt, ?_, ?_, hsum⟩
  · rw [hO.cols]; exact hP.colsEq
  · have := congrArg Sticky.rows hstick; rw [stick_rows, stick_rows] at this
    rw [this]; exact hP.rowsEq
  · have := congrArg Sticky.top hstick; rw [stick_top, stick_top] at this
    rw [this]; exact hP.top
  · have := congrArg Sticky.bot hstick; rw [stick_bot, stick_bot] at this
    rw [this]; exact hP.bot
  · have h : (u.feed (rowAnsi r p).1).altGrid.isSome = false := by
      have := congrArg Sticky.alt hstick; rw [stick_alt, stick_alt] at this
      rw [this, hP.alt]; rfl
    exact
      Option.not_isSome_iff_eq_none.mp
        (by
          rw [h]; simp)
  · have := congrArg Sticky.g0 hstick; rw [stick_g0, stick_g0] at this
    rw [this]; exact hP.g0
  · have := congrArg Sticky.g1 hstick; rw [stick_g1, stick_g1] at this
    rw [this]; exact hP.g1
  · rw [hO.gridSize]; exact hP.gsz
  · intro y'; rw [hO.sizes y']; exact hP.rlens y'
  · intro y' hy'
    rcases Nat.lt_or_ge y' Y with h | h
    · rw [row_eq_of_offRow hO (by omega)
          (by
            rw [hP.gsz]; omega)]
      exact hP.known y' h
    · have hyY : y' = Y := by omega
      subst hyY
      rw [hrowY, hval]
  · rw [hO.sb]; exact hP.sbStart
  · rw [hO.sb]; exact hP.sbData

/-- **The interior `CRLF`.** Above the region bottom the line feed only moves the cursor
down, so nothing but the cursor changes — `off` and `D` are untouched. -/
theorem painted_crlf_down {cols rows : Nat} {L B : List Row} {off D Y : Nat} {p : Pen} {u : Vt}
    (hP : Painted cols rows L B off D Y p u) (hy : Y < rows - 1) :
    Pushing cols rows L B off D (Y + 1) p (u.feed crlfB) := by
  have hylt := hP.ylt
  have hcury := hP.cury
  have hrowsEq := hP.rowsEq
  have hstate :
    u.feed crlfB = { u with cursor := { x := 0, y := u.cursor.y + 1, pending := false } } := by
    rw [show (crlfB : Bytes) = [0x0D, 0x0A] from rfl,
      crlf_step hP.ground hP.u8need
        (by
          rw [hP.cury, hP.bot]; omega)
        (by
          rw [hP.bot, hP.rowsEq]; omega)]
  rw [hstate]
  exact
    ⟨⟨hP.colsEq, hP.rowsEq, hP.top, hP.bot, hP.alt, hP.ground, hP.u8need, hP.u8acc, hP.ins, hP.wrap,
        hP.g0, hP.g1, by
        show u.cursor.y + 1 = Y + 1
        omega, hP.pen, hP.gsz, hP.rlens, hP.known, hP.dle, by omega, hP.sbStart, hP.sbData, hP.sum⟩,
      rfl, rfl⟩

/-- **The `CRLF` at the region bottom.** It scrolls: the oldest on-screen history row is
pushed into the receiver's ring (`off + 1`), the rest shift up by one (`D - 1`), and the
cursor stays where it is. No index arithmetic — row `y'` becomes what row `y' + 1` was. -/
theorem painted_crlf_push {cols rows : Nat} {L B : List Row} {off D Y : Nat} {p : Pen} {u : Vt}
    (hroom : B.length + L.length ≤ sbCap) (hP : Painted cols rows L B off D Y p u)
    (hy : Y = rows - 1) (hD : 1 ≤ D) :
    Pushing cols rows L B (off + 1) (D - 1) Y p (u.feed crlfB) := by
  have hylt := hP.ylt
  have hdle := hP.dle
  have hsum := hP.sum
  have hoff : off < L.length := by omega
  have hcrRow : ∀ z, u.carriageReturn.getRow z = u.getRow z := fun z => by
    unfold Vt.getRow; rw [frame_carriageReturn]
  have hcrGsz : u.carriageReturn.grid.size = rows := by
    rw [show u.carriageReturn.grid = u.grid from by rw [frame_carriageReturn]]; exact hP.gsz
  have hsu : u.carriageReturn.scrollUp = u.carriageReturn.scrollUpIn 0 (rows - 1) true := by
    unfold Vt.scrollUp
    rw [show u.carriageReturn.top = 0 from by
        rw [frame_carriageReturn]; exact hP.top,
      show u.carriageReturn.bot = rows - 1 from by
        rw [frame_carriageReturn]; exact hP.bot]
  have hsbEq : (u.carriageReturn.scrollUpIn 0 (rows - 1) true).sb = u.sb.push (u.getRow 0) := by
    rw [scrollUpIn_sb_push u.carriageReturn (rows - 1)
        (by
          rw [show u.carriageReturn.rows = rows from by
              rw [frame_carriageReturn]; exact hP.rowsEq])
        (by
          rw [frame_carriageReturn]; exact hP.alt),
      show u.carriageReturn.sb = u.sb from by rw [frame_carriageReturn], hcrRow 0]
  obtain ⟨hshift, hvac, hout⟩ :=
    scrollUpIn_rows u.carriageReturn 0 (rows - 1) true (by omega)
      (by
        rw [hcrGsz]; omega)
  have hGsz : (u.carriageReturn.scrollUpIn 0 (rows - 1) true).grid.size = rows := by
    rw [grid_scrollUpIn, Array.size_setIfInBounds, size_foldl_setRange]; exact hcrGsz
  have hstate :
    u.feed crlfB =
      { u with
        cursor := { x := 0, y := u.cursor.y, pending := false }
        grid := (u.carriageReturn.scrollUpIn 0 (rows - 1) true).grid
        sb := u.sb.push (u.getRow 0) } := by
    rw [show (crlfB : Bytes) = [0x0D, 0x0A] from rfl,
      crlf_scroll_step hP.ground hP.u8need (by rw [hP.cury, hP.bot, hy]), hsu, frame_scrollUpIn,
      hsbEq]
    rfl
  have hrowEq :
    ∀ y', (u.feed crlfB).getRow y' = (u.carriageReturn.scrollUpIn 0 (rows - 1) true).getRow y' := by
    intro y'
    unfold Vt.getRow
    rw [hstate,
      show (u.carriageReturn.scrollUpIn 0 (rows - 1) true).cols = u.cols from by
        rw [frame_scrollUpIn, frame_carriageReturn],
      show (u.carriageReturn.scrollUpIn 0 (rows - 1) true).pen = u.pen from by
        rw [frame_scrollUpIn, frame_carriageReturn]]
  have hsize : u.sb.data.size = B.length + off := by
    rw [show u.sb.data.size = u.sb.data.toList.length from by simp, hP.sbData]
    simp only [List.length_append, List.length_take]
    omega
  have hcap : u.sb.data.size < sbCap := by
    rw [hsize]; omega
  obtain ⟨hpd, hps⟩ := ring_push_data (r := u.sb) (u.getRow 0) hcap
  refine
    ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by omega, hylt, ?_, ?_, by
        omega⟩,
      ?_, ?_⟩
  · rw [hstate]; exact hP.colsEq
  · rw [hstate]; exact hP.rowsEq
  · rw [hstate]; exact hP.top
  · rw [hstate]; exact hP.bot
  · rw [hstate]; exact hP.alt
  · rw [hstate]; exact hP.ground
  · rw [hstate]; exact hP.u8need
  · rw [hstate]; exact hP.u8acc
  · rw [hstate]; exact hP.ins
  · rw [hstate]; exact hP.wrap
  · rw [hstate]; exact hP.g0
  · rw [hstate]; exact hP.g1
  · rw [hstate]; exact hP.cury
  · rw [hstate]; exact hP.pen
  · rw [hstate]; exact hGsz
  · intro y'
    rw [hrowEq y']
    rcases Nat.lt_trichotomy y' (rows - 1) with h | h | h
    · rw [hshift y' (Nat.zero_le _) h, hcrRow (y' + 1)]; exact hP.rlens (y' + 1)
    · subst h
      rw [hvac,
        show (blankRow u.carriageReturn.cols u.carriageReturn.pen).size = u.cols from by
          simp [blankRow, show u.carriageReturn.cols = u.cols from by rw [frame_carriageReturn]]]
      exact hP.colsEq
    · rw [hout y' (Or.inr h), hcrRow y']; exact hP.rlens y'
  · intro y' hy'
    rw [hrowEq y', hshift y' (Nat.zero_le _) (by omega), hcrRow (y' + 1),
      hP.known (y' + 1) (by omega), show off + (y' + 1) = off + 1 + y' from by omega]
  · rw [hstate]
    show (u.sb.push (u.getRow 0)).start = 0
    rw [hps]; exact hP.sbStart
  · rw [hstate]
    show (u.sb.push (u.getRow 0)).data.toList = B ++ L.take (off + 1)
    rw [hpd]
    simp only [Array.toList_push]
    rw [hP.sbData, hP.known 0 (by omega), Nat.add_zero, take_succ_getD L off hoff,
      List.append_assoc]
  · rw [hstate]
  · rw [hstate]

/-! ### The three inductions -/

/-- **The row walk.** Each unit paints one history row and pushes it down by a `CRLF`; the
`CRLF` either descends (`Y < bot`, `off` and `D` unchanged) or scrolls (`Y = bot`, one row
evicted). Either way the frontier invariant `D = Y` comes back, so the two phases are one
induction and no height is special. -/
theorem push_units {cols rows : Nat} {L B : List Row} (hcb : cols < 65533) (hpos : 0 < cols)
    (hroom : B.length + L.length ≤ sbCap) :
    ∀ (rs : List Row) (off Y : Nat) (p : Pen) (u : Vt),
      Pushing cols rows L B off Y Y p u →
        off + Y + rs.length = L.length →
        (∀ i (hi : i < rs.length), RowOk cols rs[i]) →
        (∀ i (hi : i < rs.length), rs[i] = L.getD (off + Y + i) default) →
        ∃ off' Y' p',
          Pushing cols rows L B off' Y' Y' p' (u.feed (pushBytes rs p)) ∧ off' + Y' = L.length
  | [], off, Y, p, u, hP, hlen, _, _ =>
    ⟨off, Y, p, by
      show Pushing cols rows L B off Y Y p (u.feed [])
      rw [show u.feed ([] : Bytes) = u from rfl]
      exact hP, by simpa using hlen⟩
  | r :: rs, off, Y, p, u, hP, hlen, hrok, hval => by
    have hlen' : off + Y + rs.length + 1 = L.length := by
      simp only [List.length_cons] at hlen; omega
    have hylt := hP.ylt
    have hr0 : r = L.getD (off + Y) default := by
      have := hval 0 (by simp)
      simpa using this
    have hrok0 : RowOk cols r := by
      have := hrok 0 (by simp)
      simpa using this
    have hpaint : Painted cols rows L B off (Y + 1) Y (rowAnsi r p).2 (u.feed (rowAnsi r p).1) :=
      pushing_paint hcb hpos hP hrok0 hr0 (by omega)
    rw [show pushBytes (r :: rs) p = (rowAnsi r p).1 ++ crlfB ++ pushBytes rs (rowAnsi r p).2 from
        rfl,
      feed_append, feed_append]
    rcases Nat.lt_or_ge Y (rows - 1) with hlt | hge
    · have hstep := painted_crlf_down hpaint hlt
      exact
        push_units hcb hpos hroom rs off (Y + 1) (rowAnsi r p).2 _ hstep (by omega)
          (fun i hi => by
            have :=
              hrok (i + 1)
                (by
                  simp only [List.length_cons]; omega)
            simpa using this)
          (fun i hi => by
            have :=
              hval (i + 1)
                (by
                  simp only [List.length_cons]; omega)
            rw [show off + Y + (i + 1) = off + (Y + 1) + i from by omega] at this
            simpa using this)
    · have hYb : Y = rows - 1 := by omega
      have hstep := painted_crlf_push hroom hpaint hYb (by omega)
      rw [show Y + 1 - 1 = Y from by omega] at hstep
      exact
        push_units hcb hpos hroom rs (off + 1) Y (rowAnsi r p).2 _ hstep (by omega)
          (fun i hi => by
            have :=
              hrok (i + 1)
                (by
                  simp only [List.length_cons]; omega)
            simpa using this)
          (fun i hi => by
            have :=
              hval (i + 1)
                (by
                  simp only [List.length_cons]; omega)
            rw [show off + Y + (i + 1) = off + 1 + Y + i from by omega] at this
            simpa using this)

/-- **The flush, phase one.** From above the region bottom, a `CRLF` only walks the cursor
down; nothing is evicted. -/
theorem push_descend {cols rows : Nat} {L B : List Row} :
    ∀ (j off D Y : Nat) (p : Pen) (u : Vt),
      Pushing cols rows L B off D Y p u →
        Y + j ≤ rows - 1 →
        Pushing cols rows L B off D (Y + j) p (u.feed (List.replicate j crlfB).flatten)
  | 0, _, _, Y, _, u, hP, _ => by
    rw [show (List.replicate 0 crlfB).flatten = ([] : Bytes) from rfl,
      show u.feed ([] : Bytes) = u from rfl, Nat.add_zero]
    exact hP
  | j + 1, off, D, Y, p, u, hP, hle => by
    have hstep := painted_crlf_down hP.toPainted (by omega)
    have := push_descend j off D (Y + 1) p _ hstep (by omega)
    rw [show Y + (j + 1) = Y + 1 + j from by omega]
    rw [show (List.replicate (j + 1) crlfB).flatten = crlfB ++ (List.replicate j crlfB).flatten from
        by simp [List.replicate_succ],
      feed_append]
    exact this

/-- **The flush, phase two.** At the region bottom every `CRLF` evicts the oldest on-screen
history row into the receiver's ring. -/
theorem push_evict {cols rows : Nat} {L B : List Row} (hroom : B.length + L.length ≤ sbCap) :
    ∀ (j off D : Nat) (p : Pen) (u : Vt),
      Pushing cols rows L B off D (rows - 1) p u →
        j ≤ D →
        Pushing cols rows L B (off + j) (D - j) (rows - 1) p
          (u.feed (List.replicate j crlfB).flatten)
  | 0, off, D, _, u, hP, _ => by
    rw [show (List.replicate 0 crlfB).flatten = ([] : Bytes) from rfl,
      show u.feed ([] : Bytes) = u from rfl, Nat.add_zero, Nat.sub_zero]
    exact hP
  | j + 1, off, D, p, u, hP, hle => by
    have hstep := painted_crlf_push hroom hP.toPainted rfl (by omega)
    have := push_evict hroom j (off + 1) (D - 1) p _ hstep (by omega)
    rw [show off + (j + 1) = off + 1 + j from by omega, show D - (j + 1) = D - 1 - j from by omega]
    rw [show (List.replicate (j + 1) crlfB).flatten = crlfB ++ (List.replicate j crlfB).flatten from
        by simp [List.replicate_succ],
      feed_append]
    exact this

/-! ### The claim -/

/-- Every row the history stage paints is `RowOk` at the session's width, with **no**
hypothesis: `sbTake` fuses `fitRow` in and `rowOk_fitRow` is unconditional. This is what
keeps a `v.sb` hypothesis out of the walk. -/
theorem rowOk_mem_sbRows (v : Vt) : ∀ r ∈ (sbRows v).toList, RowOk v.cols r := by
  intro r hr
  rw [show (sbRows v).toList = (sbTake v.cols sbReplayBytes v.sb.toList.reverse).reverse from by
      unfold sbRows; simp] at hr
  rw [sbTake_prefix v.cols sbReplayBytes v.sb.toList.reverse] at hr
  rw [List.mem_reverse] at hr
  obtain ⟨q, -, hq⟩ := List.mem_map.mp hr
  rw [← hq]
  exact rowOk_fitRow q v.cols

/-- **The walk, from the stage's entry state.** The row units push `L` into the ring one row
at a time and the `rows - 1` remaining flush `CRLF`s drain whatever is still on screen; the
two together evict exactly `L`, oldest first. -/
theorem push_run {cols rows : Nat} {L B : List Row} {u : Vt} (hcb : cols < 65533) (hpos : 0 < cols)
    (hroom : B.length + L.length ≤ sbCap) (hP : Pushing cols rows L B 0 0 0 {} u)
    (hrok : ∀ i (hi : i < L.length), RowOk cols L[i]) :
    (u.feed (pushBytes L {} ++ (List.replicate (rows - 1) crlfB).flatten)).sb.toList = B ++ L := by
  obtain ⟨off', Y', p', hP', hsum'⟩ :=
    push_units hcb hpos hroom L 0 0 {} u hP (by simp) hrok
      (fun i hi => by simp [List.getElem?_eq_getElem hi])
  have hylt := hP'.ylt
  have hd := push_descend ((rows - 1) - Y') off' Y' Y' p' _ hP' (by omega)
  rw [show Y' + ((rows - 1) - Y') = rows - 1 from by omega] at hd
  have he := push_evict hroom Y' off' Y' p' _ hd (Nat.le_refl _)
  rw [Nat.sub_self] at he
  rw [feed_append,
    show
      (List.replicate (rows - 1) crlfB).flatten =
        (List.replicate ((rows - 1) - Y') crlfB).flatten ++ (List.replicate Y' crlfB).flatten
      from by rw [← flatten_replicate_crlfB_add, show rows - 1 - Y' + Y' = rows - 1 from by omega],
    feed_append, ring_toList_of_start_zero he.sbStart, he.sbData,
    show L.take (off' + Y') = L from List.take_of_length_le (by omega)]

/-- **`push_walk`.** Painting the fitted history rows and then flushing with `v.rows` CRLFs
pushes exactly those rows into the receiver's ring, oldest first.

The hypotheses are the state `scrollback_entry` hands the stage — a full-screen scroll
region on the main screen, a quiesced decoder, autowrap on, IRM and DECOM off, ASCII
charsets — plus the two the ring needs: the receiver never wrapped (`ED 3` leaves
`start = 0`) and the push has room, which after `ED 3` is `(sbRows v).size ≤ sbCap` from
`Good v` and `sbTake_prefix`. `rows = 1` is not a special case: at one row every `CRLF`
evicts, and the walk's frontier invariant is vacuous there rather than absent. -/
theorem push_walk (v w : Vt) (hw : Good w) (hren : Renderable w) (hcols : w.cols = v.cols)
    (hrows : w.rows = v.rows) (halt : w.altGrid = none) (htop : w.top = 0)
    (hbot : w.bot = v.rows - 1) (hgr : w.pstate = .ground) (hun : w.u8need = 0) (hua : w.u8acc = 0)
    (hins : w.modes.insert = false) (hwrap : w.modes.wrap = true) (horg : w.modes.origin = false)
    (hz0 : w.g0Line = false) (hz1 : w.g1Line = false) (hstart : w.sb.start = 0)
    (hroom : w.sb.size + (sbRows v).size ≤ sbCap) (hne : (sbRows v).isEmpty = false) :
    (w.feed (gridAnsi (sbRows v) ++ (List.replicate v.rows crlfB).flatten)).sb.toList =
      w.sb.toList ++ (sbRows v).toList := by
  have hposc : 0 < v.cols := by
    rw [← hcols]; exact hw.colsPos
  have hcb : v.cols < 65533 := by
    have := hw.colsLe; rw [hcols] at this; omega
  have hposr : 0 < v.rows := by
    rw [← hrows]; exact hw.rowsPos
  have hLne : (sbRows v).toList ≠ [] := by
    simp at hne
    simpa using hne
  -- the stream, split at the stage's two joints
  have hcrlfsplit :
    (List.replicate v.rows crlfB).flatten =
      crlfB ++ (List.replicate (v.rows - 1) crlfB).flatten := by
    obtain ⟨k, hk⟩ : ∃ k, v.rows = k + 1 := ⟨v.rows - 1, by omega⟩
    rw [hk]
    simp [List.replicate_succ]
  have hbytes :
    gridAnsi (sbRows v) ++ (List.replicate v.rows crlfB).flatten =
      csiNum 0 0x6D ++ (csiB ++ [0x48]) ++
        (pushBytes (sbRows v).toList {} ++ (List.replicate (v.rows - 1) crlfB).flatten) := by
    rw [gridAnsi_eq, hcrlfsplit, pushBytes_eq _ {} hLne]
    simp only [List.append_assoc]
  -- the entry state: reset the pen, home the cursor
  have hsgr : w.feed (csiNum 0 0x6D) = { w with pen := {} } := by
    rw [show csiNum 0 0x6D = sgrOf [0] from by simp [csiNum, sgrOf, joinSemi],
      sgrOf_feed [0] (by decide) (by decide) (by decide) hgr hun,
      show penAfter w.pen [0] = ({} : Pen) from by simp [penAfter, sgrParamsOf, Vt.applySgr.go]]
  have hu1 :
    w.feed (csiNum 0 0x6D ++ (csiB ++ [0x48])) =
      (({ w with pen := ({} : Pen) } : Vt)).moveTo 0 0 := by
    rw [feed_append, hsgr, home_feed_eq (v := { w with pen := ({} : Pen) }) hgr hun]
  have hcur := home_places_cursor (v := { w with pen := ({} : Pen) }) hgr hun horg
  rw [home_feed_eq (v := { w with pen := ({} : Pen) }) hgr hun] at hcur
  have hrlw : ∀ (P : Pen) (y' : Nat), ((({ w with pen := P } : Vt)).getRow y').size = v.cols := by
    intro P y'
    obtain ⟨-, hrok⟩ := hren.main
    show (w.grid.getD y' (blankRow w.cols P)).size = v.cols
    by_cases hy : y' < w.grid.size
    · rw [getD_lt' w.grid y' (blankRow w.cols P) hy]
      have h := (hrok y').size
      rw [getD_lt' w.grid y' (blankRow w.cols {}) hy] at h
      rw [h]; exact hcols
    · rw [Array.getD, dite_eq_right hy]
      show (blankRow w.cols P).size = v.cols
      rw [show (blankRow w.cols P).size = w.cols from by simp [blankRow]]; exact hcols
  have hP :
    Pushing v.cols v.rows (sbRows v).toList w.sb.data.toList 0 0 0 {}
      (w.feed (csiNum 0 0x6D ++ (csiB ++ [0x48]))) := by
    rw [hu1]
    refine
      ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcur.2.1, ?_, ?_, ?_, fun y' h =>
          absurd h (by omega), by omega, hposr, ?_, ?_, by simp⟩,
        hcur.1, hcur.2.2⟩
    · rw [frame_moveTo]; exact hcols
    · rw [frame_moveTo]; exact hrows
    · rw [frame_moveTo]; exact htop
    · rw [frame_moveTo]; exact hbot
    · rw [frame_moveTo]; exact halt
    · rw [frame_moveTo]; exact hgr
    · rw [frame_moveTo]; exact hun
    · rw [frame_moveTo]; exact hua
    · rw [frame_moveTo]; exact hins
    · rw [frame_moveTo]; exact hwrap
    · rw [frame_moveTo]; exact hz0
    · rw [frame_moveTo]; exact hz1
    · rw [frame_moveTo]
    · rw [frame_moveTo]
      show w.grid.size = v.rows
      obtain ⟨hgsz, -⟩ := hren.main
      rw [hgsz]; exact hrows
    · intro y'
      rw [show
          ((({ w with pen := ({} : Pen) } : Vt)).moveTo 0 0).getRow y' =
            (({ w with pen := ({} : Pen) } : Vt)).getRow y'
          from by
          unfold Vt.getRow; rw [frame_moveTo]]
      exact hrlw {} y'
    · rw [frame_moveTo]; exact hstart
    · rw [frame_moveTo]; simp
  have hroom' : (w.sb.data.toList).length + ((sbRows v).toList).length ≤ sbCap := by
    rw [show (w.sb.data.toList).length = w.sb.size from by simp [Ring.size],
      show ((sbRows v).toList).length = (sbRows v).size from by simp]
    exact hroom
  rw [hbytes, feed_append,
    push_run (cols := v.cols) (rows := v.rows) hcb hposc hroom' hP
      (fun i hi => rowOk_mem_sbRows v _ (List.getElem_mem hi)),
    ring_toList_of_start_zero hstart]

end Linger.Core.Render
