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
theorem rowSlot_eq_nonzero (B : Bytes) (p : Pen) (x : Nat) (c : Cell) (hw : ¬ c.width = 0) :
    rowSlot (B, p, x) c
      = ((if c.pen == p then B else B ++ penSgr c.pen)
          ++ (if c.width == 2 && !c.marks.isEmpty then
                utf8 (safeChar c.base) ++ csiNum (x + 2) 0x47 ++ utf8s c.marks
                  ++ csiNum (x + 3) 0x47
              else cellText c), c.pen, x + 1) := by
  unfold rowSlot
  dsimp only
  rw [ite_eq_right (by simp [hw] : ¬ (c.width == 0))]

/-- **The seed lemma.** Painting a row from pen `p` instead of pen `q` costs at
most one `penSgr q` more, however long the row is: the excess is one optional
`SGR` at the first non-shadow cell and never accumulates. The disjunction is the
induction's invariant — either the two folds have converged (same pen, bounded
byte excess) or they have not yet diverged (`p2` is still the seed `q`, equal
lengths). -/
theorem foldl_rowSlot_seed (q : Pen) :
    ∀ (cs : List Cell) (B1 B2 : Bytes) (p1 p2 : Pen) (x : Nat),
    ((p1 = p2 ∧ B1.length ≤ B2.length + (penSgr q).length)
      ∨ (p2 = q ∧ B1.length = B2.length)) →
    (cs.foldl rowSlot (B1, p1, x)).1.length
      ≤ (cs.foldl rowSlot (B2, p2, x)).1.length + (penSgr q).length
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
        · exact Or.inl ⟨hp, by simp only [List.length_append]; omega⟩
        · exact Or.inr ⟨hp, by simp only [List.length_append]; omega⟩
      · rw [rowSlot_eq_nonzero B1 p1 x c hw, rowSlot_eq_nonzero B2 p2 x c hw]
        refine foldl_rowSlot_seed q cs _ _ _ _ _ (Or.inl ⟨rfl, ?_⟩)
        have key : (if c.pen == p1 then B1 else B1 ++ penSgr c.pen).length
            ≤ (if c.pen == p2 then B2 else B2 ++ penSgr c.pen).length
                + (penSgr q).length := by
          rcases h with ⟨hp, hle⟩ | ⟨hp, he⟩
          · rw [hp]
            by_cases hq : c.pen == p2
            · rw [ite_eq_left hq, ite_eq_left hq]; omega
            · rw [ite_eq_right hq, ite_eq_right hq]; simp only [List.length_append]; omega
          · by_cases hq : c.pen == p2
            · rw [ite_eq_left hq]
              have hcq : penSgr c.pen = penSgr q := by
                rw [show c.pen = p2 from by simpa using hq, hp]
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
  have hd : digits 0 = [0x30] := by rw [digits]; simp
  simp [penSgr, sgrColorSeq, colorCodes, penAttrCodes, sgrOf, joinSemi, csiB, hd]

/-- **The `+ 6` made a claim.** Whatever pen is in effect when a replayed row is
painted, its emitted bytes are within that row's counted `sbRowCost` — so the
budget's arithmetic is about the same rows the stage emits.

The bound is tight at the row level: `penSgr {}` = 4 is attained (a blank
80-column row is 80 bytes from the default pen and 84 from a truecolour one), so
the slack is not trimmable, and the remaining `+ 2` is the pushing CRLF the
emitted paint does not contain. -/
theorem rowAnsi_len_le_cost (row : Row) (p : Pen) :
    (rowAnsi row p).1.length ≤ sbRowCost row := by
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
  rw [ite_eq_right (by
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or, Nat.not_lt]
    exact ⟨h.1, h.2⟩)]

/-- Every clause of `CellOk`, by construction and with **no** hypothesis on the
cell: the base is `printableChar`'d, a non-shadow's width is `charWidth` of that
base, the marks are filtered to zero-width printables and capped at eight. -/
theorem cellOk_cellFit (c : Cell) : CellOk (cellFit c) := by
  refine ⟨printableChar_emittable _, fun hw => ?_, ?_, fun m hm => ?_⟩
  · show charWidth (printableChar c.base) = if c.width == 0 then 0 else charWidth (printableChar c.base)
    by_cases hz : c.width = 0
    · exact absurd (by show (if c.width == 0 then 0 else charWidth (printableChar c.base)) = 0
                       rw [ite_eq_left (by simp [hz])]) hw
    · rw [ite_eq_right (by simp [hz])]
  · show ((c.marks.filter _).take 8).length ≤ 8
    rw [List.length_take]
    omega
  · have hm' := List.mem_of_mem_take hm
    have hp := (List.mem_filter.mp hm').2
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨hp.1, by rw [← hp.2]; exact printableChar_emittable m⟩

/-- **Unconditional.** `Row.mend` supplies the pairs, `cells_map_range` the cells,
and the `Array.range` the exact width. -/
theorem rowOk_fitRow (row : Row) (cols : Nat) : RowOk cols (fitRow row cols) := by
  unfold fitRow
  exact rowOk_mend (by simp) (cells_map_range _ _ (fun i => cellOk_cellFit _))

/-- The fit is the **identity** on a cell a repaint could already reproduce. -/
theorem cellFit_id {c : Cell} (h : CellOk c) : cellFit c = c := by
  have hbase : printableChar c.base = c.base := printableChar_id_of_emittable h.base
  have hmarks : (c.marks.filter (fun m => charWidth m == 0 && printableChar m == m)).take 8
      = c.marks := by
    rw [List.filter_eq_self.mpr (fun a ha => ?_)]
    · exact List.take_of_length_le h.marksLe
    · obtain ⟨hw, hem⟩ := h.marks a ha
      simp [hw, printableChar_id_of_emittable hem]
  have hwidth : (if c.width == 0 then 0 else charWidth c.base) = c.width := by
    by_cases hz : c.width = 0
    · rw [ite_eq_left (by simp [hz]), hz]
    · rw [ite_eq_right (by simp [hz])]; exact h.width hz
  show ({ base := printableChar c.base,
          width := if c.width == 0 then 0 else charWidth (printableChar c.base),
          marks := (c.marks.filter (fun m => charWidth m == 0 && printableChar m == m)).take 8,
          pen := c.pen } : Cell) = c
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
      sbTake cols budget l
        = (l.take (sbTake cols budget l).length).map (fun r => fitRow r cols)
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
theorem sbRows_budget (v : Vt) :
    ((sbRows v).toList.map sbRowCost).sum ≤ sbReplayBytes := by
  unfold sbRows
  rw [List.toList_toArray, List.map_reverse, List.sum_reverse]
  exact sbTake_budget v.cols sbReplayBytes v.sb.toList.reverse

end Linger.Core.Render
