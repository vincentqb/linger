module

import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.History
import all Theorems.Render.Row
import all Theorems.Render.PendingGlyph
import all Theorems.Render.PendingAccumulator

namespace Linger.Core.Render

open Linger.Core.Vt

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

/-- Safe UTF-8 emission is the original glyph and marks on a canonical cell. -/
theorem cellText_feed_of_cellOk {w : Vt} {c : Cell} (hc : CellOk c) (hg : w.pstate = .ground)
    (hu : w.u8need = 0) (ha : w.u8acc = 0) :
    w.feed (cellText c) = c.marks.foldl (fun v m => v.print m) (w.print c.base) := by
  rw [cellText_feed c hg hu ha, safeChar_of_emittable hc.base]
  have hfold :
    ∀ (ms : List Char) (v : Vt),
      (∀ m ∈ ms, Emittable m) →
        ms.foldl (fun v m => v.print (safeChar m)) v = ms.foldl (fun v m => v.print m) v := by
    intro ms
    induction ms with
    | nil =>
      intros; exact List.foldl_nil.trans List.foldl_nil.symm
    | cons m ms ih =>
      intro v hm
      simp only [List.foldl_cons, safeChar_of_emittable (hm m (by simp))]
      exact ih _ (fun n hn => hm n (by simp [hn]))
  exact hfold _ _ (fun m hm => (hc.marks m hm).2)

/-- The byte-level form of the complete-state margin repaint. -/
theorem cellText_reprint_margin (w : Vt) (hg : Good w) (hr : Renderable w) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (hpend : w.cursor.pending = false) (hp : (w.getCell w.cursor.x w.cursor.y).pen = w.pen)
    (hwidth : (w.getCell w.cursor.x w.cursor.y).width ≠ 0)
    (hmargin : w.cursor.x + charWidth (w.getCell w.cursor.x w.cursor.y).base = w.cols)
    (hps : w.pstate = .ground) (hun : w.u8need = 0) (hua : w.u8acc = 0) :
    w.feed (cellText (w.getCell w.cursor.x w.cursor.y)) =
      { w with
        cursor :=
          { w.cursor with
            x := w.cols - 1, pending := true } } := by
  rw [cellText_feed_of_cellOk (cellOk_getCell hr _ _) hps hun hua]
  exact reprint_margin w hg hr h0 h1 hwrap hins hpend hp hwidth hmargin

/-- Changing the current pen does not change an existing row's cells. -/
theorem getCell_set_pen (w : Vt) (p : Pen) (x y : Nat) (hy : y < w.grid.size) :
    ({ w with pen := p } : Vt).getCell x y = w.getCell x y := by
  unfold Vt.getCell Vt.getRow
  rw [getD_of_lt w.grid y (blankRow w.cols p) (blankRow w.cols w.pen) hy]

/-- Address, set the cell's pen, repaint it, then restore the requested pen.
The row hypothesis states exactly where origin-relative CUP must land. -/
theorem reprintAnsi_feed_eq (w : Vt) (x y row : Nat) (pen : Pen) (hg : Good w) (hr : Renderable w)
    (h0 : w.g0Line = false) (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true)
    (hins : w.modes.insert = false) (hx : x < w.cols) (hy : y < w.rows) (hr0 : 0 < row)
    (hrcap : row ≤ 65535) (hrow : (w.moveTo x (row - 1)).cursor.y = y)
    (hwidth : (w.getCell x y).width ≠ 0) (hmargin : x + charWidth (w.getCell x y).base = w.cols)
    (hps : w.pstate = .ground) (hun : w.u8need = 0) (hua : w.u8acc = 0) :
    w.feed
        (csiNum2 row (x + 1) 0x48 ++ penSgr (w.getCell x y).pen ++ cellText (w.getCell x y) ++
          penSgr pen) =
      { w with
        cursor := { x := w.cols - 1, y := y, pending := true }, pen := pen } := by
  let u : Vt := { w.moveTo x (row - 1) with pen := (w.getCell x y).pen }
  have hux : u.cursor.x = x := by
    dsimp [u, Vt.moveTo]
    omega
  have huy : u.cursor.y = y := hrow
  have hcell : u.getCell u.cursor.x u.cursor.y = w.getCell x y := by
    rw [hux, huy]
    rw [getCell_set_pen _ _ x y (by simpa [Vt.moveTo, hr.main.1] using hy)]
    rfl
  have hrep :=
    cellText_reprint_margin u (Good.set_pen _ (Good.moveTo _ _ hg))
      (renderable_congr (v := w.moveTo x (row - 1)) (renderable_moveTo hr x (row - 1)) rfl rfl rfl
        rfl)
      h0 h1 hwrap hins rfl (by rw [hcell])
      (by
        rw [hcell]; exact hwidth)
      (by
        rw [hcell, hux]; exact hmargin)
      hps hun hua
  rw [hcell] at hrep
  rw [feed_append, feed_append, feed_append,
    cup_feed_eq row (x + 1) hr0 (by omega) hrcap
      (by
        have := hg.colsLe; omega)
      hps hun]
  simp only [Nat.add_sub_cancel]
  rw [penSgr_feed (v := w.moveTo x (row - 1)) _ hps hun]
  change (u.feed (cellText (w.getCell x y))).feed (penSgr pen) = _
  rw [hrep,
    penSgr_feed (v :=
      { u with
        cursor :=
          { u.cursor with
            x := u.cols - 1, pending := true } })
      _ hps hun]
  change
    ({ w with
          cursor := { x := w.cols - 1, y := u.cursor.y, pending := true }, pen := pen } :
        Vt) =
      _
  rw [huy]

/-- The guarded margin replay either emits nothing, or restores the supplied
cursor and pen while preserving every other field. The receiver owns the
canonical grid; no source cursor bounds are assumed when the guard rejects it. -/
theorem pendingAnsi_feed_eq (w : Vt) (cur : Cursor) (row : Nat) (pen : Pen) (hg : Good w)
    (hr : Renderable w) (h0 : w.g0Line = false) (h1 : w.g1Line = false)
    (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (hrow : cur.y < w.rows → 0 < row ∧ row ≤ 65535 ∧ (w.moveTo 0 (row - 1)).cursor.y = cur.y)
    (hps : w.pstate = .ground) (hun : w.u8need = 0) (hua : w.u8acc = 0) :
    w.feed (Linger.Core.Render.pendingAnsi w.cols w.grid cur row pen) =
      if pendingAnsi w.cols w.grid cur row pen = [] then w
      else
        { w with
          cursor := cur, pen := pen } := by
  let cells := w.grid.getD cur.y #[]
  let x := if (cells.at cur.x).width == 0 then cur.x - 1 else cur.x
  let c := cellFit (cells.at x)
  let bs := csiNum2 row (x + 1) 0x48 ++ penSgr c.pen ++ cellText c ++ penSgr pen
  change
    w.feed
        (if
            cur.pending && cur.y < w.grid.size && cur.x < cells.size && cur.x + 1 == w.cols &&
              charWidth c.base != 0 &&
              x + charWidth c.base == w.cols then
          bs
        else []) =
      if
          (if
                cur.pending && cur.y < w.grid.size && cur.x < cells.size && cur.x + 1 == w.cols &&
                  charWidth c.base != 0 &&
                  x + charWidth c.base == w.cols then
              bs
            else []) =
            [] then
        w
      else
        { w with
          cursor := cur, pen := pen }
  by_cases h :
    (cur.pending && cur.y < w.grid.size && cur.x < cells.size && cur.x + 1 == w.cols &&
        charWidth c.base != 0 &&
        x + charWidth c.base == w.cols) =
      true
  · rw [ite_eq_left h]
    have hh := h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at hh
    have hy : cur.y < w.rows := by
      rw [← hr.main.1]; omega
    have hm : cur.x + 1 = w.cols := hh.1.1.2
    have hp : cur.pending = true := hh.1.1.1.1.1
    have hcells : cells = w.getRow cur.y := by
      exact
        getD_of_lt w.grid cur.y #[] (blankRow w.cols w.pen)
          (by
            rw [hr.main.1]; exact hy)
    have hfit : cellFit (cells.at x) = w.getCell x cur.y := by
      rw [hcells]
      exact cellFit_id (cellOk_getCell hr x cur.y)
    have hx : x < w.cols := by
      dsimp [x]
      split <;> omega
    have hwidth : (w.getCell x cur.y).width ≠ 0 := by
      change ((w.getRow cur.y).at x).width ≠ 0
      rw [← hcells]
      dsimp [x]
      split
      · rename_i hz
        have hpair := ((rowOk_getRow hr cur.y).pairs cur.x).2
        rw [← hcells] at hpair
        have := hpair (by simpa using hz)
        omega
      · simpa using ‹¬(cells.at cur.x).width == 0›
    have hmargin : x + charWidth (w.getCell x cur.y).base = w.cols := by
      rw [← hfit]
      exact hh.2
    obtain ⟨hr0, hrcap, hry⟩ := hrow hy
    have he :=
      reprintAnsi_feed_eq w x cur.y row pen hg hr h0 h1 hwrap hins hx hy hr0 hrcap hry hwidth
        hmargin hps hun hua
    simp only [bs, c, hfit]
    rw [he]
    simp only [csiNum2, csiB, List.cons_append, List.nil_append, List.cons_ne_nil, ↓reduceIte]
    congr 1
    obtain ⟨cx, cy, cp⟩ := cur
    simp only at hm hp ⊢
    rw [hp, show w.cols - 1 = cx from by omega]
  · rw [ite_eq_right h]
    rfl

/-- Autowrap can be restored after a repaint without clearing pending wrap. -/
theorem wrap_feed_eq (on : Bool) {w : Vt} (hg : w.pstate = .ground) (hu : w.u8need = 0) :
    w.feed (modeSet 7 on) = { w with modes := { w.modes with wrap := on } } := by
  rw [modeSet_feed_eq 7 on (by decide) (by decide) hg hu]
  simp [Vt.setMode, ← hg]

/-- Charset replay is exact after SI, including the unshifted case's empty tail. -/
theorem charsetAnsi_feed_eq (v w : Vt) (hs : w.shiftOut = false) (hg : w.pstate = .ground)
    (hu : w.u8need = 0) :
    w.feed (charsetAnsi v) =
      { w with
        g0Line := v.g0Line, g1Line := v.g1Line, shiftOut := v.shiftOut } := by
  have h0 :
    w.feed (if v.g0Line then escCharset 0x28 0x30 else escCharset 0x28 0x42) =
      { w with g0Line := v.g0Line } := by
    cases v.g0Line <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [charset_feed_eq _ _ (Or.inl rfl) (by decide) (by decide) hg hu] <;>
      rfl
  have h1 :
    ({ w with g0Line := v.g0Line } : Vt).feed
        (if v.g1Line then escCharset 0x29 0x30 else escCharset 0x29 0x42) =
      { w with
        g0Line := v.g0Line, g1Line := v.g1Line } := by
    cases v.g1Line <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      rw [charset_feed_eq (w := { w with g0Line := v.g0Line }) _ _ (Or.inr rfl) (by decide)
          (by decide) hg hu] <;>
      rfl
  unfold charsetAnsi
  rw [feed_append, feed_append, h0, h1]
  cases hso : v.shiftOut
  · simp only [Bool.false_eq_true, ↓reduceIte, Vt.feed, List.foldl_nil]
    rw [← hs]
  · exact
      shift_feed_eq true (w :=
        { w with
          g0Line := v.g0Line, g1Line := v.g1Line })
        hg hu

/-- The active repaint establishes only the modes and charsets it reads. -/
theorem pending_prepare_feed (w : Vt) (hg : w.pstate = .ground) (hu : w.u8need = 0) :
    w.feed
        (modeSet 7 true ++ csiNum 4 0x6C ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++
          [0x0F]) =
      { w with
        modes :=
          { w.modes with
            wrap := true, insert := false },
        g0Line := false, g1Line := false, shiftOut := false } := by
  simp only [feed_append]
  have hi := irm_feed_eq (w := { w with modes := { w.modes with wrap := true } }) false hg hu
  simp only [Bool.false_eq_true, ↓reduceIte] at hi
  rw [wrap_feed_eq true hg hu, hi,
    charset_feed_eq (w :=
      { w with
        modes :=
          { w.modes with
            wrap := true, insert := false } })
      0x28 0x42 (Or.inl rfl) (by decide) (by decide) hg hu]
  simp only [beq_self_eq_true, show ((0x42 : UInt8) == 0x30) = false from rfl, ↓reduceIte]
  rw [charset_feed_eq (w :=
      { w with
        modes :=
          { w.modes with
            wrap := true, insert := false },
        g0Line := false })
      0x29 0x42 (Or.inr rfl) (by decide) (by decide) hg hu]
  simp only [show ((0x29 : UInt8) == 0x28) = false from rfl,
    show ((0x42 : UInt8) == 0x30) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  exact
    shift_feed_eq false (w :=
      { w with
        modes :=
          { w.modes with
            wrap := true, insert := false },
        g0Line := false, g1Line := false })
      hg hu

/-- Finishing the active repaint preserves the cursor, including pending wrap. -/
theorem pending_finish_feed (v w : Vt) (hs : w.shiftOut = false) (hg : w.pstate = .ground)
    (hu : w.u8need = 0) :
    w.feed
        (modeSet 7 v.modes.wrap ++ csiNum 4 (if v.modes.insert then 0x68 else 0x6C) ++
          charsetAnsi v ++
          penSgr v.pen) =
      { w with
        modes :=
          { w.modes with
            wrap := v.modes.wrap, insert := v.modes.insert },
        g0Line := v.g0Line, g1Line := v.g1Line, shiftOut := v.shiftOut, pen := v.pen } := by
  simp only [feed_append]
  rw [wrap_feed_eq _ hg hu,
    irm_feed_eq (w := { w with modes := { w.modes with wrap := v.modes.wrap } }) _ hg hu,
    charsetAnsi_feed_eq v
      { w with
        modes :=
          { w.modes with
            wrap := v.modes.wrap, insert := v.modes.insert } }
      hs hg hu,
    penSgr_feed (v :=
      { w with
        modes :=
          { w.modes with
            wrap := v.modes.wrap, insert := v.modes.insert },
        g0Line := v.g0Line, g1Line := v.g1Line, shiftOut := v.shiftOut })
      _ hg hu]

/-- CUP and a margin glyph restore the cursor without any grid assumptions. -/
theorem reprintAnsi_cursor_eq (w : Vt) (c : Cell) (x y row : Nat) (pen : Pen) (hg : Good w)
    (hc : CellOk c) (h0 : w.g0Line = false) (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true)
    (hins : w.modes.insert = false) (hx : x < w.cols) (hr0 : 0 < row) (hrcap : row ≤ 65535)
    (hrow : (w.moveTo x (row - 1)).cursor.y = y) (hwidth : charWidth c.base ≠ 0)
    (hmargin : x + charWidth c.base = w.cols) (hps : w.pstate = .ground) (hun : w.u8need = 0) :
    (w.feed (csiNum2 row (x + 1) 0x48 ++ penSgr c.pen ++ cellText c ++ penSgr pen)).cursor =
      { x := w.cols - 1, y := y, pending := true } := by
  let u : Vt := { w.moveTo x (row - 1) with pen := c.pen }
  have hux : u.cursor.x = x := by
    dsimp [u, Vt.moveTo]; omega
  have hrep :=
    cellText_cursor_margin_any_acc u c hc h0 h1 hwrap hins rfl
      (by
        rw [hux]; exact hx)
      hwidth
      (by
        rw [hux]; exact hmargin)
      hps hun
  rw [feed_append, feed_append, feed_append,
    cup_feed_eq row (x + 1) hr0 (by omega) hrcap
      (by
        have := hg.colsLe; omega)
      hps hun]
  simp only [Nat.add_sub_cancel]
  rw [penSgr_feed (v := w.moveTo x (row - 1)) _ hps hun]
  change ((u.feed (cellText c)).feed (penSgr pen)).cursor = _
  have hu := (cellText_ground_need_any_acc u c hps hun).2
  rw [penSgr_feed _ (ends_cellText c u hps) hu]
  change (u.feed (cellText c)).cursor = _
  rw [hrep]
  change ({ x := w.cols - 1, y := (w.moveTo x (row - 1)).cursor.y, pending := true } : Cursor) = _
  rw [hrow]

/-- Position restoration needs no representability of either grid. The fitted
source cell and the margin guard supply all facts consumed by the cursor proof. -/
theorem pendingAnsi_cursor_eq (w : Vt) (grid : Array Row) (cur : Cursor) (row : Nat) (pen : Pen)
    (hg : Good w) (h0 : w.g0Line = false) (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true)
    (hins : w.modes.insert = false) (hr0 : 0 < row) (hrcap : row ≤ 65535)
    (hrow : (w.moveTo 0 (row - 1)).cursor.y = cur.y) (hps : w.pstate = .ground)
    (hun : w.u8need = 0) :
    (w.feed (pendingAnsi w.cols grid cur row pen)).cursor =
      if pendingAnsi w.cols grid cur row pen = [] then w.cursor else cur := by
  let cells := grid.getD cur.y #[]
  let x := if (cells.at cur.x).width == 0 then cur.x - 1 else cur.x
  let c := cellFit (cells.at x)
  let bs := csiNum2 row (x + 1) 0x48 ++ penSgr c.pen ++ cellText c ++ penSgr pen
  change
    (w.feed
          (if
              cur.pending && cur.y < grid.size && cur.x < cells.size && cur.x + 1 == w.cols &&
                charWidth c.base != 0 &&
                x + charWidth c.base == w.cols then
            bs
          else [])).cursor =
      if
          (if
                cur.pending && cur.y < grid.size && cur.x < cells.size && cur.x + 1 == w.cols &&
                  charWidth c.base != 0 &&
                  x + charWidth c.base == w.cols then
              bs
            else []) =
            [] then
        w.cursor
      else cur
  split
  · rename_i h
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne] at h
    have hm : cur.x + 1 = w.cols := h.1.1.2
    have hp : cur.pending = true := h.1.1.1.1.1
    have hx : x < w.cols := by
      dsimp [x]; split <;> omega
    have he :=
      reprintAnsi_cursor_eq w c x cur.y row pen hg (cellOk_cellFit _) h0 h1 hwrap hins hx hr0 hrcap
        hrow h.1.2 h.2 hps hun
    rw [show bs = csiNum2 row (x + 1) 0x48 ++ penSgr c.pen ++ cellText c ++ penSgr pen from rfl, he]
    simp only [csiNum2, csiB, List.cons_append, List.nil_append, List.cons_ne_nil, ↓reduceIte]
    obtain ⟨cx, cy, cp⟩ := cur
    simp only at hm hp ⊢
    rw [hp, show w.cols - 1 = cx from by omega]
  · rfl

/-- The active wrapper restores its temporary modes and charsets after the exact
margin repaint. Its only cursor change is the supplied pending cursor when the
guarded glyph can be emitted; every other field is given explicitly. -/
theorem cursorPendingAnsi_feed_eq (v w : Vt) (hg : Good w) (hr : Renderable w)
    (hcols : w.cols = v.cols) (hgrid : w.grid = v.grid)
    (hrow :
      (v.cursor.pending &&
            (!v.modes.origin ||
              (((v.top == 0 && v.bot == v.rows - 1) || (v.top < v.bot && v.bot < v.rows)) &&
                v.top ≤ v.cursor.y &&
                v.cursor.y ≤ v.bot))) =
          true →
        v.cursor.y < w.rows →
          let row := if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1
          0 < row ∧ row ≤ 65535 ∧ (w.moveTo 0 (row - 1)).cursor.y = v.cursor.y)
    (hps : w.pstate = .ground) (hun : w.u8need = 0) (hua : w.u8acc = 0) :
    w.feed (Linger.Core.Render.cursorPendingAnsi v) =
      if
          v.cursor.pending &&
            (!v.modes.origin ||
              (((v.top == 0 && v.bot == v.rows - 1) || (v.top < v.bot && v.bot < v.rows)) &&
                v.top ≤ v.cursor.y &&
                v.cursor.y ≤ v.bot)) then
        { w with
          cursor :=
            if
                pendingAnsi v.cols v.grid v.cursor
                    (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen =
                  [] then
              w.cursor
            else v.cursor,
          modes :=
            { w.modes with
              wrap := v.modes.wrap, insert := v.modes.insert },
          g0Line := v.g0Line, g1Line := v.g1Line, shiftOut := v.shiftOut, pen := v.pen }
      else w := by
  unfold cursorPendingAnsi
  split
  · rename_i hon
    let a : Vt :=
      { w with
        modes :=
          { w.modes with
            wrap := true, insert := false },
        g0Line := false, g1Line := false, shiftOut := false }
    have hprep :
      w.feed
          (modeSet 7 true ++ csiNum 4 0x6C ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++
            [0x0F]) =
        a :=
      pending_prepare_feed w hps hun
    have hga : Good a := by
      rw [← hprep]; exact Good.feed _ hg
    have hra : Renderable a := renderable_congr hr rfl rfl rfl rfl
    have hp :=
      pendingAnsi_feed_eq a v.cursor
        (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen hga hra rfl rfl
        rfl rfl (hrow hon) hps hun hua
    change
      a.feed
          (pendingAnsi w.cols w.grid v.cursor
            (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen) =
        _ at hp
    have hp' :
      a.feed
          (pendingAnsi v.cols v.grid v.cursor
            (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen) =
        if
            pendingAnsi v.cols v.grid v.cursor
                (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen =
              [] then
          a
        else
          { a with
            cursor := v.cursor, pen := v.pen } := by
      simpa only [← hcols, ← hgrid] using hp
    refine
      Eq.trans (b :=
        ((w.feed
                  (modeSet 7 true ++ csiNum 4 0x6C ++ escCharset 0x28 0x42 ++
                    escCharset 0x29 0x42 ++
                    [0x0F])).feed
              (pendingAnsi v.cols v.grid v.cursor
                (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen)).feed
          (modeSet 7 v.modes.wrap ++ csiNum 4 (if v.modes.insert then 0x68 else 0x6C) ++
            charsetAnsi v ++
            penSgr v.pen))
        ?_ ?_
    · simp only [feed_append]
    rw [hprep]
    rw [hp']
    by_cases hbs :
      pendingAnsi v.cols v.grid v.cursor
          (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen =
        []
    · simp only [hbs, ↓reduceIte]
      rw [pending_finish_feed v a rfl hps hun]
    · simp only [hbs, ↓reduceIte]
      rw [pending_finish_feed v
          { a with
            cursor := v.cursor, pen := v.pen }
          rfl hps hun]
  · rfl

/-- Absolute pending addresses, including the rejected out-of-bounds case. -/
theorem pending_row_absolute (w : Vt) (cur : Cursor) (hg : Good w) (ho : w.modes.origin = false)
    (hy : cur.y < w.rows) :
    0 < cur.y + 1 ∧ cur.y + 1 ≤ 65535 ∧ (w.moveTo 0 (cur.y + 1 - 1)).cursor.y = cur.y := by
  refine
    ⟨by omega, by
      have := hg.rowsLe; omega, ?_⟩
  simp only [Vt.moveTo, ho, Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_sub_cancel]
  omega

/-- The origin-relative row is used only when the source region was installed
and contains the cursor. No `Good` or grid hypothesis on the source is needed. -/
theorem pending_row_active (v w : Vt) (hg : Good w) (hrows : w.rows = v.rows)
    (ho : w.modes.origin = v.modes.origin)
    (hreg :
      (v.top = 0 ∧ v.bot = v.rows - 1) ∨ (v.top < v.bot ∧ v.bot < v.rows) →
        w.top = v.top ∧ w.bot = v.bot)
    (hon :
      (v.cursor.pending &&
          (!v.modes.origin ||
            (((v.top == 0 && v.bot == v.rows - 1) || (v.top < v.bot && v.bot < v.rows)) &&
              v.top ≤ v.cursor.y &&
              v.cursor.y ≤ v.bot))) =
        true)
    (hy : v.cursor.y < w.rows) :
    let row := if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1
    0 < row ∧ row ≤ 65535 ∧ (w.moveTo 0 (row - 1)).cursor.y = v.cursor.y := by
  cases hv : v.modes.origin
  · simpa only [hv, Bool.false_eq_true, ↓reduceIte] using
      pending_row_absolute w v.cursor hg (ho.trans hv) hy
  · simp only [hv, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hon
    obtain ⟨ht, hb⟩ := hreg hon.2.1.1
    have hw : w.modes.origin = true := ho.trans hv
    simp only [↓reduceIte, Vt.moveTo, hw, ht, hb, Nat.add_sub_cancel]
    have := hg.rowsLe
    have := hon.2.1.2
    have := hon.2.2
    omega

/-- DECSC saves the complete cursor, including deferred wrap. -/
theorem save_feed_eq (w : Vt) (hg : w.pstate = .ground) (hu : w.u8need = 0) :
    w.feed (escSeq 0x37) = { w with saved := ⟨w.cursor, w.pen⟩ } := by
  rw [show escSeq 0x37 = [0x1B, 0x37] from rfl,
    show w.feed [0x1B, 0x37] = (w.step 0x1B).step 0x37 from by simp [Vt.feed], esc_step_eq hg hu,
    step_of_esc_quiet (v := { w with pstate := .esc }) 0x37 rfl hu]
  simp [Vt.stepEsc, ← hg]

/-- The saved repair changes only the cursor, pen and saved slot. -/
theorem savedPendingAnsi_feed_eq (v w : Vt) (hg : Good w) (hr : Renderable w)
    (hcols : w.cols = v.cols) (hgrid : w.grid = v.grid) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (ho : w.modes.origin = false) (hps : w.pstate = .ground) (hun : w.u8need = 0)
    (hua : w.u8acc = 0) :
    w.feed (Linger.Core.Render.savedPendingAnsi v) =
      if v.saved.cur.pending then
        let z :=
          if pendingAnsi v.cols v.grid v.saved.cur (v.saved.cur.y + 1) v.saved.pen = [] then w
          else
            { w with
              cursor := v.saved.cur, pen := v.saved.pen }
        { z with saved := ⟨z.cursor, z.pen⟩ }
      else w := by
  unfold savedPendingAnsi
  split
  · have hp :=
      pendingAnsi_feed_eq w v.saved.cur (v.saved.cur.y + 1) v.saved.pen hg hr h0 h1 hwrap hins
        (pending_row_absolute w v.saved.cur hg ho) hps hun hua
    have hp' :
      w.feed (pendingAnsi v.cols v.grid v.saved.cur (v.saved.cur.y + 1) v.saved.pen) =
        if pendingAnsi v.cols v.grid v.saved.cur (v.saved.cur.y + 1) v.saved.pen = [] then w
        else
          { w with
            cursor := v.saved.cur, pen := v.saved.pen } := by
      simpa only [← hcols, ← hgrid] using hp
    rw [feed_append, hp']
    split
    · exact save_feed_eq w hps hun
    · exact
        save_feed_eq
          { w with
            cursor := v.saved.cur, pen := v.saved.pen }
          hps hun
  · rfl

theorem mmap_id_save : MMap id (escSeq 0x37) := by
  intro w hg hu
  rw [save_feed_eq w hg hu]
  exact ⟨hg, hu, rfl⟩

theorem mmap_id_hts : MMap id (escSeq 0x48) := by
  intro w hg hu
  rw [show escSeq 0x48 = [0x1B, 0x48] from rfl,
    show w.feed [0x1B, 0x48] = (w.step 0x1B).step 0x48 from by simp [Vt.feed], esc_step_eq hg hu,
    step_of_esc_quiet (v := { w with pstate := .esc }) 0x48 rfl hu]
  exact ⟨rfl, hu, rfl⟩

theorem mmap_id_savedAnsi (v : Vt) : MMap id (savedAnsi v) := by
  unfold savedAnsi
  exact mmap_id_append (mmap_id_append (mmap_id_penSgr _) (mmap_id_cup _ _)) mmap_id_save

theorem mmap_id_regionAnsi (v : Vt) : MMap id (regionAnsi v) := by
  unfold regionAnsi
  split
  · exact MMap.nil
  · rw [show
        csiNum2 (v.top + 1) (v.bot + 1) 0x72 = csiB ++ joinSemi [v.top + 1, v.bot + 1] ++ [0x72]
        from by simp [csiNum2, joinSemi]]
    exact
      mmap_id_csi_seq _ 0x72 (paramBytes_joinSemi _) (by decide) (by decide) modes_csiDispatch_stbm

theorem mmap_id_tabsAnsi (v : Vt) : MMap id (tabsAnsi v) := by
  have htbc : MMap id (csiNum 3 0x67) := by
    refine mmap_id_csi_seq (digits 3) 0x67 (paramBytes_digits 3) (by decide) (by decide) ?_
    intro w s
    by_cases hi : s.ignore = true
    · simp [Vt.csiDispatch, hi]
    · unfold Vt.csiDispatch
      rw [ite_eq_right hi]
      change
        (match s.arg 0 0 with
            | 0 => { w with tabs := w.tabs.setIfInBounds w.cursor.x false }
            | 3 => { w with tabs := Array.replicate w.cols false }
            | _ => w).modes =
          w.modes
      split <;> rfl
  have hcha (i : Nat) : MMap id (csiNum (i + 1) 0x47) := by
    refine mmap_id_csi_seq (digits (i + 1)) 0x47 (paramBytes_digits _) (by decide) (by decide) ?_
    intro w s
    by_cases hi : s.ignore = true
    · simp [Vt.csiDispatch, hi]
    · unfold Vt.csiDispatch
      rw [ite_eq_right hi]
      change (w.setCol (s.arg 0 1 - 1)).modes = w.modes
      rw [frame_setCol]
  have hrun :
    ∀ is : List Nat, MMap id (is.flatMap (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48)) := by
    intro is
    induction is with
    | nil => exact MMap.nil
    | cons i is ih => exact mmap_id_append (mmap_id_append (hcha i) mmap_id_hts) ih
  exact mmap_id_append htbc (hrun _)

/-- Origin is replayed even for a decoded mouse value outside the allowlist. -/
theorem modesAnsi_origin (v w : Vt) (hg : w.pstate = .ground) (hu : w.u8need = 0) :
    (w.feed (modesAnsi v)).modes.origin = v.modes.origin := by
  by_cases hm :
    v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002 ∨ v.modes.mouse = 1003
  · exact congrArg Modes.origin (mmap_modesAnsi v hm w hg hu).2.2
  · let z : Vt := { v with modes := { v.modes with mouse := 0 } }
    have hn : v.modes.mouse ≠ 1000 ∧ v.modes.mouse ≠ 1002 ∧ v.modes.mouse ≠ 1003 := by
      simp only [not_or] at hm
      exact hm.2
    have he : modesAnsi v = modesAnsi z := by simp [modesAnsi, z, hn.1, hn.2.1, hn.2.2]
    rw [he]
    have ho := congrArg Modes.origin (mmap_modesAnsi z (Or.inl rfl) w hg hu).2.2
    exact ho

/-- The active repair's cursor equation is independent of grid canonicality and
the inactive UTF-8 accumulator. -/
theorem cursorPendingAnsi_cursor_eq (v w : Vt) (hg : Good w) (hcols : w.cols = v.cols)
    (hrow :
      (v.cursor.pending &&
            (!v.modes.origin ||
              (((v.top == 0 && v.bot == v.rows - 1) || (v.top < v.bot && v.bot < v.rows)) &&
                v.top ≤ v.cursor.y &&
                v.cursor.y ≤ v.bot))) =
          true →
        let row := if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1
        0 < row ∧ row ≤ 65535 ∧ (w.moveTo 0 (row - 1)).cursor.y = v.cursor.y)
    (hps : w.pstate = .ground) (hun : w.u8need = 0) :
    (w.feed (Linger.Core.Render.cursorPendingAnsi v)).cursor =
      if
          v.cursor.pending &&
            (!v.modes.origin ||
              (((v.top == 0 && v.bot == v.rows - 1) || (v.top < v.bot && v.bot < v.rows)) &&
                v.top ≤ v.cursor.y &&
                v.cursor.y ≤ v.bot)) then
        if
            pendingAnsi v.cols v.grid v.cursor
                (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen =
              [] then
          w.cursor
        else v.cursor
      else w.cursor := by
  unfold cursorPendingAnsi
  split
  · rename_i hon
    let a : Vt :=
      { w with
        modes :=
          { w.modes with
            wrap := true, insert := false },
        g0Line := false, g1Line := false, shiftOut := false }
    let bs :=
      pendingAnsi v.cols v.grid v.cursor
        (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen
    have hprep :
      w.feed
          (modeSet 7 true ++ csiNum 4 0x6C ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++
            [0x0F]) =
        a :=
      pending_prepare_feed w hps hun
    have hga : Good a := by
      rw [← hprep]; exact Good.feed _ hg
    obtain ⟨hr0, hrle, hry⟩ := hrow hon
    have hp :=
      pendingAnsi_cursor_eq a v.grid v.cursor
        (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen hga rfl rfl rfl
        rfl hr0 hrle hry hps hun
    have hp' : (a.feed bs).cursor = if bs = [] then w.cursor else v.cursor := by
      simpa only [show a.cols = v.cols from hcols] using hp
    obtain ⟨hbps, hbun, -⟩ :=
      mmap_id_pendingAnsi v.cols v.grid v.cursor
        (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen a hps hun
    have hbs :=
      (smap_id_pendingAnsi v.cols v.grid v.cursor
          (if v.modes.origin then v.cursor.y - v.top + 1 else v.cursor.y + 1) v.pen a hps).2
    have hbso : (a.feed bs).shiftOut = false := by
      rw [← stick_so, hbs]; rfl
    change
      ((w.feed
            (modeSet 7 true ++ csiNum 4 0x6C ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++
              [0x0F] ++
              bs ++
              modeSet 7 v.modes.wrap ++
              csiNum 4 (if v.modes.insert then 0x68 else 0x6C) ++
              charsetAnsi v ++
              penSgr v.pen))).cursor =
        _
    have he :
      w.feed
          (modeSet 7 true ++ csiNum 4 0x6C ++ escCharset 0x28 0x42 ++ escCharset 0x29 0x42 ++
            [0x0F] ++
            bs ++
            modeSet 7 v.modes.wrap ++
            csiNum 4 (if v.modes.insert then 0x68 else 0x6C) ++
            charsetAnsi v ++
            penSgr v.pen) =
        (a.feed bs).feed
          (modeSet 7 v.modes.wrap ++ csiNum 4 (if v.modes.insert then 0x68 else 0x6C) ++
            charsetAnsi v ++
            penSgr v.pen) := by
      rw [← hprep]
      simp only [feed_append]
    rw [he, pending_finish_feed v (a.feed bs) hbso hbps hbun]
    exact hp'
  · rfl

theorem cursorPendingAnsi_position (v w : Vt) (hg : Good w) (hcols : w.cols = v.cols)
    (ho : v.modes.origin = false) (hwo : w.modes.origin = false) (hx : w.cursor.x = v.cursor.x)
    (hy : w.cursor.y = v.cursor.y) (hps : w.pstate = .ground) (hun : w.u8need = 0) :
    (w.feed (cursorPendingAnsi v)).cursor.x = v.cursor.x ∧
      (w.feed (cursorPendingAnsi v)).cursor.y = v.cursor.y := by
  have he :=
    cursorPendingAnsi_cursor_eq v w hg hcols
      (fun _ => by
        simpa only [ho, Bool.false_eq_true, ↓reduceIte] using
          pending_row_absolute w v.cursor hg hwo (hy ▸ hg.curY))
      hps hun
  simp only [ho, Bool.false_eq_true, ↓reduceIte] at he
  rw [he]
  split
  · split
    · exact ⟨hx, hy⟩
    · exact ⟨rfl, rfl⟩
  · exact ⟨hx, hy⟩

theorem restore_placed_ground_need (v w : Vt) :
    (w.feed (restoreBody v ++ cursorAnsi v)).pstate = .ground ∧
      (w.feed (restoreBody v ++ cursorAnsi v)).u8need = 0 := by
  have hu : (w.feed (restoreBody v)).u8need = 0 := restoreBody_u8need v w
  obtain ⟨hp, hn, -⟩ := mmap_id_cursorAnsi v _ (restoreBody_grounds v w) hu
  simpa only [feed_append] using And.intro hp hn

/-- Receiver-quantified cursor position. Besides `Good v`, the session needs only DECOM off;
the replayed mouse mode needs no premise (`restoreBody_origin`). The extra margin bytes may
restore pending wrap, but cannot move an already placed cursor. -/
theorem restore_cursor_any (v w : Vt) (hgood : Good v) (hgw : Good w) (hcols : w.cols = v.cols)
    (hrows : w.rows = v.rows) (ho : v.modes.origin = false) :
    ((w.feed (restore v)).cursor.x = v.cursor.x) ∧
      ((w.feed (restore v)).cursor.y = v.cursor.y) := by
  let u := w.feed (restoreBody v ++ cursorAnsi v)
  have hgu : Good u := Good.feed _ hgw
  have hc : u.cols = v.cols := by
    rw [← dims_fst, dims_feed _ hgw, dims_fst]
    exact hcols
  have hp : u.pstate = .ground := (restore_placed_ground_need v w).1
  have hn : u.u8need = 0 := (restore_placed_ground_need v w).2
  have hx : u.cursor.x = v.cursor.x := by
    simpa only [u] using (restore_cursor_placed_any v w hgood hgw hcols hrows ho).1
  have hy : u.cursor.y = v.cursor.y := by
    simpa only [u] using (restore_cursor_placed_any v w hgood hgw hcols hrows ho).2
  have hu : (w.feed (restoreBody v)).u8need = 0 := restoreBody_u8need v w
  have hmo := (mmap_id_cursorAnsi v _ (restoreBody_grounds v w) hu).2.2
  simp only [id_eq] at hmo
  have horg : u.modes.origin = false := by
    dsimp only [u]
    rw [feed_append]
    exact (congrArg Modes.origin hmo).trans (restoreBody_origin v w ho)
  rw [show restore v = (restoreBody v ++ cursorAnsi v) ++ cursorPendingAnsi v from by
      simp only [restore, List.append_assoc],
    feed_append]
  exact cursorPendingAnsi_position v u hgu hc ho horg hx hy hp hn

/-- The pending repair retains the original cursor-position contract, independently
of grid representability or the inactive UTF-8 accumulator. -/
theorem restore_cursor (v : Vt) (hgood : Good v) (ho : v.modes.origin = false) :
    (((Vt.init v.cols v.rows).feed (restore v)).cursor.x = v.cursor.x) ∧
      (((Vt.init v.cols v.rows).feed (restore v)).cursor.y = v.cursor.y) :=
  restore_cursor_any v _ hgood (good_init _ _) (init_dims v hgood).1 (init_dims v hgood).2 ho

/-- Even an out-of-range decoded scroll region cannot designate a character bank. -/
theorem regionAnsi_charsets (v w : Vt) (hg : w.pstate = .ground) (hu : w.u8need = 0) :
    (w.feed (regionAnsi v)).g0Line = w.g0Line ∧ (w.feed (regionAnsi v)).g1Line = w.g1Line := by
  unfold regionAnsi
  split
  · exact ⟨rfl, rfl⟩
  · have hf (u : Vt) (s : CsiState) :
      ((u.csiDispatch s 0x72).g0Line, (u.csiDispatch s 0x72).g1Line) = (u.g0Line, u.g1Line) := by
      by_cases hi : s.ignore = true
      · simp [Vt.csiDispatch, hi]
      · unfold Vt.csiDispatch
        rw [ite_eq_right hi]
        dsimp only
        split <;>
          first
          | (rename_i he; exact absurd he (by decide))
          | ((repeat' split) <;> rfl)
    rw [show
        csiNum2 (v.top + 1) (v.bot + 1) 0x72 =
          [0x1B, 0x5B] ++ (joinSemi [v.top + 1, v.bot + 1] ++ [0x72])
        from by simp [csiNum2, csiB, joinSemi, List.append_assoc],
      feed_append, keeps_csi_open hg hu]
    have h :=
      (csi_tail_proj (π := fun u : Vt => (u.g0Line, u.g1Line)) (fun _ _ => rfl)
          (joinSemi [v.top + 1, v.bot + 1]) 0x72 (paramBytes_joinSemi _) (by decide) (by decide) hf
          (v := { w with pstate := .csi {} }) rfl hu rfl).1
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- A region that the source can address is still installed after the metadata
tail. Invalid decoded regions do not acquire a new fidelity premise. -/
theorem pending_tail_region (v u : Vt) (hg : Good u) (hrows : u.rows = v.rows) (ht : u.top = 0)
    (hb : u.bot = v.rows - 1) (hp : u.pstate = .ground)
    (hreg : (v.top = 0 ∧ v.bot = v.rows - 1) ∨ (v.top < v.bot ∧ v.bot < v.rows)) :
    let c :=
      u.feed
        (regionAnsi v ++ tabsAnsi v ++ savedAnsi v ++ savedPendingAnsi v ++ titleAnsi v ++
          modesAnsi v ++
          charsetAnsi v ++
          penSgr v.pen ++
          cursorAnsi v)
    c.top = v.top ∧ c.bot = v.bot := by
  have hcap : v.rows ≤ 1000 := by
    rw [← hrows]; exact hg.rowsLe
  have htc : v.top + 1 < 65535 := by rcases hreg with h | h <;> omega
  have hbc : v.bot + 1 < 65535 := by rcases hreg with h | h <;> omega
  have hmid :=
    ((((smap_id_tabsAnsi v).append (smap_id_savedAnsi v)).append
              (smap_id_savedPendingAnsi v)).append
          (smap_id_titleAnsi v)).append
      (smap_id_modesAnsi v)
  have hm := ((smap_regionAnsi v htc hbc).comp hmid).congr (fun _ => rfl)
  have hs :=
    (hm.comp (smap_charsetAnsi v)).comp ((smap_id_penSgr v.pen).append (smap_id_cursorAnsi v))
  have he := (hs u hp).2
  simp only [List.append_assoc, id_eq] at he
  have hfun :
    (if v.top == 0 && v.bot == v.rows - 1 then id else stStbm v.top v.bot) (stick u) =
      if v.top == 0 && v.bot == v.rows - 1 then stick u else stStbm v.top v.bot (stick u) := by
    split <;> rfl
  rw [hfun] at he
  dsimp only
  simp only [List.append_assoc]
  have htop := congrArg Sticky.top he
  have hbot := congrArg Sticky.bot he
  change
    _ =
      (if v.top == 0 && v.bot == v.rows - 1 then stick u
        else stStbm v.top v.bot (stick u)).top at htop
  change
    _ =
      (if v.top == 0 && v.bot == v.rows - 1 then stick u
        else stStbm v.top v.bot (stick u)).bot at hbot
  rw [stick_top] at htop
  rw [stick_bot] at hbot
  rw [htop, hbot]
  split
  · rename_i h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact ⟨ht.trans h.1.symm, hb.trans h.2.symm⟩
  · rename_i h
    have hh : v.top < v.bot ∧ v.bot < u.rows := by
      rcases hreg with heq | hh
      · exact False.elim (h (by simp [heq.1, heq.2]))
      · exact
          ⟨hh.1, by
            rw [hrows]; exact hh.2⟩
    rw [stStbm_of hh.1 hh.2]
    exact ⟨rfl, rfl⟩

/-- The two printable tail stages repaint existing cells. The intervening
metadata stages may move cursors and set modes, but supply the exact geometry
and decoder state needed by the second repaint. -/
theorem pending_tail_frames (v u : Vt) (hg : Good u) (hr : Renderable u) (hcols : u.cols = v.cols)
    (hrows : u.rows = v.rows) (hgrid : u.grid = v.grid) (ht : u.top = 0) (hb : u.bot = v.rows - 1)
    (h0 : u.g0Line = false) (h1 : u.g1Line = false) (hwrap : u.modes.wrap = true)
    (hins : u.modes.insert = false) (ho : u.modes.origin = false) (hp : u.pstate = .ground)
    (hn : u.u8need = 0) (ha : u.u8acc = 0) :
    let a := u.feed (regionAnsi v ++ tabsAnsi v ++ savedAnsi v)
    let b := a.feed (savedPendingAnsi v)
    let c := b.feed (titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen ++ cursorAnsi v)
    let d := c.feed (cursorPendingAnsi v)
    b.pstate = .ground ∧
      b.u8need = 0 ∧
      b.grid = a.grid ∧
      b.sb = a.sb ∧ c.pstate = .ground ∧ c.u8need = 0 ∧ d.grid = c.grid ∧ d.sb = c.sb := by
  intro a b c d
  have hpre := ((keeps_regionAnsi v).append (keeps_tabsAnsi v)).append (keeps_savedAnsi v)
  obtain ⟨ap, an, ag⟩ := hpre u hp hn
  have am :=
    (mmap_id_append (mmap_id_append (mmap_id_regionAnsi v) (mmap_id_tabsAnsi v))
        (mmap_id_savedAnsi v) u hp hn).2.2
  simp only [id_eq] at am
  have ac : a.cols = v.cols := by
    rw [← dims_fst, dims_feed _ hg, dims_fst]
    exact hcols
  have aa : a.u8acc = 0 := u8Ok_feed _ (fun _ => ha) an
  have ast :=
    (((smap_id_tabsAnsi v).append (smap_id_savedAnsi v)) (u.feed (regionAnsi v))
        (keeps_regionAnsi v u hp hn).1).2
  simp only [id_eq, feed_append] at ast
  have a0 : a.g0Line = false := by
    dsimp only [a]
    simp only [feed_append]
    rw [← stick_g0, ast, stick_g0]
    exact (regionAnsi_charsets v u hp hn).1.trans h0
  have a1 : a.g1Line = false := by
    dsimp only [a]
    simp only [feed_append]
    rw [← stick_g1, ast, stick_g1]
    exact (regionAnsi_charsets v u hp hn).2.trans h1
  have ae : a.feed (savedPendingAnsi v) = _ :=
    savedPendingAnsi_feed_eq v a (Good.feed _ hg) (renderable_feed hr _) ac (ag.trans hgrid) a0 a1
      ((congrArg Modes.wrap am).trans hwrap) ((congrArg Modes.insert am).trans hins)
      ((congrArg Modes.origin am).trans ho) ap an aa
  have bframe :
    b.pstate = .ground ∧ b.u8need = 0 ∧ b.u8acc = 0 ∧ b.grid = a.grid ∧ b.sb = a.sb := by
    by_cases hpend : v.saved.cur.pending = true
    · by_cases hempty :
          pendingAnsi v.cols v.grid v.saved.cur (v.saved.cur.y + 1) v.saved.pen = [] <;>
        simpa only [b, ae, hpend, hempty, ↓reduceIte] using
          (show a.pstate = .ground ∧ a.u8need = 0 ∧ a.u8acc = 0 ∧ a.grid = a.grid ∧ a.sb = a.sb from
            ⟨ap, an, aa, rfl, rfl⟩)
    · dsimp only [b]
      rw [ae, ite_eq_right hpend]
      exact ⟨ap, an, aa, rfl, rfl⟩
  have hpost :=
    ((((keeps_titleAnsi v).append (keeps_modesAnsi v)).append (keeps_charsetAnsi v)).append
          (keeps_penSgr v.pen)).append
      (keeps_cursorAnsi v)
  obtain ⟨cp, cn, cg⟩ := hpost b bframe.1 bframe.2.1
  have ca : c.u8acc = 0 := u8Ok_feed _ (fun _ => bframe.2.2.1) cn
  have cgood : Good c := Good.feed _ (Good.feed _ (Good.feed _ hg))
  have cren : Renderable c := renderable_feed (renderable_feed (renderable_feed hr _) _) _
  have cc : c.cols = v.cols := by
    rw [← dims_fst, dims_feed _ (Good.feed _ (Good.feed _ hg)), dims_feed _ (Good.feed _ hg),
      dims_feed _ hg, dims_fst]
    exact hcols
  have cr : c.rows = v.rows := by
    rw [← dims_snd, dims_feed _ (Good.feed _ (Good.feed _ hg)), dims_feed _ (Good.feed _ hg),
      dims_feed _ hg, dims_snd]
    exact hrows
  have cgrid : c.grid = v.grid := cg.trans (bframe.2.2.2.1.trans (ag.trans hgrid))
  have co : c.modes.origin = v.modes.origin := by
    have htitle := keeps_titleAnsi v b bframe.1 bframe.2.1
    have hmode := keeps_modesAnsi v (b.feed (titleAnsi v)) htitle.1 htitle.2.1
    have hlast :=
      mmap_id_append (mmap_id_append (mmap_id_charsetAnsi v) (mmap_id_penSgr v.pen))
        (mmap_id_cursorAnsi v)
    have he := (hlast ((b.feed (titleAnsi v)).feed (modesAnsi v)) hmode.1 hmode.2.1).2.2
    simp only [id_eq, feed_append] at he
    dsimp only [c]
    simp only [feed_append]
    rw [he]
    exact modesAnsi_origin v (b.feed (titleAnsi v)) htitle.1 htitle.2.1
  have creg :
    (v.top = 0 ∧ v.bot = v.rows - 1) ∨ (v.top < v.bot ∧ v.bot < v.rows) →
      c.top = v.top ∧ c.bot = v.bot := by
    intro hv
    have hh := pending_tail_region v u hg hrows ht hb hp hv
    simpa only [a, b, c, feed_append] using hh
  have ce :=
    cursorPendingAnsi_feed_eq v c cgood cren cc cgrid
      (fun hon hy => pending_row_active v c cgood cr co creg hon hy) cp cn ca
  have dframe : d.grid = c.grid ∧ d.sb = c.sb := by
    dsimp only [d]
    rw [ce]
    split <;> exact ⟨rfl, rfl⟩
  exact ⟨bframe.1, bframe.2.1, bframe.2.2.2.1, bframe.2.2.2.2, cp, cn, dframe.1, dframe.2⟩

end Linger.Core.Render
