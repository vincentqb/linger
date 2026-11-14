module

public import Linger.Selector.CoreCode.Picker
public import Linger.Display.CoreSpec
public import Terminal.CoreCode.Vt
import all Linger.Selector.CoreCode.Picker
import all Linger.Selector.Proofs.Frame
import Linger.Display.Proofs.Clean
import all Terminal.CoreCode.Vt
import all Terminal.CoreCode.Render
-- The receiver's fields and the repaint's rungs are module-private, hence `import all`.
import all Terminal.Proofs.Render
import all Terminal.Proofs.Vt

public section

/-! # The picker repaints only what changed

A frame paints every cell of the screen, row by row, as a repaint paints a grid
(`Render.gridAnsi_writes_rows`). Each row the picker builds is one a repaint reproduces
(`RowOk`): its cells are `Fit` and come in whole pairs (`Linger.Selector.Proofs.Frame`). An update
moves the cursor to each row that differs and paints it from the default pen, which writes that
row and leaves every other row as it was (`rowAnsi_writes_row`). So over a terminal that shows a
frame, the update shows the next one, and it writes nothing to a row the two share. -/

namespace Linger.Selector.Picker

open Terminal.Vt Terminal.Render

/-- What the receiver must hold for a row's paint to land in place: a quiet decoder, no insert
mode, autowrap, absolute cursor rows, ASCII character sets, and a full grid of full rows. -/
private structure Canon (cols rows : Nat) (u : Vt) : Prop where
  colsEq : u.cols = cols
  rowsEq : u.rows = rows
  ground : u.pstate = .ground
  u8need : u.u8need = 0
  u8acc : u.u8acc = 0
  ins : u.modes.insert = false
  wrap : u.modes.wrap = true
  origin : u.modes.origin = false
  g0 : u.g0Line = false
  g1 : u.g1Line = false
  gsz : u.grid.size = rows
  rlens : ∀ y, (u.getRow y).size = cols

private theorem at_toArray (l : List Cell) (x : Nat) : Row.at l.toArray x = l.getD x default := by
  unfold Row.at
  rw [List.getD_eq_getElem?_getD]
  by_cases h : x < l.length <;> simp [Array.getD, h]

private theorem getD_cons_succ (c : Cell) (l : List Cell) (k : Nat) :
    (c :: l).getD (k + 1) default = l.getD k default := by simp [List.getD]

private theorem paired_pairs {l : List Cell} (h : Paired l) :
    ∀ x,
      ((l.getD x default).width = 2 → l.getD (x + 1) default = Cell.shadow (l.getD x default)) ∧
        ((l.getD x default).width = 0 → x ≠ 0 ∧ (l.getD (x - 1) default).width = 2) := by
  induction h with
  | nil =>
    intro x
    have : (default : Cell).width = 1 := rfl
    simp [this]
  | @narrow c l hw rest ih =>
    intro x
    cases x with
    | zero => simp [List.getD, hw]
    | succ k =>
      rw [getD_cons_succ, getD_cons_succ]
      refine ⟨(ih k).1, fun h0 => ⟨by omega, ?_⟩⟩
      obtain ⟨hk, hw2⟩ := (ih k).2 h0
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      simpa [getD_cons_succ] using hw2
  | @wide c l hw rest ih =>
    intro x
    match x with
    | 0 => simp [List.getD, hw, Cell.shadow]
    | 1 => simp [List.getD, hw]
    |
    k +
        2 =>
      rw [show k + 2 = (k + 1) + 1 from rfl, getD_cons_succ, getD_cons_succ, getD_cons_succ,
        getD_cons_succ]
      refine ⟨(ih k).1, fun h0 => ⟨by omega, ?_⟩⟩
      cases k with
      | zero =>
        have := (ih 0).2 h0
        omega
      | succ j =>
        obtain ⟨-, hw2⟩ := (ih (j + 1)).2 h0
        simpa [getD_cons_succ] using hw2

private theorem cellOk_of_fit {c : Cell} (h : Fit c) : CellOk c := by
  obtain ⟨hb, hm, hl, hw, -⟩ := h
  simp only [Linger.Display.Printable] at hb
  refine ⟨⟨hb.1, hb.2.1⟩, hw, hl, fun m hmem => ?_⟩
  obtain ⟨hp, h0⟩ := hm m hmem
  simp only [Linger.Display.Printable] at hp
  exact ⟨h0, hp.1, hp.2.1⟩

/-- A frame line's row is one a repaint reproduces. -/
private theorem lineRow_rowOk (cols : Nat) (line : List (String × List (List Nat))) :
    RowOk cols (lineRow cols line) := by
  obtain ⟨hsize, hpaired, hfit⟩ := lineRow_ok cols line
  refine ⟨hsize, fun x => ?_, fun x => ?_⟩
  · rw [show lineRow cols line = (lineRow cols line).toList.toArray from by simp, at_toArray,
      List.getD_eq_getElem?_getD]
    by_cases hx : x < (lineRow cols line).toList.length
    · rw [List.getElem?_eq_getElem hx, Option.getD_some]
      exact cellOk_of_fit (hfit _ (List.getElem_mem hx))
    · rw [List.getElem?_eq_none (by omega), Option.getD_none]
      exact cellOk_default
  · have := paired_pairs hpaired x
    unfold PairOk
    rw [show lineRow cols line = (lineRow cols line).toList.toArray from by simp, at_toArray,
      at_toArray, at_toArray]
    exact this

private theorem picture_rowOk (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) :
    ∀ row ∈ picture state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
      RowOk cols row := by
  intro row hrow
  simp only [picture, List.mem_map] at hrow
  obtain ⟨line, -, rfl⟩ := hrow
  exact lineRow_rowOk cols line

private theorem threadRows_eq :
    ∀ (rows : List Row) (pen : Pen), threadRows rows pen = rowsAnsi rows pen
  | [], _ => rfl
  | _ :: rest, _ => by simp only [threadRows, rowsAnsi, threadRows_eq rest]

private theorem joinCRLF_eq :
    ∀ (rows : List (List UInt8)), (rows.intersperse crlfB).flatten = joinCRLF rows
  | [] => rfl
  | [_] => by simp [joinCRLF]
  | a :: b :: rest => by
    rw [List.intersperse_cons_cons, List.flatten_cons, List.flatten_cons,
      show joinCRLF (a :: b :: rest) = a ++ [0x0D, 0x0A] ++ joinCRLF (b :: rest) from rfl, ←
      joinCRLF_eq (b :: rest)]
    simp [crlfB]

/-- The frame is a repaint's paint of its picture. -/
private theorem frame_eq (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) :
    frame state snapshot statusOf loaded withColor savedTmux remoteAge cols rows =
      gridAnsi
        (picture state snapshot statusOf loaded withColor savedTmux remoteAge cols
            rows).toArray := by
  rw [gridAnsi_eq, frame, threadRows_eq, joinCRLF_eq]
  simp [csiPlain]

/-- A live receiver at a control-sequence boundary, in the modes the paint needs. -/
private theorem canon_of_live {v : Vt} (hv : LiveReachableVt v) (between : v.atBoundary = true)
    (replacing : v.getModes.insert = false) (wraps : v.getModes.wrap = true)
    (absolute : v.getModes.origin = false) (ascii0 : (stick v).g0 = false)
    (ascii1 : (stick v).g1 = false) : Canon v.colCount v.rowCount v := by
  have good := good_of_liveReachable hv
  have shaped := renderable_of_liveReachable hv
  have ⟨hg, hu⟩ := (atBoundary_iff v).mp between
  refine
    ⟨rfl, rfl, hg, hu, u8Ok_of_liveReachable hv hu, replacing, wraps, absolute, ascii0, ascii1,
      shaped.main.1, fun y => ?_⟩
  show (v.grid.getD y (blankRow v.cols v.pen)).size = v.cols
  by_cases hy : y < v.grid.size
  · have := (shaped.main.2 y).size
    rw [getD_lt' v.grid y _ hy, ← getD_lt' v.grid y (blankRow v.cols {}) hy]
    exact this
  · rw [Array.getD, dite_eq_right hy]
    simp [blankRow]

private theorem getRow_eq_of_cells {u w : Vt} {y : Nat} (hs : (w.getRow y).size = (u.getRow y).size)
    (hc : ∀ x, w.getCell x y = u.getCell x y) : w.getRow y = u.getRow y := by
  apply Array.ext hs
  intro x h1 h2
  have := hc x
  simp only [Vt.getCell, Array.getD, h1, h2, dite_true] at this
  exact this

/-- **A row's paint at its row.** Moving the cursor to row `y`'s first column, resetting the
pen and painting a reproducible row writes exactly that row and no other, and leaves the
receiver as the next paint needs it. -/
private theorem paint_at {cols rows : Nat} {u : Vt} (hu : Canon cols rows u) {g : Row}
    (hg : RowOk cols g) (hpos : 0 < cols) (hcb : cols < 65533) {y : Nat} (hy : y < rows)
    (hcap : y + 1 ≤ 65535) :
    Canon cols rows (u.feed (csiNum2 (y + 1) 1 0x48 ++ (csiNum 0 0x6D ++ (rowAnsi g {}).1))) ∧
      (u.feed (csiNum2 (y + 1) 1 0x48 ++ (csiNum 0 0x6D ++ (rowAnsi g {}).1))).getRow y = g ∧
      ∀ y',
        y' ≠ y →
          y' < rows →
          (u.feed (csiNum2 (y + 1) 1 0x48 ++ (csiNum 0 0x6D ++ (rowAnsi g {}).1))).getRow y' =
            u.getRow y' := by
  rw [feed_append, cup_feed_eq (y + 1) 1 (by omega) (by omega) hcap (by omega) hu.ground hu.u8need,
    show y + 1 - 1 = y from by omega, show 1 - 1 = 0 from rfl]
  have hmove : u.moveTo 0 y = { u with cursor := { x := 0, y := y, pending := false } } := by
    have hx : min 0 (u.cols - 1) = 0 := Nat.zero_min _
    have hy' : min (0 + y) (u.rows - 1) = y := by
      rw [hu.rowsEq]; omega
    simp only [Vt.moveTo, hu.origin, Bool.false_eq_true, ↓reduceIte, hx, hy']
  rw [hmove, feed_append]
  have hsgr :
    Vt.feed { u with cursor := { x := 0, y := y, pending := false } } (csiNum 0 0x6D) =
      { u with
        cursor := { x := 0, y := y, pending := false }, pen := {} } := by
    rw [show csiNum 0 0x6D = sgrOf [0] from by simp [csiNum, sgrOf, joinSemi],
      sgrOf_feed (v := { u with cursor := { x := 0, y := y, pending := false } }) [0] (by decide)
        (by decide) (by decide) hu.ground hu.u8need,
      show penAfter u.pen [0] = ({} : Pen) from by
        simp [penAfter, sgrParamsOf, Vt.applySgr.go, Vt.sgrAttr]]
  rw [hsgr]
  obtain ⟨w, hw⟩ :
    ∃ w : Vt,
      ({ u with
            cursor := { x := 0, y := y, pending := false }, pen := {} } :
          Vt) =
        w :=
    ⟨_, rfl⟩
  rw [hw]
  have hwg : w.grid = u.grid := by rw [← hw]
  have hwcu : w.cols = u.cols := by rw [← hw]
  have hwc : w.cols = cols := hwcu.trans hu.colsEq
  have hrow : RowOk w.cols g := by
    rw [hwc]; exact hg
  have hsize : ∀ y', (w.getRow y').size = (u.getRow y').size := size_getRow_congr hwg hwcu
  have hsame : ∀ y', y' < u.grid.size → w.getRow y' = u.getRow y' := by
    intro y' hy'
    show w.grid.getD y' (blankRow w.cols w.pen) = u.grid.getD y' (blankRow u.cols u.pen)
    rw [hwg, getD_lt' u.grid y' _ hy', getD_lt' u.grid y' _ hy']
  have hm : Matches w { x := 0, y := y, pen := {}, pending := false } g 0 := by
    have hrl : (w.getRow y).size = w.cols := by rw [hsize, hu.rlens, hwc]
    have hin : y < w.grid.size := by
      rw [hwg, hu.gsz]; exact hy
    subst hw
    exact
      matches_zero rfl rfl rfl rfl hu.ground hu.u8need hu.u8acc hu.ins hu.wrap hu.g0 hu.g1 hrl hin
  obtain ⟨pd, hM, hO⟩ :=
    rowAnsi_writes_row hrow
      (by
        rw [hwc]; exact hcb)
      (by
        rw [hwc]; exact hpos)
      hm
  have hwground : w.pstate = .ground := by
    rw [← hw]; exact hu.ground
  have hquiet :=
    quiet_rowAnsi g {} w hwground
      (by
        rw [← hw]; exact hu.origin)
  have hstick : stick (w.feed (rowAnsi g {}).1) = stick w := (smap_id_rowAnsi g {} w hwground).2
  have hrows' : (w.feed (rowAnsi g {}).1).rows = rows := by
    have := congrArg Sticky.rows hstick
    rw [stick_rows, stick_rows] at this
    rw [this, ← hw]; exact hu.rowsEq
  refine
    ⟨⟨hO.cols.trans hwc, hrows', hM.ground, hM.u8need, hM.u8acc, hM.ins, hM.wrap, hquiet.2,
        hM.ascii0, hM.ascii1, by
        rw [hO.gridSize, hwg]; exact hu.gsz, fun y' => by
        rw [hO.sizes y', hsize y']; exact hu.rlens y'⟩,
      row_eq_of_paint (hO.cols.trans hwc) hg
        (by
          rw [hwc] at hM; exact hM),
      fun y' hne hlt => ?_⟩
  have hlt' : y' < u.grid.size := by
    rw [hu.gsz]; exact hlt
  rw [← hsame y' hlt']
  exact
    getRow_eq_of_cells (hO.sizes y')
      (fun x =>
        hO.cells x y' hne
          (by
            rw [hwg]; exact hlt'))

/-- A row's own paint: the pen reset, then the row from the default pen. -/
private def seg (g : Row) : List UInt8 := csiNum 0 0x6D ++ (rowAnsi g {}).1

/-- **The update, row by row.** From row `y` on, each row whose paint differs from the row
`before` holds there is painted, and every other row is left as it was. -/
private theorem updateFrom_rows {cols rows : Nat} (hpos : 0 < cols) (hcb : cols < 65533)
    (hcap : rows ≤ 65535) :
    ∀ (after : List Row) (y : Nat) (before : List (List UInt8)) (u : Vt),
      Canon cols rows u →
        y + after.length ≤ rows →
        (∀ g ∈ after, RowOk cols g) →
        Canon cols rows (u.feed (updateFrom y before (after.map seg))) ∧
          (∀ i (hi : i < after.length),
            (u.feed (updateFrom y before (after.map seg))).getRow (y + i) =
              if before[i]? = some (seg after[i]) then u.getRow (y + i) else after[i]) ∧
          ∀ y' < rows,
            (y' < y ∨ y + after.length ≤ y') →
              (u.feed (updateFrom y before (after.map seg))).getRow y' = u.getRow y' := by
  intro after
  induction after with
  | nil =>
    intro y before u hu _ _
    exact
      ⟨by simpa [updateFrom, feed_nil] using hu, fun i hi => absurd hi (by simp), fun y' _ _ => by
        simp [updateFrom, feed_nil]⟩
  | cons g rest ih =>
    intro y before u hu hlen hok
    simp only [List.length_cons] at hlen
    have hg := hok g (by simp)
    have hrest : ∀ r ∈ rest, RowOk cols r := fun r hr => hok r (by simp [hr])
    have hhead : before.head? = before[0]? := by cases before <;> rfl
    simp only [List.map_cons, updateFrom]
    by_cases hsame : before.head? = some (seg g)
    · simp only [hsame, ↓reduceIte, List.nil_append]
      obtain ⟨hc, hin, hout⟩ := ih (y + 1) before.tail u hu (by omega) hrest
      refine ⟨hc, fun i hi => ?_, fun y' hy' hside => ?_⟩
      · cases i with
        | zero =>
          simp only [Nat.add_zero]
          rw [hout y (by omega) (.inl (by omega))]
          simp [← hhead, hsame]
        | succ j =>
          have := hin j (by simpa using hi)
          rw [show y + (j + 1) = y + 1 + j from by omega, this, List.getElem?_tail]
          simp
      · simp only [List.length_cons] at hside
        exact hout y' hy' (by omega)
    · simp only [hsame, ↓reduceIte]
      rw [feed_append]
      obtain ⟨hc1, hrow1, hoff1⟩ := paint_at hu hg hpos hcb (y := y) (by omega) (by omega)
      have hseg :
        csiNum2 (y + 1) 1 0x48 ++ seg g =
          csiNum2 (y + 1) 1 0x48 ++ (csiNum 0 0x6D ++ (rowAnsi g {}).1) :=
        rfl
      rw [hseg] at *
      obtain ⟨hc, hin, hout⟩ := ih (y + 1) before.tail _ hc1 (by omega) hrest
      refine ⟨hc, fun i hi => ?_, fun y' hy' hside => ?_⟩
      · cases i with
        | zero =>
          simp only [Nat.add_zero]
          rw [hout y (by omega) (.inl (by omega)), hrow1]
          simp [← hhead, hsame]
        | succ j =>
          have hj : j < rest.length := by simpa using hi
          have := hin j hj
          rw [show y + (j + 1) = y + 1 + j from by omega, this, List.getElem?_tail,
            hoff1 _ (by omega) (by omega)]
          simp
      · simp only [List.length_cons] at hside
        rw [hout y' hy' (by omega), hoff1 y' (by omega) hy']

/-- **The full paint.** Over a receiver as `Canon` asks, at the terminal's size, a frame's
paint leaves every row showing the frame's row, and the receiver as an update needs it. -/
private theorem paint_full {v : Vt} (good : Good v) (hc : Canon v.cols v.rows v) (htop : v.top = 0)
    (hbot : v.bot = v.rows - 1) (p : List Row) (hlen : p.length = v.rows)
    (hok : ∀ g ∈ p, RowOk v.cols g) :
    Canon v.cols v.rows (v.feed (gridAnsi p.toArray)) ∧
      ∀ y (hy : y < v.rows), (v.feed (gridAnsi p.toArray)).getRow y = p[y]'(by omega) := by
  have hpos : 0 < v.cols := good.colsPos
  have hcb : v.cols < 65533 := by
    have := good.colsLe; omega
  have hvok : ∀ y', RowOk v.cols (p.toArray.getD y' (blankRow v.cols {})) := by
    intro y'
    by_cases hy : y' < p.toArray.size
    · rw [getD_lt' _ _ _ hy]
      exact hok _ (by simp)
    · rw [Array.getD, dite_eq_right hy]
      exact rowOk_blankRow _ _
  obtain ⟨hgrid, hg, hun, hua, hins, hwrap, -⟩ :=
    gridAnsi_writes_rows (u := v) (tg := p.toArray) rfl rfl hpos hcb htop hbot hc.ground hc.u8need
      hc.u8acc hc.ins hc.wrap hc.origin hc.g0 hc.g1 hc.gsz hc.rlens hvok (by simp [hlen])
  have hd : dims (v.feed (gridAnsi p.toArray)) = dims v := dims_feed _ good
  have hcols : (v.feed (gridAnsi p.toArray)).cols = v.cols := by rw [← dims_fst, hd, dims_fst]
  have hrows : (v.feed (gridAnsi p.toArray)).rows = v.rows := by rw [← dims_snd, hd, dims_snd]
  have hstick := (smap_id_gridAnsi p.toArray v hc.ground).2
  have hquiet := quiet_gridAnsi p.toArray v hc.ground hc.origin
  have hrow : ∀ y (hy : y < v.rows), (v.feed (gridAnsi p.toArray)).getRow y = p[y]'(by omega) := by
    intro y hy
    show (v.feed (gridAnsi p.toArray)).grid.getD y _ = _
    rw [hgrid,
      getD_lt' _ _ _
        (by
          simp [hlen]; exact hy)]
    simp
  refine
    ⟨⟨hcols, hrows, hg, hun, hua, hins, hwrap, hquiet.2, ?_, ?_, by
        rw [hgrid]; simp [hlen], fun y => ?_⟩,
      hrow⟩
  · exact (congrArg Sticky.g0 hstick).trans hc.g0
  · exact (congrArg Sticky.g1 hstick).trans hc.g1
  · by_cases hy : y < v.rows
    · rw [hrow y hy]
      exact (hok _ (by simp)).size
    · show ((v.feed (gridAnsi p.toArray)).grid.getD y _).size = v.cols
      rw [Array.getD,
        dite_eq_right
          (by
            rw [hgrid]; simp [hlen]; omega)]
      simp [blankRow, hcols]

private theorem csiNum2_length (a b : Nat) (final : UInt8) :
    (csiNum2 a b final).length =
      (Linger.Display.digits a).length + (Linger.Display.digits b).length + 4 := by
  simp [csiNum2, csiB, Linger.Display.render_digits]
  omega

/-- **The update's length.** Each row that differs costs its cursor move and its paint. -/
private theorem updateFrom_length :
    ∀ (after : List (List UInt8)) (y : Nat) (before : List (List UInt8)),
      (updateFrom y before after).length ≤
        ((List.range after.length).map fun i =>
            if before[i]? = after[i]? then 0
            else (Linger.Display.digits (y + i + 1)).length + 5 + (after[i]?.getD []).length).sum
  | [], _, _ => by simp [updateFrom]
  | row :: rest, y, before => by
    have ih := updateFrom_length rest (y + 1) before.tail
    have hhead : before.head? = before[0]? := by cases before <;> rfl
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
    have htail :
      ((List.range rest.length).map
            ((fun i =>
                if before[i]? = (row :: rest)[i]? then 0
                else
                  (Linger.Display.digits (y + i + 1)).length + 5 +
                    ((row :: rest)[i]?.getD []).length) ∘
              Nat.succ)).sum =
        ((List.range rest.length).map fun i =>
            if before.tail[i]? = rest[i]? then 0
            else
              (Linger.Display.digits (y + 1 + i + 1)).length + 5 +
                (rest[i]?.getD []).length).sum := by
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, List.getElem?_tail, List.getElem?_cons_succ,
        show y + (i + 1) + 1 = y + 1 + i + 1 from by omega]
    rw [htail]
    simp only [updateFrom, List.length_append]
    have hfirst :
      (if before.head? = some row then ([] : List UInt8)
          else csiNum2 (y + 1) 1 0x48 ++ row).length ≤
        if before[0]? = (row :: rest)[0]? then 0
        else
          (Linger.Display.digits (y + 0 + 1)).length + 5 + ((row :: rest)[0]?.getD []).length := by
      rw [hhead]
      split
      · simp_all
      · rename_i hne
        have h1 : (Linger.Display.digits 1).length = 1 := by
          rw [Linger.Display.digits]; simp
        simp only [List.getElem?_cons_zero, hne, ↓reduceIte, List.length_append, csiNum2_length, h1,
          Nat.add_zero, Option.getD_some]
        omega
    omega

/-- **The picker repaints only what changed.** Over a live receiver at a control-sequence
boundary, without insert or origin mode, with autowrap, a whole scroll region and ASCII
character sets: written over the paint of one frame, the update shows exactly the paint of the
next; it leaves alone every row the two frames share, whatever that row holds; and it costs, for
each row that differs, a cursor move and the row's paint. -/
theorem repaints_changes (sa sb : State) (na nb : Snapshot)
    (fa fb : String → Linger.Display.Status.Status) (la ca ta lb cb tb : Bool) (aa ab : Option Nat)
    (v : Vt) (hv : Live Vt.init Vt.feed Vt.resize Vt.quiesce Vt.Decodable v)
    (between : v.atBoundary = true) (replacing : v.getModes.insert = false)
    (wraps : v.getModes.wrap = true) (absolute : v.getModes.origin = false)
    (top : (stick v).top = 0) (bottom : (stick v).bot = v.rowCount - 1)
    (ascii0 : (stick v).g0 = false) (ascii1 : (stick v).g1 = false) :
    (∀ y < v.rowCount,
        ((v.feed (frame sa na fa la ca ta aa v.colCount v.rowCount)).feed
                (update (frameRows sa na fa la ca ta aa v.colCount v.rowCount)
                  (frameRows sb nb fb lb cb tb ab v.colCount v.rowCount))).getRow
            y =
          (v.feed (frame sb nb fb lb cb tb ab v.colCount v.rowCount)).getRow y) ∧
      (∀ y < v.rowCount,
        (frameRows sa na fa la ca ta aa v.colCount v.rowCount)[y]? =
            (frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)[y]? →
          (v.feed
                  (update (frameRows sa na fa la ca ta aa v.colCount v.rowCount)
                    (frameRows sb nb fb lb cb tb ab v.colCount v.rowCount))).getRow
              y =
            v.getRow y) ∧
      (update (frameRows sa na fa la ca ta aa v.colCount v.rowCount)
            (frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)).length ≤
        ((List.range (frameRows sb nb fb lb cb tb ab v.colCount v.rowCount).length).map fun y =>
            if
                (frameRows sa na fa la ca ta aa v.colCount v.rowCount)[y]? =
                  (frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)[y]? then
              0
            else
              (Linger.Display.digits (y + 1)).length + 5 +
                ((frameRows sb nb fb lb cb tb ab v.colCount v.rowCount)[y]?.getD
                    []).length).sum := by
  have good := good_of_liveReachable hv
  have hc : Canon v.cols v.rows v := canon_of_live hv between replacing wraps absolute ascii0 ascii1
  have hpos : 0 < v.cols := good.colsPos
  have hcb : v.cols < 65533 := by
    have := good.colsLe; omega
  have hR : 1 ≤ v.rows := good.rowsPos
  have hRle : v.rows ≤ 1000 := good.rowsLe
  have hlen :
    ∀ (s : State) (n : Snapshot) (f : String → Linger.Display.Status.Status) (l c t : Bool)
      (a : Option Nat), (picture s n f l c t a v.colCount v.rowCount).length = v.rows := by
    intro s n f l c t a
    rw [picture_length]
    show max 1 v.rows = v.rows
    omega
  have hok :
    ∀ (s : State) (n : Snapshot) (f : String → Linger.Display.Status.Status) (l c t : Bool)
      (a : Option Nat), ∀ g ∈ picture s n f l c t a v.colCount v.rowCount, RowOk v.cols g :=
    fun s n f l c t a => picture_rowOk s n f l c t a v.colCount v.rowCount
  have hrowsA :
    frameRows sa na fa la ca ta aa v.colCount v.rowCount =
      (picture sa na fa la ca ta aa v.colCount v.rowCount).map seg :=
    rfl
  have hrowsB :
    frameRows sb nb fb lb cb tb ab v.colCount v.rowCount =
      (picture sb nb fb lb cb tb ab v.colCount v.rowCount).map seg :=
    rfl
  generalize hpa : picture sa na fa la ca ta aa v.colCount v.rowCount = pa at hrowsA
  generalize hpb : picture sb nb fb lb cb tb ab v.colCount v.rowCount = pb at hrowsB
  have hla : pa.length = v.rows := hpa ▸ hlen _ _ _ _ _ _ _
  have hlb : pb.length = v.rows := hpb ▸ hlen _ _ _ _ _ _ _
  have hoka : ∀ g ∈ pa, RowOk v.cols g := hpa ▸ hok _ _ _ _ _ _ _
  have hokb : ∀ g ∈ pb, RowOk v.cols g := hpb ▸ hok _ _ _ _ _ _ _
  have htop : v.top = 0 := top
  have hbot : v.bot = v.rows - 1 := bottom
  have hframeA : frame sa na fa la ca ta aa v.colCount v.rowCount = gridAnsi pa.toArray := by
    rw [frame_eq, hpa]
  have hframeB : frame sb nb fb lb cb tb ab v.colCount v.rowCount = gridAnsi pb.toArray := by
    rw [frame_eq, hpb]
  rw [hframeA, hframeB, hrowsA, hrowsB]
  obtain ⟨hcu, hshowA⟩ := paint_full good hc htop hbot pa hla hoka
  obtain ⟨-, hshowB⟩ := paint_full good hc htop hbot pb hlb hokb
  refine ⟨fun y hy => ?_, fun y hy hshared => ?_, ?_⟩
  · have hy' : y < v.rows := hy
    obtain ⟨-, hin, -⟩ :=
      updateFrom_rows hpos hcb (by omega) pb 0 (pa.map seg) _ hcu (by omega) hokb
    have := hin y (by omega)
    rw [Nat.zero_add] at this
    show
      (Vt.feed (Vt.feed v (gridAnsi pa.toArray)) (updateFrom 0 (pa.map seg) (pb.map seg))).getRow
          y =
        _
    rw [this, hshowB y hy']
    split
    · rename_i heq
      rw [hshowA y hy']
      have hsegs : seg (pa[y]'(by omega)) = seg (pb[y]'(by omega)) := by
        simpa [List.getElem?_map, List.getElem?_eq_getElem (show y < pa.length by omega)] using heq
      have e1 :=
        (paint_at hcu (hoka _ (List.getElem_mem (show y < pa.length by omega))) hpos hcb hy'
            (by omega)).2.1
      have e2 :=
        (paint_at hcu (hokb _ (List.getElem_mem (show y < pb.length by omega))) hpos hcb hy'
            (by omega)).2.1
      have hseg' :
        csiNum 0 0x6D ++ (rowAnsi (pa[y]'(by omega)) {}).1 =
          csiNum 0 0x6D ++ (rowAnsi (pb[y]'(by omega)) {}).1 :=
        hsegs
      rw [hseg'] at e1
      exact e1.symm.trans e2
    · rfl
  · obtain ⟨-, hin, -⟩ := updateFrom_rows hpos hcb (by omega) pb 0 (pa.map seg) v hc (by omega) hokb
    have :=
      hin y
        (by
          have : y < v.rows := hy; omega)
    rw [Nat.zero_add] at this
    show (Vt.feed v (updateFrom 0 (pa.map seg) (pb.map seg))).getRow y = _
    rw [this]
    have hsome :
      (pa.map seg)[y]? =
        some
          (seg
            (pb[y]'(by
                have : y < v.rows := hy; omega))) := by
      rw [hshared, List.getElem?_map,
        List.getElem?_eq_getElem
          (by
            have : y < v.rows := hy; omega)]
      rfl
    simp only [hsome, ↓reduceIte]
  · have := updateFrom_length (pb.map seg) 0 (pa.map seg)
    simp only [Nat.zero_add] at this
    exact this

end Linger.Selector.Picker
