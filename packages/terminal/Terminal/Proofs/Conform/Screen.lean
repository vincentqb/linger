module

import all Terminal.CoreCode.Render
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.State
import all Terminal.Proofs.Vt.Renderable

-- Module-private by default: `Vt`'s fields are sealed (see `packages/terminal/Terminal/Proofs/Vt/State.lean`).

/-! # The emulator's operations, as the reference's

The screen half of `vt_conforms`: `screenOf` reads a terminal as a `Vt.Ref.Screen`, and each
operation a sequence of the set dispatches to does to that screen what the reference says its
sequence does, on every terminal the facts below hold of. -/

namespace Terminal.Vt.Conform

open Terminal.Vt

/-- A grid read as cells by column and row. -/
abbrev gridOf (g : Array Row) (cols : Nat) (p : Pen) : Ref.Grid := fun x y =>
  (g.getD y (blankRow cols p)).getD x default

/-- What DECSC saved, as the reference holds it. -/
abbrev savedOf (s : Saved) : Ref.Saved :=
  { x := s.cur.x, y := s.cur.y, pending := s.cur.pending, pen := s.pen, origin := s.origin }

/-- A terminal as the reference's screen. -/
abbrev screenOf (v : Vt) : Ref.Screen :=
  { cols := v.cols, rows := v.rows, cell := gridOf v.grid v.cols v.pen, x := v.cursor.x,
    y := v.cursor.y, pending := v.cursor.pending, pen := v.pen, modes := v.modes, top := v.top,
    bot := v.bot, tabs := fun i => v.tabs.getD i false, saved := savedOf v.saved,
    main := v.altGrid.map fun gs => (gridOf gs.1 v.cols {}, savedOf gs.2), title := v.title,
    bell := v.bell }

/-- A `Bool` predicate of the reference against its emulator form: both as propositions, then
arithmetic. -/
local macro "bool_omega" : tactic =>
  `(tactic|
    ( rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      simp <;> omega))

/-- What the proofs use of a live, plain terminal. -/
structure Facts (v : Vt) : Prop where
  colsPos : 1 ≤ v.cols
  rowsPos : 1 ≤ v.rows
  curX : v.cursor.x < v.cols
  curY : v.cursor.y < v.rows
  topLe : v.top ≤ v.bot
  botLt : v.bot < v.rows
  region : v.top < v.bot ∨ v.rows = 1
  originIn : v.modes.origin = true → v.top ≤ v.cursor.y ∧ v.cursor.y ≤ v.bot
  pendX : v.cursor.pending = true → v.cursor.x + 1 = v.cols
  savX : v.saved.cur.x < v.cols
  savY : v.saved.cur.y < v.rows
  gridSize : v.grid.size = v.rows
  rowSize : ∀ y < v.rows, (v.grid.getD y (blankRow v.cols v.pen)).size = v.cols
  narrow : ∀ y x, ((v.grid.getD y (blankRow v.cols v.pen)).getD x default).width = 1
  tabsSize : v.tabs.size = v.cols
  insertOff : v.modes.insert = false
  g0 : v.g0Line = false
  g1 : v.g1Line = false
  altSize : ∀ g s, v.altGrid = some (g, s) → g.size = v.rows

theorem screenOf_pstate (v : Vt) (p : PState) : screenOf { v with pstate := p } = screenOf v := rfl

theorem facts_pstate {v : Vt} (h : Facts v) (p : PState) : Facts { v with pstate := p } :=
  { h with }

theorem getD_blankRow (cols : Nat) (p : Pen) (x : Nat) :
    (blankRow cols p).getD x default = if x < cols then Cell.erased p else default := by
  unfold blankRow
  by_cases hx : x < cols <;> simp [Array.getD, hx]

theorem facts_of_live {v : Vt} (hv : LiveReachableVt v)
    (hp : Ref.Plain Vt.colCount Vt.rowCount Vt.getRow Vt.getModes stick v) : Facts v := by
  have hg := good_of_liveReachable hv
  have hr := renderable_of_liveReachable hv
  have ht := tabsOk_of_liveReachable hv
  obtain ⟨hn, hi, h0, h1⟩ := hp
  refine
    { colsPos := hg.colsPos, rowsPos := hg.rowsPos, curX := hg.curX, curY := hg.curY,
      topLe := hg.topLe, botLt := hg.botLt, region := hg.region, originIn := hg.originIn,
      pendX := hg.pendX, savX := hg.savX, savY := hg.savY, gridSize := hr.main.1,
      rowSize := fun y _ => ?_, narrow := fun y x => ?_, tabsSize := ht, insertOff := hi, g0 := h0,
      g1 := h1, altSize := fun g s hg => (hr.alt g s hg).1 }
  · have := (hr.main.2 y).size
    by_cases hy : y < v.grid.size
    · rwa [getD_of_lt v.grid y _ (blankRow v.cols {}) hy]
    · simp [Array.getD, hy, blankRow]
  · by_cases hy : y < v.rows
    · by_cases hx : x < v.cols
      · exact hn y hy x hx
      · have hs := (hr.main.2 y).size
        rw [getD_of_lt v.grid y _ (blankRow v.cols {})
            (by
              rw [hr.main.1]; exact hy)]
        rw [getD_of_lt v.grid y _ (blankRow v.cols {})
            (by
              rw [hr.main.1]; exact hy)] at hs
        have hd := at_of_size_le _ x (by omega : (v.grid.getD y (blankRow v.cols {})).size ≤ x)
        unfold Row.at at hd
        rw [hd]
        rfl
    · rw [show v.grid.getD y (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
          simp [Array.getD, hr.main.1, hy],
        getD_blankRow]
      split <;> rfl

theorem same_refl (a : Ref.Screen) : Ref.Same a a := by
  unfold Ref.Same
  refine
    ⟨rfl, rfl, fun _ _ _ _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl,
      fun g c h => ⟨g, h, fun _ _ _ _ => rfl⟩, id, rfl, rfl⟩

theorem same_of_eq {a b : Ref.Screen} (h : a = b) : Ref.Same a b := h ▸ same_refl a

/-- A screen whose cells agree with another's on the screen, and which is otherwise the same. -/
theorem same_cell (b : Ref.Screen) (c : Ref.Grid)
    (h : ∀ y < b.rows, ∀ x < b.cols, c x y = b.cell x y) : Ref.Same { b with cell := c } b := by
  unfold Ref.Same
  refine
    ⟨rfl, rfl, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, fun g c h =>
      ⟨g, h, fun _ _ _ _ => rfl⟩, id, rfl, rfl⟩

/-! ## Cursor motion -/

theorem count_pos (n : Nat) : 0 < Ref.count n := by
  unfold Ref.count; split <;> omega

theorem moveRel_up {w : Vt} (h : Facts w) (c : Nat) :
    screenOf (w.moveRel 0 (-(Int.ofNat c))) =
      { screenOf w with
        y := max (w.cursor.y - c) (if w.top ≤ w.cursor.y then w.top else 0),
        pending := false } := by
  have := h.curX; have := h.curY; have := h.topLe; have := h.botLt
  simp only [screenOf, Vt.moveRel, Ref.Screen.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  all_goals simp
  all_goals (try split) <;> (try split) <;> omega

theorem moveRel_down {w : Vt} (h : Facts w) (c : Nat) :
    screenOf (w.moveRel 0 (Int.ofNat c)) =
      { screenOf w with
        y := min (w.cursor.y + c) (if w.cursor.y ≤ w.bot then w.bot else w.rows - 1),
        pending := false } := by
  have := h.curX; have := h.curY; have := h.topLe; have := h.botLt
  simp only [screenOf, Vt.moveRel, Ref.Screen.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  all_goals simp
  all_goals (try split) <;> (try split) <;> omega

theorem moveRel_right {w : Vt} (h : Facts w) (c : Nat) :
    screenOf (w.moveRel (Int.ofNat c) 0) =
      { screenOf w with
        x := min (w.cursor.x + c) (w.cols - 1), pending := false } := by
  have := h.curX; have := h.curY; have := h.topLe; have := h.botLt
  simp only [screenOf, Vt.moveRel, Ref.Screen.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  all_goals simp
  all_goals (try split) <;> (try split) <;> omega

theorem moveRel_left {w : Vt} (h : Facts w) (c : Nat) :
    screenOf (w.moveRel (-(Int.ofNat c)) 0) =
      { screenOf w with
        x := w.cursor.x - c, pending := false } := by
  have := h.curX; have := h.curY; have := h.topLe; have := h.botLt
  simp only [screenOf, Vt.moveRel, Ref.Screen.mk.injEq]
  refine ⟨trivial, ?_, ?_⟩
  all_goals simp
  all_goals (try split) <;> (try split) <;> omega

theorem moveTo_eq (w : Vt) (x y : Nat) :
    screenOf (w.moveTo x y) =
      { screenOf w with
        x := min x (w.cols - 1),
        y := if w.modes.origin then min (w.top + y) w.bot else min y (w.rows - 1),
        pending := false } := by
  simp only [screenOf, Vt.moveTo, Ref.Screen.mk.injEq]
  refine ⟨trivial, trivial, ?_⟩
  split <;> simp_all

theorem setCol_eq (w : Vt) (x : Nat) :
    screenOf (w.setCol x) =
      { screenOf w with
        x := min x (w.cols - 1), pending := false } := rfl

theorem carriageReturn_eq (w : Vt) : screenOf w.carriageReturn = (screenOf w).cr := rfl

/-! ## Arrays, read one cell at a time -/

theorem getD_setIfInBounds' {α : Type} (g : Array α) (i j : Nat) (x d : α) :
    (g.setIfInBounds i x).getD j d = if j = i ∧ i < g.size then x else g.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < g.size <;> simp [h2]
  · simp [h1, Ne.symm h1]

theorem getD_modify' {α : Type} (g : Array α) (i j : Nat) (f : α → α) (d : α) :
    (g.modify i f).getD j d = if j = i ∧ i < g.size then f (g.getD i d) else g.getD j d := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h1 : i = j
  · subst h1; by_cases h2 : i < g.size <;> simp [h2]
  · simp [h1, Ne.symm h1]

theorem size_foldl_set {α : Type} (r : Array α) (k : Nat) (idx : Nat → Nat) (f : Nat → α) :
    ((List.range k).foldl (fun r i => r.setIfInBounds (idx i) (f i)) r).size = r.size := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append]; simp [ih]

theorem foldl_set_fwd {α : Type} (r : Array α) (b k : Nat) (f : Nat → α) (j : Nat) (d : α) :
    ((List.range k).foldl (fun r i => r.setIfInBounds (b + i) (f i)) r).getD j d =
      if b ≤ j ∧ j < b + k ∧ j < r.size then f (j - b) else r.getD j d := by
  induction k with
  | zero =>
    simp; omega
  | succ k
    ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_setIfInBounds',
      ih, size_foldl_set]
    repeat' split
    all_goals
      first
      | rfl
      | (congr 1; omega)

theorem foldl_set_bwd {α : Type} (r : Array α) (t k : Nat) (hk : k ≤ t + 1) (f : Nat → α) (j : Nat)
    (d : α) :
    ((List.range k).foldl (fun r i => r.setIfInBounds (t - i) (f (t - i))) r).getD j d =
      if t + 1 - k ≤ j ∧ j ≤ t ∧ j < r.size then f j else r.getD j d := by
  induction k with
  | zero =>
    simp; omega
  | succ k
    ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, getD_setIfInBounds',
      ih (by omega), size_foldl_set]
    repeat' split
    all_goals
      first
      | rfl
      | (congr 1; omega)

/-! ## Narrow rows need no mending -/

/-- Every cell of the row, and every read past it, is one column wide. -/
def Narrow (r : Row) : Prop := ∀ x, (r.getD x default).width = 1

theorem mendAt_narrow {r : Row} (h : Narrow r) (x : Nat) : r.mendAt x = r := by
  have hx : (r.at x).width = 1 := h x
  unfold Row.mendAt Row.halfPair
  simp [hx]

theorem mend_narrow {r : Row} (h : Narrow r) : r.mend = r := by
  unfold Row.mend
  generalize List.range r.size = l
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, mendAt_narrow h a, ih]

theorem mendNear_narrow {r : Row} (h : Narrow r) (x : Nat) : r.mendNear x = r := by
  unfold Row.mendNear
  rw [mendAt_narrow h, mendAt_narrow h, mendAt_narrow h, mendAt_narrow h]

theorem narrow_set {r : Row} (h : Narrow r) (i : Nat) {c : Cell} (hc : c.width = 1) :
    Narrow (r.setIfInBounds i c) := by
  intro x
  rw [getD_setIfInBounds']
  split
  · exact hc
  · exact h x

theorem narrow_foldl_set {r : Row} (h : Narrow r) (k : Nat) (idx : Nat → Nat) (f : Nat → Cell)
    (hf : ∀ i, (f i).width = 1) :
    Narrow ((List.range k).foldl (fun r i => r.setIfInBounds (idx i) (f i)) r) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact narrow_set ih _ (hf k)

theorem narrow_blankRow (cols : Nat) (p : Pen) : Narrow (blankRow cols p) := by
  intro x
  rw [getD_blankRow]
  split <;> rfl

/-! ## Erasing -/

/-- A grid of `rows` narrow rows of `cols` cells. -/
structure Shape (v : Vt) : Prop where
  size : v.grid.size = v.rows
  rowSize : ∀ y < v.rows, (v.getRow y).size = v.cols
  narrow : ∀ y, Narrow (v.getRow y)

theorem Facts.shape {v : Vt} (h : Facts v) : Shape v := ⟨h.gridSize, h.rowSize, h.narrow⟩

theorem Shape.size_getRow {v : Vt} (hs : Shape v) (j : Nat) : (v.getRow j).size = v.cols := by
  by_cases hj : j < v.rows
  · exact hs.rowSize j hj
  · show (v.grid.getD j (blankRow v.cols v.pen)).size = v.cols
    rw [show v.grid.getD j (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
        simp [Array.getD, hs.size, hj]]
    simp [blankRow]

theorem gridOf_getRow (v : Vt) (x y : Nat) :
    gridOf v.grid v.cols v.pen x y = (v.getRow y).getD x default := rfl

theorem eraseRowSpan_fields (v : Vt) (y a b : Nat) :
    v.eraseRowSpan y a b = { v with grid := (v.eraseRowSpan y a b).grid } := rfl

theorem getRow_eraseRowSpan {v : Vt} (hs : Shape v) (y a b j : Nat) (hj : j < v.rows) :
    (v.eraseRowSpan y a b).getRow j =
      if j = y then
        (List.range (b - a)).foldl (fun r i => r.setIfInBounds (a + i) (Cell.erased v.pen))
          (v.getRow y)
      else v.getRow j := by
  show (v.grid.modify y _).getD j (blankRow v.cols v.pen) = _
  rw [getD_modify']
  by_cases hjy : j = y
  · subst hjy
    rw [ite_eq_left
        ⟨rfl, by
          rw [hs.size]; exact hj⟩,
      ite_eq_left rfl]
    exact mend_narrow (narrow_foldl_set (hs.narrow j) _ _ _ fun _ => rfl)
  · rw [ite_eq_right (fun h => hjy h.1), ite_eq_right hjy]
    rfl

theorem shape_eraseRowSpan {v : Vt} (hs : Shape v) (y a b : Nat) :
    Shape (v.eraseRowSpan y a b) := by
  refine
    ⟨by
      show (v.grid.modify y _).size = v.rows; simp [hs.size], fun j hj => ?_, fun j => ?_⟩
  · show ((v.eraseRowSpan y a b).getRow j).size = v.cols
    rw [getRow_eraseRowSpan hs y a b j hj]
    split
    · rw [size_foldl_set]; subst_vars; exact hs.rowSize _ hj
    · exact hs.rowSize j hj
  · by_cases hj : j < v.rows
    · rw [getRow_eraseRowSpan hs y a b j hj]
      split
      · exact narrow_foldl_set (hs.narrow y) _ _ _ fun _ => rfl
      · exact hs.narrow j
    · show Narrow ((v.grid.modify y _).getD j (blankRow v.cols v.pen))
      rw [show (v.grid.modify y _).getD j (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
          simp [Array.getD, hs.size, hj]]
      exact narrow_blankRow _ _

theorem cell_eraseRowSpan {v : Vt} (hs : Shape v) (y a b x j : Nat) (hx : x < v.cols)
    (hj : j < v.rows) :
    ((v.eraseRowSpan y a b).getRow j).getD x default =
      if j = y ∧ a ≤ x ∧ x < b then Cell.erased v.pen else (v.getRow j).getD x default := by
  rw [getRow_eraseRowSpan hs y a b j hj]
  by_cases hjy : j = y
  · subst hjy
    rw [ite_eq_left rfl, foldl_set_fwd, hs.rowSize j hj]
    by_cases hin : a ≤ x ∧ x < b
    · rw [ite_eq_left ⟨hin.1, by omega, hx⟩, ite_eq_left ⟨rfl, hin⟩]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  · rw [ite_eq_right hjy, ite_eq_right (fun h => hjy h.1)]

/-- Erase `k` whole rows from row `b`, one at a time, as ED does. -/
def eraseRows (v : Vt) (b k : Nat) : Vt :=
  (List.range k).foldl (fun v' i => v'.eraseRowSpan (b + i) 0 v'.cols) v

theorem eraseRows_fields (v : Vt) (b k : Nat) :
    eraseRows v b k = { v with grid := (eraseRows v b k).grid } := by
  unfold eraseRows
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]; rfl

theorem eraseRows_succ (v : Vt) (b k : Nat) :
    eraseRows v b (k + 1) = (eraseRows v b k).eraseRowSpan (b + k) 0 v.cols := by
  unfold eraseRows
  rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [show ((List.range k).foldl (fun v' i => v'.eraseRowSpan (b + i) 0 v'.cols) v).cols = v.cols
      from by
      rw [show
          (List.range k).foldl (fun v' i => v'.eraseRowSpan (b + i) 0 v'.cols) v = eraseRows v b k
          from rfl,
        eraseRows_fields]]

theorem eraseRows_cell {v : Vt} (hs : Shape v) (b k : Nat) :
    Shape (eraseRows v b k) ∧
      ∀ x < v.cols,
        ∀ j < v.rows,
          ((eraseRows v b k).getRow j).getD x default =
            if b ≤ j ∧ j < b + k then Cell.erased v.pen else (v.getRow j).getD x default := by
  induction k with
  | zero =>
    exact
      ⟨hs, fun x _ j _ => by
        simp [eraseRows]; omega⟩
  | succ k ih =>
    obtain ⟨hs', hc⟩ := ih
    have hf := eraseRows_fields v b k
    rw [eraseRows_succ]
    refine ⟨shape_eraseRowSpan hs' _ _ _, fun x hx j hj => ?_⟩
    have hx' : x < (eraseRows v b k).cols := by
      rw [hf]; exact hx
    have hj' : j < (eraseRows v b k).rows := by
      rw [hf]; exact hj
    rw [cell_eraseRowSpan hs' _ _ _ x j hx' hj', hc x hx j hj]
    rw [show (eraseRows v b k).pen = v.pen by rw [hf]]
    repeat' split
    all_goals
      first
      | rfl
      | (exfalso; omega)

theorem same_cells (b : Ref.Screen) (c c' : Ref.Grid)
    (h : ∀ y < b.rows, ∀ x < b.cols, c x y = c' x y) :
    Ref.Same { b with cell := c } { b with cell := c' } := by
  unfold Ref.Same
  refine
    ⟨rfl, rfl, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, fun g c h =>
      ⟨g, h, fun _ _ _ _ => rfl⟩, id, rfl, rfl⟩

theorem screenOf_grid (v : Vt) (g : Array Row) :
    screenOf { v with grid := g } = { screenOf v with cell := gridOf g v.cols v.pen } := rfl

theorem span_ok {w : Vt} (h : Facts w) (a b : Nat) (f : Nat → Nat → Bool)
    (hf :
      ∀ x < w.cols, ∀ y < w.rows, f x y = (y == w.cursor.y && decide (a ≤ x) && decide (x < b))) :
    Ref.Same (screenOf (w.eraseRowSpan w.cursor.y a b)) ((screenOf w).erase f) := by
  rw [eraseRowSpan_fields, screenOf_grid]
  refine same_cells _ _ _ fun y hy x hx => ?_
  show ((w.eraseRowSpan _ a b).getRow y).getD x default = _
  rw [cell_eraseRowSpan h.shape _ _ _ x y hx hy, hf x hx y hy]
  by_cases hc : y = w.cursor.y ∧ a ≤ x ∧ x < b
  · rw [ite_eq_left hc, ite_eq_left (by simp [hc])]; rfl
  · rw [ite_eq_right hc,
      ite_eq_right
        (by
          simp; omega)];
    rfl

theorem eraseLine_ok {w : Vt} (h : Facts w) (m : Fin 3) :
    Ref.Same (screenOf (w.eraseLine m.val)) (Ref.Seq.apply (screenOf w) (.el m)) := by
  have hx := h.curX
  rcases m with ⟨_ | _ | _ | m, hm⟩
  all_goals
    first
    | omega
    | refine span_ok h _ _ _ fun x hx y _ => ?_
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
      simp
      omega

theorem gridOf_inb (g : Array Row) (c c' : Nat) (p p' : Pen) (x y : Nat) (hy : y < g.size) :
    gridOf g c p x y = gridOf g c' p' x y := by simp [gridOf, Array.getD, hy]

theorem same_of_frame {v u : Vt} (c : Ref.Grid) (hf : u = { v with grid := u.grid })
    (hsize : u.grid.size = v.rows)
    (hcell : ∀ y < v.rows, ∀ x < v.cols, (u.getRow y).getD x default = c x y) :
    Ref.Same (screenOf u) { screenOf v with cell := c } := by
  conv =>
    lhs; rw [hf]
  refine same_cells (screenOf v) (gridOf u.grid v.cols v.pen) c fun y hy x hx => ?_
  rw [← hcell y hy x hx]
  show gridOf u.grid v.cols v.pen x y = gridOf u.grid u.cols u.pen x y
  exact
    gridOf_inb _ _ _ _ _ x y
      (by
        rw [hsize]; exact hy)

theorem rows_ok {w : Vt} (g : Array Row) (hsu : Shape { w with grid := g }) (base k : Nat)
    (f : Nat → Nat → Bool)
    (hf :
      ∀ x < w.cols,
        ∀ y < w.rows,
          (g.getD y (blankRow w.cols w.pen)).getD x default =
            (if f x y && !(decide (base ≤ y) && decide (y < base + k)) then Cell.erased w.pen
            else (w.getRow y).getD x default))
    (hf' : ∀ x < w.cols, ∀ y < w.rows, decide (base ≤ y) && decide (y < base + k) → f x y) :
    Ref.Same (screenOf (eraseRows { w with grid := g } base k)) ((screenOf w).erase f) := by
  have hsh := (eraseRows_cell hsu base k).1
  have hfr := eraseRows_fields { w with grid := g } base k
  refine same_of_frame _ hfr (by rw [hsh.size, hfr]) fun y hy x hx => ?_
  rw [(eraseRows_cell hsu base k).2 x hx y hy]
  show
    (if base ≤ y ∧ y < base + k then Cell.erased w.pen
      else (g.getD y (blankRow w.cols w.pen)).getD x default) =
      _
  by_cases hb : base ≤ y ∧ y < base + k
  · rw [ite_eq_left hb, ite_eq_left (hf' x hx y hy (by simp [hb]))]; rfl
  · rw [ite_eq_right hb, hf x hx y hy]
    by_cases hfx : f x y = true
    · rw [ite_eq_left
          (by
            simp [hfx]; omega),
        ite_eq_left hfx];
      rfl
    · rw [ite_eq_right (by simp [hfx]), ite_eq_right hfx]; rfl

theorem eraseScreen_ok {w : Vt} (h : Facts w) (m : Fin 3) :
    Ref.Same (screenOf (w.eraseScreen m.val)) (Ref.Seq.apply (screenOf w) (.ed m)) := by
  have hs := h.shape
  have hx := h.curX
  rcases m with ⟨_ | _ | _ | m, hm⟩
  · show
      Ref.Same
        (screenOf
          (eraseRows (w.eraseRowSpan w.cursor.y w.cursor.x w.cols) (w.cursor.y + 1)
            (w.rows - w.cursor.y - 1)))
        _
    refine
      rows_ok (w.eraseRowSpan w.cursor.y w.cursor.x w.cols).grid (shape_eraseRowSpan hs _ _ _) _ _ _
        (fun x hx' y hy => ?_)
        (fun x _ y _ hb => by
          revert hb; bool_omega)
    show ((w.eraseRowSpan w.cursor.y w.cursor.x w.cols).getRow y).getD x default = _
    rw [cell_eraseRowSpan hs _ _ _ x y hx' hy]
    by_cases hc : y = w.cursor.y ∧ w.cursor.x ≤ x ∧ x < w.cols
    · rw [ite_eq_left hc,
        ite_eq_left
          (by
            simp; omega)]
    · rw [ite_eq_right hc,
        ite_eq_right
          (by
            simp; omega)]
  · show
      Ref.Same
        (screenOf
          ((List.range w.cursor.y).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols)
            (w.eraseRowSpan w.cursor.y 0 (w.cursor.x + 1))))
        _
    rw [show
        (fun (v' : Vt) (y : Nat) => v'.eraseRowSpan y 0 v'.cols) =
          (fun (v' : Vt) (i : Nat) => v'.eraseRowSpan (0 + i) 0 v'.cols)
        from by simp]
    refine
      rows_ok (w.eraseRowSpan w.cursor.y 0 (w.cursor.x + 1)).grid (shape_eraseRowSpan hs _ _ _) 0
        w.cursor.y _ (fun x hx' y hy => ?_)
        (fun x _ y _ hb => by
          revert hb; bool_omega)
    show ((w.eraseRowSpan w.cursor.y 0 (w.cursor.x + 1)).getRow y).getD x default = _
    rw [cell_eraseRowSpan hs _ _ _ x y hx' hy]
    by_cases hc : y = w.cursor.y ∧ 0 ≤ x ∧ x < w.cursor.x + 1
    · rw [ite_eq_left hc,
        ite_eq_left
          (by
            simp; omega)]
    · rw [ite_eq_right hc,
        ite_eq_right
          (by
            simp; omega)]
  · show
      Ref.Same (screenOf ((List.range w.rows).foldl (fun v' y => v'.eraseRowSpan y 0 v'.cols) w)) _
    rw [show
        (fun (v' : Vt) (y : Nat) => v'.eraseRowSpan y 0 v'.cols) =
          (fun (v' : Vt) (i : Nat) => v'.eraseRowSpan (0 + i) 0 v'.cols)
        from by simp]
    refine
      rows_ok w.grid hs 0 w.rows _ (fun x _ y hy => ?_)
        (fun x _ y _ hb => by
          revert hb; bool_omega)
    rw [ite_eq_right
        (by
          simp; omega)]
    rfl
  · omega

theorem eraseChars_ok {w : Vt} (h : Facts w) (n : Nat) :
    Ref.Same (screenOf (w.eraseChars (Ref.count n))) (Ref.Seq.apply (screenOf w) (.ech n)) :=
  span_ok h _ _ _ fun x hx y _ => by bool_omega

/-! ## Scrolling -/

theorem getRow_scrollUpIn (v : Vt) (top bot : Nat) (a : Bool) (j : Nat) :
    (v.scrollUpIn top bot a).getRow j =
      if j = bot ∧ bot < v.grid.size then blankRow v.cols v.pen
      else
        if top ≤ j ∧ j < top + (bot - top) ∧ j < v.grid.size then v.getRow (top + (j - top) + 1)
        else v.getRow j := by
  have e :
    (v.scrollUpIn top bot a).getRow j =
      (((List.range (bot - top)).foldl
                (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1)))
                v.grid).setIfInBounds
            bot (blankRow v.cols v.pen)).getD
        j (blankRow v.cols v.pen) := by
    unfold Vt.scrollUpIn; split <;> rfl
  rw [e, getD_setIfInBounds', size_foldl_set, foldl_set_fwd]
  rfl

theorem getRow_scrollDownIn (v : Vt) (top bot : Nat) (j : Nat) :
    (v.scrollDownIn top bot).getRow j =
      if j = top ∧ top < v.grid.size then blankRow v.cols v.pen
      else
        if bot + 1 - (bot - top) ≤ j ∧ j ≤ bot ∧ j < v.grid.size then v.getRow (j - 1)
        else v.getRow j := by
  have e :
    (v.scrollDownIn top bot).getRow j =
      (((List.range (bot - top)).foldl
                (fun g i => g.setIfInBounds (bot - i) (v.getRow (bot - i - 1)))
                v.grid).setIfInBounds
            top (blankRow v.cols v.pen)).getD
        j (blankRow v.cols v.pen) :=
    rfl
  rw [e, getD_setIfInBounds', size_foldl_set,
    foldl_set_bwd v.grid bot (bot - top) (by omega) (fun j => v.getRow (j - 1))]
  rfl

theorem scrollUpIn_fields (v : Vt) (top bot : Nat) (a : Bool) :
    ∃ sb,
      v.scrollUpIn top bot a =
        { v with
          grid := (v.scrollUpIn top bot a).grid, sb } := by
  unfold Vt.scrollUpIn; split
  · exact ⟨_, rfl⟩
  · exact ⟨v.sb, rfl⟩

theorem scrollDownIn_fields (v : Vt) (top bot : Nat) :
    v.scrollDownIn top bot = { v with grid := (v.scrollDownIn top bot).grid } := rfl

theorem shape_scrollUpIn {v : Vt} (hs : Shape v) (top bot : Nat) (a : Bool) :
    Shape (v.scrollUpIn top bot a) := by
  obtain ⟨sb, e⟩ := scrollUpIn_fields v top bot a
  have hc : (v.scrollUpIn top bot a).cols = v.cols := by rw [e]
  have hr : (v.scrollUpIn top bot a).rows = v.rows := by rw [e]
  refine ⟨?_, fun j _ => ?_, fun j => ?_⟩
  · have :
      (v.scrollUpIn top bot a).grid =
        ((List.range (bot - top)).foldl
              (fun g i => g.setIfInBounds (top + i) (v.getRow (top + i + 1))) v.grid).setIfInBounds
          bot (blankRow v.cols v.pen) := by
      unfold Vt.scrollUpIn; split <;> rfl
    rw [hr, this]
    simp [size_foldl_set, hs.size]
  · rw [getRow_scrollUpIn, hc]
    split
    · simp [blankRow]
    · split
      · exact hs.size_getRow _
      · exact hs.size_getRow _
  · rw [getRow_scrollUpIn]
    split
    · exact narrow_blankRow _ _
    · split
      · exact hs.narrow _
      · exact hs.narrow _

theorem shape_scrollDownIn {v : Vt} (hs : Shape v) (top bot : Nat) :
    Shape (v.scrollDownIn top bot) := by
  refine ⟨?_, fun j _ => ?_, fun j => ?_⟩
  · show (((List.range (bot - top)).foldl _ v.grid).setIfInBounds top _).size = v.rows
    simp [size_foldl_set, hs.size]
  · rw [getRow_scrollDownIn]
    split
    · simp [blankRow]; rfl
    · split
      · exact hs.size_getRow _
      · exact hs.size_getRow _
  · rw [getRow_scrollDownIn]
    split
    · exact narrow_blankRow _ _
    · split
      · exact hs.narrow _
      · exact hs.narrow _

theorem cell_scrollUpIn {v : Vt} (hs : Shape v) (top bot : Nat) (a : Bool) (htb : top ≤ bot)
    (hb : bot < v.rows) (x j : Nat) (hx : x < v.cols) (hj : j < v.rows) :
    ((v.scrollUpIn top bot a).getRow j).getD x default =
      if top ≤ j ∧ j < bot then (v.getRow (j + 1)).getD x default
      else if j = bot then Cell.erased v.pen else (v.getRow j).getD x default := by
  rw [getRow_scrollUpIn, hs.size]
  by_cases h1 : j = bot
  · rw [ite_eq_left ⟨h1, hb⟩, ite_eq_right (by omega), ite_eq_left h1, getD_blankRow,
      ite_eq_left hx]
  · rw [ite_eq_right (fun h => h1 h.1)]
    by_cases h2 : top ≤ j ∧ j < bot
    · rw [ite_eq_left ⟨h2.1, by omega, hj⟩, ite_eq_left h2,
        show top + (j - top) + 1 = j + 1 by omega]
    · rw [ite_eq_right (by omega), ite_eq_right h2, ite_eq_right h1]

theorem cell_scrollDownIn {v : Vt} (hs : Shape v) (top bot : Nat) (htb : top ≤ bot)
    (_hb : bot < v.rows) (x j : Nat) (hx : x < v.cols) (hj : j < v.rows) :
    ((v.scrollDownIn top bot).getRow j).getD x default =
      if top < j ∧ j ≤ bot then (v.getRow (j - 1)).getD x default
      else if j = top then Cell.erased v.pen else (v.getRow j).getD x default := by
  rw [getRow_scrollDownIn, hs.size]
  by_cases h1 : j = top
  · rw [ite_eq_left ⟨h1, by omega⟩, ite_eq_right (by omega), ite_eq_left h1, getD_blankRow,
      ite_eq_left hx]
  · rw [ite_eq_right (fun h => h1 h.1)]
    by_cases h2 : top < j ∧ j ≤ bot
    · rw [ite_eq_left ⟨by omega, h2.2, hj⟩, ite_eq_left h2]
    · rw [ite_eq_right (by omega), ite_eq_right h2, ite_eq_right h1]

theorem same_of_cells {v u : Vt} (c : Ref.Grid)
    (hf : screenOf u = { screenOf v with cell := gridOf u.grid v.cols v.pen })
    (hsize : u.grid.size = v.rows)
    (hcell : ∀ y < v.rows, ∀ x < v.cols, (u.getRow y).getD x default = c x y) :
    Ref.Same (screenOf u) { screenOf v with cell := c } := by
  rw [hf]
  refine same_cells (screenOf v) (gridOf u.grid v.cols v.pen) c fun y hy x hx => ?_
  rw [← hcell y hy x hx]
  exact
    gridOf_inb _ _ _ _ _ x y
      (by
        rw [hsize]; exact hy)

theorem same_on (B : Ref.Screen) (u : Vt) (c : Ref.Grid)
    (hf : screenOf u = { B with cell := gridOf u.grid u.cols u.pen })
    (hcell : ∀ y < B.rows, ∀ x < B.cols, (u.getRow y).getD x default = c x y) :
    Ref.Same (screenOf u) { B with cell := c } := by
  rw [hf]
  exact same_cells B (gridOf u.grid u.cols u.pen) c hcell

theorem scrollUp_ok {w : Vt} (hs : Shape w) (htb : w.top ≤ w.bot) (hb : w.bot < w.rows) :
    Ref.Same (screenOf w.scrollUp) (screenOf w).scrollUp := by
  obtain ⟨sb, e⟩ := scrollUpIn_fields w w.top w.bot true
  have hsz := (shape_scrollUpIn hs w.top w.bot true).size
  rw [e] at hsz
  refine same_of_cells _ (by rw [Vt.scrollUp, e]) hsz fun y hy x hx => ?_
  rw [Vt.scrollUp, cell_scrollUpIn hs _ _ _ htb hb x y hx hy]
  rfl

theorem scrollDown_ok {w : Vt} (hs : Shape w) (htb : w.top ≤ w.bot) (hb : w.bot < w.rows) :
    Ref.Same (screenOf w.scrollDown) (screenOf w).scrollDown := by
  have hsz := (shape_scrollDownIn hs w.top w.bot).size
  refine same_of_cells _ rfl hsz fun y hy x hx => ?_
  rw [Vt.scrollDown, cell_scrollDownIn hs _ _ htb hb x y hx hy]
  rfl

theorem same_pending {a b : Ref.Screen} (h : Ref.Same a b) (p : Bool) :
    Ref.Same { a with pending := p } { b with pending := p } := by
  obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

theorem Shape.cursor {v : Vt} (hs : Shape v) (c : Cursor) : Shape { v with cursor := c } :=
  ⟨hs.size, hs.rowSize, hs.narrow⟩

theorem lineFeed_ok {w : Vt} (h : Facts w) :
    Ref.Same (screenOf w.lineFeed) (screenOf w).lineFeed := by
  unfold Vt.lineFeed Vt.clearPending Ref.Screen.lineFeed
  dsimp only
  by_cases hy : w.cursor.y = w.bot
  · rw [ite_eq_left (by simp [hy]), ite_eq_left hy]
    exact scrollUp_ok (h.shape.cursor _) h.topLe h.botLt
  · rw [ite_eq_right (by simp [hy]), ite_eq_right hy]
    by_cases hr : w.cursor.y + 1 < w.rows
    · rw [ite_eq_left hr, ite_eq_left hr]; exact same_refl _
    · rw [ite_eq_right hr, ite_eq_right hr]; exact same_refl _

theorem reverseIndex_ok {w : Vt} (h : Facts w) :
    Ref.Same (screenOf w.reverseIndex) (screenOf w).reverseIndex := by
  unfold Vt.reverseIndex Vt.clearPending Ref.Screen.reverseIndex
  dsimp only
  by_cases hy : w.cursor.y = w.top
  · rw [ite_eq_left (by simp [hy]), ite_eq_left hy]
    exact scrollDown_ok (h.shape.cursor _) h.topLe h.botLt
  · rw [ite_eq_right (by simp [hy]), ite_eq_right hy]
    exact same_refl _

/-! ## Inserting and deleting lines -/

theorem repeat_scrollDown {v : Vt} (hs : Shape v) (y bot : Nat) (hyb : y ≤ bot) (hb : bot < v.rows)
    (k : Nat) :
    (List.range k).foldl (fun w _ => w.scrollDownIn y bot) v =
        { v with grid := ((List.range k).foldl (fun w _ => w.scrollDownIn y bot) v).grid } ∧
      Shape ((List.range k).foldl (fun w _ => w.scrollDownIn y bot) v) ∧
      ∀ x < v.cols,
        ∀ j < v.rows,
          (((List.range k).foldl (fun w _ => w.scrollDownIn y bot) v).getRow j).getD x default =
            if y ≤ j ∧ j ≤ bot then
              if j < y + k then Cell.erased v.pen else (v.getRow (j - k)).getD x default
            else (v.getRow j).getD x default := by
  induction k with
  | zero =>
    refine ⟨rfl, hs, fun x _ j _ => ?_⟩
    simp only [List.range_zero, List.foldl_nil]
    split
    · rw [ite_eq_right (by omega), Nat.sub_zero]
    · rfl
  | succ k ih =>
    obtain ⟨e, hs', hc⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hu : (List.range k).foldl (fun w _ => w.scrollDownIn y bot) v = u at e hs' hc
    refine ⟨by rw [scrollDownIn_fields, e], shape_scrollDownIn hs' _ _, fun x hx j hj => ?_⟩
    have hx' : x < u.cols := by
      rw [e]; exact hx
    have hj' : j < u.rows := by
      rw [e]; exact hj
    rw [cell_scrollDownIn hs' _ _ hyb
        (by
          rw [e]; exact hb)
        x j hx' hj']
    rw [show u.pen = v.pen by rw [e], hc x hx j hj]
    by_cases h0 : j = 0
    · subst h0
      repeat' split
      all_goals
        first
        | rfl
        | (exfalso; omega)
    · rw [hc x hx (j - 1) (by omega)]
      repeat' split
      all_goals
        first
        | rfl
        | (exfalso; omega)
        | (congr 2; omega)

theorem repeat_scrollUp {v : Vt} (hs : Shape v) (y bot : Nat) (hyb : y ≤ bot) (hb : bot < v.rows)
    (k : Nat) :
    (∃ sb,
        (List.range k).foldl (fun w _ => w.scrollUpIn y bot false) v =
          { v with
            grid := ((List.range k).foldl (fun w _ => w.scrollUpIn y bot false) v).grid, sb }) ∧
      Shape ((List.range k).foldl (fun w _ => w.scrollUpIn y bot false) v) ∧
      ∀ x < v.cols,
        ∀ j < v.rows,
          (((List.range k).foldl (fun w _ => w.scrollUpIn y bot false) v).getRow j).getD x default =
            if y ≤ j ∧ j ≤ bot then
              if j + k ≤ bot then (v.getRow (j + k)).getD x default else Cell.erased v.pen
            else (v.getRow j).getD x default := by
  induction k with
  | zero =>
    refine ⟨⟨v.sb, rfl⟩, hs, fun x _ j _ => ?_⟩
    simp only [List.range_zero, List.foldl_nil]
    split
    · rw [ite_eq_left (by omega), Nat.add_zero]
    · rfl
  | succ k ih =>
    obtain ⟨⟨sb, e⟩, hs', hc⟩ := ih
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize hu : (List.range k).foldl (fun w _ => w.scrollUpIn y bot false) v = u at e hs' hc
    obtain ⟨sb', e'⟩ := scrollUpIn_fields u y bot false
    refine ⟨⟨sb', by rw [e', e]⟩, shape_scrollUpIn hs' _ _ _, fun x hx j hj => ?_⟩
    have hx' : x < u.cols := by
      rw [e]; exact hx
    have hj' : j < u.rows := by
      rw [e]; exact hj
    rw [cell_scrollUpIn hs' _ _ _ hyb
        (by
          rw [e]; exact hb)
        x j hx' hj']
    rw [show u.pen = v.pen by rw [e], hc x hx j hj]
    by_cases h0 : j + 1 < v.rows
    · rw [hc x hx (j + 1) h0]
      repeat' split
      all_goals
        first
        | rfl
        | (exfalso; omega)
        | (congr 2; omega)
    · repeat' split
      all_goals
        first
        | rfl
        | (exfalso; omega)

theorem insertLines_ok {w : Vt} (h : Facts w) (n : Nat) :
    Ref.Same (screenOf (w.insertLines (Ref.count n))) (Ref.Seq.apply (screenOf w) (.il n)) := by
  unfold Vt.insertLines Vt.repeatAtMost
  simp only [Ref.Seq.apply]
  by_cases hout : w.cursor.y < w.top ∨ w.bot < w.cursor.y
  · rw [ite_eq_left
        (by
          simp; omega),
      ite_eq_left hout];
    exact same_refl _
  · rw [ite_eq_right
        (by
          simp; omega),
      ite_eq_right hout]
    have hyb : w.cursor.y ≤ w.bot := by omega
    obtain ⟨e, hs', hc⟩ :=
      repeat_scrollDown h.shape w.cursor.y w.bot hyb h.botLt
        (min (Ref.count n) (w.bot - w.cursor.y + 1))
    generalize
      (List.range (min (Ref.count n) (w.bot - w.cursor.y + 1))).foldl
        (fun w' _ => w'.scrollDownIn w.cursor.y w.bot) w =
      u at e hs' hc
    refine
      same_on
        { screenOf w with
          x := 0, pending := false }
        u.carriageReturn _
        (by
          rw [e]; rfl)
        fun j hj x hx => ?_
    rw [show u.carriageReturn.getRow j = u.getRow j from rfl, hc x hx j hj]
    have := count_pos n
    by_cases h1 : w.cursor.y ≤ j ∧ j ≤ w.bot
    · rw [ite_eq_left h1, ite_eq_left h1]
      by_cases h2 : j < w.cursor.y + Ref.count n
      · rw [ite_eq_left (by omega), ite_eq_left h2]; rfl
      · rw [ite_eq_right (by omega), ite_eq_right h2,
          show min (Ref.count n) (w.bot - w.cursor.y + 1) = Ref.count n by omega]
        rfl
    · rw [ite_eq_right h1, ite_eq_right h1]
      rfl

theorem deleteLines_ok {w : Vt} (h : Facts w) (n : Nat) :
    Ref.Same (screenOf (w.deleteLines (Ref.count n))) (Ref.Seq.apply (screenOf w) (.dl n)) := by
  unfold Vt.deleteLines Vt.repeatAtMost
  simp only [Ref.Seq.apply]
  by_cases hout : w.cursor.y < w.top ∨ w.bot < w.cursor.y
  · rw [ite_eq_left
        (by
          simp; omega),
      ite_eq_left hout];
    exact same_refl _
  · rw [ite_eq_right
        (by
          simp; omega),
      ite_eq_right hout]
    have hyb : w.cursor.y ≤ w.bot := by omega
    obtain ⟨⟨sb, e⟩, hs', hc⟩ :=
      repeat_scrollUp h.shape w.cursor.y w.bot hyb h.botLt
        (min (Ref.count n) (w.bot - w.cursor.y + 1))
    generalize
      (List.range (min (Ref.count n) (w.bot - w.cursor.y + 1))).foldl
        (fun w' _ => w'.scrollUpIn w.cursor.y w.bot false) w =
      u at e hs' hc
    refine
      same_on
        { screenOf w with
          x := 0, pending := false }
        u.carriageReturn _
        (by
          rw [e]; rfl)
        fun j hj x hx => ?_
    rw [show u.carriageReturn.getRow j = u.getRow j from rfl, hc x hx j hj]
    have := count_pos n
    by_cases h1 : w.cursor.y ≤ j ∧ j ≤ w.bot
    · rw [ite_eq_left h1, ite_eq_left h1]
      by_cases h2 : j + Ref.count n ≤ w.bot
      · rw [ite_eq_left (by omega), ite_eq_left h2,
          show min (Ref.count n) (w.bot - w.cursor.y + 1) = Ref.count n by omega];
        rfl
      · rw [ite_eq_right (by omega), ite_eq_right h2]; rfl
    · rw [ite_eq_right h1, ite_eq_right h1]
      rfl

/-! ## Inserting and deleting characters -/

theorem cell_setRow {v : Vt} (hs : Shape v) (R : Row) (hR : Narrow R) (x j : Nat)
    (hj : j < v.rows) :
    (Vt.getRow ({ v with grid := v.grid.setIfInBounds v.cursor.y R.mend }) j).getD x default =
      if j = v.cursor.y then R.getD x default else (v.getRow j).getD x default := by
  show ((v.grid.setIfInBounds v.cursor.y R.mend).getD j (blankRow v.cols v.pen)).getD x default = _
  rw [getD_setIfInBounds', mend_narrow hR]
  by_cases hjy : j = v.cursor.y
  · rw [ite_eq_left
        ⟨hjy, by
          rw [hs.size]; omega⟩,
      ite_eq_left hjy]
  · rw [ite_eq_right (fun h => hjy h.1), ite_eq_right hjy]; rfl

theorem insertChars_ok {w : Vt} (h : Facts w) (n : Nat) :
    Ref.Same (screenOf (w.insertChars (Ref.count n))) (Ref.Seq.apply (screenOf w) (.ich n)) := by
  have hs := h.shape
  have hx := h.curX
  have hy := h.curY
  have hp := count_pos n
  simp only [Ref.Seq.apply]
  refine same_on (screenOf w) _ _ rfl fun j hj x' hx' => ?_
  unfold Vt.insertChars
  change j < w.rows at hj
  change x' < w.cols at hx'
  rw [cell_setRow hs _
      (narrow_foldl_set (hs.narrow _) _ _ _
        (fun i => by
          split; exact hs.narrow _ _; rfl))
      x' j hj]
  rw [foldl_set_bwd (w.getRow w.cursor.y) (w.cols - 1) (w.cols - w.cursor.x) (by omega)
      (fun i =>
        if i ≥ w.cursor.x + min (Ref.count n) (w.cols - w.cursor.x) then
          (w.getRow w.cursor.y).getD (i - min (Ref.count n) (w.cols - w.cursor.x)) default
        else Cell.erased w.pen),
    hs.rowSize _ hy]
  by_cases hjy : j = w.cursor.y
  · subst hjy
    repeat' split
    all_goals
      first
      | rfl
      | (exfalso; omega)
      | (congr 1; omega)
  · rw [ite_eq_right hjy, ite_eq_right (fun h => hjy h.1)]; rfl

theorem deleteChars_ok {w : Vt} (h : Facts w) (n : Nat) :
    Ref.Same (screenOf (w.deleteChars (Ref.count n))) (Ref.Seq.apply (screenOf w) (.dch n)) := by
  have hs := h.shape
  have hx := h.curX
  have hy := h.curY
  have hp := count_pos n
  simp only [Ref.Seq.apply]
  refine same_on (screenOf w) _ _ rfl fun j hj x' hx' => ?_
  unfold Vt.deleteChars
  change j < w.rows at hj
  change x' < w.cols at hx'
  rw [cell_setRow hs _
      (narrow_foldl_set (hs.narrow _) _ _ _
        (fun i => by
          split; exact hs.narrow _ _; rfl))
      x' j hj]
  rw [foldl_set_fwd (w.getRow w.cursor.y) w.cursor.x (w.cols - w.cursor.x)
      (fun i =>
        if w.cursor.x + i + min (Ref.count n) (w.cols - w.cursor.x) < w.cols then
          (w.getRow w.cursor.y).getD (w.cursor.x + i + min (Ref.count n) (w.cols - w.cursor.x))
            default
        else Cell.erased w.pen),
    hs.rowSize _ hy]
  by_cases hjy : j = w.cursor.y
  · subst hjy
    repeat' split
    all_goals
      first
      | rfl
      | (exfalso; omega)
      | (congr 1; omega)
  · rw [ite_eq_right hjy, ite_eq_right (fun h => hjy h.1)]; rfl

/-! ## Printing -/

theorem Facts.cr {w : Vt} (h : Facts w) : Facts w.carriageReturn :=
  { h with
    curX := h.colsPos, pendX := fun hp => absurd hp (by simp [Vt.carriageReturn]),
    originIn := h.originIn, curY := h.curY }

theorem shape_lineFeed {w : Vt} (hs : Shape w) : Shape w.lineFeed := by
  unfold Vt.lineFeed Vt.clearPending
  dsimp only
  split
  · exact shape_scrollUpIn (hs.cursor _) _ _ _
  · split
    · exact hs.cursor _
    · exact hs.cursor _

theorem lineFeed_frame (w : Vt) :
    w.lineFeed.cols = w.cols ∧
      w.lineFeed.rows = w.rows ∧ w.lineFeed.pen = w.pen ∧ w.lineFeed.modes = w.modes := by
  unfold Vt.lineFeed Vt.clearPending Vt.scrollUp
  dsimp only
  split
  · obtain ⟨sb, e⟩ :=
      scrollUpIn_fields { w with cursor := { w.cursor with pending := false } } w.top w.bot true
    rw [e]; exact ⟨rfl, rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem lineFeed_cursor {w : Vt} (h : Facts w) : w.lineFeed.cursor.y < w.rows := by
  unfold Vt.lineFeed Vt.clearPending Vt.scrollUp
  dsimp only
  split
  · obtain ⟨sb, e⟩ :=
      scrollUpIn_fields { w with cursor := { w.cursor with pending := false } } w.top w.bot true
    rw [e]; exact h.curY
  · split
    · dsimp only; omega
    · exact h.curY

theorem lineFeed_x (w : Vt) : w.lineFeed.cursor.x = w.cursor.x := by
  unfold Vt.lineFeed Vt.clearPending Vt.scrollUp
  dsimp only
  split
  · obtain ⟨sb, e⟩ :=
      scrollUpIn_fields { w with cursor := { w.cursor with pending := false } } w.top w.bot true
    rw [e]
  · split <;> rfl

theorem cell_put {v : Vt} (hs : Shape v) (c : Cell) (hc : c.width = 1) (x' j : Nat)
    (hj : j < v.rows) :
    (((v.putCell v.cursor.x v.cursor.y c).mendRow v.cursor.x v.cursor.y).getRow j).getD x' default =
      if x' = v.cursor.x ∧ j = v.cursor.y ∧ v.cursor.x < v.cols ∧ v.cursor.y < v.rows then c
      else (v.getRow j).getD x' default := by
  show
    ((((v.grid.modify v.cursor.y (·.setIfInBounds v.cursor.x c)).modify v.cursor.y
                (·.mendNear v.cursor.x))).getD
            j (blankRow v.cols v.pen)).getD
        x' default =
      _
  simp only [getD_modify', Array.size_modify]
  have hsz := hs.size
  by_cases hjy : j = v.cursor.y
  · subst hjy
    rw [ite_eq_left
        (by
          simp; omega),
      ite_eq_left
        (by
          simp; omega),
      show (v.grid.getD v.cursor.y (blankRow v.cols v.pen)) = v.getRow v.cursor.y from rfl,
      mendNear_narrow (narrow_set (hs.narrow _) _ hc), getD_setIfInBounds', hs.rowSize _ hj]
    by_cases hx : x' = v.cursor.x ∧ v.cursor.x < v.cols
    · rw [ite_eq_left hx, ite_eq_left ⟨hx.1, rfl, hx.2, hj⟩]
    · rw [ite_eq_right hx, ite_eq_right (by omega)]
  · rw [ite_eq_right (fun h => hjy h.1), ite_eq_right (fun h => hjy h.1), ite_eq_right (by omega)];
    rfl

theorem putAdvance_ok {u : Vt} (hs : Shape u) (hx : u.cursor.x < u.cols) (hy : u.cursor.y < u.rows)
    (c : Char) {R : Ref.Screen} (hR : Ref.Same (screenOf u) R) (hp : R.pending = false) :
    Ref.Same
      (screenOf
        (((u.putCell u.cursor.x u.cursor.y
                  { base := c, marks := [], width := 1, pen := u.pen }).mendRow
              u.cursor.x u.cursor.y).printAdvance
          1))
      (let s := R.put R.x R.y { base := c, pen := R.pen }
       if s.cols ≤ s.x + 1 then
        { s with
          x := s.cols - 1, pending := s.modes.wrap }
      else { s with x := s.x + 1 }) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hR
  dsimp only at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  unfold Vt.printAdvance
  dsimp only
  dsimp only [Ref.Screen.put]
  have hcells :
    ∀ j < u.rows,
      ∀ x' < u.cols,
        (((u.putCell u.cursor.x u.cursor.y
                        { base := c, marks := [], width := 1, pen := u.pen }).mendRow
                    u.cursor.x u.cursor.y).getRow
                j).getD
            x' default =
          (if x' = R.x ∧ j = R.y then ({ base := c, pen := R.pen } : Cell) else R.cell x' j) := by
    intro j hj x' hx'
    rw [cell_put hs _ rfl x' j hj, ← h4, ← h5, ← h7]
    by_cases hc : x' = u.cursor.x ∧ j = u.cursor.y
    · rw [ite_eq_left ⟨hc.1, hc.2, hx, hy⟩, ite_eq_left hc]
    · rw [ite_eq_right (by omega), ite_eq_right hc]; exact h3 j hj x' hx'
  have hm2 : (u.cursor.x + 1 ≥ u.cols) = (R.cols ≤ R.x + 1) := by rw [← h1, ← h4]
  by_cases hm : u.cursor.x + 1 ≥ u.cols
  · have hm' : R.cols ≤ R.x + 1 := hm2 ▸ hm
    simp only [hm', ↓reduceIte, Vt.putCell, Vt.mendRow, hm]
    exact
      ⟨h1, h2, fun j hj x' hx' => hcells j hj x' hx', by rw [h1], h5, by rw [h8], h7, h8, h9, h10,
        h11, h12, h13, h14, h15, h16⟩
  · have hm' : ¬R.cols ≤ R.x + 1 := hm2 ▸ hm
    simp only [hm', ↓reduceIte, Vt.putCell, Vt.mendRow, hm]
    exact
      ⟨h1, h2, fun j hj x' hx' => hcells j hj x' hx', by rw [h4], h5, hp.symm, h7, h8, h9, h10, h11,
        h12, h13, h14, h15, h16⟩

theorem printChar_ascii {w : Vt} (h : Facts w) (c : Char) (h1 : 0x20 ≤ c.toNat)
    (h2 : c.toNat < 0x7F) : w.printChar c = c := by
  unfold Vt.printChar printableChar
  simp only [h.g0, h.g1, Bool.and_false, Bool.or_false, Bool.false_eq_true, ite_false]
  rw [ite_eq_right
      (by
        simp; omega)]

theorem print_ok {w : Vt} (h : Facts w) (c : Char) (h1 : 0x20 ≤ c.toNat) (h2 : c.toNat < 0x7F) :
    Ref.Same (screenOf (w.print c)) ((screenOf w).print c) := by
  have hw : charWidth c = 1 := charWidth_low c (by omega)
  unfold Vt.print
  rw [printChar_ascii h c h1 h2]
  dsimp only
  rw [hw]
  simp only [show (1 == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  have hwrap : (w.printWrap.printWideWrap 1) = w.printWrap := by
    unfold Vt.printWideWrap; simp
  have hshift : (w.printWrap.printShift 1) = w.printWrap := by
    unfold Vt.printShift
    rw [ite_eq_right]
    show ¬w.printWrap.modes.insert = true
    unfold Vt.printWrap Vt.clearPending
    split
    · rw [(lineFeed_frame _).2.2.2]; simp [Vt.carriageReturn, h.insertOff]
    · simp [h.insertOff]
  rw [hwrap, hshift]
  unfold Vt.printPut
  simp only [show (1 == 2) = false from rfl, Bool.false_eq_true, Bool.false_and, ↓reduceIte]
  unfold Ref.Screen.print
  dsimp only
  unfold Vt.printWrap
  by_cases hp : w.cursor.pending = true ∧ w.modes.wrap = true
  · rw [ite_eq_left (by simp [hp])]
    rw [ite_eq_left (show (screenOf w).pending = true ∧ (screenOf w).modes.wrap = true from hp)]
    have hc := h.cr
    have hs := shape_lineFeed hc.shape
    have hf := lineFeed_frame w.carriageReturn
    refine putAdvance_ok hs ?_ ?_ c (lineFeed_ok hc) ?_
    · rw [hf.1, lineFeed_x]; exact hc.curX
    · rw [hf.2.1]; exact lineFeed_cursor hc
    · unfold Ref.Screen.lineFeed; split
      · rfl
      · split <;> rfl
  · rw [ite_eq_right (by simpa using hp)]
    rw [ite_eq_right (show ¬((screenOf w).pending = true ∧ (screenOf w).modes.wrap = true) from hp)]
    exact
      putAdvance_ok (h.shape.cursor { w.cursor with pending := false }) h.curX h.curY c
        (same_refl _) rfl

/-! ## The cursor, the pen, the modes and the title -/

theorem backspace_ok (w : Vt) : screenOf w.backspace = (screenOf w).backspace := by
  unfold Vt.backspace Vt.clearPending Ref.Screen.backspace
  by_cases hp : w.cursor.pending = true
  · rw [ite_eq_left hp, ite_eq_left hp]
  · rw [ite_eq_right hp, ite_eq_right hp]

theorem nextStop_eq (tabs : Array Bool) (cols i : Nat) :
    Ref.nextStop (fun j => tabs.getD j false) cols i = nextTabStop tabs cols i := by
  fun_induction nextTabStop tabs cols i with
  | case1 i hi ht =>
    unfold Ref.nextStop
    rw [show cols - i = (cols - i - 1) + 1 by omega, List.range'_succ, List.find?_cons, ht]
    rfl
  | case2 i hi ht ih =>
    unfold Ref.nextStop at ih ⊢
    rw [show cols - i = (cols - (i + 1)) + 1 by omega, List.range'_succ, List.find?_cons,
      show tabs.getD i false = false by simpa using ht]
    exact ih
  | case3 i hi =>
    unfold Ref.nextStop
    by_cases hc : i < cols
    · rw [show cols - i = 1 by omega, show i = cols - 1 by omega]
      simp only [List.range'_one, List.find?_cons, List.find?_nil]
      split <;> rfl
    · rw [show cols - i = 0 by omega]; rfl

theorem tab_ok (w : Vt) : screenOf w.tab = (screenOf w).tab := by
  unfold Vt.tab Vt.clearPending Ref.Screen.tab
  simp only [screenOf, nextStop_eq]

theorem saveCursor_ok (w : Vt) : screenOf w.saveCursor = Ref.Seq.apply (screenOf w) .decsc := rfl

/-- A screen differing from another only in the pen its rows past the screen read in. -/
theorem same_pen {w : Vt} (h : Facts w) (u : Vt) (B : Ref.Screen) (hg : u.grid = w.grid)
    (hf : screenOf u = { B with cell := gridOf u.grid u.cols u.pen })
    (hB : B.cell = (screenOf w).cell) (hr : B.rows = w.rows) : Ref.Same (screenOf u) B := by
  have :=
    same_on B u B.cell hf fun y hy x _ => by
      rw [hB]
      show gridOf u.grid u.cols u.pen x y = gridOf w.grid w.cols w.pen x y
      rw [hg]
      exact
        gridOf_inb _ _ _ _ _ x y
          (by
            rw [h.gridSize]; omega)
  exact this

theorem restoreCursor_ok {w : Vt} (h : Facts w) :
    Ref.Same (screenOf w.restoreCursor) (Ref.Seq.apply (screenOf w) .decrc) := by
  refine same_pen h _ _ rfl ?_ rfl rfl
  unfold Vt.restoreCursor Vt.restoreFrom
  simp only [Ref.Seq.apply]
  by_cases ho : w.saved.origin = true
  · rw [ite_eq_left ho]; simp [ho]
  · rw [ite_eq_right ho]; simp [ho]

theorem bell_ok (w : Vt) : screenOf { w with bell := true } = Ref.Seq.apply (screenOf w) .bel := rfl

/-! ## SGR -/

theorem u8_min (i : UInt8) : UInt8.ofNat (min i.toNat 255) = i := by
  have h := i.toNat_lt
  rw [Nat.min_eq_left (by omega), UInt8.ofNat_toNat]

theorem go_attr (p : Pen) (a : Ref.Sgr) (rest : List (Nat × Bool)) :
    Vt.applySgr.go p ((a.params.map fun n => (n, false)) ++ rest) =
      Vt.applySgr.go (a.apply p) rest := by
  cases a with
  | fg8 i =>
    rcases i with ⟨i, hi⟩
    simp only [Ref.Sgr.params, Ref.Sgr.apply, List.map, List.cons_append, List.nil_append]
    rw [Vt.applySgr.go]
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | bg8 i =>
    rcases i with ⟨i, hi⟩
    simp only [Ref.Sgr.params, Ref.Sgr.apply, List.map, List.cons_append, List.nil_append]
    rw [Vt.applySgr.go]
    match i, hi with
    | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ => rfl
  | fg256 i
  | bg256
    i =>
    simp only [Ref.Sgr.params, Ref.Sgr.apply, List.map, List.cons_append, List.nil_append]
    rw [Vt.applySgr.go]
    simp [color256, u8_min]
  | fgRgb r g b
  | bgRgb r g
    b =>
    simp only [Ref.Sgr.params, Ref.Sgr.apply, List.map, List.cons_append, List.nil_append]
    rw [Vt.applySgr.go]
    simp [u8_min]
  | _ =>
    simp only [Ref.Sgr.params, Ref.Sgr.apply, List.map, List.cons_append, List.nil_append]
    rw [Vt.applySgr.go]
    rfl

theorem go_attrs (p : Pen) (attrs : List Ref.Sgr) :
    Vt.applySgr.go p ((attrs.flatMap Ref.Sgr.params).map fun n => (n, false)) =
      attrs.foldl Ref.Sgr.apply p := by
  induction attrs generalizing p with
  | nil => simp [Vt.applySgr.go]
  | cons a as ih =>
    rw [List.flatMap_cons, List.map_append, go_attr, ih]; rfl

/-! ## The alternate screen -/

theorem enterAlt_ok {w : Vt} (h : Facts w) :
    Ref.Same (screenOf (w.enterAlt true)) (screenOf w).enterAlt := by
  unfold Vt.enterAlt Ref.Screen.enterAlt
  rw [show (screenOf w).main = w.altGrid.map (fun gs => (gridOf gs.1 w.cols {}, savedOf gs.2)) from
      rfl]
  cases ha : w.altGrid with
  | some gs =>
    rw [ite_eq_left (by simp)]
    simp only [Option.map_some]
    exact same_refl _
  | none =>
    rw [ite_eq_right (by simp)]
    simp only [Option.map_none]
    refine
      ⟨rfl, rfl, fun y hy x hx => ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl,
        fun g c hgc => ?_, fun hn => by simp at hn, rfl, rfl⟩
    · simp only [gridOf] at hy hx ⊢
      rw [show
          (Array.replicate w.rows (blankRow w.cols {})).getD y (blankRow w.cols w.pen) =
            blankRow w.cols {}
          from by simp [Array.getD, hy],
        getD_blankRow, ite_eq_left hx]
      rfl
    · simp at hgc
      obtain ⟨rfl, rfl⟩ := hgc
      exact
        ⟨_, rfl, fun y hy x _ =>
          gridOf_inb _ _ _ _ _ x y
            (by
              rw [h.gridSize]; exact hy)⟩

theorem leaveAlt_ok {w : Vt} (h : Facts w) :
    Ref.Same (screenOf (w.leaveAlt true)) (screenOf w).leaveAlt := by
  unfold Vt.leaveAlt Ref.Screen.leaveAlt
  rw [show (screenOf w).main = w.altGrid.map (fun gs => (gridOf gs.1 w.cols {}, savedOf gs.2)) from
      rfl]
  cases ha : w.altGrid with
  | none =>
    simp only [screenOf, ha, Option.map_none]
    exact same_refl _
  | some gs =>
    obtain ⟨g, sv⟩ := gs
    have hg := h.altSize g sv ha
    simp only [screenOf, Option.map_some, ite_true]
    refine
      ⟨rfl, rfl, fun y hy x _ =>
        gridOf_inb _ _ _ _ _ x y
          (by
            rw [hg]; exact hy),
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ => rfl, rfl, fun g c hgc => by simp at hgc,
        fun _ => rfl, rfl, rfl⟩

end Terminal.Vt.Conform
