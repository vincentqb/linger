import Zmx.Core.Vt
/-! # §Total / §Chunk / §Bound — the emulator theorems

THEOREMS.md rows for `Vt`:
* §Chunk — `feed` is invariant under re-chunking (definitional, from
  `feed = foldl step`, but stated so a rewrite cannot silently lose it).
* §Bound — the anti-zellij row: no field of `Vt` grows with input
  volume. Scrollback ≤ `sbCap`, OSC accumulator ≤ 2048, CSI params
  ≤ 16, UTF-8 pending ≤ 3 — preserved by `step` for ANY byte, hence by
  `feed` for ANY byte stream.
* §Total — `step` preserves the structural sanity of the screen: grid
  dimensions don't change, and the cursor (plus every stashed cursor)
  stays strictly inside them. Together with "no `partial def` in
  `Zmx/Core`" (checked by grep in e2e) this is the no-crash statement.

The invariant is one structure, `Good`, so each preservation lemma is
one implication and `step` is a case-bash over the parser states.
-/

namespace Zmx.Core.Vt

/-- Everything §Total and §Bound need, as one induction hypothesis. -/
structure Good (v : Vt) : Prop where
  colsPos : 1 ≤ v.cols
  rowsPos : 1 ≤ v.rows
  colsLe : v.cols ≤ 1000
  rowsLe : v.rows ≤ 1000
  curX : v.cursor.x < v.cols
  curY : v.cursor.y < v.rows
  savX : v.saved.cur.x < v.cols
  savY : v.saved.cur.y < v.rows
  altCur : ∀ g c p, v.altGrid = some (g, c, p) → c.x < v.cols ∧ c.y < v.rows
  topLe : v.top ≤ v.bot
  botLt : v.bot < v.rows
  sbLe : v.sb.size ≤ sbCap
  u8Le : v.u8need ≤ 3
  csiLe : ∀ s, v.pstate = .csi s → s.params.size ≤ 16
  oscLe : ∀ acc e, v.pstate = .osc acc e → acc.size ≤ 2048

/-- The state a fresh session starts in is Good. -/
theorem good_init (cols rows : Nat) : Good (Vt.init cols rows) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [Vt.init, clampDim, Ring.size, sbCap] <;> omega

end Zmx.Core.Vt


namespace Zmx.Core.Vt.Good

open Zmx.Core.Vt

/-- "Preserves Good and the screen dimensions." Every constituent of
`step` gets one of these; `step` composes them. -/
def Pres (f : Vt → Vt) : Prop :=
  ∀ v, Good v → Good (f v) ∧ (f v).cols = v.cols ∧ (f v).rows = v.rows

theorem Pres.id : Pres (fun v => v) := fun _ h => ⟨h, rfl, rfl⟩

theorem Pres.comp {f g : Vt → Vt} (hf : Pres f) (hg : Pres g) :
    Pres (fun v => g (f v)) := by
  intro v h
  obtain ⟨h1, hc1, hr1⟩ := hf v h
  obtain ⟨h2, hc2, hr2⟩ := hg (f v) h1
  exact ⟨h2, by rw [hc2, hc1], by rw [hr2, hr1]⟩

theorem Pres.foldl {α : Type} {f : Vt → α → Vt}
    (hf : ∀ a, Pres (f · a)) : ∀ (l : List α), Pres (fun v => l.foldl f v)
  | [] => Pres.id
  | a :: l => by
    have := Pres.comp (hf a) (Pres.foldl hf l)
    simpa [List.foldl_cons] using this

/-- Replacing only the grid touches nothing Good watches. Same for
pen, modes, tabs, title, bell — all definitional repacks. -/
theorem set_grid {v : Vt} (g : Array Row) (h : Good v) :
    Good { v with grid := g } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem set_pen {v : Vt} (p : Pen) (h : Good v) :
    Good { v with pen := p } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem set_modes {v : Vt} (m : Modes) (h : Good v) :
    Good { v with modes := m } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem set_ground {v : Vt} (h : Good v) :
    Good { v with pstate := .ground } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8,
    (fun _ h => nomatch h), (fun _ _ h => nomatch h)⟩

theorem set_tabs {v : Vt} (t : Array Bool) (h : Good v) :
    Good { v with tabs := t } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

end Zmx.Core.Vt.Good


namespace Zmx.Core.Vt.Good


/-! ## Cursor-writing primitives -/

theorem clearPending {v : Vt} (h : Good v) : Good v.clearPending := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem moveTo {v : Vt} (x y : Nat) (h : Good v) : Good (v.moveTo x y) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.moveTo
  refine ⟨cp, rp, cl, rl, ?_, ?_, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · dsimp only; omega
  · by_cases ho : v.modes.origin <;> simp [ho] <;> omega

theorem moveRel {v : Vt} (dx dy : Int) (h : Good v) : Good (v.moveRel dx dy) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.moveRel
  refine ⟨cp, rp, cl, rl, ?_, ?_, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · dsimp only; omega
  · by_cases hr : (v.cursor.y ≥ v.top && v.cursor.y ≤ v.bot) <;> simp [hr] <;> omega

theorem carriageReturn {v : Vt} (h : Good v) : Good v.carriageReturn := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, by dsimp only [Vt.carriageReturn]; omega, cy,
    sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem backspace {v : Vt} (h : Good v) : Good v.backspace := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.backspace Vt.clearPending
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · exact ⟨cp, rp, cl, rl, by dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem tab {v : Vt} (h : Good v) : Good v.tab := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.tab Vt.clearPending
  exact ⟨cp, rp, cl, rl, by dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem backTab {v : Vt} (h : Good v) : Good v.backTab := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.backTab
  exact ⟨cp, rp, cl, rl, by dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ## Scrolling — grid + ring only; the cursor is untouched -/

theorem ring_push_le {r : Ring} (row : Row) (h : r.size ≤ sbCap) :
    (r.push row).size ≤ sbCap := by
  unfold Ring.size at h ⊢
  unfold Ring.push
  split
  · simp only [Array.size_push]
    omega
  · simpa [Array.size_setIfInBounds] using h

theorem scrollUpIn {v : Vt} (t b : Nat) (allowSb : Bool) (h : Good v) :
    Good (v.scrollUpIn t b allowSb) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.scrollUpIn
  dsimp only
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl,
      ring_push_le _ sb, u8, hcsi, hosc⟩
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem scrollDownIn {v : Vt} (t b : Nat) (h : Good v) :
    Good (v.scrollDownIn t b) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem scrollUp {v : Vt} (h : Good v) : Good v.scrollUp := scrollUpIn _ _ _ h

theorem scrollDown {v : Vt} (h : Good v) : Good v.scrollDown := scrollDownIn _ _ h

theorem lineFeed {v : Vt} (h : Good v) : Good v.lineFeed := by
  have h' := clearPending h
  unfold Vt.lineFeed
  dsimp only
  split
  · exact scrollUp h'
  · split
    · obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h'
      exact ⟨cp, rp, cl, rl, cx, by dsimp only; omega, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
    · exact h'

theorem reverseIndex {v : Vt} (h : Good v) : Good v.reverseIndex := by
  have h' := clearPending h
  unfold Vt.reverseIndex
  dsimp only
  split
  · exact scrollDown h'
  · obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h'
    exact ⟨cp, rp, cl, rl, cx, by dsimp only; omega, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem setCol {v : Vt} (x : Nat) (h : Good v) : Good (v.setCol x) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, by dsimp only [Vt.setCol]; omega, cy,
    sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ## Folded repetitions -/

theorem good_foldl {α : Type} {f : Vt → α → Vt}
    (hf : ∀ v a, Good v → Good (f v a)) :
    ∀ (l : List α) {v : Vt}, Good v → Good (l.foldl f v)
  | [], _, h => h
  | a :: l, v, h => by
    rw [List.foldl_cons]
    exact good_foldl hf l (hf v a h)

/-! ## Erase / insert / delete — grid-only (plus ED 3's scrollback reset) -/

theorem eraseRowSpan {v : Vt} (y a b : Nat) (h : Good v) : Good (v.eraseRowSpan y a b) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem eraseLine {v : Vt} (m : Nat) (h : Good v) : Good (v.eraseLine m) := by
  unfold Vt.eraseLine
  split <;> exact eraseRowSpan _ _ _ h

theorem eraseScreen {v : Vt} (m : Nat) (h : Good v) : Good (v.eraseScreen m) := by
  unfold Vt.eraseScreen
  split
  · exact good_foldl (fun v' i hh => eraseRowSpan _ _ _ hh) _ (eraseLine _ h)
  · exact good_foldl (fun v' y hh => eraseRowSpan _ _ _ hh) _ (eraseLine _ h)
  · -- ED 3: also drops scrollback; an empty ring is within any cap
    have h' : Good ((List.range v.rows).foldl
        (fun v' y => v'.eraseRowSpan y 0 v'.cols) v) :=
      good_foldl (fun v' y hh => eraseRowSpan _ _ _ hh) _ h
    obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, -, u8, hcsi, hosc⟩ := h'
    exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl,
      by simp [Ring.size], u8, hcsi, hosc⟩
  · exact good_foldl (fun v' y hh => eraseRowSpan _ _ _ hh) _ h

theorem insertLines {v : Vt} (n : Nat) (h : Good v) : Good (v.insertLines n) := by
  unfold Vt.insertLines
  split
  · exact h
  · exact good_foldl (fun v a hh => scrollDownIn _ _ hh) _ h

theorem deleteLines {v : Vt} (n : Nat) (h : Good v) : Good (v.deleteLines n) := by
  unfold Vt.deleteLines
  split
  · exact h
  · exact good_foldl (fun v a hh => scrollUpIn _ _ _ hh) _ h

theorem deleteChars {v : Vt} (n : Nat) (h : Good v) : Good (v.deleteChars n) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem insertChars {v : Vt} (n : Nat) (h : Good v) : Good (v.insertChars n) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem eraseChars {v : Vt} (n : Nat) (h : Good v) : Good (v.eraseChars n) :=
  eraseRowSpan _ _ _ h

theorem applySgr {v : Vt} (ps : List (Nat × Bool)) (h : Good v) : Good (v.applySgr ps) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ## Alt screen -/

theorem enterAlt {v : Vt} (saveCursor : Bool) (h : Good v) : Good (v.enterAlt saveCursor) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.enterAlt
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · refine ⟨cp, rp, cl, rl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sb, u8, hcsi, hosc⟩
    · dsimp only; omega
    · dsimp only; omega
    · dsimp only
      split
      · exact cx
      · exact sx
    · dsimp only
      split
      · exact cy
      · exact sy
    · intro g c p heq
      simp only [Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨-, hc, -⟩ := heq
      subst hc
      exact ⟨cx, cy⟩
    · dsimp only; omega
    · dsimp only; omega

theorem leaveAlt {v : Vt} (restoreCursor : Bool) (h : Good v) :
    Good (v.leaveAlt restoreCursor) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.leaveAlt
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · rename_i g cur pen heq
    obtain ⟨hax, hay⟩ := ac g cur pen heq
    refine ⟨cp, rp, cl, rl, ?_, ?_, sx, sy, (fun _ _ _ hh => nomatch hh), ?_, ?_,
      sb, u8, hcsi, hosc⟩
    · dsimp only
      split
      · exact hax
      · exact cx
    · dsimp only
      split
      · exact hay
      · exact cy
    · dsimp only; omega
    · dsimp only; omega

/-! ## Mode switching -/


theorem setMode {v : Vt} (priv : Bool) (n : Nat) (on : Bool) (h : Good v) :
    Good (v.setMode priv n on) := by
  unfold Vt.setMode
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  split <;> split
  all_goals first
    | exact h'
    | exact set_modes _ h'
    | exact moveTo 0 0 (set_modes _ h')
    | (split <;> first
        | exact enterAlt _ h'
        | exact leaveAlt _ h'
        | exact ⟨cp, rp, cl, rl, cx, cy, cx, cy, ac, tl, bl, sb, u8, hcsi, hosc⟩
        | exact ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩)

/-! ## CSI dispatch -/

theorem csiDispatch {v : Vt} (s : CsiState) (final : UInt8) (h : Good v) :
    Good (v.csiDispatch s final) := by
  unfold Vt.csiDispatch
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  split
  · exact h'
  · split
    all_goals first
      | exact h'
      | exact insertChars _ h'
      | exact moveRel _ _ h'
      | exact carriageReturn (moveRel _ _ h')
      | exact setCol _ h'
      | exact moveTo _ _ h'
      | exact eraseScreen _ h'
      | exact eraseLine _ h'
      | exact insertLines _ h'
      | exact deleteLines _ h'
      | exact deleteChars _ h'
      | exact eraseChars _ h'
      | exact setMode _ _ _ h'
      | exact good_foldl (fun v' i hh => tab hh) _ h'
      | exact good_foldl (fun v' i hh => scrollUp hh) _ h'
      | exact good_foldl (fun v' i hh => scrollDown hh) _ h'
      | exact good_foldl (fun v' i hh => backTab hh) _ h'
      | exact ⟨cp, rp, cl, rl, cx, by dsimp only; omega, sx, sy, ac, tl, bl,
          sb, u8, hcsi, hosc⟩
      | exact ⟨cp, rp, cl, rl, cx, cy, cx, cy, ac, tl, bl, sb, u8, hcsi, hosc⟩
      | exact ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
      | (split <;> first
          | exact applySgr _ h'
          | exact set_tabs _ h'
          | exact h'
          | exact ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
          | (dsimp only
             split <;> first
              | exact h'
              | (rename_i hg
                 simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                 refine moveTo 0 0
                   ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, ?_, ?_, sb, u8, hcsi, hosc⟩ <;>
                   (dsimp only; omega))))


/-- Private final-`u` sequences (notably kitty's `CSI ? u` query) are
state-neutral; only public ANSI `CSI u` is DECRC. -/
theorem csiDispatch_private_u (v : Vt) (s : CsiState)
    (hi : s.ignore = false) (hp : s.priv ≠ 0) :
    v.csiDispatch s 0x75 = v := by
  simp [Vt.csiDispatch, hi, hp]

/-- Public ANSI `CSI u` still restores the saved cursor and pen. -/
theorem csiDispatch_public_u (v : Vt) (s : CsiState)
    (hi : s.ignore = false) (hp : s.priv = 0) :
    v.csiDispatch s 0x75 = { v with cursor := v.saved.cur, pen := v.saved.pen } := by
  simp [Vt.csiDispatch, hi, hp]

/-! ## Printing -/

theorem putCell {v : Vt} (x y : Nat) (c : Cell) (h : Good v) : Good (v.putCell x y c) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

/-! ### Wide-pair repair

`mendAt` and `mendRow` are grid-only record updates, so `Good` passes
straight through them. Stated as their own lemmas rather than left to `split`:
their guards read cells through `getD` chains, and letting a proof descend into
those is what made `Good.printPut` time out at `whnf`. -/

theorem mendAt {v : Vt} (x y : Nat) (h : Good v) : Good (v.mendAt x y) := set_grid _ h

theorem mendRow {v : Vt} (y : Nat) (h : Good v) : Good (v.mendRow y) := set_grid _ h

theorem printWrap {v : Vt} (h : Good v) : Good v.printWrap := by
  unfold Vt.printWrap
  split
  · exact lineFeed (carriageReturn h)
  · exact clearPending h

theorem printWideWrap {v : Vt} (w : Nat) (h : Good v) : Good (v.printWideWrap w) := by
  unfold Vt.printWideWrap
  split
  · exact lineFeed (carriageReturn h)
  · exact h

theorem printShift {v : Vt} (w : Nat) (h : Good v) : Good (v.printShift w) := by
  unfold Vt.printShift
  split
  · exact set_grid _ h
  · exact h

theorem printPut {v : Vt} (ch : Char) (w : Nat) (h : Good v) : Good (v.printPut ch w) := by
  unfold Vt.printPut
  dsimp only
  split
  · exact mendRow _ (putCell _ _ _ h)
  · split
    · exact mendRow _ (putCell _ _ _ (putCell _ _ _ h))
    · exact mendRow _ (putCell _ _ _ h)

theorem printAdvance {v : Vt} (w : Nat) (h : Good v) : Good (v.printAdvance w) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.printAdvance
  dsimp only
  split
  · exact ⟨cp, rp, cl, rl, by dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · exact ⟨cp, rp, cl, rl, by dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem printMark {v : Vt} (ch : Char) (h : Good v) : Good (v.printMark ch) := by
  unfold Vt.printMark
  dsimp only
  repeat' split
  all_goals first
    | exact h
    | exact mendRow _ (putCell _ _ _ h)

theorem print {v : Vt} (ch : Char) (h : Good v) : Good (v.print ch) := by
  unfold Vt.print
  dsimp only
  split
  · exact printMark _ h
  · exact printAdvance _ (printPut _ _ (printShift _ (printWideWrap _ (printWrap h))))

theorem acceptChar {v : Vt} (n : Nat) (h : Good v) : Good (v.acceptChar n) := by
  unfold Vt.acceptChar
  split
  · exact print _ h
  · exact print _ h

/-! ## Control bytes and parser transitions -/

theorem ctl {v : Vt} (b : UInt8) (h : Good v) : Good (v.ctl b) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  unfold Vt.ctl
  split
  all_goals first
    | exact h'
    | exact backspace h'
    | exact tab h'
    | exact lineFeed h'
    | exact carriageReturn h'
    | exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem oscFinish {v : Vt} (acc : Array UInt8) (h : Good v) : Good (v.oscFinish acc) := by
  unfold Vt.oscFinish
  dsimp only
  have hg := set_ground h
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := hg
  split
  · split
    · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
    · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem csiFinish {v : Vt} (s : CsiState) (final : UInt8) (h : Good v) :
    Good (v.csiFinish s final) := by
  unfold Vt.csiFinish
  exact set_ground (csiDispatch _ _ h)

/-! ## Parser-state setters within their §Bound caps -/

theorem set_pstate_csi {v : Vt} (s : CsiState)
    (hp : s.params.size ≤ 16) (h : Good v) :
    Good { v with pstate := .csi s } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  refine ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, ?_, ?_⟩
  · intro s' heq
    simp only [PState.csi.injEq] at heq
    subst heq
    exact hp
  · intro _ _ heq
    exact nomatch heq

theorem set_pstate_osc {v : Vt} (acc : Array UInt8) (e : Bool)
    (hacc : acc.size ≤ 2048) (h : Good v) :
    Good { v with pstate := .osc acc e } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  refine ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, ?_, ?_⟩
  · intro _ heq
    exact nomatch heq
  · intro acc' e' heq
    simp only [PState.osc.injEq] at heq
    obtain ⟨h1, -⟩ := heq
    subst h1
    exact hacc

theorem set_pstate_esc {v : Vt} (h : Good v) : Good { v with pstate := .esc } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8,
    (fun _ heq => nomatch heq), (fun _ _ heq => nomatch heq)⟩

theorem set_pstate_escInter {v : Vt} (b : UInt8) (h : Good v) :
    Good { v with pstate := .escInter b } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8,
    (fun _ heq => nomatch heq), (fun _ _ heq => nomatch heq)⟩

theorem set_pstate_str {v : Vt} (e : Bool) (h : Good v) :
    Good { v with pstate := .str e } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, -, -⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8,
    (fun _ heq => nomatch heq), (fun _ _ heq => nomatch heq)⟩

theorem csiPush_le (s : CsiState) (sub : Bool)
    (hp : s.params.size ≤ 16) :
    (csiPush s sub).params.size ≤ 16 := by
  unfold csiPush
  split
  · split
    · exact hp
    · rename_i hlt
      simp only [Array.size_push]
      omega
  · exact hp


theorem set_u8 {v : Vt} (n a : Nat) (hn : n ≤ 3) (h : Good v) :
    Good { v with u8need := n, u8acc := a } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, -, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, hn, hcsi, hosc⟩

theorem set_sb {v : Vt} (r : Ring) (hr : r.size ≤ sbCap) (h : Good v) :
    Good { v with sb := r } := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, -, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, hr, u8, hcsi, hosc⟩

/-! ## Per-parser-state steps -/

set_option maxRecDepth 4096 in
theorem stepGround {v : Vt} (b : UInt8) (h : Good v) : Good (v.stepGround b) := by
  unfold Vt.stepGround
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  repeat' split
  all_goals first
    | exact set_pstate_esc h'
    | exact ctl _ h'
    | exact acceptChar _ h'
    | exact acceptChar _ (set_u8 0 0 (by omega) h')
    | exact set_u8 (v.u8need - 1) _ (by omega) h'
    | exact set_u8 1 _ (by omega) h'
    | exact set_u8 2 _ (by omega) h'
    | exact set_u8 3 _ (by omega) h'
    | exact h'

theorem stepEsc {v : Vt} (b : UInt8) (h : Good v) : Good (v.stepEsc b) := by
  unfold Vt.stepEsc
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  have h' : Good v := ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  split
  all_goals first
    | exact h'
    | exact set_pstate_csi {} (by simp) h'
    | exact set_pstate_osc #[] false (by simp) h'
    | exact set_pstate_str _ h'
    | exact set_pstate_escInter _ h'
    | exact set_ground h'
    | exact set_ground (lineFeed h')
    | exact set_ground (lineFeed (carriageReturn h'))
    | exact set_ground (reverseIndex h')
    | -- DECSC: save cursor + ground
      exact ⟨cp, rp, cl, rl, cx, cy, cx, cy, ac, tl, bl, sb, u8,
        (fun _ heq => nomatch heq), (fun _ _ heq => nomatch heq)⟩
    | -- DECRC: restore cursor + ground
      exact ⟨cp, rp, cl, rl, sx, sy, sx, sy, ac, tl, bl, sb, u8,
        (fun _ heq => nomatch heq), (fun _ _ heq => nomatch heq)⟩
    | -- HTS: tabs + ground
      exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8,
        (fun _ heq => nomatch heq), (fun _ _ heq => nomatch heq)⟩
    | -- RIS: fresh screen, scrollback conditionally carried
      (dsimp only
       split
       · exact set_sb _ sb (good_init v.cols v.rows)
       · exact set_sb _ (by simp [Ring.size]) (good_init v.cols v.rows))
    | (split
       · exact set_pstate_escInter _ h'
       · exact set_ground h')

theorem stepEscInter {v : Vt} (i b : UInt8) (h : Good v) : Good (v.stepEscInter i b) := by
  unfold Vt.stepEscInter
  have hg := set_ground h
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := hg
  dsimp only
  split
  · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · split
    · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
    · exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem stepCsi {v : Vt} (s : CsiState) (b : UInt8)
    (hs : s.params.size ≤ 16) (h : Good v) : Good (v.stepCsi s b) := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | exact set_pstate_csi _ hs h
    | exact set_pstate_csi _ (csiPush_le s _ hs) h
    | exact csiFinish _ _ h
    | exact set_pstate_esc h
    | exact ctl _ h
    | exact set_ground h

theorem stepOsc {v : Vt} (acc : Array UInt8) (e : Bool) (b : UInt8)
    (hacc : acc.size ≤ 2048) (h : Good v) : Good (v.stepOsc acc e b) := by
  unfold Vt.stepOsc
  split
  · exact oscFinish _ h
  · split
    · exact oscFinish _ h
    · split
      · exact set_pstate_osc _ _ hacc h
      · split
        · exact set_pstate_osc _ _ hacc h
        · rename_i hlt
          refine set_pstate_osc _ _ ?_ h
          simp only [Array.size_push]
          omega

theorem stepStr {v : Vt} (e : Bool) (b : UInt8) (h : Good v) : Good (v.stepStr e b) := by
  unfold Vt.stepStr
  split
  · exact set_ground h
  · split
    · exact set_pstate_str _ h
    · exact set_pstate_str _ h

/-! ## §Total + §Bound, one byte and a whole stream -/

/-- `step` preserves the composite invariant for ANY byte: the cursor
and every stashed cursor stay in bounds, and no buffer exceeds its cap.
This is the anti-zellij theorem at the emulator layer. -/
theorem step {v : Vt} (b : UInt8) (h : Good v) : Good (v.step b) := by
  unfold Vt.step Vt.abortUtf8
  dsimp only
  by_cases hc : (v.u8need > 0 && (b < 0x80 || b ≥ 0xC0)) = true
  · rw [if_pos hc]
    have h' := set_u8 0 0 (by omega) h
    split
    all_goals first
      | exact stepGround _ h'
      | exact stepEsc _ h'
      | exact stepEscInter _ _ h'
      | (rename_i heq; exact stepCsi _ _ (h'.csiLe _ heq) h')
      | (rename_i heq; exact stepOsc _ _ _ (h'.oscLe _ _ heq) h')
      | exact stepStr _ _ h'
  · rw [if_neg hc]
    split
    all_goals first
      | exact stepGround _ h
      | exact stepEsc _ h
      | exact stepEscInter _ _ h
      | (rename_i heq; exact stepCsi _ _ (h.csiLe _ heq) h)
      | (rename_i heq; exact stepOsc _ _ _ (h.oscLe _ _ heq) h)
      | exact stepStr _ _ h

/-- The stream form: any byte stream, fed to a Good `Vt`, leaves it
Good. With `Vt.init`'s `good_init` this covers every state the daemon
can ever hold. -/
theorem feed {v : Vt} (bytes : List UInt8) (h : Good v) : Good (v.feed bytes) :=
  good_foldl (fun _ b hh => step b hh) bytes h

/-- Resize lands Good regardless of requested dimensions. -/
theorem resize {v : Vt} (cols rows : Nat) (h : Good v) : Good (v.resize cols rows) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.resize
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, sb, u8, hcsi, hosc⟩
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · intro g c p heq
    simp only at heq
    rcases hv : v.altGrid with - | x
    · rw [hv] at heq
      exact nomatch heq
    · obtain ⟨g0, c0, p0⟩ := x
      rw [hv] at heq
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      obtain ⟨-, hcc, -⟩ := heq
      subst hcc
      constructor
      · simp [clampDim] <;> omega
      · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega
  · simp [clampDim] <;> omega

/-! ## §Chunk — re-chunking invariance, definitional by design -/

/-- Feeding `a ++ b` is feeding `a` then `b`. `Vt.feed` is a `foldl`,
so this is `List.foldl_append` — stated so a future rewrite of `feed`
into something chunk-sensitive cannot survive the build. -/
theorem feed_append (v : Vt) (a b : List UInt8) :
    v.feed (a ++ b) = (v.feed a).feed b := by
  simp [Vt.feed]

/-- Byte-at-a-time equals one-shot: the strongest §Chunk corollary
(any chunking refines to single bytes). -/
theorem feed_singletons (v : Vt) (bytes : List UInt8) :
    v.feed bytes = bytes.foldl (fun acc b => acc.feed [b]) v := by
  induction bytes generalizing v with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ← ih]
    rfl

end Zmx.Core.Vt.Good



namespace Zmx.Core.Vt
/-! ## Frames: the generalization of the four invariance layers

`pstate`, `u8need`, `dims` and `origin` above are ~110 lemmas that are
~28 written four times: "operation X does not write field F". The general
statement is a **frame condition** — X's footprint, stated once, covering
every field at once:

```
theorem frame_putCell : v.putCell x y c = { v with grid := (v.putCell x y c).grid }
```

Read: *`putCell` writes only `grid`*. Every field invariance is then a
corollary by rewriting, including fields nobody has thought of yet — so a
fifth layer costs nothing instead of another 28 lemmas.

Why this beats the two ideas recorded in THEOREMS.md:

* Better than *bundling* the four fields, which fixes only the fields we
  happened to need.
* Better than *splitting* `Vt` into `{screen, parser, meta}`, because the
  read/write distinction is **per-operation**: `print` reads `cols`/`rows`
  to clamp and reads `modes` for wrap/insert while writing neither, so a
  partition that groups `dims` with the cells still lets `Screen → Screen`
  resize the grid. The refactor that *would* capture it moves read-only
  data into parameter position (`print : Dims → Modes → … `), which is far
  larger and mostly subsumed by frames anyway.

What frames do **not** buy, and this is the honest limit: a frame says
what an operation leaves alone, never what the written fields *become*.
Grid fidelity (§Replay stage 3d — the replayed cells equal the saved
cells) needs the positive specification, which is real content, not
bookkeeping. Frames retire the sprawl; they do not shorten the road to
3d.

Below: the pattern demonstrated on four operations of increasing shape,
with the four existing layers re-derived from one of them to show the
collapse is real. The conversion of the leaf operations is **done** (step 4
of specs/archive/bigger-theorems.md): 30 frames, 28 collapsed layer
proofs. What stays per-field is `print`, `csiDispatch` and the fold-based
operations — precisely the part that was never mechanical, and where the
conditional cases (`RIS`, `setMode`) live.
-/

/-- Pure record update: `rfl` suffices. -/
theorem frame_putCell (v : Vt) (x y : Nat) (c : Cell) :
    v.putCell x y c = { v with grid := (v.putCell x y c).grid } := rfl

theorem frame_moveTo (v : Vt) (x y : Nat) :
    v.moveTo x y = { v with cursor := (v.moveTo x y).cursor } := rfl

theorem frame_eraseRowSpan (v : Vt) (y a b : Nat) :
    v.eraseRowSpan y a b = { v with grid := (v.eraseRowSpan y a b).grid } := rfl

/-- Branching operation: one `split`, both branches record updates.
`scrollUpIn` may also push the evicted line to scrollback. -/
theorem frame_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    v.scrollUpIn t b a
      = { v with grid := (v.scrollUpIn t b a).grid, sb := (v.scrollUpIn t b a).sb } := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

/-- Composite over stages: `lineFeed` moves the cursor and may scroll. -/
theorem frame_lineFeed (v : Vt) :
    v.lineFeed = { v with grid := v.lineFeed.grid, cursor := v.lineFeed.cursor,
                          sb := v.lineFeed.sb } := by
  unfold Vt.lineFeed Vt.scrollUp Vt.scrollUpIn Vt.clearPending
  dsimp only
  repeat' split
  all_goals rfl

/-! ### The collapse, demonstrated

Each of these four is an instance of the layers above — and each is now a
one-line consequence of a single frame, for *any* field rather than a
chosen one. -/

example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).pstate = v.pstate := by
  rw [frame_scrollUpIn]

example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).u8need = v.u8need := by
  rw [frame_scrollUpIn]

example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).cols = v.cols := by
  rw [frame_scrollUpIn]

example (v : Vt) (t b : Nat) (a : Bool) :
    (v.scrollUpIn t b a).modes.origin = v.modes.origin := by
  rw [frame_scrollUpIn]

/-- …and a field no layer ever covered, free: the scroll region. -/
example (v : Vt) (t b : Nat) (a : Bool) : (v.scrollUpIn t b a).top = v.top := by
  rw [frame_scrollUpIn]

/-- …and the saved-cursor slot, also free. -/
example (v : Vt) : v.lineFeed.saved = v.saved := by
  rw [frame_lineFeed]

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! ### The frame set for the leaf operations

One frame per operation, replacing what was four single-field lemmas
each. Every field invariance — including fields no layer covers — is one
`rw` away, so a new field costs nothing here.

Not covered, by measurement rather than omission: `print`,
`csiDispatch`, and the fold-based operations (`eraseScreen`,
`insertLines`, `deleteLines`). A frame proves by `rfl` only when the
result is a *syntactic* record update; a composed chain times out and a
`List.foldl` is not an update at all. Those keep their per-field lemmas
(see THEOREMS.md).
-/

theorem frame_clearPending (v : Vt) :
    v.clearPending = { v with cursor := v.clearPending.cursor } := rfl

theorem frame_carriageReturn (v : Vt) :
    v.carriageReturn = { v with cursor := v.carriageReturn.cursor } := rfl

theorem frame_moveRel (v : Vt) (dx dy : Int) :
    v.moveRel dx dy = { v with cursor := (v.moveRel dx dy).cursor } := rfl

theorem frame_setCol (v : Vt) (x : Nat) :
    v.setCol x = { v with cursor := (v.setCol x).cursor } := rfl

theorem frame_scrollDownIn (v : Vt) (t b : Nat) :
    v.scrollDownIn t b = { v with grid := (v.scrollDownIn t b).grid } := rfl

theorem frame_deleteChars (v : Vt) (n : Nat) :
    v.deleteChars n = { v with grid := (v.deleteChars n).grid } := rfl

theorem frame_insertChars (v : Vt) (n : Nat) :
    v.insertChars n = { v with grid := (v.insertChars n).grid } := rfl

theorem frame_applySgr (v : Vt) (ps : List (Nat × Bool)) :
    v.applySgr ps = { v with pen := (v.applySgr ps).pen } := rfl

theorem frame_backTab (v : Vt) : v.backTab = { v with cursor := v.backTab.cursor } := rfl

theorem frame_eraseChars (v : Vt) (n : Nat) :
    v.eraseChars n = { v with grid := (v.eraseChars n).grid } := rfl

theorem frame_backspace (v : Vt) :
    v.backspace = { v with cursor := v.backspace.cursor } := by
  unfold Vt.backspace; split <;> rfl

theorem frame_tab (v : Vt) : v.tab = { v with cursor := v.tab.cursor } := by
  unfold Vt.tab Vt.clearPending; dsimp only

theorem frame_eraseLine (v : Vt) (m : Nat) :
    v.eraseLine m = { v with grid := (v.eraseLine m).grid } := by
  unfold Vt.eraseLine; repeat' split
  all_goals rfl

theorem frame_reverseIndex (v : Vt) :
    v.reverseIndex = { v with grid := v.reverseIndex.grid,
                              cursor := v.reverseIndex.cursor } := by
  unfold Vt.reverseIndex Vt.scrollDown Vt.scrollDownIn Vt.clearPending
  dsimp only
  repeat' split
  all_goals rfl

theorem frame_printWrap (v : Vt) :
    v.printWrap = { v with grid := v.printWrap.grid, cursor := v.printWrap.cursor,
                           sb := v.printWrap.sb } := by
  unfold Vt.printWrap Vt.carriageReturn Vt.lineFeed Vt.clearPending Vt.scrollUp
    Vt.scrollUpIn
  dsimp only
  repeat' split
  all_goals rfl

theorem frame_printWideWrap (v : Vt) (w : Nat) :
    v.printWideWrap w = { v with grid := (v.printWideWrap w).grid,
                                 cursor := (v.printWideWrap w).cursor,
                                 sb := (v.printWideWrap w).sb } := by
  unfold Vt.printWideWrap Vt.carriageReturn Vt.lineFeed Vt.clearPending Vt.scrollUp
    Vt.scrollUpIn
  dsimp only
  repeat' split
  all_goals rfl

theorem frame_printShift (v : Vt) (w : Nat) :
    v.printShift w = { v with grid := (v.printShift w).grid } := by
  unfold Vt.printShift; dsimp only; split <;> rfl

/-- Wide-pair repair writes only the grid. One frame covers all four layers
below, plus any field a later one adds. -/
theorem frame_mendAt (v : Vt) (x y : Nat) :
    v.mendAt x y = { v with grid := (v.mendAt x y).grid } := rfl

theorem frame_mendRow (v : Vt) (y : Nat) :
    v.mendRow y = { v with grid := (v.mendRow y).grid } := rfl

theorem frame_printPut (v : Vt) (ch : Char) (w : Nat) :
    v.printPut ch w = { v with grid := (v.printPut ch w).grid } := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [frame_mendRow]; rfl)

theorem frame_printMark (v : Vt) (ch : Char) :
    v.printMark ch = { v with grid := (v.printMark ch).grid } := by
  unfold Vt.printMark
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | (rw [frame_mendRow]; rfl)

theorem frame_printAdvance (v : Vt) (w : Nat) :
    v.printAdvance w = { v with cursor := (v.printAdvance w).cursor } := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem frame_enterAlt (v : Vt) (s : Bool) :
    v.enterAlt s = { v with grid := (v.enterAlt s).grid,
                            cursor := (v.enterAlt s).cursor,
                            saved := (v.enterAlt s).saved,
                            altGrid := (v.enterAlt s).altGrid,
                            top := (v.enterAlt s).top, bot := (v.enterAlt s).bot } := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem frame_leaveAlt (v : Vt) (s : Bool) :
    v.leaveAlt s = { v with grid := (v.leaveAlt s).grid,
                            cursor := (v.leaveAlt s).cursor,
                            pen := (v.leaveAlt s).pen,
                            altGrid := (v.leaveAlt s).altGrid,
                            top := (v.leaveAlt s).top, bot := (v.leaveAlt s).bot } := by
  unfold Vt.leaveAlt; split <;> rfl

theorem frame_stepEscInter (v : Vt) (i b : UInt8) :
    v.stepEscInter i b = { v with pstate := (v.stepEscInter i b).pstate,
                                  g0Line := (v.stepEscInter i b).g0Line,
                                  g1Line := (v.stepEscInter i b).g1Line } := by
  unfold Vt.stepEscInter; dsimp only; repeat' split
  all_goals rfl

theorem frame_stepStr (v : Vt) (e : Bool) (b : UInt8) :
    v.stepStr e b = { v with pstate := (v.stepStr e b).pstate } := by
  unfold Vt.stepStr; repeat' split
  all_goals rfl

theorem frame_oscFinish (v : Vt) (acc : Array UInt8) :
    v.oscFinish acc = { v with pstate := (v.oscFinish acc).pstate,
                               title := (v.oscFinish acc).title } := by
  unfold Vt.oscFinish; dsimp only; repeat' split
  all_goals rfl

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! ## Parser-state invariance of the printing path

Feeding a *printable* byte must not disturb the parser: only ESC (and
the sequence states it opens) may change `pstate`. That is obvious by
inspection of the code — no printing or cursor operation mentions
`pstate` — but "obvious by inspection" is what these lemmas replace.

They are the missing rung under §Replay stage 3b
(`Theorems/Render.lean`): a restore stream's grid repaint is a long run
of printable bytes, and the theorem that a restore leaves the parser
quiesced needs each of them to be parser-neutral.

Cheap because they are staged: every operation is a record update that
leaves `pstate` untouched, so each proof is `rfl` under enough `split`s.
(This also closes, for `pstate`, the same gap the step-4 notes recorded
as open for `cols`/`rows` — the shape of proof is identical, ~15 small
lemmas, and it turned out to be worth writing after all.)
-/

theorem ps_clearPending (v : Vt) : v.clearPending.pstate = v.pstate := rfl
theorem ps_carriageReturn (v : Vt) : v.carriageReturn.pstate = v.pstate := rfl
theorem ps_putCell (v : Vt) (x y : Nat) (c : Cell) :
    (v.putCell x y c).pstate = v.pstate := rfl
theorem ps_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).pstate = v.pstate := rfl
theorem ps_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).pstate = v.pstate := rfl
theorem ps_setCol (v : Vt) (x : Nat) : (v.setCol x).pstate = v.pstate := rfl
theorem ps_scrollDownIn (v : Vt) (t b : Nat) : (v.scrollDownIn t b).pstate = v.pstate := rfl
theorem ps_eraseRowSpan (v : Vt) (y a b : Nat) :
    (v.eraseRowSpan y a b).pstate = v.pstate := rfl

theorem ps_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    (v.scrollUpIn t b a).pstate = v.pstate := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem ps_scrollUp (v : Vt) : v.scrollUp.pstate = v.pstate := ps_scrollUpIn _ _ _ _

theorem ps_scrollDown (v : Vt) : v.scrollDown.pstate = v.pstate := ps_scrollDownIn _ _ _

theorem ps_lineFeed (v : Vt) : v.lineFeed.pstate = v.pstate := by
  rw [frame_lineFeed]

theorem ps_reverseIndex (v : Vt) : v.reverseIndex.pstate = v.pstate := by
  rw [frame_reverseIndex]

theorem ps_backspace (v : Vt) : v.backspace.pstate = v.pstate := by
  unfold Vt.backspace; split <;> rfl

theorem ps_tab (v : Vt) : v.tab.pstate = v.pstate := by
  unfold Vt.tab; dsimp only; exact ps_clearPending v

theorem ps_printWrap (v : Vt) : v.printWrap.pstate = v.pstate := by
  rw [frame_printWrap]

theorem ps_printWideWrap (v : Vt) (w : Nat) : (v.printWideWrap w).pstate = v.pstate := by
  rw [frame_printWideWrap]

theorem ps_printShift (v : Vt) (w : Nat) : (v.printShift w).pstate = v.pstate := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem ps_mendRow (v : Vt) (y : Nat) :
    (v.mendRow y).pstate = v.pstate := by
  rw [frame_mendRow]

theorem ps_printPut (v : Vt) (ch : Char) (w : Nat) :
    (v.printPut ch w).pstate = v.pstate := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [ps_mendRow]; rfl)

theorem ps_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).pstate = v.pstate := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

/-- The composite: printing a glyph never touches the parser. -/
theorem ps_printMark (v : Vt) (ch : Char) : (v.printMark ch).pstate = v.pstate := by
  rw [frame_printMark]

theorem ps_print (v : Vt) (c : Char) : (v.print c).pstate = v.pstate := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | rw [ps_printMark]
    | rw [ps_printAdvance, ps_printPut, ps_printShift, ps_printWideWrap, ps_printWrap]

theorem ps_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).pstate = v.pstate := by
  unfold Vt.acceptChar; split <;> exact ps_print _ _

/-- Printing never touches the UTF-8 decoder's accumulator — it writes the
grid, the cursor and (on scroll) the scrollback, which is exactly what the
frames say. This is what lets a whole run of glyphs be fed without
re-establishing the decoder's precondition between them, and it is proved by
*peeling* the frames one stage at a time: as a single `rfl` over the composite
it times out at `whnf` (see SCRATCHPAD). The `u8need` twin is `un_print`,
further down with the rest of that layer. -/
theorem ua_print (v : Vt) (c : Char) : (v.print c).u8acc = v.u8acc := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | rw [frame_printMark]
    | rw [frame_putCell]
    | rw [frame_printAdvance, frame_printPut, frame_printShift, frame_printWideWrap,
          frame_printWrap]

theorem ua_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).u8acc = v.u8acc := by
  unfold Vt.acceptChar; split <;> exact ua_print _ _

/-- A C0 control byte executes without changing the parser state. -/
theorem ps_ctl (v : Vt) (b : UInt8) : (v.ctl b).pstate = v.pstate := by
  unfold Vt.ctl
  repeat' split
  all_goals first
    | exact ps_backspace v
    | exact ps_tab v
    | exact ps_lineFeed v
    | exact ps_carriageReturn v
    | rfl

theorem ps_abortUtf8 (v : Vt) (b : UInt8) : (v.abortUtf8 b).pstate = v.pstate := by
  unfold Vt.abortUtf8; split <;> rfl

/-- §Replay's rung: from `ground`, any byte other than ESC leaves the
parser in `ground`. (`u8need` may change — a UTF-8 lead byte — which is
why `Ends` tracks it separately.) -/
theorem ps_stepGround (v : Vt) (b : UInt8) (hb : b ≠ 0x1B) :
    (v.stepGround b).pstate = v.pstate := by
  have hesc : (b == 0x1B) = false := beq_eq_false_iff_ne.mpr hb
  unfold Vt.stepGround
  simp only [hesc, Bool.false_eq_true, if_false]
  repeat' split
  -- rewriting with the stage lemmas is *guided* (matches only the right
  -- shape); a blind `exact` on the wrong branch whnf's the print chain
  all_goals try simp only [ps_ctl, ps_acceptChar]
  all_goals rfl

end Zmx.Core.Vt





namespace Zmx.Core.Vt
/-! ## No half-decoded character (`u8need`) survives an operation

The companion of the `pstate` layer above. Same staged shape, same
reason: §Replay needs to know that a restore stream leaves the emulator
holding no partial UTF-8 sequence, so a checkpoint taken right after a
reattach is exact and the next byte from the application is read as
itself.

Stated as *preservation* equations (`… .u8need = v.u8need`) rather than
as implications, so they can be used as guided `simp` rewrites — an
`exact` against the wrong branch whnf's the print chain to death.
`stepEsc` is the one exception: its `RIS` branch rebuilds through
`Vt.init`, where `u8need` is zero by construction, so that one is stated
in "stays zero" form.
-/

/-- A fold of `u8need`-preserving steps preserves it. One lemma for every
`List.range` fold in the erase/scroll/insert operations. -/
theorem un_foldl {α : Type} (f : Vt → α → Vt)
    (hf : ∀ v a, (f v a).u8need = v.u8need) :
    ∀ (l : List α) (v : Vt), (l.foldl f v).u8need = v.u8need
  | [], _ => rfl
  | a :: as, v => (un_foldl f hf as (f v a)).trans (hf v a)

theorem un_clearPending (v : Vt) : v.clearPending.u8need = v.u8need := rfl
theorem un_carriageReturn (v : Vt) : v.carriageReturn.u8need = v.u8need := rfl
theorem un_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).u8need = v.u8need := rfl
theorem un_moveRel (v : Vt) (dx dy : Int) : (v.moveRel dx dy).u8need = v.u8need := rfl
theorem un_setCol (v : Vt) (x : Nat) : (v.setCol x).u8need = v.u8need := rfl
theorem un_putCell (v : Vt) (x y : Nat) (c : Cell) :
    (v.putCell x y c).u8need = v.u8need := rfl
theorem un_eraseRowSpan (v : Vt) (y a b : Nat) :
    (v.eraseRowSpan y a b).u8need = v.u8need := rfl
theorem un_scrollDownIn (v : Vt) (t b : Nat) :
    (v.scrollDownIn t b).u8need = v.u8need := rfl
theorem un_deleteChars (v : Vt) (n : Nat) : (v.deleteChars n).u8need = v.u8need := rfl
theorem un_insertChars (v : Vt) (n : Nat) : (v.insertChars n).u8need = v.u8need := rfl
theorem un_applySgr (v : Vt) (ps : List (Nat × Bool)) :
    (v.applySgr ps).u8need = v.u8need := rfl
theorem un_backTab (v : Vt) : v.backTab.u8need = v.u8need := rfl

theorem un_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    (v.scrollUpIn t b a).u8need = v.u8need := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem un_scrollUp (v : Vt) : v.scrollUp.u8need = v.u8need := un_scrollUpIn _ _ _ _
theorem un_scrollDown (v : Vt) : v.scrollDown.u8need = v.u8need := un_scrollDownIn _ _ _

theorem un_lineFeed (v : Vt) : v.lineFeed.u8need = v.u8need := by
  rw [frame_lineFeed]

theorem un_reverseIndex (v : Vt) : v.reverseIndex.u8need = v.u8need := by
  rw [frame_reverseIndex]

theorem un_backspace (v : Vt) : v.backspace.u8need = v.u8need := by
  unfold Vt.backspace; split <;> rfl

theorem un_tab (v : Vt) : v.tab.u8need = v.u8need := by
  unfold Vt.tab; dsimp only; exact un_clearPending v

theorem un_eraseChars (v : Vt) (n : Nat) : (v.eraseChars n).u8need = v.u8need :=
  un_eraseRowSpan _ _ _ _

theorem un_eraseLine (v : Vt) (m : Nat) : (v.eraseLine m).u8need = v.u8need := by
  rw [frame_eraseLine]

theorem un_eraseScreen (v : Vt) (m : Nat) : (v.eraseScreen m).u8need = v.u8need := by
  unfold Vt.eraseScreen
  repeat' split
  all_goals first
    | exact (un_foldl _ (fun w i => un_eraseRowSpan w _ _ _) _ _).trans (un_eraseLine _ _)
    | exact un_foldl _ (fun w i => un_eraseRowSpan w _ _ _) _ _

theorem un_insertLines (v : Vt) (n : Nat) : (v.insertLines n).u8need = v.u8need := by
  unfold Vt.insertLines
  dsimp only
  split
  · rfl
  · exact un_foldl _ (fun w _ => un_scrollDownIn w _ _) _ _

theorem un_deleteLines (v : Vt) (n : Nat) : (v.deleteLines n).u8need = v.u8need := by
  unfold Vt.deleteLines
  dsimp only
  split
  · rfl
  · exact un_foldl _ (fun w _ => un_scrollUpIn w _ _ _) _ _

theorem un_enterAlt (v : Vt) (s : Bool) : (v.enterAlt s).u8need = v.u8need := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem un_leaveAlt (v : Vt) (s : Bool) : (v.leaveAlt s).u8need = v.u8need := by
  unfold Vt.leaveAlt; split <;> rfl

theorem un_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    (v.setMode priv n on).u8need = v.u8need := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [un_moveTo, un_enterAlt, un_leaveAlt]
  all_goals rfl

theorem un_printWrap (v : Vt) : v.printWrap.u8need = v.u8need := by
  rw [frame_printWrap]

theorem un_printWideWrap (v : Vt) (w : Nat) : (v.printWideWrap w).u8need = v.u8need := by
  rw [frame_printWideWrap]

theorem un_printShift (v : Vt) (w : Nat) : (v.printShift w).u8need = v.u8need := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem un_mendRow (v : Vt) (y : Nat) :
    (v.mendRow y).u8need = v.u8need := by
  rw [frame_mendRow]

theorem un_printPut (v : Vt) (ch : Char) (w : Nat) :
    (v.printPut ch w).u8need = v.u8need := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [un_mendRow]; rfl)

theorem un_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).u8need = v.u8need := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem un_printMark (v : Vt) (ch : Char) : (v.printMark ch).u8need = v.u8need := by
  rw [frame_printMark]

theorem un_print (v : Vt) (c : Char) : (v.print c).u8need = v.u8need := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | rw [un_printMark]
    | rw [un_printAdvance, un_printPut, un_printShift, un_printWideWrap, un_printWrap]

theorem un_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).u8need = v.u8need := by
  unfold Vt.acceptChar; split <;> exact un_print _ _

theorem un_ctl (v : Vt) (b : UInt8) : (v.ctl b).u8need = v.u8need := by
  unfold Vt.ctl
  repeat' split
  all_goals first
    | exact un_backspace v
    | exact un_tab v
    | exact un_lineFeed v
    | exact un_carriageReturn v
    | rfl

theorem un_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiDispatch s final).u8need = v.u8need := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals try simp only [un_insertChars, un_moveRel, un_carriageReturn, un_setCol,
    un_moveTo, un_eraseScreen, un_eraseLine, un_insertLines, un_deleteLines,
    un_deleteChars, un_eraseChars, un_setMode, un_applySgr]
  all_goals first
    | rfl
    | exact un_foldl _ (fun w _ => un_tab w) _ _
    | exact un_foldl _ (fun w _ => un_scrollUp w) _ _
    | exact un_foldl _ (fun w _ => un_scrollDown w) _ _
    | exact un_foldl _ (fun w _ => un_backTab w) _ _

theorem un_csiFinish (v : Vt) (s : CsiState) (final : UInt8) :
    (v.csiFinish s final).u8need = v.u8need := by
  unfold Vt.csiFinish
  dsimp only
  split <;> exact un_csiDispatch _ _ _

theorem un_stepCsi (v : Vt) (s : CsiState) (b : UInt8) :
    (v.stepCsi s b).u8need = v.u8need := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | rfl
    | exact un_csiFinish _ _ _
    | exact un_ctl _ _

theorem un_stepEscInter (v : Vt) (i b : UInt8) :
    (v.stepEscInter i b).u8need = v.u8need := by
  rw [frame_stepEscInter]

theorem un_oscFinish (v : Vt) (acc : Array UInt8) :
    (v.oscFinish acc).u8need = v.u8need := by
  rw [frame_oscFinish]

theorem un_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    (v.stepOsc acc e b).u8need = v.u8need := by
  unfold Vt.stepOsc
  repeat' split
  all_goals first
    | rfl
    | exact un_oscFinish _ _

theorem un_stepStr (v : Vt) (e : Bool) (b : UInt8) :
    (v.stepStr e b).u8need = v.u8need := by
  rw [frame_stepStr]

/-- `stepEsc` in "stays zero" form: `RIS` rebuilds through `Vt.init`,
which has no pending sequence by construction. -/
theorem uz_stepEsc {v : Vt} (b : UInt8) (h : v.u8need = 0) :
    (v.stepEsc b).u8need = 0 := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals try simp only [un_lineFeed, un_carriageReturn, un_reverseIndex]
  all_goals first
    | exact h
    | rfl

/-- `stepGround` keeps `u8need` at zero for any byte that is not a
multi-byte UTF-8 lead (≥ 0xC0): a lead byte is exactly what *starts* a
pending sequence. -/
theorem uz_stepGround {v : Vt} (b : UInt8) (hb : b < 0xC0) (h : v.u8need = 0) :
    (v.stepGround b).u8need = 0 := by
  unfold Vt.stepGround
  repeat' split
  all_goals try simp only [un_ctl, un_acceptChar]
  all_goals first
    | exact h
    | rfl
    | (simp [h])
    | (exfalso
       simp only [UInt8.lt_iff_toNat_lt, Bool.not_eq_true,
         decide_eq_false_iff_not, decide_eq_true_eq, Nat.not_lt,
         show ((0x20 : UInt8)).toNat = 32 from rfl,
         show ((0x80 : UInt8)).toNat = 128 from rfl,
         show ((0xC0 : UInt8)).toNat = 192 from rfl,
         show ((0xE0 : UInt8)).toNat = 224 from rfl,
         show ((0xF0 : UInt8)).toNat = 240 from rfl,
         show ((0xF8 : UInt8)).toNat = 248 from rfl] at *
       omega)

/-- One step keeps `u8need` at zero, in any parser state, for any byte
that is not a UTF-8 lead byte. -/
theorem uz_step {v : Vt} (b : UInt8) (hb : b < 0xC0) (h : v.u8need = 0) :
    (v.step b).u8need = 0 := by
  have hab : (v.abortUtf8 b).u8need = 0 := by
    unfold Vt.abortUtf8
    split
    · rfl
    · exact h
  unfold Vt.step
  dsimp only
  split
  all_goals try simp only [un_stepEscInter, un_stepCsi, un_stepOsc, un_stepStr]
  all_goals first
    | exact hab
    | exact uz_stepGround _ hb hab
    | exact uz_stepEsc _ hab

/-- Feeding ESC from ANY state (pending UTF-8 or not) leaves none: the
abort fires, and no ESC branch of any parser state re-arms it. -/
theorem uz_step_esc (v : Vt) : (v.step 0x1B).u8need = 0 := by
  have hab : (v.abortUtf8 0x1B).u8need = 0 := by
    rcases Nat.eq_zero_or_pos v.u8need with hz | hpos
    · unfold Vt.abortUtf8
      split
      · rfl
      · exact hz
    · have hg : (v.u8need > 0 && ((0x1B : UInt8) < 0x80 || (0x1B : UInt8) ≥ 0xC0)) = true := by
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
        exact ⟨hpos, Or.inl (by decide)⟩
      unfold Vt.abortUtf8
      rw [if_pos hg]
  unfold Vt.step
  dsimp only
  split
  all_goals try simp only [un_stepEscInter, un_stepCsi, un_stepOsc, un_stepStr]
  all_goals first
    | exact hab
    | exact uz_stepGround _ (by decide) hab
    | exact uz_stepEsc _ hab

/-- A run of non-lead bytes keeps `u8need` at zero. -/
theorem uz_feed : ∀ (bs : List UInt8) (v : Vt), (∀ b ∈ bs, b < 0xC0) →
    v.u8need = 0 → (v.feed bs).u8need = 0
  | [], _, _, h => h
  | x :: xs, v, hb, h => by
    have hstep : v.feed (x :: xs) = (v.step x).feed xs := by simp [Vt.feed]
    rw [hstep]
    exact uz_feed xs _ (fun b hm => hb b (by simp [hm]))
      (uz_step x (hb x (by simp)) h)

end Zmx.Core.Vt


namespace Zmx.Core.Vt
/-! ## The grid keeps its dimensions

The third invariance layer, and the one the step-4 notes recorded as
open: "every operation preserves `cols`/`rows` syntactically except RIS
(which re-derives them via `clampDim`, identity under `Good`), but
stating it needs per-op lemmas". Here they are — the same staged,
equation-form shape as the `pstate` and `u8need` layers, over the pair
`dims v = (v.cols, v.rows)` so one lemma covers both fields.

Needed because §Replay's cursor claim goes through `moveTo`, which clamps
against the *replayed* state's dimensions: `w.cursor = v.cursor` is only
meaningful once `w.cols = v.cols`.

`RIS` is the one conditional case (hence `dims_step` takes `Good v`):
`Vt.init` re-clamps, and `Good` is exactly what makes that the identity.
-/

/-- Grid dimensions as a pair, so one lemma per operation covers both. -/
def dims (v : Vt) : Nat × Nat := (v.cols, v.rows)

theorem dims_foldl {α : Type} (f : Vt → α → Vt) (hf : ∀ v a, dims (f v a) = dims v) :
    ∀ (l : List α) (v : Vt), dims (l.foldl f v) = dims v
  | [], _ => rfl
  | a :: as, v => (dims_foldl f hf as (f v a)).trans (hf v a)

theorem dims_clearPending (v : Vt) : dims v.clearPending = dims v := rfl
theorem dims_carriageReturn (v : Vt) : dims v.carriageReturn = dims v := rfl
theorem dims_moveTo (v : Vt) (x y : Nat) : dims (v.moveTo x y) = dims v := rfl
theorem dims_moveRel (v : Vt) (dx dy : Int) : dims (v.moveRel dx dy) = dims v := rfl
theorem dims_setCol (v : Vt) (x : Nat) : dims (v.setCol x) = dims v := rfl
theorem dims_putCell (v : Vt) (x y : Nat) (c : Cell) : dims (v.putCell x y c) = dims v := rfl
theorem dims_eraseRowSpan (v : Vt) (y a b : Nat) : dims (v.eraseRowSpan y a b) = dims v := rfl
theorem dims_scrollDownIn (v : Vt) (t b : Nat) : dims (v.scrollDownIn t b) = dims v := rfl
theorem dims_deleteChars (v : Vt) (n : Nat) : dims (v.deleteChars n) = dims v := rfl
theorem dims_insertChars (v : Vt) (n : Nat) : dims (v.insertChars n) = dims v := rfl
theorem dims_applySgr (v : Vt) (ps : List (Nat × Bool)) : dims (v.applySgr ps) = dims v := rfl
theorem dims_backTab (v : Vt) : dims v.backTab = dims v := rfl

theorem dims_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    dims (v.scrollUpIn t b a) = dims v := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem dims_scrollUp (v : Vt) : dims v.scrollUp = dims v := dims_scrollUpIn _ _ _ _
theorem dims_scrollDown (v : Vt) : dims v.scrollDown = dims v := dims_scrollDownIn _ _ _

theorem dims_lineFeed (v : Vt) : dims v.lineFeed = dims v := by
  rw [frame_lineFeed]
  rfl

theorem dims_reverseIndex (v : Vt) : dims v.reverseIndex = dims v := by
  rw [frame_reverseIndex]
  rfl

theorem dims_backspace (v : Vt) : dims v.backspace = dims v := by
  unfold Vt.backspace; split <;> rfl

theorem dims_tab (v : Vt) : dims v.tab = dims v := by
  unfold Vt.tab; dsimp only; exact dims_clearPending v

theorem dims_eraseChars (v : Vt) (n : Nat) : dims (v.eraseChars n) = dims v :=
  dims_eraseRowSpan _ _ _ _

theorem dims_eraseLine (v : Vt) (m : Nat) : dims (v.eraseLine m) = dims v := by
  rw [frame_eraseLine]
  rfl

theorem dims_eraseScreen (v : Vt) (m : Nat) : dims (v.eraseScreen m) = dims v := by
  unfold Vt.eraseScreen
  repeat' split
  all_goals first
    | exact (dims_foldl _ (fun w i => dims_eraseRowSpan w _ _ _) _ _).trans
        (dims_eraseLine _ _)
    | exact dims_foldl _ (fun w i => dims_eraseRowSpan w _ _ _) _ _

theorem dims_insertLines (v : Vt) (n : Nat) : dims (v.insertLines n) = dims v := by
  unfold Vt.insertLines
  dsimp only
  split
  · rfl
  · exact dims_foldl _ (fun w _ => dims_scrollDownIn w _ _) _ _

theorem dims_deleteLines (v : Vt) (n : Nat) : dims (v.deleteLines n) = dims v := by
  unfold Vt.deleteLines
  dsimp only
  split
  · rfl
  · exact dims_foldl _ (fun w _ => dims_scrollUpIn w _ _ _) _ _

theorem dims_enterAlt (v : Vt) (s : Bool) : dims (v.enterAlt s) = dims v := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem dims_leaveAlt (v : Vt) (s : Bool) : dims (v.leaveAlt s) = dims v := by
  unfold Vt.leaveAlt; split <;> rfl

theorem dims_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) :
    dims (v.setMode priv n on) = dims v := by
  unfold Vt.setMode
  repeat' split
  all_goals try simp only [dims_moveTo, dims_enterAlt, dims_leaveAlt]
  all_goals rfl

theorem dims_printWrap (v : Vt) : dims v.printWrap = dims v := by
  rw [frame_printWrap]
  rfl

theorem dims_printWideWrap (v : Vt) (w : Nat) : dims (v.printWideWrap w) = dims v := by
  rw [frame_printWideWrap]
  rfl

theorem dims_printShift (v : Vt) (w : Nat) : dims (v.printShift w) = dims v := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem dims_mendRow (v : Vt) (y : Nat) :
    dims (v.mendRow y) = dims v := by
  rw [frame_mendRow]; rfl

theorem dims_printPut (v : Vt) (ch : Char) (w : Nat) : dims (v.printPut ch w) = dims v := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [dims_mendRow]; rfl)

theorem dims_printAdvance (v : Vt) (w : Nat) : dims (v.printAdvance w) = dims v := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem dims_printMark (v : Vt) (ch : Char) : dims (v.printMark ch) = dims v := by
  rw [frame_printMark]; rfl

theorem dims_print (v : Vt) (c : Char) : dims (v.print c) = dims v := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | rw [dims_printMark]
    | rw [dims_printAdvance, dims_printPut, dims_printShift, dims_printWideWrap,
        dims_printWrap]

theorem dims_acceptChar (v : Vt) (n : Nat) : dims (v.acceptChar n) = dims v := by
  unfold Vt.acceptChar; split <;> exact dims_print _ _

theorem dims_ctl (v : Vt) (b : UInt8) : dims (v.ctl b) = dims v := by
  unfold Vt.ctl
  repeat' split
  all_goals first
    | exact dims_backspace v
    | exact dims_tab v
    | exact dims_lineFeed v
    | exact dims_carriageReturn v
    | rfl

theorem dims_csiDispatch (v : Vt) (s : CsiState) (final : UInt8) :
    dims (v.csiDispatch s final) = dims v := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals try simp only [dims_insertChars, dims_moveRel, dims_carriageReturn,
    dims_setCol, dims_moveTo, dims_eraseScreen, dims_eraseLine, dims_insertLines,
    dims_deleteLines, dims_deleteChars, dims_eraseChars, dims_setMode, dims_applySgr]
  all_goals first
    | rfl
    | exact dims_foldl _ (fun w _ => dims_tab w) _ _
    | exact dims_foldl _ (fun w _ => dims_scrollUp w) _ _
    | exact dims_foldl _ (fun w _ => dims_scrollDown w) _ _
    | exact dims_foldl _ (fun w _ => dims_backTab w) _ _

theorem dims_csiFinish (v : Vt) (s : CsiState) (final : UInt8) :
    dims (v.csiFinish s final) = dims v := by
  unfold Vt.csiFinish
  dsimp only
  split <;> exact dims_csiDispatch _ _ _

theorem dims_stepCsi (v : Vt) (s : CsiState) (b : UInt8) :
    dims (v.stepCsi s b) = dims v := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | rfl
    | exact dims_csiFinish _ _ _
    | exact dims_ctl _ _

theorem dims_stepEscInter (v : Vt) (i b : UInt8) : dims (v.stepEscInter i b) = dims v := by
  rw [frame_stepEscInter]
  rfl

theorem dims_oscFinish (v : Vt) (acc : Array UInt8) : dims (v.oscFinish acc) = dims v := by
  rw [frame_oscFinish]
  rfl

theorem dims_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    dims (v.stepOsc acc e b) = dims v := by
  unfold Vt.stepOsc
  repeat' split
  all_goals first
    | rfl
    | exact dims_oscFinish _ _

theorem dims_stepStr (v : Vt) (e : Bool) (b : UInt8) : dims (v.stepStr e b) = dims v := by
  rw [frame_stepStr]
  rfl

theorem dims_abortUtf8 (v : Vt) (b : UInt8) : dims (v.abortUtf8 b) = dims v := by
  unfold Vt.abortUtf8; split <;> rfl

/-- `RIS` rebuilds the state through `Vt.init`, which re-clamps the
dimensions — the identity exactly when they are already in range, which
is what `Good` says. This is the one place the dims layer needs a
hypothesis. -/
theorem dims_stepEsc {v : Vt} (b : UInt8) (h : Good v) :
    dims (v.stepEsc b) = dims v := by
  have hcp := h.colsPos
  have hcl := h.colsLe
  have hrp := h.rowsPos
  have hrl := h.rowsLe
  have hc : clampDim v.cols = v.cols := by unfold clampDim; omega
  have hr : clampDim v.rows = v.rows := by unfold clampDim; omega
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | exact dims_lineFeed v
    | exact dims_reverseIndex v
    | exact (dims_lineFeed _).trans (dims_carriageReturn v)
    | (simp only [dims, Vt.init, hc, hr])

theorem dims_stepGround (v : Vt) (b : UInt8) : dims (v.stepGround b) = dims v := by
  unfold Vt.stepGround
  repeat' split
  all_goals try simp only [dims_ctl, dims_acceptChar]
  all_goals rfl

/-- One step keeps the dimensions, for any byte. -/
theorem dims_step {v : Vt} (b : UInt8) (h : Good v) : dims (v.step b) = dims v := by
  have hg : Good (v.abortUtf8 b) := by
    unfold Vt.abortUtf8
    split
    · exact Good.set_u8 0 0 (by omega) h
    · exact h
  have hd : dims (v.abortUtf8 b) = dims v := dims_abortUtf8 v b
  unfold Vt.step
  dsimp only
  split
  all_goals try simp only [dims_stepGround, dims_stepEscInter, dims_stepCsi,
    dims_stepOsc, dims_stepStr]
  all_goals first
    | exact hd
    | exact (dims_stepEsc _ hg).trans hd

/-- **The dims layer's payoff.** No byte stream changes the grid
dimensions: what a client's emulator is told to paint, it paints at the
size it already had. -/
theorem dims_feed : ∀ (bs : List UInt8) {v : Vt}, Good v → dims (v.feed bs) = dims v
  | [], _, _ => rfl
  | x :: xs, v, h => by
    have hstep : v.feed (x :: xs) = (v.step x).feed xs := by simp [Vt.feed]
    rw [hstep]
    exact (dims_feed xs (Good.step x h)).trans (dims_step x h)

end Zmx.Core.Vt


namespace Zmx.Core.Vt
/-! ## Origin mode survives everything that is not a mode set

The rung §Replay's *restore-level* cursor claim stands on: a session with
DECOM off must replay with DECOM off, or the final `CUP` would be read
region-relative and land somewhere else.

The structural fact that makes this cheap: `modes` is only ever written
by `setMode`, which `csiDispatch` reaches only through the `h`/`l`
finals. So one conditional lemma (`org_setMode`: only *private* mode 6
touches `origin`) plus the usual arm sweep carries it. Fourth instance of
the invariance-layer recipe, and the one that will also serve pen,
region and mode fidelity.
-/

theorem org_foldl {α : Type} (f : Vt → α → Vt)
    (hf : ∀ v a, (f v a).modes.origin = v.modes.origin) :
    ∀ (l : List α) (v : Vt), (l.foldl f v).modes.origin = v.modes.origin
  | [], _ => rfl
  | a :: as, v => (org_foldl f hf as (f v a)).trans (hf v a)

theorem org_clearPending (v : Vt) : v.clearPending.modes.origin = v.modes.origin := rfl
theorem org_carriageReturn (v : Vt) :
    v.carriageReturn.modes.origin = v.modes.origin := rfl
theorem org_moveTo (v : Vt) (x y : Nat) : (v.moveTo x y).modes.origin = v.modes.origin := rfl
theorem org_moveRel (v : Vt) (dx dy : Int) :
    (v.moveRel dx dy).modes.origin = v.modes.origin := rfl
theorem org_setCol (v : Vt) (x : Nat) : (v.setCol x).modes.origin = v.modes.origin := rfl
theorem org_putCell (v : Vt) (x y : Nat) (c : Cell) :
    (v.putCell x y c).modes.origin = v.modes.origin := rfl
theorem org_eraseRowSpan (v : Vt) (y a b : Nat) :
    (v.eraseRowSpan y a b).modes.origin = v.modes.origin := rfl
theorem org_scrollDownIn (v : Vt) (t b : Nat) :
    (v.scrollDownIn t b).modes.origin = v.modes.origin := rfl
theorem org_deleteChars (v : Vt) (n : Nat) :
    (v.deleteChars n).modes.origin = v.modes.origin := rfl
theorem org_insertChars (v : Vt) (n : Nat) :
    (v.insertChars n).modes.origin = v.modes.origin := rfl
theorem org_applySgr (v : Vt) (ps : List (Nat × Bool)) :
    (v.applySgr ps).modes.origin = v.modes.origin := rfl
theorem org_backTab (v : Vt) : v.backTab.modes.origin = v.modes.origin := rfl

theorem org_scrollUpIn (v : Vt) (t b : Nat) (a : Bool) :
    (v.scrollUpIn t b a).modes.origin = v.modes.origin := by
  unfold Vt.scrollUpIn; dsimp only; split <;> rfl

theorem org_scrollUp (v : Vt) : v.scrollUp.modes.origin = v.modes.origin :=
  org_scrollUpIn _ _ _ _
theorem org_scrollDown (v : Vt) : v.scrollDown.modes.origin = v.modes.origin :=
  org_scrollDownIn _ _ _

theorem org_lineFeed (v : Vt) : v.lineFeed.modes.origin = v.modes.origin := by
  rw [frame_lineFeed]

theorem org_reverseIndex (v : Vt) : v.reverseIndex.modes.origin = v.modes.origin := by
  rw [frame_reverseIndex]

theorem org_backspace (v : Vt) : v.backspace.modes.origin = v.modes.origin := by
  unfold Vt.backspace; split <;> rfl

theorem org_tab (v : Vt) : v.tab.modes.origin = v.modes.origin := by
  unfold Vt.tab; dsimp only; exact org_clearPending v

theorem org_eraseChars (v : Vt) (n : Nat) :
    (v.eraseChars n).modes.origin = v.modes.origin := org_eraseRowSpan _ _ _ _

theorem org_eraseLine (v : Vt) (m : Nat) :
    (v.eraseLine m).modes.origin = v.modes.origin := by
  rw [frame_eraseLine]

theorem org_eraseScreen (v : Vt) (m : Nat) :
    (v.eraseScreen m).modes.origin = v.modes.origin := by
  unfold Vt.eraseScreen
  repeat' split
  all_goals first
    | exact (org_foldl _ (fun w i => org_eraseRowSpan w _ _ _) _ _).trans
        (org_eraseLine _ _)
    | exact org_foldl _ (fun w i => org_eraseRowSpan w _ _ _) _ _

theorem org_insertLines (v : Vt) (n : Nat) :
    (v.insertLines n).modes.origin = v.modes.origin := by
  unfold Vt.insertLines
  dsimp only
  split
  · rfl
  · exact org_foldl _ (fun w _ => org_scrollDownIn w _ _) _ _

theorem org_deleteLines (v : Vt) (n : Nat) :
    (v.deleteLines n).modes.origin = v.modes.origin := by
  unfold Vt.deleteLines
  dsimp only
  split
  · rfl
  · exact org_foldl _ (fun w _ => org_scrollUpIn w _ _ _) _ _

theorem org_enterAlt (v : Vt) (s : Bool) :
    (v.enterAlt s).modes.origin = v.modes.origin := by
  unfold Vt.enterAlt; dsimp only; split <;> rfl

theorem org_leaveAlt (v : Vt) (s : Bool) :
    (v.leaveAlt s).modes.origin = v.modes.origin := by
  unfold Vt.leaveAlt; split <;> rfl

/-- **The conditional rung.** Only *private* mode 6 (DECOM) writes
`origin`; every other mode number, private or not, leaves it alone. -/
theorem org_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool)
    (h : ¬(priv = true ∧ n = 6)) :
    (v.setMode priv n on).modes.origin = v.modes.origin := by
  unfold Vt.setMode
  split
  · rename_i hp
    -- private modes: only 6 touches origin, and that case is excluded
    repeat' split
    all_goals first
      | rfl
      | exact org_enterAlt _ _
      | exact org_leaveAlt _ _
      | (exfalso
         apply h
         refine ⟨hp, ?_⟩
         first | rfl | assumption | omega)
  · -- non-private: only IRM (4), which is a different flag
    repeat' split
    all_goals rfl

/-- `csiDispatch` preserves `origin` unless the sequence *is* a DECOM
set/reset — i.e. private, with first parameter 6. -/
theorem org_csiDispatch (v : Vt) (s : CsiState) (final : UInt8)
    (h : ¬((s.priv == 0x3F) = true ∧ s.arg 0 0 = 6)) :
    (v.csiDispatch s final).modes.origin = v.modes.origin := by
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals try simp only [org_insertChars, org_moveRel, org_carriageReturn,
    org_setCol, org_moveTo, org_eraseScreen, org_eraseLine, org_insertLines,
    org_deleteLines, org_deleteChars, org_eraseChars, org_applySgr]
  all_goals first
    | rfl
    | exact org_setMode _ _ _ _ (fun hc => h ⟨hc.1, hc.2⟩)
    | exact org_foldl _ (fun w _ => org_tab w) _ _
    | exact org_foldl _ (fun w _ => org_scrollUp w) _ _
    | exact org_foldl _ (fun w _ => org_scrollDown w) _ _
    | exact org_foldl _ (fun w _ => org_backTab w) _ _

theorem org_csiFinish (v : Vt) (s : CsiState) (final : UInt8)
    (hp : (s.priv == 0x3F) = false) :
    (v.csiFinish s final).modes.origin = v.modes.origin := by
  -- every record `csiFinish` builds keeps `priv`, so one hypothesis covers
  -- all three dispatch sites
  have hnot : ∀ (t : CsiState), t.priv = s.priv →
      ¬((t.priv == 0x3F) = true ∧ t.arg 0 0 = 6) := by
    intro t ht hc
    rw [ht, hp] at hc
    exact absurd hc.1 (by simp)
  unfold Vt.csiFinish
  dsimp only
  split
  · split
    · exact org_csiDispatch _ _ _ (hnot _ rfl)
    · exact org_csiDispatch _ _ _ (hnot _ rfl)
  · exact org_csiDispatch _ _ _ (hnot _ rfl)

theorem org_ctl (v : Vt) (b : UInt8) : (v.ctl b).modes.origin = v.modes.origin := by
  unfold Vt.ctl
  repeat' split
  all_goals first
    | exact org_backspace v
    | exact org_tab v
    | exact org_lineFeed v
    | exact org_carriageReturn v
    | rfl

/-- Inside a CSI, `origin` survives unless the sequence is a private
mode-6 set/reset — and a private-marker byte only *records* the marker. -/
theorem org_stepCsi (v : Vt) (s : CsiState) (b : UInt8)
    (hp : (s.priv == 0x3F) = false) :
    (v.stepCsi s b).modes.origin = v.modes.origin := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | rfl
    | exact org_csiFinish _ _ _ hp
    | exact org_ctl _ _

theorem org_printWrap (v : Vt) : v.printWrap.modes.origin = v.modes.origin := by
  rw [frame_printWrap]

theorem org_printWideWrap (v : Vt) (w : Nat) :
    (v.printWideWrap w).modes.origin = v.modes.origin := by
  rw [frame_printWideWrap]

theorem org_printShift (v : Vt) (w : Nat) :
    (v.printShift w).modes.origin = v.modes.origin := by
  unfold Vt.printShift; dsimp only; split <;> rfl

theorem org_mendRow (v : Vt) (y : Nat) :
    (v.mendRow y).modes.origin = v.modes.origin := by
  rw [frame_mendRow]

theorem org_printPut (v : Vt) (ch : Char) (w : Nat) :
    (v.printPut ch w).modes.origin = v.modes.origin := by
  unfold Vt.printPut
  dsimp only
  repeat' split
  all_goals (rw [org_mendRow]; rfl)

theorem org_printAdvance (v : Vt) (w : Nat) :
    (v.printAdvance w).modes.origin = v.modes.origin := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem org_printMark (v : Vt) (ch : Char) :
    (v.printMark ch).modes.origin = v.modes.origin := by
  rw [frame_printMark]

theorem org_print (v : Vt) (c : Char) : (v.print c).modes.origin = v.modes.origin := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | rw [org_printMark]
    | rw [org_printAdvance, org_printPut, org_printShift, org_printWideWrap,
        org_printWrap]

theorem org_acceptChar (v : Vt) (n : Nat) :
    (v.acceptChar n).modes.origin = v.modes.origin := by
  unfold Vt.acceptChar; split <;> exact org_print _ _

theorem org_stepGround (v : Vt) (b : UInt8) :
    (v.stepGround b).modes.origin = v.modes.origin := by
  unfold Vt.stepGround
  repeat' split
  all_goals try simp only [org_ctl, org_acceptChar]
  all_goals rfl

theorem org_stepEscInter (v : Vt) (i b : UInt8) :
    (v.stepEscInter i b).modes.origin = v.modes.origin := by
  rw [frame_stepEscInter]

theorem org_oscFinish (v : Vt) (acc : Array UInt8) :
    (v.oscFinish acc).modes.origin = v.modes.origin := by
  rw [frame_oscFinish]

theorem org_stepOsc (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    (v.stepOsc acc e b).modes.origin = v.modes.origin := by
  unfold Vt.stepOsc
  repeat' split
  all_goals first
    | rfl
    | exact org_oscFinish _ _

theorem org_stepStr (v : Vt) (e : Bool) (b : UInt8) :
    (v.stepStr e b).modes.origin = v.modes.origin := by
  rw [frame_stepStr]

theorem org_abortUtf8 (v : Vt) (b : UInt8) :
    (v.abortUtf8 b).modes.origin = v.modes.origin := by
  unfold Vt.abortUtf8; split <;> rfl

/-- `stepEsc` preserves `origin` except at `RIS`, which resets it to the
default — `false`, which is what a DECOM-off session wants anyway, so the
statement is "stays false". -/
theorem org_stepEsc {v : Vt} (b : UInt8) (h : v.modes.origin = false) :
    (v.stepEsc b).modes.origin = false := by
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals try simp only [org_lineFeed, org_carriageReturn, org_reverseIndex]
  all_goals first
    | exact h
    | rfl

/-! ### The private-CSI escape hatch

`org_stepCsi` above needs the private marker to be *absent*, because a
private sequence could be DECOM. That is too coarse for the one construct
that has a marker: `csiPriv n final` emits `CSI ? <digits> <final>`, so
every mode replay would be excluded. When the pending parameter is known,
"is this DECOM?" can be decided instead of assumed away — and that is
exactly the state `Render`'s private sequences reach: no pushed parameter,
one pending accumulator, whose value is not 6.
-/

theorem priv_csiPush (s : CsiState) (sub : Bool) : (csiPush s sub).priv = s.priv := by
  unfold csiPush
  repeat' split
  all_goals rfl

/-- The pending parameter is what `csiFinish` pushes, so it is what
`arg 0` reads back — and if it is not 6, no `h`/`l` final can be DECOM,
marker or no marker. -/
theorem org_csiFinish_pending (v : Vt) (s : CsiState) (final : UInt8)
    (hparams : s.params = #[]) (hhave : s.haveCur = true) (hne : min s.cur 65535 ≠ 6) :
    (v.csiFinish s final).modes.origin = v.modes.origin := by
  have hsize : ¬ (s.params.size ≥ 16) := by rw [hparams]; simp
  unfold Vt.csiFinish
  dsimp only
  rw [if_pos hhave, if_neg hsize]
  refine org_csiDispatch _ _ _ ?_
  rintro ⟨-, h6⟩
  apply hne
  rw [← h6]
  unfold CsiState.arg
  rw [hparams]
  simp only [Array.push, Array.getD]
  split <;> simp_all

/-- `stepCsi` under the same knowledge: no branch can turn `origin` on. -/
theorem org_stepCsi_pending (v : Vt) (s : CsiState) (b : UInt8)
    (hparams : s.params = #[]) (hhave : s.haveCur = true) (hne : min s.cur 65535 ≠ 6) :
    (v.stepCsi s b).modes.origin = v.modes.origin := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | rfl
    | exact org_csiFinish_pending _ _ _ hparams hhave hne
    | exact org_ctl _ _

/-! ### The dispatcher: `origin` across one whole `Vt.step`

The lemmas above are per parser state; a byte-stream proof composes
`Vt.step` itself (`Theorems/Render.lean`). `abortUtf8` runs first inside
`step` and touches only `u8need`/`u8acc`, so each case is its branch
lemma followed by `org_abortUtf8`. -/

theorem org_step_of_ground {v : Vt} (b : UInt8) (hg : v.pstate = .ground) :
    (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.ground := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepGround, org_abortUtf8]

/-- From `.esc` the claim has to be "stays false" rather than "unchanged":
`RIS` resets `origin` to its default, which is `false`. -/
theorem org_step_of_esc {v : Vt} (b : UInt8) (hg : v.pstate = .esc)
    (h : v.modes.origin = false) : (v.step b).modes.origin = false := by
  have hw : (v.abortUtf8 b).pstate = PState.esc := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw]
  exact org_stepEsc b (by rw [org_abortUtf8]; exact h)

theorem org_step_of_escInter {v : Vt} {i : UInt8} (b : UInt8)
    (hg : v.pstate = .escInter i) : (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.escInter i := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepEscInter, org_abortUtf8]

theorem org_step_of_osc {v : Vt} {acc : Array UInt8} {e : Bool} (b : UInt8)
    (hg : v.pstate = .osc acc e) : (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.osc acc e := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepOsc, org_abortUtf8]

theorem org_step_of_csi {v : Vt} {s : CsiState} (b : UInt8) (hg : v.pstate = .csi s)
    (hp : (s.priv == 0x3F) = false) :
    (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepCsi _ _ _ hp, org_abortUtf8]

/-- The marker-tolerant companion of `org_step_of_csi`. -/
theorem org_step_of_csi_pending {v : Vt} {s : CsiState} (b : UInt8)
    (hg : v.pstate = .csi s) (hparams : s.params = #[]) (hhave : s.haveCur = true)
    (hne : min s.cur 65535 ≠ 6) : (v.step b).modes.origin = v.modes.origin := by
  have hw : (v.abortUtf8 b).pstate = PState.csi s := by
    rw [ps_abortUtf8]; exact hg
  unfold Vt.step
  dsimp only
  rw [hw, org_stepCsi_pending _ _ _ hparams hhave hne, org_abortUtf8]

end Zmx.Core.Vt







namespace Zmx.Core.Vt
/-! ## Wide pairs: the repair's postcondition

`Render.rowAnsi` can express a row only if every wide glyph in it is whole: a
width-2 base immediately followed by its width-0 shadow, that shadow carrying
nothing of its own (the painter emits the base and nothing else), and no shadow
without a base. Half a pair is not displayable either — a lone base re-wraps on
replay, a lone shadow paints nothing while still occupying a column — so rather
than adding side conditions to the replay theorem, the emulator does not reach
those shapes. Every cell-writing operation ends in `Row.mend`.

This section proves the postcondition that makes those calls worth anything:
after `Row.mend`, **every column satisfies `PairOk`**. It is what `Renderable`
rests on, and proving it once here is what keeps the pair invariant out of every
individual mutation's proof.
-/

/-- Reading back the cell a `setIfInBounds` wrote. -/
theorem getD_set_self {α} [Inhabited α] (r : Array α) (x : Nat) (c d : α)
    (h : x < r.size) : (r.setIfInBounds x c).getD x d = c := by
  simp [Array.getD, Array.setIfInBounds, h]

/-- …and reading back any other cell. -/
theorem getD_set_ne {α} [Inhabited α] (r : Array α) (x j : Nat) (c d : α)
    (h : j ≠ x) : (r.setIfInBounds x c).getD j d = r.getD j d := by
  simp only [Array.getD, Array.setIfInBounds]
  split
  · simp only [Array.size_set]
    split
    · simp [Array.getElem_set, Ne.symm h]
    · rfl
  · rfl

/-- Out of range reads a default (width-1) cell, which is what lets the pair
rules treat "no neighbour" and "a narrow neighbour" alike. -/
theorem at_of_size_le (row : Row) (x : Nat) (h : row.size ≤ x) : row.at x = default := by
  unfold Row.at
  simp [Array.getD, Nat.not_lt.mpr h]

/-- **The pair rule for one column**, in `Prop`: a base keeps its shadow (and
that shadow is exactly what repainting the base re-creates), and a shadow keeps
its base. -/
def PairOk (row : Row) (x : Nat) : Prop :=
  ((row.at x).width = 2 → row.at (x + 1) = Cell.shadow (row.at x))
    ∧ ((row.at x).width = 0 → x ≠ 0 ∧ (row.at (x - 1)).width = 2)

/-- `halfPair` reads nothing but the three neighbouring widths. -/
theorem halfPair_congr {row row' : Row} (x : Nat)
    (h0 : (row'.at (x - 1)).width = (row.at (x - 1)).width)
    (h1 : (row'.at x).width = (row.at x).width)
    (h2 : (row'.at (x + 1)).width = (row.at (x + 1)).width) :
    row'.halfPair x = row.halfPair x := by
  simp only [Row.halfPair]
  rw [h0, h1, h2]

/-- `halfPair` in `Prop` — the width half of `PairOk`. -/
theorem halfPair_eq_false_iff (row : Row) (x : Nat) :
    row.halfPair x = false ↔
      ((row.at x).width = 2 → (row.at (x + 1)).width = 0)
        ∧ ((row.at x).width = 0 → x ≠ 0 ∧ (row.at (x - 1)).width = 2) := by
  unfold Row.halfPair
  simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne,
    bne_eq_false_iff_eq, ne_eq]
  constructor
  · intro h
    refine ⟨fun h2 => ?_, fun h0 => ?_⟩
    · rcases h.1 with hc | hs
      · exact absurd h2 hc
      · exact hs
    · rcases h.2 with hc | hs
      · exact absurd h0 hc
      · exact ⟨hs.1, hs.2⟩
  · intro h
    refine ⟨?_, ?_⟩
    · by_cases h2 : (row.at x).width = 2
      · exact Or.inr (h.1 h2)
      · exact Or.inl h2
    · by_cases h0 : (row.at x).width = 0
      · exact Or.inr ⟨(h.2 h0).1, (h.2 h0).2⟩
      · exact Or.inl h0

/-- A width-1 cell is not half of anything, so a blanked column is repaired. -/
theorem halfPair_of_width_one (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    row.halfPair x = false := by
  rw [halfPair_eq_false_iff]
  exact ⟨fun h2 => absurd (h.symm.trans h2) (by decide),
         fun h0 => absurd (h.symm.trans h0) (by decide)⟩

/-! ### One repair step -/

theorem size_mendAt (row : Row) (x : Nat) : (Row.mendAt row x).size = row.size := by
  unfold Row.mendAt
  repeat' split
  all_goals first
    | simp
    | rfl

theorem mendAt_ne (row : Row) (x j : Nat) (h : j ≠ x) :
    (Row.mendAt row x).at j = row.at j := by
  unfold Row.mendAt Row.at
  repeat' split
  all_goals first
    | exact getD_set_ne _ _ _ _ _ h
    | rfl

/-- A half pair becomes a blank. -/
theorem mendAt_self_blank (row : Row) (x : Nat) (hx : x < row.size)
    (h : row.halfPair x = true) :
    (Row.mendAt row x).at x = Cell.erased (row.at x).pen := by
  unfold Row.mendAt Row.at
  rw [if_pos h]
  exact getD_set_self _ _ _ _ hx

/-- A whole pair's shadow becomes canonical. -/
theorem mendAt_self_shadow (row : Row) (x : Nat) (hx : x < row.size)
    (h : row.halfPair x = false) (hw : (row.at x).width = 0) :
    (Row.mendAt row x).at x = Cell.shadow (row.at (x - 1)) := by
  unfold Row.mendAt Row.at
  rw [if_neg (by simp [h]), if_pos (by simp [Row.at] at hw ⊢; exact hw)]
  exact getD_set_self _ _ _ _ hx

/-- Anything else is left alone. -/
theorem mendAt_self_id (row : Row) (x : Nat)
    (h : row.halfPair x = false) (hw : (row.at x).width ≠ 0) :
    (Row.mendAt row x).at x = row.at x := by
  unfold Row.mendAt Row.at
  rw [if_neg (by simp [h]), if_neg (by simp only [Row.at] at hw ⊢; simpa using hw)]

/-- A repair that does not blank preserves every width, since a canonical
shadow is still a shadow. -/
theorem width_mendAt_of_whole (row : Row) (x j : Nat) (h : row.halfPair x = false) :
    ((Row.mendAt row x).at j).width = (row.at j).width := by
  by_cases hj : j = x
  · subst hj
    by_cases hw : (row.at j).width = 0
    · by_cases hb : j < row.size
      · rw [mendAt_self_shadow row j hb h hw]; rw [hw]; rfl
      · rw [at_of_size_le row j (by omega)] at hw
        exact absurd hw (by decide)
    · rw [mendAt_self_id row j h hw]
  · rw [mendAt_ne row x j hj]

/-! ### The sweep -/

/-- The repaired column comes out repaired. -/
theorem halfPair_mendAt_self (row : Row) (n : Nat) (hn : n < row.size) :
    (Row.mendAt row n).halfPair n = false := by
  by_cases h : row.halfPair n = true
  · refine halfPair_of_width_one _ _ ?_
    rw [mendAt_self_blank row n hn h]
    rfl
  · have h' : row.halfPair n = false := by simpa using h
    rw [halfPair_congr n (width_mendAt_of_whole row n _ h')
      (width_mendAt_of_whole row n _ h') (width_mendAt_of_whole row n _ h')]
    exact h'

/-- …and so does its shadow clause. -/
theorem shadow_mendAt_self (row : Row) (n : Nat) (hn : n < row.size)
    (hw : ((Row.mendAt row n).at n).width = 0) :
    n ≠ 0 ∧ (Row.mendAt row n).at n = Cell.shadow ((Row.mendAt row n).at (n - 1)) := by
  by_cases h : row.halfPair n = true
  · rw [mendAt_self_blank row n hn h] at hw
    simp [Cell.erased] at hw
  · have h' : row.halfPair n = false := by simpa using h
    have hw0 : (row.at n).width = 0 := by
      rw [width_mendAt_of_whole row n n h'] at hw; exact hw
    have hne : n ≠ 0 := ((halfPair_eq_false_iff row n).mp h').2 hw0 |>.1
    refine ⟨hne, ?_⟩
    rw [mendAt_self_shadow row n hn h' hw0, mendAt_ne row n (n - 1) (by omega)]

/-- A repair step leaves every column below it repaired.

The content is that a *whole* pair is never touched: blanking column `n` could
only orphan a base at `n - 1` if `n` were that base's shadow, and such a shadow
is exactly what `mendAt`'s guard protects. That argument is direction-free,
which is why the sweep's order does not matter (see `Row.mend`); the `j < n`
form is what the sweep induction consumes. -/
theorem halfPair_mendAt_lt (row : Row) (n j : Nat) (hj : j < n)
    (h : row.halfPair j = false) : (Row.mendAt row n).halfPair j = false := by
  rw [halfPair_eq_false_iff] at h ⊢
  have hj0 : (Row.mendAt row n).at j = row.at j := mendAt_ne row n j (by omega)
  have hjm : (Row.mendAt row n).at (j - 1) = row.at (j - 1) :=
    mendAt_ne row n (j - 1) (by omega)
  refine ⟨fun h2 => ?_, fun h0 => ?_⟩
  · rw [hj0] at h2
    by_cases hn : j + 1 = n
    · -- the column being repaired is this base's shadow, so it is not blanked
      subst hn
      have hshadow : row.halfPair (j + 1) = false := by
        rw [halfPair_eq_false_iff]
        have hw : (row.at (j + 1)).width = 0 := h.1 h2
        exact ⟨fun hc => absurd (hw.symm.trans hc) (by decide),
               fun _ => ⟨by omega, h2⟩⟩
      rw [width_mendAt_of_whole row (j + 1) (j + 1) hshadow]
      exact h.1 h2
    · rw [mendAt_ne row n (j + 1) (by omega)]
      exact h.1 h2
  · rw [hj0] at h0
    exact ⟨(h.2 h0).1, by rw [hjm]; exact (h.2 h0).2⟩

/-- …including their shadow clause, which reads only columns at or below `j`. -/
theorem shadow_mendAt_lt (row : Row) (n j : Nat) (hj : j < n)
    (h : (row.at j).width = 0 → j ≠ 0 ∧ row.at j = Cell.shadow (row.at (j - 1))) :
    ((Row.mendAt row n).at j).width = 0 →
      j ≠ 0 ∧ (Row.mendAt row n).at j = Cell.shadow ((Row.mendAt row n).at (j - 1)) := by
  intro hw
  have hj0 : (Row.mendAt row n).at j = row.at j := mendAt_ne row n j (by omega)
  have hjm : (Row.mendAt row n).at (j - 1) = row.at (j - 1) :=
    mendAt_ne row n (j - 1) (by omega)
  rw [hj0] at hw
  exact ⟨(h hw).1, by rw [hj0, hjm]; exact (h hw).2⟩

/-- The sweep, up to a bound: every column below `n` is repaired — both the
width rule and the canonical-shadow rule — and the row keeps its size. -/
theorem mendUpto_spec (row : Row) :
    ∀ n, ((List.range n).foldl (fun r x => Row.mendAt r x) row).size = row.size
      ∧ ∀ j, j < n → n ≤ row.size →
          (((List.range n).foldl (fun r x => Row.mendAt r x) row).halfPair j = false
            ∧ ((((List.range n).foldl (fun r x => Row.mendAt r x) row).at j).width = 0 →
                j ≠ 0 ∧ ((List.range n).foldl (fun r x => Row.mendAt r x) row).at j
                  = Cell.shadow (((List.range n).foldl (fun r x => Row.mendAt r x) row).at (j - 1))))
  | 0 => ⟨rfl, fun _ hj => absurd hj (by omega)⟩
  | n + 1 => by
    have ih := mendUpto_spec row n
    have hstep : (List.range (n + 1)).foldl (fun r x => Row.mendAt r x) row
        = Row.mendAt ((List.range n).foldl (fun r x => Row.mendAt r x) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    refine ⟨by rw [hstep, size_mendAt]; exact ih.1, fun j hj hn => ?_⟩
    rw [hstep]
    by_cases hje : j = n
    · subst hje
      have hlt : j < ((List.range j).foldl (fun r x => Row.mendAt r x) row).size := by
        rw [ih.1]; omega
      exact ⟨halfPair_mendAt_self _ _ hlt, fun hw => shadow_mendAt_self _ _ hlt hw⟩
    · have hprev := ih.2 j (by omega) (by omega)
      exact ⟨halfPair_mendAt_lt _ _ _ (by omega) hprev.1,
             shadow_mendAt_lt _ _ _ (by omega) hprev.2⟩

theorem size_mend (row : Row) : (Row.mend row).size = row.size := by
  unfold Row.mend
  exact (mendUpto_spec row row.size).1

theorem mend_halfPair (row : Row) (x : Nat) (hx : x < row.size) :
    (Row.mend row).halfPair x = false := by
  unfold Row.mend
  exact ((mendUpto_spec row row.size).2 x hx (by omega)).1

theorem mend_shadow (row : Row) (x : Nat) (hx : x < row.size)
    (hw : ((Row.mend row).at x).width = 0) :
    x ≠ 0 ∧ (Row.mend row).at x = Cell.shadow ((Row.mend row).at (x - 1)) := by
  unfold Row.mend at hw ⊢
  exact ((mendUpto_spec row row.size).2 x hx (by omega)).2 hw

/-- **The repair's postcondition.** Every column of a mended row satisfies the
pair rule — for any input row at all, which is what lets every mutation end in
`Row.mend` and lets `Renderable` be an invariant rather than a hypothesis. -/
theorem mend_pairOk (row : Row) (x : Nat) (hx : x < row.size) :
    PairOk (Row.mend row) x := by
  have hsz : (Row.mend row).size = row.size := size_mend row
  refine ⟨fun h2 => ?_, fun h0 => ?_⟩
  · -- a base keeps its shadow, and that shadow is canonical
    have hhp := (halfPair_eq_false_iff (Row.mend row) x).mp (mend_halfPair row x hx)
    have hw : ((Row.mend row).at (x + 1)).width = 0 := hhp.1 h2
    have hb : x + 1 < (Row.mend row).size := by
      rcases Nat.lt_or_ge (x + 1) (Row.mend row).size with h | h
      · exact h
      · rw [at_of_size_le _ _ h] at hw
        exact absurd hw (by decide)
    have hsh := mend_shadow row (x + 1) (by rw [hsz] at hb; exact hb) hw
    have hx1 : x + 1 - 1 = x := by omega
    rw [hx1] at hsh
    exact hsh.2
  · have hhp := (halfPair_eq_false_iff (Row.mend row) x).mp (mend_halfPair row x hx)
    exact hhp.2 h0

/-! ### What the sweep leaves alone

A repaint reads back the cell it just wrote, so the sweep must be the identity
on a cell that is already well formed. Two cases cover every write: a narrow
glyph, and a wide glyph together with its canonical shadow. -/

private theorem mendUpto_keeps_narrow (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    ∀ n, ((List.range n).foldl (fun r y => Row.mendAt r y) row).at x = row.at x
  | 0 => rfl
  | n + 1 => by
    have ih := mendUpto_keeps_narrow row x h n
    have hstep : (List.range (n + 1)).foldl (fun r y => Row.mendAt r y) row
        = Row.mendAt ((List.range n).foldl (fun r y => Row.mendAt r y) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    rw [hstep]
    by_cases hn : n = x
    · subst hn
      have hw1 : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at n).width = 1 := by
        rw [ih]; exact h
      rw [mendAt_self_id _ _ (halfPair_of_width_one _ _ hw1) (by rw [hw1]; decide)]
      exact ih
    · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
      exact ih

/-- The sweep is the identity on a narrow cell. -/
theorem mend_keeps_narrow (row : Row) (x : Nat) (h : (row.at x).width = 1) :
    (Row.mend row).at x = row.at x := mendUpto_keeps_narrow row x h row.size

private theorem mendUpto_keeps_wide (row : Row) (x : Nat)
    (h2 : (row.at x).width = 2) (hs : row.at (x + 1) = Cell.shadow (row.at x)) :
    ∀ n, ((List.range n).foldl (fun r y => Row.mendAt r y) row).at x = row.at x
      ∧ ((List.range n).foldl (fun r y => Row.mendAt r y) row).at (x + 1) = row.at (x + 1)
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    have ih := mendUpto_keeps_wide row x h2 hs n
    have hstep : (List.range (n + 1)).foldl (fun r y => Row.mendAt r y) row
        = Row.mendAt ((List.range n).foldl (fun r y => Row.mendAt r y) row) n := by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    -- the two columns still hold a whole pair, so neither repair branch moves them
    have hb : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at x).width = 2 := by
      rw [ih.1]; exact h2
    have hsh : (((List.range n).foldl (fun r y => Row.mendAt r y) row).at (x + 1)).width = 0 := by
      rw [ih.2, hs]; rfl
    have hwhole : ((List.range n).foldl (fun r y => Row.mendAt r y) row).halfPair x = false := by
      rw [halfPair_eq_false_iff]
      exact ⟨fun _ => hsh, fun h0 => absurd (hb.symm.trans h0) (by decide)⟩
    have hwhole1 : ((List.range n).foldl (fun r y => Row.mendAt r y) row).halfPair (x + 1)
        = false := by
      rw [halfPair_eq_false_iff]
      refine ⟨fun hc => absurd (hsh.symm.trans hc) (by decide), fun _ => ⟨by omega, ?_⟩⟩
      simpa using hb
    rw [hstep]
    refine ⟨?_, ?_⟩
    · by_cases hn : n = x
      · subst hn
        rw [mendAt_self_id _ _ hwhole (by rw [hb]; decide)]
        exact ih.1
      · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
        exact ih.1
    · by_cases hn : n = x + 1
      · subst hn
        rw [mendAt_self_shadow _ _ ?_ hwhole1 hsh]
        · rw [show x + 1 - 1 = x from by omega, ih.1, hs]
        · -- the column is in range, or its cell would read as a width-1 default
          rcases Nat.lt_or_ge (x + 1)
            ((List.range (x + 1)).foldl (fun r y => Row.mendAt r y) row).size with hlt | hge
          · exact hlt
          · rw [at_of_size_le _ _ hge] at hsh
            exact absurd hsh (by decide)
      · rw [mendAt_ne _ _ _ (fun hc => hn hc.symm)]
        exact ih.2

/-- The sweep is the identity on a wide glyph and its canonical shadow. -/
theorem mend_keeps_wide (row : Row) (x : Nat)
    (h2 : (row.at x).width = 2) (hs : row.at (x + 1) = Cell.shadow (row.at x)) :
    (Row.mend row).at x = row.at x ∧ (Row.mend row).at (x + 1) = row.at (x + 1) :=
  mendUpto_keeps_wide row x h2 hs row.size

/-! ### Reading a mended row back out of the grid -/

theorem getCell_mendRow_same (v : Vt) (y x : Nat) (hy : y < v.grid.size) :
    (v.mendRow y).getCell x y = (v.getRow y).mend.at x := by
  unfold Vt.mendRow Vt.getCell Vt.getRow Row.at
  dsimp only
  rw [getD_set_self _ _ _ _ hy]

theorem getCell_mendRow_other (v : Vt) (y y' x : Nat) (h : y' ≠ y) :
    (v.mendRow y).getCell x y' = v.getCell x y' := by
  unfold Vt.mendRow Vt.getCell Vt.getRow
  dsimp only
  rw [getD_set_ne _ _ _ _ _ h]

/-! ### Write a cell, mend the row, read it back

What a repaint needs at every glyph. The write survives the sweep exactly when
it did not leave a half pair, and the two shapes a print produces are a narrow
cell and a wide base whose shadow the same print already wrote. -/

theorem grid_size_putCell (u : Vt) (x y : Nat) (c : Cell) :
    (u.putCell x y c).grid.size = u.grid.size := by
  unfold Vt.putCell
  simp

theorem getRow_putCell_same (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) :
    (u.putCell x y c).getRow y = (u.getRow y).setIfInBounds x c := by
  unfold Vt.putCell Vt.getRow
  dsimp only
  rw [getD_set_self _ _ _ _ hy]

theorem size_getRow_putCell (u : Vt) (x y : Nat) (c : Cell) (hy : y < u.grid.size) :
    ((u.putCell x y c).getRow y).size = (u.getRow y).size := by
  rw [getRow_putCell_same u x y c hy]
  simp

theorem getRow_putCell_self (u : Vt) (x y : Nat) (c : Cell)
    (hy : y < u.grid.size) (hx : x < (u.getRow y).size) :
    ((u.putCell x y c).getRow y).at x = c := by
  rw [getRow_putCell_same u x y c hy]
  unfold Row.at
  exact getD_set_self _ _ _ _ hx

/-- One narrow write survives the repair sweep. -/
theorem getCell_write_mendRow_narrow (u : Vt) (x y : Nat) (c : Cell)
    (hc : c.width = 1) (hy : y < u.grid.size) (hx : x < (u.getRow y).size) :
    ((u.putCell x y c).mendRow y).getCell x y = c := by
  have hcell := getRow_putCell_self u x y c hy hx
  rw [getCell_mendRow_same _ _ _ (by rw [grid_size_putCell]; exact hy)]
  rw [mend_keeps_narrow _ _ (by rw [hcell]; exact hc)]
  exact hcell

/-- A wide write and its shadow survive together. -/
theorem getCell_write_mendRow_wide (u : Vt) (x y : Nat) (cb : Cell)
    (h2 : cb.width = 2) (hy : y < u.grid.size) (hx : x + 1 < (u.getRow y).size) :
    (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).mendRow y).getCell x y = cb
      ∧ (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).mendRow y).getCell (x + 1) y
          = Cell.shadow cb := by
  have hy' : y < (u.putCell x y cb).grid.size := by rw [grid_size_putCell]; exact hy
  have hrow' : ((u.putCell x y cb).getRow y).size = (u.getRow y).size :=
    size_getRow_putCell u x y cb hy
  have hshadow := getRow_putCell_self (u.putCell x y cb) (x + 1) y (Cell.shadow cb) hy'
    (by rw [hrow']; exact hx)
  have hbase : (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).getRow y).at x = cb := by
    rw [getRow_putCell_same _ (x + 1) y _ hy']
    unfold Row.at
    rw [getD_set_ne _ _ _ _ _ (by omega)]
    have := getRow_putCell_self u x y cb hy (by omega)
    unfold Row.at at this
    exact this
  have hkeep := mend_keeps_wide
    (((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).getRow y) x
    (by rw [hbase]; exact h2) (by rw [hbase, hshadow])
  have hgs : y < ((u.putCell x y cb).putCell (x + 1) y (Cell.shadow cb)).grid.size := by
    rw [grid_size_putCell]; exact hy'
  rw [getCell_mendRow_same _ _ _ hgs, getCell_mendRow_same _ _ _ hgs]
  exact ⟨by rw [hkeep.1]; exact hbase, by rw [hkeep.2]; exact hshadow⟩

/-- A write plus repair on one row leaves every other row alone. -/
theorem getCell_write_mendRow_other (u : Vt) (x y : Nat) (c : Cell) (x' y' : Nat)
    (h : y' ≠ y) : ((u.putCell x y c).mendRow y).getCell x' y' = u.getCell x' y' := by
  rw [getCell_mendRow_other _ _ _ _ h]
  unfold Vt.putCell Vt.getCell Vt.getRow
  dsimp only
  exact congrArg (fun r => Array.getD r x' default) (getD_set_ne _ _ _ _ _ h)

/-! ### `print`, reduced to its write

Three shape lemmas so the per-glyph fidelity theorems never have to walk
`print`'s five stages. Each is stated with `v.cursor` and `v.pen` rather than
`v.clearPending`'s, which are definitionally the same — `clearPending` writes
only the wrap flag. -/

theorem getCell_printAdvance (v : Vt) (n x y : Nat) :
    (v.printAdvance n).getCell x y = v.getCell x y := by
  unfold Vt.getCell Vt.getRow
  rw [frame_printAdvance]

theorem print_narrow_eq {v : Vt} {ch : Char}
    (hpc : v.printChar ch = ch) (hw : charWidth ch = 1)
    (hins : v.modes.insert = false) (hpend : v.cursor.pending = false) :
    v.print ch = ((v.clearPending.putCell v.cursor.x v.cursor.y
        { base := ch, marks := [], width := 1, pen := v.pen }).mendRow
          v.cursor.y).printAdvance 1 := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [if_neg (by decide)]
  have h1 : v.printWrap = v.clearPending := by
    unfold Vt.printWrap; rw [if_neg (by simp [hpend])]
  have h2 : ∀ (w : Vt), w.printWideWrap 1 = w := by
    intro w; unfold Vt.printWideWrap; rw [if_neg (by simp)]
  have h3 : ∀ (w : Vt), w.modes.insert = false → w.printShift 1 = w := by
    intro w hw'; unfold Vt.printShift; rw [if_neg (by simp [hw'])]
  have h4 : ∀ (w : Vt) (c : Char), w.printPut c 1
      = (w.putCell w.cursor.x w.cursor.y
          { base := c, marks := [], width := 1, pen := w.pen }).mendRow w.cursor.y := by
    intro w c
    unfold Vt.printPut
    dsimp only
    rw [if_neg (by simp), if_neg (by decide)]
  rw [h1, h2, h3 _ (by rw [frame_clearPending]; exact hins), h4]
  rfl

theorem print_wide_eq {v : Vt} {ch : Char}
    (hpc : v.printChar ch = ch) (hw : charWidth ch = 2)
    (hins : v.modes.insert = false) (hpend : v.cursor.pending = false)
    (hfit : v.cursor.x + 1 < v.cols) :
    v.print ch = (((v.clearPending.putCell v.cursor.x v.cursor.y
        { base := ch, marks := [], width := 2, pen := v.pen }).putCell
          (v.cursor.x + 1) v.cursor.y
            (Cell.shadow { base := ch, marks := [], width := 2, pen := v.pen })).mendRow
              v.cursor.y).printAdvance 2 := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [if_neg (by decide)]
  have hcp : v.clearPending = { v with cursor := { v.cursor with pending := false } } := rfl
  have h1 : v.printWrap = v.clearPending := by
    unfold Vt.printWrap; rw [if_neg (by simp [hpend])]
  have h2 : v.clearPending.printWideWrap 2 = v.clearPending := by
    unfold Vt.printWideWrap
    rw [if_neg (by first | (simp [hcp]; done) | (simp [hcp]; omega))]
  have h3 : ∀ (w : Vt), w.modes.insert = false → w.printShift 2 = w := by
    intro w hw'; unfold Vt.printShift; rw [if_neg (by simp [hw'])]
  have h4 : ∀ (w : Vt) (c : Char), w.cursor.x + 1 < w.cols → w.printPut c 2
      = ((w.putCell w.cursor.x w.cursor.y
            { base := c, marks := [], width := 2, pen := w.pen }).putCell
          (w.cursor.x + 1) w.cursor.y
            (Cell.shadow { base := c, marks := [], width := 2, pen := w.pen })).mendRow
              w.cursor.y := by
    intro w c hf
    unfold Vt.printPut
    dsimp only
    rw [if_neg (by first | (simp; done) | (simp; omega)), if_pos (by decide)]
    rfl
  rw [h1, h2, h3 _ (by rw [frame_clearPending]; exact hins),
    h4 _ ch (by first | (simp [hcp]; done) | (simp [hcp]; omega))]
  rfl

theorem print_mark_eq {v : Vt} {m : Char}
    (hpc : v.printChar m = m) (hw : charWidth m = 0) (hpend : v.cursor.pending = false)
    (hx0 : v.cursor.x ≠ 0) (hnw : (v.getCell (v.cursor.x - 1) v.cursor.y).width ≠ 0)
    (hcap : (v.getCell (v.cursor.x - 1) v.cursor.y).marks.length < 8) :
    v.print m = (v.putCell (v.cursor.x - 1) v.cursor.y
      { v.getCell (v.cursor.x - 1) v.cursor.y with
        marks := (v.getCell (v.cursor.x - 1) v.cursor.y).marks ++ [m] }).mendRow v.cursor.y := by
  unfold Vt.print
  simp only [hpc, hw]
  rw [if_pos (by decide)]
  unfold Vt.printMark
  simp only [hpend, if_false, Bool.false_eq_true]
  rw [if_neg (show ¬((v.cursor.x == 0) = true) from by simp only [beq_iff_eq]; exact hx0)]
  rw [if_neg (show ¬(((v.getCell (v.cursor.x - 1) v.cursor.y).width == 0
      && v.cursor.x - 1 != 0) = true) from by
    simp only [Bool.and_eq_true, beq_iff_eq]
    exact fun h => hnw h.1)]
  rw [if_neg (show ¬((v.getCell (v.cursor.x - 1) v.cursor.y).marks.length ≥ 8) from by omega)]

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! ## §Renderable — the emulator only reaches grids a repaint can reproduce

`Good` bounds the emulator; this bounds what it *stores*. `Render.restore`
paints a grid by emitting one glyph per cell, so a cell it can reproduce must
hold a printable base of the width it claims, at most eight zero-width marks,
and — for a wide glyph — its shadow, carrying nothing of its own.

The point of proving this is negative: it means the replay theorem needs no side
conditions. Every clause is established at the write, not assumed: controls are
neutralized on store (`printableChar`), marks are capped and land on a base
(`printMark`), and pairs are repaired at every row mutation (`Row.mend`), so
`mend_pairOk` discharges the pair clause uniformly.

The predicate is stated over the grid *array* with a fixed default row, not over
`Vt.getRow` (whose default carries the current pen). That is what lets every
operation which does not touch `grid`/`cols`/`rows`/`altGrid` be discharged by
its frame — most of `csiDispatch` — instead of by its own lemma.
-/

/-- A codepoint the emitter reproduces as itself: not a C0 control and not DEL.

Stated concretely rather than as `printableChar c = c`, which would be a
tautology against the very function that establishes it — mutating
`printableChar` would weaken the predicate and the storer together and
`renderable_print` would still prove. This way such a mutation has to break
`printableChar_emittable`, which is a claim about `printableChar`'s *range*. -/
def Emittable (c : Char) : Prop := 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F

theorem printableChar_emittable (c : Char) : Emittable (printableChar c) := by
  unfold Emittable printableChar
  split
  · exact ⟨by decide, by decide⟩
  · rename_i h
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq, not_or,
      Nat.not_lt] at h
    exact ⟨h.1, h.2⟩

theorem emittable_space : Emittable ' ' := ⟨by decide, by decide⟩

/-- A cell a repaint can reproduce. -/
structure CellOk (c : Cell) : Prop where
  base : Emittable c.base
  width : c.width ≠ 0 → charWidth c.base = c.width
  marksLe : c.marks.length ≤ 8
  marks : ∀ m ∈ c.marks, charWidth m = 0 ∧ Emittable m

theorem cellOk_erased (p : Pen) : CellOk (Cell.erased p) :=
  ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩

theorem cellOk_shadow (c : Cell) : CellOk (Cell.shadow c) :=
  ⟨emittable_space, fun h => absurd rfl h, Nat.zero_le _, fun _ hm => nomatch hm⟩

theorem cellOk_default : CellOk (default : Cell) :=
  ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩

/-- A row a repaint can reproduce: exact width, reproducible cells, whole
pairs. Cells are quantified over *all* indices — an out-of-range read is a
default cell, which is fine — so no proof has to carry column bounds. -/
structure RowOk (cols : Nat) (row : Row) : Prop where
  size : row.size = cols
  cells : ∀ x, CellOk (row.at x)
  pairs : ∀ x, PairOk row x

/-- A width-1 row is trivially paired. -/
theorem pairOk_of_width_one {row : Row} (h : ∀ x, (row.at x).width = 1) (x : Nat) :
    PairOk row x :=
  ⟨fun h2 => absurd ((h x).symm.trans h2) (by decide),
   fun h0 => absurd ((h x).symm.trans h0) (by decide)⟩

theorem at_blankRow (cols : Nat) (p : Pen) (x : Nat) :
    (blankRow cols p).at x = if x < cols then Cell.erased p else default := by
  unfold Row.at blankRow
  by_cases h : x < cols
  · rw [if_pos h]
    simp [Array.getD, h]
  · rw [if_neg h]
    simp [Array.getD, h]

theorem rowOk_blankRow (cols : Nat) (p : Pen) : RowOk cols (blankRow cols p) := by
  refine ⟨by simp [blankRow], fun x => ?_, pairOk_of_width_one (fun x => ?_)⟩
  · rw [at_blankRow]
    split
    · exact cellOk_erased p
    · exact cellOk_default
  · rw [at_blankRow]
    split <;> rfl

/-- A grid a repaint can reproduce. -/
def GridOk (cols rows : Nat) (g : Array Row) : Prop :=
  g.size = rows ∧ ∀ y, RowOk cols (g.getD y (blankRow cols {}))

structure Renderable (v : Vt) : Prop where
  main : GridOk v.cols v.rows v.grid
  alt : ∀ g c p, v.altGrid = some (g, c, p) → GridOk v.cols v.rows g

theorem gridOk_replicate (cols rows : Nat) (p : Pen) :
    GridOk cols rows (Array.replicate rows (blankRow cols p)) := by
  refine ⟨by simp, fun y => ?_⟩
  by_cases h : y < rows
  · rw [show (Array.replicate rows (blankRow cols p)).getD y (blankRow cols {})
        = blankRow cols p from by simp [Array.getD, h]]
    exact rowOk_blankRow cols p
  · rw [show (Array.replicate rows (blankRow cols p)).getD y (blankRow cols {})
        = blankRow cols {} from by simp [Array.getD, h]]
    exact rowOk_blankRow cols {}

theorem renderable_init (cols rows : Nat) : Renderable (Vt.init cols rows) :=
  ⟨gridOk_replicate _ _ _, fun _ _ _ h => nomatch h⟩

/-! ### Frames discharge everything that does not write the grid -/

/-- An operation that leaves `grid`, `cols`, `rows` and `altGrid` alone
preserves `Renderable`. Most of `csiDispatch` is this. -/
theorem renderable_congr {v w : Vt} (h : Renderable v)
    (hg : w.grid = v.grid) (hc : w.cols = v.cols) (hr : w.rows = v.rows)
    (ha : w.altGrid = v.altGrid) : Renderable w := by
  refine ⟨by rw [hg, hc, hr]; exact h.main, fun g c p hs => ?_⟩
  rw [hc, hr]
  exact h.alt g c p (by rw [← ha]; exact hs)

/-! ### Writing cells -/

theorem cells_set {row : Row} (i : Nat) (c : Cell)
    (hrow : ∀ x, CellOk (row.at x)) (hc : CellOk c) :
    ∀ x, CellOk (Row.at (row.setIfInBounds i c) x) := by
  intro x
  unfold Row.at
  unfold Row.at at hrow
  by_cases hx : x = i
  · subst hx
    by_cases hb : x < row.size
    · rw [getD_set_self _ _ _ _ hb]; exact hc
    · rw [show row.setIfInBounds x c = row from by
        simp only [Array.setIfInBounds]; rw [dif_neg hb]]
      exact hrow x
  · rw [getD_set_ne _ _ _ _ _ hx]; exact hrow x

theorem cells_foldl {β : Type} {f : Row → β → Row}
    (hf : ∀ (r : Row) (b : β), (∀ x, CellOk (r.at x)) → ∀ x, CellOk ((f r b).at x)) :
    ∀ (l : List β) (row : Row), (∀ x, CellOk (row.at x)) → ∀ x, CellOk ((l.foldl f row).at x)
  | [], _, h => h
  | b :: l, row, h => by
    rw [List.foldl_cons]
    exact cells_foldl hf l (f row b) (hf row b h)

theorem cells_mendAt {row : Row} (i : Nat) (hrow : ∀ x, CellOk (row.at x)) :
    ∀ x, CellOk ((Row.mendAt row i).at x) := by
  unfold Row.mendAt
  repeat' split
  all_goals first
    | exact cells_set _ _ hrow (cellOk_erased _)
    | exact cells_set _ _ hrow (cellOk_shadow _)
    | exact hrow

theorem cells_mend {row : Row} (hrow : ∀ x, CellOk (row.at x)) :
    ∀ x, CellOk ((Row.mend row).at x) := by
  unfold Row.mend
  exact cells_foldl (fun r b h => cells_mendAt b h) _ row hrow

/-- **The row-mutation workhorse.** A row whose cells are reproducible becomes a
reproducible row once mended — pairs included, by `mend_pairOk`. Every row
mutation ends in `Row.mend`, so every row mutation ends here. -/
theorem rowOk_mend {cols : Nat} {row : Row} (hsize : row.size = cols)
    (hcells : ∀ x, CellOk (row.at x)) : RowOk cols (Row.mend row) := by
  refine ⟨by rw [size_mend]; exact hsize, cells_mend hcells, fun x => ?_⟩
  by_cases hx : x < row.size
  · exact mend_pairOk row x hx
  · -- past the end every read is a default width-1 cell
    have hz : ∀ j, row.size ≤ j → (Row.mend row).at j = default := by
      intro j hj
      exact at_of_size_le _ _ (by rw [size_mend]; exact hj)
    refine ⟨fun h2 => absurd ((by rw [hz x (by omega)] : (Row.mend row).at x = default) ▸ h2)
              (by decide), fun h0 => ?_⟩
    exact absurd ((by rw [hz x (by omega)] : (Row.mend row).at x = default) ▸ h0) (by decide)

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! ### One row at a time

Every cell-writing operation has the same shape: write into one row, then mend
it. `GridOkExcept y` is the state in between — every row reproducible except
row `y`, which has the right width and reproducible cells but no pair claim yet.
`mendRow` closes it. -/

theorem getD_of_lt {α} (g : Array α) (y : Nat) (d d' : α) (h : y < g.size) :
    g.getD y d = g.getD y d' := by
  simp [Array.getD, h]

def GridOkExcept (cols rows y : Nat) (g : Array Row) : Prop :=
  g.size = rows
    ∧ (∀ y', y' ≠ y → RowOk cols (g.getD y' (blankRow cols {})))
    ∧ (g.getD y (blankRow cols {})).size = cols
    ∧ (∀ x, CellOk ((g.getD y (blankRow cols {})).at x))

theorem gridOkExcept_of_gridOk {cols rows : Nat} {g : Array Row} (y : Nat)
    (h : GridOk cols rows g) : GridOkExcept cols rows y g :=
  ⟨h.1, fun y' _ => h.2 y', (h.2 y).size, (h.2 y).cells⟩

/-- Writing one reproducible cell into the excepted row keeps the shape. -/
theorem gridOkExcept_set {cols rows y : Nat} {g : Array Row}
    (h : GridOkExcept cols rows y g) (x : Nat) (c : Cell) (hc : CellOk c) (d : Row)
    (hd : y < g.size → g.getD y d = g.getD y (blankRow cols {})) :
    GridOkExcept cols rows y (g.setIfInBounds y ((g.getD y d).setIfInBounds x c)) := by
  obtain ⟨hsz, hother, hrsz, hcells⟩ := h
  refine ⟨by simp [hsz], fun y' hy' => ?_, ?_, ?_⟩
  · rw [getD_set_ne _ _ _ _ _ hy']; exact hother y' hy'
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb, Array.size_setIfInBounds, hd hb]; exact hrsz
    · rw [show g.setIfInBounds y ((g.getD y d).setIfInBounds x c) = g from by
        simp only [Array.setIfInBounds]; rw [dif_neg hb]]
      exact hrsz
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb, hd hb]
      exact cells_set _ _ hcells hc
    · rw [show g.setIfInBounds y ((g.getD y d).setIfInBounds x c) = g from by
        simp only [Array.setIfInBounds]; rw [dif_neg hb]]
      exact hcells

/-- Replacing the excepted row wholesale, with a row built from it. -/
theorem gridOkExcept_replace {cols rows y : Nat} {g : Array Row}
    (h : GridOkExcept cols rows y g) (r : Row)
    (hsz : r.size = cols) (hcells : ∀ x, CellOk (r.at x)) :
    GridOkExcept cols rows y (g.setIfInBounds y r) := by
  obtain ⟨hgsz, hother, hrsz, hocells⟩ := h
  refine ⟨by simp [hgsz], fun y' hy' => ?_, ?_, ?_⟩
  · rw [getD_set_ne _ _ _ _ _ hy']; exact hother y' hy'
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hsz
    · rw [show g.setIfInBounds y r = g from by
        simp only [Array.setIfInBounds]; rw [dif_neg hb]]
      exact hrsz
  · by_cases hb : y < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hcells
    · rw [show g.setIfInBounds y r = g from by
        simp only [Array.setIfInBounds]; rw [dif_neg hb]]
      exact hocells

/-- …and the repair closes it. -/
theorem gridOk_of_except {cols rows y : Nat} {g : Array Row}
    (h : GridOkExcept cols rows y g) :
    GridOk cols rows (g.setIfInBounds y (Row.mend (g.getD y (blankRow cols {})))) := by
  obtain ⟨hsz, hother, hrsz, hcells⟩ := h
  refine ⟨by simp [hsz], fun y' => ?_⟩
  by_cases hy' : y' = y
  · subst hy'
    by_cases hb : y' < g.size
    · rw [getD_set_self _ _ _ _ hb]
      exact rowOk_mend hrsz hcells
    · rw [show g.setIfInBounds y' (Row.mend (g.getD y' (blankRow cols {}))) = g from by
        simp only [Array.setIfInBounds]; rw [dif_neg hb]]
      -- out of range: the read is the default row, which is reproducible
      rw [show g.getD y' (blankRow cols {}) = blankRow cols {} from by
        simp [Array.getD, hb]]
      exact rowOk_blankRow cols {}
  · rw [getD_set_ne _ _ _ _ _ hy']
    exact hother y' hy'

/-! ### Folds that build a row -/

theorem size_foldl {β : Type} {f : Row → β → Row}
    (hf : ∀ (r : Row) (b : β), (f r b).size = r.size) :
    ∀ (l : List β) (row : Row), (l.foldl f row).size = row.size
  | [], _ => rfl
  | b :: l, row => by
    rw [List.foldl_cons, size_foldl hf l (f row b), hf row b]

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! ### Renderable is preserved by every operation

Two shapes cover the emulator. An operation that leaves `grid`, `cols`, `rows`
and `altGrid` alone is discharged by its frame (`renderable_congr`) — that is
most of `csiDispatch`. An operation that writes cells goes
`GridOk → GridOkExcept y → write → mendRow`, which is why every row mutation
ends in `Row.mend`. -/

/-- Same grid, dimensions and stash ⇒ same verdict, whatever else moved. -/
theorem renderable_of_gridOk {v w : Vt} (h : Renderable v)
    (hc : w.cols = v.cols) (hr : w.rows = v.rows) (ha : w.altGrid = v.altGrid)
    (hg : GridOk w.cols w.rows w.grid) : Renderable w :=
  ⟨hg, fun g c p hs => by rw [hc, hr]; exact h.alt g c p (by rw [← ha]; exact hs)⟩

theorem gridOkExcept_putCell {v : Vt} {y : Nat}
    (h : GridOkExcept v.cols v.rows y v.grid) (x : Nat) (c : Cell) (hc : CellOk c) :
    GridOkExcept v.cols v.rows y (v.putCell x y c).grid := by
  unfold Vt.putCell Vt.getRow
  dsimp only
  exact gridOkExcept_set h x c hc _ (fun hb => getD_of_lt _ _ _ _ hb)

theorem gridOk_mendRow {v : Vt} {y : Nat}
    (h : GridOkExcept v.cols v.rows y v.grid) :
    GridOk v.cols v.rows (v.mendRow y).grid := by
  have hkey : (v.mendRow y).grid
      = v.grid.setIfInBounds y (Row.mend (v.grid.getD y (blankRow v.cols {}))) := by
    unfold Vt.mendRow Vt.getRow
    dsimp only
    by_cases hb : y < v.grid.size
    · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    · simp only [Array.setIfInBounds]
      rw [dif_neg hb, dif_neg hb]
  rw [hkey]
  exact gridOk_of_except h

/-- The write-then-repair sandwich, as one step. -/
theorem renderable_write_mend {v : Vt} (h : Renderable v) (y : Nat)
    (f : Vt → Vt) (hf : GridOkExcept v.cols v.rows y (f v).grid)
    (hc : (f v).cols = v.cols) (hr : (f v).rows = v.rows)
    (ha : (f v).altGrid = v.altGrid) :
    Renderable ((f v).mendRow y) := by
  refine renderable_of_gridOk h (by rw [Vt.mendRow]; exact hc) (by rw [Vt.mendRow]; exact hr)
    (by rw [Vt.mendRow]; exact ha) ?_
  have := gridOk_mendRow (v := f v) (y := y) (by rw [hc, hr]; exact hf)
  rw [hc, hr] at this
  show GridOk ((f v).mendRow y).cols ((f v).mendRow y).rows ((f v).mendRow y).grid
  rw [show ((f v).mendRow y).cols = v.cols from by rw [Vt.mendRow]; exact hc,
    show ((f v).mendRow y).rows = v.rows from by rw [Vt.mendRow]; exact hr]
  exact this

/-! #### Printing -/

theorem renderable_printPut {v : Vt} (h : Renderable v) (ch : Char) (w : Nat)
    (hpc : Emittable ch) (hw : charWidth ch = w) :
    Renderable (v.printPut ch w) := by
  have hbase : CellOk { base := ch, marks := [], width := w, pen := v.pen } :=
    ⟨hpc, fun _ => hw, Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hblank : CellOk { base := ' ', marks := [], width := 1, pen := v.pen } :=
    ⟨emittable_space, fun _ => rfl, Nat.zero_le _, fun _ hm => nomatch hm⟩
  have hshadow : CellOk { base := ' ', marks := [], width := 0, pen := v.pen } :=
    ⟨emittable_space, fun hz => absurd rfl hz, Nat.zero_le _,
      fun _ hm => nomatch hm⟩
  unfold Vt.printPut
  dsimp only
  split
  · exact renderable_write_mend h _ (fun u => u.putCell v.cursor.x v.cursor.y _)
      (gridOkExcept_putCell (gridOkExcept_of_gridOk _ h.main) _ _ hblank) rfl rfl rfl
  · split
    · exact renderable_write_mend h _
        (fun u => (u.putCell v.cursor.x v.cursor.y _).putCell (v.cursor.x + 1) v.cursor.y _)
        (gridOkExcept_putCell (gridOkExcept_putCell
          (gridOkExcept_of_gridOk _ h.main) _ _ hbase) _ _ hshadow) rfl rfl rfl
    · exact renderable_write_mend h _ (fun u => u.putCell v.cursor.x v.cursor.y _)
        (gridOkExcept_putCell (gridOkExcept_of_gridOk _ h.main) _ _ hbase) rfl rfl rfl

/-- Every cell of a renderable emulator is reproducible, including the
out-of-range reads that `getCell` answers with a default. -/
theorem cellOk_getCell {v : Vt} (h : Renderable v) (x y : Nat) : CellOk (v.getCell x y) := by
  unfold Vt.getCell Vt.getRow
  by_cases hb : y < v.grid.size
  · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    exact (h.main.2 y).cells _
  · rw [show v.grid.getD y (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
      simp [Array.getD, hb]]
    exact (rowOk_blankRow v.cols v.pen).cells _

/-- Appending one legal mark to a cell, then repairing the row. Stated over an
arbitrary column so `printMark`'s shadow redirect does not have to be unfolded
inside the proof. -/
theorem renderable_addMark {v : Vt} (h : Renderable v) (cx y : Nat) (ch : Char)
    (hpc : Emittable ch) (hw : charWidth ch = 0)
    (hcap : (v.getCell cx y).marks.length < 8) :
    Renderable ((v.putCell cx y { v.getCell cx y with
      marks := (v.getCell cx y).marks ++ [ch] }).mendRow y) := by
  have hold := cellOk_getCell h cx y
  refine renderable_write_mend h y (fun u => u.putCell cx y _)
    (gridOkExcept_putCell (gridOkExcept_of_gridOk y h.main) cx _ ?_) rfl rfl rfl
  refine ⟨hold.base, hold.width, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]
    omega
  · intro m hm
    rcases List.mem_append.mp hm with hm' | hm'
    · exact hold.marks m hm'
    · rw [show m = ch from by simpa using hm']
      exact ⟨hw, hpc⟩

theorem renderable_printMark {v : Vt} (h : Renderable v) (ch : Char)
    (hpc : Emittable ch) (hw : charWidth ch = 0) :
    Renderable (v.printMark ch) := by
  unfold Vt.printMark
  dsimp only
  repeat' split
  all_goals first
    | exact h
    | exact renderable_addMark h _ _ _ hpc hw (by omega)

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! #### Whole-row moves, and the stages around a write -/

theorem rowOk_getRow {v : Vt} (h : Renderable v) (y : Nat) : RowOk v.cols (v.getRow y) := by
  unfold Vt.getRow
  by_cases hb : y < v.grid.size
  · rw [getD_of_lt v.grid y (blankRow v.cols v.pen) (blankRow v.cols {}) hb]
    exact h.main.2 y
  · rw [show v.grid.getD y (blankRow v.cols v.pen) = blankRow v.cols v.pen from by
      simp [Array.getD, hb]]
    exact rowOk_blankRow v.cols v.pen

theorem gridOk_set_row {cols rows : Nat} {g : Array Row} (h : GridOk cols rows g)
    (y : Nat) (r : Row) (hr : RowOk cols r) : GridOk cols rows (g.setIfInBounds y r) := by
  refine ⟨by simp [h.1], fun y' => ?_⟩
  by_cases hy' : y' = y
  · subst hy'
    by_cases hb : y' < g.size
    · rw [getD_set_self _ _ _ _ hb]; exact hr
    · rw [show g.setIfInBounds y' r = g from by
        simp only [Array.setIfInBounds]; rw [dif_neg hb]]
      exact h.2 y'
  · rw [getD_set_ne _ _ _ _ _ hy']; exact h.2 y'

theorem gridOk_foldl {cols rows : Nat} {β : Type} {f : Array Row → β → Array Row}
    (hf : ∀ (g : Array Row) (b : β), GridOk cols rows g → GridOk cols rows (f g b)) :
    ∀ (l : List β) (g : Array Row), GridOk cols rows g → GridOk cols rows (l.foldl f g)
  | [], _, h => h
  | b :: l, g, h => by
    rw [List.foldl_cons]
    exact gridOk_foldl hf l (f g b) (hf g b h)

/-- Scrolling moves whole rows and blanks one, so it never breaks a pair. The
scrollback push is outside `Renderable`'s scope (a repaint paints the screen). -/
theorem renderable_scrollUpIn {v : Vt} (h : Renderable v) (t b : Nat) (a : Bool) :
    Renderable (v.scrollUpIn t b a) := by
  have hgrid : GridOk v.cols v.rows (v.scrollUpIn t b a).grid := by
    have hstep : GridOk v.cols v.rows
        ((List.range (b - t)).foldl
          (fun g i => g.setIfInBounds (t + i) (v.getRow (t + i + 1))) v.grid) :=
      gridOk_foldl (fun g i hg => gridOk_set_row hg _ _ (rowOk_getRow h _)) _ _ h.main
    have hblank := gridOk_set_row hstep b (blankRow v.cols v.pen) (rowOk_blankRow _ _)
    unfold Vt.scrollUpIn
    dsimp only
    split <;> exact hblank
  refine renderable_of_gridOk h ?_ ?_ ?_ ?_
  · rw [frame_scrollUpIn]
  · rw [frame_scrollUpIn]
  · rw [frame_scrollUpIn]
  · rw [show (v.scrollUpIn t b a).cols = v.cols from by rw [frame_scrollUpIn],
      show (v.scrollUpIn t b a).rows = v.rows from by rw [frame_scrollUpIn]]
    exact hgrid

theorem renderable_scrollDownIn {v : Vt} (h : Renderable v) (t b : Nat) :
    Renderable (v.scrollDownIn t b) := by
  have hgrid : GridOk v.cols v.rows (v.scrollDownIn t b).grid := by
    have hstep : GridOk v.cols v.rows
        ((List.range (b - t)).foldl
          (fun g i => g.setIfInBounds (b - i) (v.getRow (b - i - 1))) v.grid) :=
      gridOk_foldl (fun g i hg => gridOk_set_row hg _ _ (rowOk_getRow h _)) _ _ h.main
    exact gridOk_set_row hstep t (blankRow v.cols v.pen) (rowOk_blankRow _ _)
  refine renderable_of_gridOk h ?_ ?_ ?_ ?_
  · rw [frame_scrollDownIn]
  · rw [frame_scrollDownIn]
  · rw [frame_scrollDownIn]
  · rw [show (v.scrollDownIn t b).cols = v.cols from by rw [frame_scrollDownIn],
      show (v.scrollDownIn t b).rows = v.rows from by rw [frame_scrollDownIn]]
    exact hgrid

theorem renderable_scrollUp {v : Vt} (h : Renderable v) : Renderable v.scrollUp :=
  renderable_scrollUpIn h _ _ _

theorem renderable_scrollDown {v : Vt} (h : Renderable v) : Renderable v.scrollDown :=
  renderable_scrollDownIn h _ _

/-- Cursor-only motion: the frame says the grid, dimensions and stash are
untouched, so the verdict carries. -/
theorem renderable_clearPending {v : Vt} (h : Renderable v) : Renderable v.clearPending :=
  renderable_congr h rfl rfl rfl rfl

theorem renderable_carriageReturn {v : Vt} (h : Renderable v) : Renderable v.carriageReturn :=
  renderable_congr h rfl rfl rfl rfl

theorem renderable_printAdvance {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printAdvance w) := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_printAdvance]

theorem renderable_lineFeed {v : Vt} (h : Renderable v) : Renderable v.lineFeed := by
  have h' := renderable_clearPending h
  unfold Vt.lineFeed
  dsimp only
  split
  · exact renderable_scrollUp h'
  · split
    · exact renderable_congr h' rfl rfl rfl rfl
    · exact h'

theorem renderable_reverseIndex {v : Vt} (h : Renderable v) : Renderable v.reverseIndex := by
  have h' := renderable_clearPending h
  unfold Vt.reverseIndex
  dsimp only
  split
  · exact renderable_scrollDown h'
  · exact renderable_congr h' rfl rfl rfl rfl

theorem renderable_printWrap {v : Vt} (h : Renderable v) : Renderable v.printWrap := by
  unfold Vt.printWrap
  split
  · exact renderable_lineFeed (renderable_carriageReturn h)
  · exact renderable_clearPending h

theorem renderable_printWideWrap {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printWideWrap w) := by
  unfold Vt.printWideWrap
  split
  · exact renderable_lineFeed (renderable_carriageReturn h)
  · exact h

/-- Insert mode shifts cells within a row and then repairs it. Every cell it
writes came from the same row, so `CellOk` carries; the width bookkeeping is
`Row.mend`'s. -/
theorem renderable_printShift {v : Vt} (h : Renderable v) (w : Nat) :
    Renderable (v.printShift w) := by
  unfold Vt.printShift
  dsimp only
  split
  · rename_i hins
    refine renderable_of_gridOk h rfl rfl rfl ?_
    show GridOk v.cols v.rows (v.grid.setIfInBounds v.cursor.y (Row.mend _))
    refine gridOk_set_row h.main _ _ (rowOk_mend ?_ ?_)
    · exact size_foldl (fun r b => by simp) _ _ |>.trans (rowOk_getRow h v.cursor.y).size
    · exact cells_foldl (fun r b hr =>
        cells_set _ _ hr ((rowOk_getRow h v.cursor.y).cells _)) _ _
        (rowOk_getRow h v.cursor.y).cells
  · exact h

/-- **Printing preserves `Renderable`.** The stored codepoint is
`printableChar`-stable by construction, which is what `CellOk.base` needs, and
its width is `charWidth` of exactly that codepoint. -/
theorem renderable_print {v : Vt} (h : Renderable v) (ch : Char) :
    Renderable (v.print ch) := by
  have hpc' : ∀ (u : Vt) (c : Char), Emittable (u.printChar c) := by
    intro u c
    unfold Vt.printChar
    exact printableChar_emittable _
  unfold Vt.print
  dsimp only
  split
  · rename_i h0
    exact renderable_printMark h _ (hpc' v ch) (by simpa using h0)
  · exact renderable_printAdvance (renderable_printPut
      (renderable_printShift (renderable_printWideWrap (renderable_printWrap h) _) _) _ _
        (hpc' v ch) rfl) _

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! #### Erase, insert, delete -/

/-- Every row mutation has the same skeleton: fold writes over the row, mend it,
put it back. Only the written cells differ, and each is either copied from the
same row or an erased blank. -/
theorem renderable_row_mutation {v : Vt} (h : Renderable v) {β : Type}
    (y : Nat) (f : Row → β → Row) (l : List β)
    (hsz : ∀ (r : Row) (b : β), (f r b).size = r.size)
    (hc : ∀ (r : Row) (b : β), (∀ x, CellOk (r.at x)) → ∀ x, CellOk ((f r b).at x)) :
    GridOk v.cols v.rows
      (v.grid.setIfInBounds y (Row.mend (l.foldl f (v.getRow y)))) := by
  refine gridOk_set_row h.main _ _ (rowOk_mend ?_ ?_)
  · exact (size_foldl hsz l (v.getRow y)).trans (rowOk_getRow h y).size
  · exact cells_foldl hc l (v.getRow y) (rowOk_getRow h y).cells

theorem renderable_eraseRowSpan {v : Vt} (h : Renderable v) (y a b : Nat) :
    Renderable (v.eraseRowSpan y a b) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h y _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (cellOk_erased _))

theorem renderable_eraseChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.eraseChars n) := renderable_eraseRowSpan h _ _ _

theorem renderable_eraseLine {v : Vt} (h : Renderable v) (m : Nat) :
    Renderable (v.eraseLine m) := by
  unfold Vt.eraseLine
  split <;> exact renderable_eraseRowSpan h _ _ _

theorem renderable_foldl {β : Type} {f : Vt → β → Vt}
    (hf : ∀ (u : Vt) (b : β), Renderable u → Renderable (f u b)) :
    ∀ (l : List β) (v : Vt), Renderable v → Renderable (l.foldl f v)
  | [], _, h => h
  | b :: l, v, h => by
    rw [List.foldl_cons]
    exact renderable_foldl hf l (f v b) (hf v b h)

theorem renderable_eraseScreen {v : Vt} (h : Renderable v) (m : Nat) :
    Renderable (v.eraseScreen m) := by
  unfold Vt.eraseScreen
  split
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _
      (renderable_eraseLine h _)
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _
      (renderable_eraseLine h _)
  · -- ED 3 also drops scrollback, which `Renderable` does not watch
    exact renderable_congr
      (renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _ h)
      rfl rfl rfl rfl
  · exact renderable_foldl (fun u i hu => renderable_eraseRowSpan hu _ _ _) _ _ h

theorem renderable_deleteChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.deleteChars n) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h _ _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (by
      split
      · exact (rowOk_getRow h v.cursor.y).cells _
      · exact cellOk_erased _))

theorem renderable_insertChars {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.insertChars n) := by
  refine renderable_of_gridOk h rfl rfl rfl ?_
  exact renderable_row_mutation h _ _ _ (fun r b => by simp)
    (fun r b hr => cells_set _ _ hr (by
      split
      · exact (rowOk_getRow h v.cursor.y).cells _
      · exact cellOk_erased _))

theorem renderable_insertLines {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.insertLines n) := by
  unfold Vt.insertLines
  split
  · exact h
  · exact renderable_foldl (fun u i hu => renderable_scrollDownIn hu _ _) _ _ h

theorem renderable_deleteLines {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.deleteLines n) := by
  unfold Vt.deleteLines
  split
  · exact h
  · exact renderable_foldl (fun u i hu => renderable_scrollUpIn hu _ _ _) _ _ h

/-! #### Cursor, pen, modes, and the alt screen -/

theorem renderable_moveTo {v : Vt} (h : Renderable v) (x y : Nat) :
    Renderable (v.moveTo x y) := renderable_congr h rfl rfl rfl rfl

/-- Setting a field and then homing the cursor, as one step. Stated over the
*result* record so `csiDispatch`'s `DECSTBM` and `setMode`'s `DECOM` arms unify
with it instead of with the incoming state. -/
theorem renderable_moveTo_congr {v w : Vt} (h : Renderable v)
    (hg : w.grid = v.grid) (hc : w.cols = v.cols) (hr : w.rows = v.rows)
    (ha : w.altGrid = v.altGrid) (x y : Nat) : Renderable (w.moveTo x y) :=
  renderable_moveTo (renderable_congr h hg hc hr ha) x y

theorem renderable_moveRel {v : Vt} (h : Renderable v) (dx dy : Int) :
    Renderable (v.moveRel dx dy) := renderable_congr h rfl rfl rfl rfl

theorem renderable_setCol {v : Vt} (h : Renderable v) (x : Nat) :
    Renderable (v.setCol x) := renderable_congr h rfl rfl rfl rfl

theorem renderable_applySgr {v : Vt} (h : Renderable v) (ps : List (Nat × Bool)) :
    Renderable (v.applySgr ps) := renderable_congr h rfl rfl rfl rfl

theorem renderable_backspace {v : Vt} (h : Renderable v) : Renderable v.backspace := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_backspace]

theorem renderable_tab {v : Vt} (h : Renderable v) : Renderable v.tab := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_tab]

theorem renderable_backTab {v : Vt} (h : Renderable v) : Renderable v.backTab := by
  refine renderable_congr h ?_ ?_ ?_ ?_ <;> rw [frame_backTab]

theorem renderable_enterAlt {v : Vt} (h : Renderable v) (s : Bool) :
    Renderable (v.enterAlt s) := by
  unfold Vt.enterAlt
  split
  · exact h
  · refine ⟨gridOk_replicate _ _ _, fun g c p hs => ?_⟩
    -- the stash is the main grid we just left
    simp only [Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hg, -, -⟩ := hs
    subst hg
    exact h.main

theorem renderable_leaveAlt {v : Vt} (h : Renderable v) (s : Bool) :
    Renderable (v.leaveAlt s) := by
  unfold Vt.leaveAlt
  split
  · exact h
  · rename_i g cur pen heq
    exact ⟨h.alt g cur pen heq, fun _ _ _ hs => nomatch hs⟩

theorem renderable_setMode {v : Vt} (h : Renderable v) (priv : Bool) (n : Nat) (on : Bool) :
    Renderable (v.setMode priv n on) := by
  unfold Vt.setMode
  split <;> split
  all_goals first
    | exact h
    | exact renderable_congr h rfl rfl rfl rfl
    | (refine renderable_moveTo_congr h ?_ ?_ ?_ ?_ 0 0 <;> rfl)
    | (split <;> first
        | exact renderable_enterAlt h _
        | exact renderable_leaveAlt h _
        | exact renderable_congr h rfl rfl rfl rfl)

/-! #### Dispatch, and the parser -/

set_option maxHeartbeats 1000000 in
theorem renderable_csiDispatch {v : Vt} (h : Renderable v) (s : CsiState) (final : UInt8) :
    Renderable (v.csiDispatch s final) := by
  unfold Vt.csiDispatch
  split
  · exact h
  · split
    all_goals first
      | exact h
      | exact renderable_congr h rfl rfl rfl rfl
      | exact renderable_insertChars h _
      | exact renderable_moveRel h _ _
      | exact renderable_carriageReturn (renderable_moveRel h _ _)
      | exact renderable_setCol h _
      | exact renderable_moveTo h _ _
      | exact renderable_eraseScreen h _
      | exact renderable_eraseLine h _
      | exact renderable_insertLines h _
      | exact renderable_deleteLines h _
      | exact renderable_deleteChars h _
      | exact renderable_eraseChars h _
      | exact renderable_setMode h _ _ _
      | exact renderable_foldl (fun u i hu => renderable_tab hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_scrollUp hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_scrollDown hu) _ _ h
      | exact renderable_foldl (fun u i hu => renderable_backTab hu) _ _ h
      | (split <;> first
          | exact renderable_applySgr h _
          | exact renderable_congr h rfl rfl rfl rfl
          | exact h
          | (dsimp only
             split <;> first
              | exact h
              | (refine renderable_moveTo_congr h ?_ ?_ ?_ ?_ 0 0 <;> rfl)))

theorem renderable_acceptChar {v : Vt} (h : Renderable v) (n : Nat) :
    Renderable (v.acceptChar n) := by
  unfold Vt.acceptChar
  split <;> exact renderable_print h _

theorem renderable_ctl {v : Vt} (h : Renderable v) (b : UInt8) : Renderable (v.ctl b) := by
  unfold Vt.ctl
  split
  all_goals first
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_backspace h
    | exact renderable_tab h
    | exact renderable_lineFeed h
    | exact renderable_carriageReturn h
    | exact h

theorem renderable_oscFinish {v : Vt} (h : Renderable v) (acc : Array UInt8) :
    Renderable (v.oscFinish acc) := by
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

theorem renderable_csiFinish {v : Vt} (h : Renderable v) (s : CsiState) (final : UInt8) :
    Renderable (v.csiFinish s final) := by
  unfold Vt.csiFinish
  exact renderable_congr (renderable_csiDispatch h _ _) rfl rfl rfl rfl

/-- Setting the UTF-8 accumulator and then accepting a codepoint. Named for the
same reason as `renderable_moveTo_congr`: `stepGround`'s continuation-byte arm
applies `acceptChar` to a *record*, and an `exact` with `rfl` arguments would fix
the implicit state to the incoming one instead. -/
theorem renderable_acceptChar_congr {v w : Vt} (h : Renderable v)
    (hg : w.grid = v.grid) (hc : w.cols = v.cols) (hr : w.rows = v.rows)
    (ha : w.altGrid = v.altGrid) (n : Nat) : Renderable (w.acceptChar n) :=
  renderable_acceptChar (renderable_congr h hg hc hr ha) n

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
theorem renderable_stepGround {v : Vt} (h : Renderable v) (b : UInt8) :
    Renderable (v.stepGround b) := by
  unfold Vt.stepGround
  repeat' split
  all_goals first
    | exact h
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_ctl h _
    | exact renderable_acceptChar h _
    | (refine renderable_acceptChar_congr h ?_ ?_ ?_ ?_ _ <;> rfl)

theorem renderable_stepEsc {v : Vt} (h : Renderable v) (b : UInt8) :
    Renderable (v.stepEsc b) := by
  unfold Vt.stepEsc
  split
  all_goals first
    | exact h
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_congr (renderable_lineFeed h) rfl rfl rfl rfl
    | exact renderable_congr (renderable_lineFeed (renderable_carriageReturn h)) rfl rfl rfl rfl
    | exact renderable_congr (renderable_reverseIndex h) rfl rfl rfl rfl
    | -- RIS: a fresh screen of the same dimensions
      (dsimp only
       split <;> exact renderable_congr (renderable_init v.cols v.rows) rfl rfl rfl rfl)
    | (split <;> exact renderable_congr h rfl rfl rfl rfl)

theorem renderable_stepEscInter {v : Vt} (h : Renderable v) (i b : UInt8) :
    Renderable (v.stepEscInter i b) := by
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

theorem renderable_stepCsi {v : Vt} (h : Renderable v) (s : CsiState) (b : UInt8) :
    Renderable (v.stepCsi s b) := by
  unfold Vt.stepCsi
  repeat' split
  all_goals first
    | exact renderable_congr h rfl rfl rfl rfl
    | exact renderable_csiFinish h _ _
    | exact renderable_ctl h _

theorem renderable_stepOsc {v : Vt} (h : Renderable v) (acc : Array UInt8) (e : Bool)
    (b : UInt8) : Renderable (v.stepOsc acc e b) := by
  unfold Vt.stepOsc
  repeat' split
  all_goals first
    | exact renderable_oscFinish h _
    | exact renderable_congr h rfl rfl rfl rfl

theorem renderable_stepStr {v : Vt} (h : Renderable v) (e : Bool) (b : UInt8) :
    Renderable (v.stepStr e b) := by
  unfold Vt.stepStr
  repeat' split
  all_goals exact renderable_congr h rfl rfl rfl rfl

/-- **§Renderable is preserved by every byte.** With `renderable_init` this
covers every state the daemon can hold: the emulator never stores a grid the row
painter cannot express, for any input at all. -/
theorem renderable_step {v : Vt} (h : Renderable v) (b : UInt8) : Renderable (v.step b) := by
  unfold Vt.step Vt.abortUtf8
  dsimp only
  have h' : Renderable (if v.u8need > 0 && (b < 0x80 || b ≥ 0xC0) then
      { v with u8need := 0, u8acc := 0 } else v) := by
    split
    · exact renderable_congr h rfl rfl rfl rfl
    · exact h
  split
  all_goals first
    | exact renderable_stepGround h' _
    | exact renderable_stepEsc h' _
    | exact renderable_stepEscInter h' _ _
    | exact renderable_stepCsi h' _ _
    | exact renderable_stepOsc h' _ _ _
    | exact renderable_stepStr h' _ _

/-- The stream form. -/
theorem renderable_feed {v : Vt} (h : Renderable v) (bytes : List UInt8) :
    Renderable (v.feed bytes) :=
  renderable_foldl (fun _ b hu => renderable_step hu b) bytes v h

/-- Forgetting partial parser state cannot change the screen. -/
theorem renderable_quiesce {v : Vt} (h : Renderable v) : Renderable v.quiesce :=
  renderable_congr h rfl rfl rfl rfl

end Zmx.Core.Vt

namespace Zmx.Core.Vt
/-! #### Resize

The last operation that writes cells. Both `resizeRow` and `Vt.resize`'s `fit`
are maps over their target range, so each needs one lemma about `getD` of a
mapped `Array.range` and nothing about array splicing. -/

/-- Reading a mapped `Array.range`: in range it is the function, out of range the
default. Generic in the element type, because `resizeRow` maps over cells and
`Vt.resize`'s `fit` maps over rows. -/
theorem getD_map_range {α : Type} (f : Nat → α) (n x : Nat) (d : α) :
    ((Array.range n).map f).getD x d = if x < n then f x else d := by
  by_cases hb : x < n
  · rw [if_pos hb]
    have hsz : x < ((Array.range n).map f).size := by simp [hb]
    rw [Array.getD, dif_pos hsz]
    simp
  · rw [if_neg hb]
    have hsz : ¬ x < ((Array.range n).map f).size := by simpa using hb
    rw [Array.getD, dif_neg hsz]

theorem cells_map_range (f : Nat → Cell) (n : Nat) (hf : ∀ i, CellOk (f i)) :
    ∀ x, CellOk (Row.at ((Array.range n).map f) x) := by
  intro x
  unfold Row.at
  rw [getD_map_range]
  split
  · exact hf x
  · exact cellOk_default

theorem rowOk_resizeRow (row : Row) (c : Nat) (p : Pen) (h : ∀ x, CellOk (row.at x)) :
    RowOk c (resizeRow row c p) := by
  unfold resizeRow
  refine rowOk_mend (by simp) (cells_map_range _ _ (fun i => ?_))
  by_cases hi : i < row.size
  · rw [if_pos hi]
    exact h i
  · rw [if_neg hi]
    exact cellOk_erased p

/-- A grid re-fitted to `c × r` is reproducible: each row is an old row at the
new width, or a blank. -/
theorem gridOk_fit {cols : Nat} {g : Array Row} (c r : Nat)
    (h : ∀ y, RowOk cols (g.getD y (blankRow cols {}))) :
    GridOk c r ((Array.range r).map (fun j =>
      let src := if g.size ≥ r then g.size - r + j else j
      if src < g.size then resizeRow (g.getD src #[]) c {} else blankRow c {})) := by
  -- a source row that exists is one of `g`'s, whatever default the read carries
  have hsrc : ∀ (j : Nat), j < g.size → ∀ x, CellOk (Row.at (g.getD j (#[] : Row)) x) := by
    intro j hj x
    have hc := (h j).cells x
    unfold Row.at at hc ⊢
    rw [getD_of_lt g j (blankRow cols {}) (#[] : Row) hj] at hc
    exact hc
  refine ⟨by simp, fun y => ?_⟩
  rw [getD_map_range]
  by_cases hy : y < r
  · rw [if_pos hy]
    dsimp only
    by_cases hge : g.size ≥ r
    · rw [if_pos hge]
      by_cases hb : g.size - r + y < g.size
      · rw [if_pos hb]
        exact rowOk_resizeRow _ _ _ (hsrc _ hb)
      · rw [if_neg hb]
        exact rowOk_blankRow c {}
    · rw [if_neg hge]
      by_cases hb : y < g.size
      · rw [if_pos hb]
        exact rowOk_resizeRow _ _ _ (hsrc _ hb)
      · rw [if_neg hb]
        exact rowOk_blankRow c {}
  · rw [if_neg hy]
    exact rowOk_blankRow c {}

theorem renderable_resize {v : Vt} (h : Renderable v) (cols rows : Nat) :
    Renderable (v.resize cols rows) := by
  unfold Vt.resize
  refine ⟨gridOk_fit _ _ h.main.2, fun g c p hs => ?_⟩
  dsimp only at hs
  rcases hv : v.altGrid with - | x
  · rw [hv] at hs; exact nomatch hs
  · obtain ⟨g0, c0, p0⟩ := x
    rw [hv] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨hg, -, -⟩ := hs
    subst hg
    exact gridOk_fit _ _ (h.alt g0 c0 p0 hv).2

/-! ### §LiveReachable — the states a running session can actually hold

The predicate a replay theorem may assume: the least set containing a fresh
emulator and closed under the three things a live session does to one — feed pty
bytes, resize on attach, and forget partial parser state (what a checkpoint
save/load does). Fidelity is claimed for these and not for an arbitrary decoded
checkpoint, which no theorem can vouch for. -/

inductive LiveReachableVt : Vt → Prop where
  | init (cols rows : Nat) : LiveReachableVt (Vt.init cols rows)
  | feed {v : Vt} (h : LiveReachableVt v) (bytes : List UInt8) : LiveReachableVt (v.feed bytes)
  | resize {v : Vt} (h : LiveReachableVt v) (cols rows : Nat) :
      LiveReachableVt (v.resize cols rows)
  | quiesce {v : Vt} (h : LiveReachableVt v) : LiveReachableVt v.quiesce

/-- **The shape hypothesis, discharged.** Every state a live session can hold is
one the row painter can express — so the replay theorem needs no side condition
on the grid, and cannot be satisfied vacuously by excluding awkward states. -/
theorem renderable_of_liveReachable {v : Vt} (h : LiveReachableVt v) : Renderable v := by
  induction h with
  | init c r => exact renderable_init c r
  | feed _ bytes ih => exact renderable_feed ih bytes
  | resize _ c r ih => exact renderable_resize ih c r
  | quiesce _ ih => exact renderable_quiesce ih

/-- …and `Good` likewise, so the two invariants travel together. -/
theorem good_of_liveReachable {v : Vt} (h : LiveReachableVt v) : Good v := by
  induction h with
  | init c r => exact good_init c r
  | feed _ bytes ih => exact Good.feed bytes ih
  | resize _ c r ih => exact Good.resize c r ih
  | quiesce _ ih => exact Good.set_ground (Good.set_u8 0 0 (by omega) ih)

end Zmx.Core.Vt
