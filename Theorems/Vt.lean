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
          | (dsimp only
             split <;> first
              | exact h'
              | (rename_i hg
                 simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
                 refine moveTo 0 0
                   ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, ?_, ?_, sb, u8, hcsi, hosc⟩ <;>
                   (dsimp only; omega))))


/-! ## Printing -/

theorem putCell {v : Vt} (x y : Nat) (c : Cell) (h : Good v) : Good (v.putCell x y c) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  exact ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

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
  · exact putCell _ _ _ (putCell _ _ _ h)
  · exact putCell _ _ _ h

theorem printAdvance {v : Vt} (w : Nat) (h : Good v) : Good (v.printAdvance w) := by
  obtain ⟨cp, rp, cl, rl, cx, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩ := h
  unfold Vt.printAdvance
  dsimp only
  split
  · exact ⟨cp, rp, cl, rl, by dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩
  · exact ⟨cp, rp, cl, rl, by dsimp only; omega, cy, sx, sy, ac, tl, bl, sb, u8, hcsi, hosc⟩

theorem print {v : Vt} (ch : Char) (h : Good v) : Good (v.print ch) := by
  unfold Vt.print
  dsimp only
  split <;> split
  all_goals first
    | exact putCell _ _ _ h
    | exact printAdvance _ (printPut _ _ (printShift _ (printWideWrap _ (printWrap h))))
    | (repeat' split
       all_goals first
         | exact h
         | exact putCell _ _ _ h)

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
collapse is real. Converting the rest is mechanical and is the recorded
next simplification (specs/bigger-theorems.md).
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

theorem frame_printPut (v : Vt) (ch : Char) (w : Nat) :
    v.printPut ch w = { v with grid := (v.printPut ch w).grid } := by
  unfold Vt.printPut Vt.putCell; dsimp only; split <;> rfl

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

theorem ps_printPut (v : Vt) (ch : Char) (w : Nat) :
    (v.printPut ch w).pstate = v.pstate := by
  unfold Vt.printPut; dsimp only; split <;> rfl

theorem ps_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).pstate = v.pstate := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

/-- The composite: printing a glyph never touches the parser. -/
theorem ps_print (v : Vt) (c : Char) : (v.print c).pstate = v.pstate := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | rw [ps_printAdvance, ps_printPut, ps_printShift, ps_printWideWrap, ps_printWrap]

theorem ps_acceptChar (v : Vt) (n : Nat) : (v.acceptChar n).pstate = v.pstate := by
  unfold Vt.acceptChar; split <;> exact ps_print _ _

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

theorem un_printPut (v : Vt) (ch : Char) (w : Nat) :
    (v.printPut ch w).u8need = v.u8need := by
  unfold Vt.printPut; dsimp only; split <;> rfl

theorem un_printAdvance (v : Vt) (w : Nat) : (v.printAdvance w).u8need = v.u8need := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem un_print (v : Vt) (c : Char) : (v.print c).u8need = v.u8need := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
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

theorem dims_printPut (v : Vt) (ch : Char) (w : Nat) : dims (v.printPut ch w) = dims v := by
  unfold Vt.printPut; dsimp only; split <;> rfl

theorem dims_printAdvance (v : Vt) (w : Nat) : dims (v.printAdvance w) = dims v := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem dims_print (v : Vt) (c : Char) : dims (v.print c) = dims v := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
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

theorem org_printPut (v : Vt) (ch : Char) (w : Nat) :
    (v.printPut ch w).modes.origin = v.modes.origin := by
  unfold Vt.printPut; dsimp only; split <;> rfl

theorem org_printAdvance (v : Vt) (w : Nat) :
    (v.printAdvance w).modes.origin = v.modes.origin := by
  unfold Vt.printAdvance; dsimp only; split <;> rfl

theorem org_print (v : Vt) (c : Char) : (v.print c).modes.origin = v.modes.origin := by
  unfold Vt.print
  dsimp only
  repeat' split
  all_goals first
    | rfl
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

end Zmx.Core.Vt




