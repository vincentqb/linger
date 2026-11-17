module

import all Terminal.CoreCode.Render
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.Unread
import all Terminal.Proofs.Render.PendingGlyph
import all Terminal.Proofs.Render.PendingWrap
import all Terminal.Proofs.Render.Grid
import all Terminal.Proofs.Render.Tabs
import all Terminal.Proofs.Replay
import all Terminal.Proofs.Render.Sync

/-! # A repaint restores its terminal

`step` reads every field of a terminal but four (`Terminal.Proofs.Vt.Unread`): the cells, the
cursor with its deferred wrap, the pen, the modes but the mouse mode, the scroll region, the tab
ruler, the stashed main screen with its cursor, the DECSC slot, the charsets and the shift state,
the parser state and the UTF-8 decoder. `restore_readable_quiesce` says that a live receiver of
the repaint of a live terminal of its size holds each of them as the terminal does once its
partial parser state is forgotten, which between control sequences and characters is the
terminal itself (`restore_readable`). `restores` reads that through the emulator's accessors, as
`Terminal.Vt.Restores` states it, and later output keeps the two reading the same by
`readable_feed`.

The paint's lemmas give the grid, the pen, the modes and the ruler (`restore_grid_any`,
`restore_pen_any`, `restore_modes_any`, `restore_tabs_any`). This module adds the rest: the stash
the paint leaves (`screens_stash`), the parked cursors and the DECSC slot exactly (`parkAnsi_eq`,
`savedAnsi_eq`), a frame that keeps the stash and the slot through the tail (`Stays`), and the
cursor, region and charsets the tail installs (`tail_shows`). Of the four fields `readable`
blanks, the history and the title differ in general, the bell is the receiver's, and a decoded
mouse mode outside the three a program can set is not replayed. -/

namespace Terminal.Render

open Terminal.Vt

/-- A margin cell of a reproducible row always repaints: deferred wrap pending at the right
margin of a row the painter can express names a glyph that ends there. -/
theorem pendingAnsi_ne_nil {cols rows : Nat} {grid : Array Row} {cur : Cursor} (row : Nat)
    (pen : Pen) (hg : GridOk cols rows grid) (hy : cur.y < rows) (hp : cur.pending = true)
    (hx : cur.x + 1 = cols) : pendingAnsi cols grid cur row pen ≠ [] := by
  have hcells : grid.getD cur.y #[] = grid.getD cur.y (blankRow cols {}) :=
    getD_of_lt grid cur.y _ _ (hg.1 ▸ hy)
  have hrow : RowOk cols (grid.getD cur.y #[]) := hcells ▸ hg.2 cur.y
  have hsize : cur.y < grid.size := hg.1 ▸ hy
  unfold pendingAnsi
  dsimp only
  generalize grid.getD cur.y #[] = cells at hrow ⊢
  -- the margin glyph: a shadow's base one column left, or a narrow glyph in the margin
  obtain ⟨x, hxd, hw, hm⟩ :
    ∃ x,
      (if ((cells.at cur.x).width == 0) = true then cur.x - 1 else cur.x) = x ∧
        charWidth (cellFit (cells.at x)).base ≠ 0 ∧
        x + charWidth (cellFit (cells.at x)).base = cols :=
    by
    by_cases hz : (cells.at cur.x).width = 0
    · obtain ⟨hx0, h2⟩ := (hrow.pairs cur.x).2 hz
      refine ⟨cur.x - 1, by simp [hz], ?_, ?_⟩
      · rw [cellFit_id (hrow.cells _), (hrow.cells _).width (by omega), h2]; decide
      · rw [cellFit_id (hrow.cells _), (hrow.cells _).width (by omega), h2]; omega
    · have hc := hrow.cells cur.x
      have hone : (cells.at cur.x).width = 1 := by
        rcases PendingGlyph.base_width hc hz with h | h
        · exact h
        · have hsh := (hrow.pairs cur.x).1 h
          have hout : cells.at (cur.x + 1) = default := by
            unfold Row.at
            simp [Array.getD, hrow.size, hx]
          rw [hout] at hsh
          exact
            absurd (congrArg Cell.width hsh)
              (by
                simp [Cell.shadow]; decide)
      refine ⟨cur.x, by simp [hz], ?_, ?_⟩
      · rw [cellFit_id hc, hc.width hz, hone]; decide
      · rw [cellFit_id hc, hc.width hz, hone]; omega
  rw [hxd]
  have hcx : cur.x < cells.size := by
    rw [hrow.size]; omega
  rw [ite_eq_left (by simp [hp, hsize, hcx, hx, hw, hm])]
  simp [csiNum2, csiB]

/-- **A park establishes its saved cursor exactly**, deferred wrap included, on a receiver in the
paint's state whose grid can be repainted: the cursor, the pen and origin mode, which it turns on
with the saved one, and nothing else. -/
theorem parkAnsi_eq (w : Vt) (sv : Saved) (hg : Good w) (hr : Renderable w) (h0 : w.g0Line = false)
    (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true) (hins : w.modes.insert = false)
    (htop : w.top = 0) (hbot : w.bot = w.rows - 1) (hps : w.pstate = .ground) (hun : w.u8need = 0)
    (hua : w.u8acc = 0) (hx : sv.cur.x < w.cols) (hy : sv.cur.y < w.rows)
    (hpx : sv.cur.pending = true → sv.cur.x + 1 = w.cols) :
    w.feed (parkAnsi w.cols w.grid sv) =
      { w with
        cursor := sv.cur, pen := sv.pen,
        modes := if sv.origin then { w.modes with origin := true } else w.modes } := by
  generalize hm : (if sv.origin then { w.modes with origin := true } else w.modes) = M
  obtain ⟨c1, hw1⟩ :
    ∃ c1,
      w.feed (if sv.origin then modeSet 6 true else []) =
        { w with
          cursor := c1, modes := M } :=
    by
    rw [← hm]
    cases ho : sv.origin
    · exact ⟨w.cursor, by simp only [Bool.false_eq_true, ↓reduceIte, feed_nil]⟩
    · refine ⟨(Vt.moveTo { w with modes := { w.modes with origin := true } } 0 0).cursor, ?_⟩
      simp only [↓reduceIte]
      rw [modeSet_feed_eq 6 true (by decide) (by decide) hps hun]
      simp [Vt.setMode, Vt.moveTo, ← hps]
  have hMwrap : M.wrap = true := by
    rw [← hm]; split <;> exact hwrap
  have hMins : M.insert = false := by
    rw [← hm]; split <;> exact hins
  have hrowsLe := hg.rowsLe
  have hcolsLe := hg.colsLe
  have hw2 :
    w.feed ((if sv.origin then modeSet 6 true else []) ++ penSgr sv.pen) =
      { w with
        cursor := c1, modes := M, pen := sv.pen } := by
    rw [feed_append, hw1,
      penSgr_feed (v :=
        { w with
          cursor := c1, modes := M })
        sv.pen hps hun]
  -- the address: the region is the whole screen, so it is absolute under either origin mode
  have e3 :
    w.feed
        ((if sv.origin then modeSet 6 true else []) ++ penSgr sv.pen ++
          csiNum2 (sv.cur.y + 1) (sv.cur.x + 1) 0x48) =
      { w with
        cursor := { x := sv.cur.x, y := sv.cur.y, pending := false }, modes := M,
        pen := sv.pen } := by
    rw [feed_append, hw2,
      cup_feed_eq (v :=
        { w with
          cursor := c1, modes := M, pen := sv.pen })
        (sv.cur.y + 1) (sv.cur.x + 1) (by omega) (by omega) (by omega) (by omega) hps hun]
    simp only [Vt.moveTo, Nat.add_sub_cancel]
    congr 2
    · omega
    · by_cases hM : M.origin <;> simp [hM, htop, hbot] <;> omega
  generalize hu :
    ({ w with
        cursor := { x := sv.cur.x, y := sv.cur.y, pending := false }, modes := M, pen := sv.pen } :
      Vt) =
    u at e3
  have g3 : Good u := e3 ▸ Good.feed _ hg
  have r3 : Renderable u := e3 ▸ renderable_feed hr _
  have huc : u.cols = w.cols := by rw [← hu]
  have hug : u.grid = w.grid := by rw [← hu]
  have he :=
    pendingAnsi_feed_eq u sv.cur (sv.cur.y + 1) sv.pen g3 r3
      (by
        rw [← hu]; exact h0)
      (by
        rw [← hu]; exact h1)
      (by
        rw [← hu]; exact hMwrap)
      (by
        rw [← hu]; exact hMins)
      (fun hy => by
        subst hu
        refine
          ⟨by omega, by
            dsimp only at hy; omega, ?_⟩
        dsimp only at hy ⊢
        unfold Vt.moveTo
        by_cases hM : M.origin <;> simp [hM, htop, hbot] <;> omega)
      (by
        rw [← hu]; exact hps)
      (by
        rw [← hu]; exact hun)
      (by
        rw [← hu]; exact hua)
  rw [show
      parkAnsi w.cols w.grid sv =
        (if sv.origin then modeSet 6 true else []) ++ penSgr sv.pen ++
          csiNum2 (sv.cur.y + 1) (sv.cur.x + 1) 0x48 ++
          pendingAnsi w.cols w.grid sv.cur (sv.cur.y + 1) sv.pen
      from rfl,
    feed_append, e3, ← huc, ← hug, he]
  by_cases hp : sv.cur.pending = true
  · rw [ite_eq_right
        (pendingAnsi_ne_nil _ _ r3.main
          (by
            rw [← hu]; exact hy)
          hp
          (by
            rw [← hu]; exact hpx hp))]
    subst hu
    rfl
  · have hnil : pendingAnsi u.cols u.grid sv.cur (sv.cur.y + 1) sv.pen = [] := by
      unfold pendingAnsi
      simp [hp]
    rw [ite_eq_left hnil]
    subst hu
    have hc : ({ x := sv.cur.x, y := sv.cur.y, pending := false } : Cursor) = sv.cur := by
      revert hp
      cases sv.cur
      simp
    rw [hc]

/-- **The DECSC slot's replay installs the session's slot exactly**, cursor with its deferred
wrap, pen and origin mode, on a receiver in the paint's state that already shows the session's
grid; it changes nothing else but the cursor and the pen. -/
theorem savedAnsi_eq (v w : Vt) (hgv : Good v) (hg : Good w) (hr : Renderable w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) (hgrid : w.grid = v.grid)
    (h0 : w.g0Line = false) (h1 : w.g1Line = false) (hwrap : w.modes.wrap = true)
    (hins : w.modes.insert = false) (ho : w.modes.origin = false) (htop : w.top = 0)
    (hbot : w.bot = w.rows - 1) (hps : w.pstate = .ground) (hun : w.u8need = 0)
    (hua : w.u8acc = 0) :
    ∃ c p,
      w.feed (savedAnsi v) =
        { w with
          cursor := c, pen := p, saved := v.saved } := by
  have hpk :=
    parkAnsi_eq w v.saved hg hr h0 h1 hwrap hins htop hbot hps hun hua (hcols ▸ hgv.savX)
      (hrows ▸ hgv.savY) (fun h => hcols ▸ hgv.savPendX h)
  generalize hM : (if v.saved.origin then { w.modes with origin := true } else w.modes) = M at hpk
  rw [show savedAnsi v = parkAnsi w.cols w.grid v.saved ++ escSeq 0x37 ++ originOffAnsi v.saved from
      by
      rw [hcols, hgrid]; rfl,
    feed_append, feed_append, hpk,
    save_feed_eq
      { w with
        cursor := v.saved.cur, pen := v.saved.pen, modes := M }
      hps hun]
  have hmeq : ({ w.modes with origin := false } : Modes) = w.modes := by rw [← ho]
  have hsv : ∀ o, o = v.saved.origin → (⟨v.saved.cur, v.saved.pen, o⟩ : Saved) = v.saved := by
    rintro o rfl; rfl
  unfold originOffAnsi
  cases hs : v.saved.origin
  · rw [hs] at hM
    simp only [Bool.false_eq_true, ↓reduceIte] at hM ⊢
    subst hM
    exact
      ⟨v.saved.cur, v.saved.pen, by
        rw [hsv w.modes.origin (ho.trans hs.symm)]; rfl⟩
  · rw [hs] at hM
    simp only [↓reduceIte] at hM ⊢
    subst hM
    rw [modeSet_feed_eq 6 false (by decide) (by decide) ?hg ?hu]
    · simp only [Vt.setMode, Vt.moveTo, Bool.false_eq_true, ↓reduceIte, ← hps]
      rw [hmeq, hsv true hs.symm]
      exact ⟨_, _, rfl⟩
    · exact hps
    · exact hun

/-! ### The tail keeps the stash and the slot

`stash` is the stashed main screen with its cursor, and the DECSC slot: what the paint and the
slot's replay establish and every later stage leaves alone. `Stays` is `Fixes` at it, built from
the per-construct facts below the way `Keeps` is at the grid. -/

/-- The stashed main screen and the DECSC slot. -/
def stash (v : Vt) : Option (Array Row × Saved) × Saved := (v.altGrid, v.saved)

theorem psBlind_stash : PsBlind stash := fun _ _ => rfl

/-- From ground, `bs` returns to ground with nothing half-decoded and keeps the stash and the slot. -/
abbrev Stays (bs : Bytes) : Prop := Fixes stash bs

theorem Stays.streamPred : StreamPred Stays := Fixes.streamPred stash

theorem stash_cup (w : Vt) (t : CsiState) : stash (w.csiDispatch t 0x48) = stash w := by
  rw [frame_csiDispatch_cup]; rfl

theorem stash_cha (w : Vt) (t : CsiState) : stash (w.csiDispatch t 0x47) = stash w := by
  rw [frame_csiDispatch_cha]; rfl

theorem stash_sgr (w : Vt) (t : CsiState) : stash (w.csiDispatch t 0x6D) = stash w := by
  rw [frame_csiDispatch_sgr]; rfl

theorem stash_tbc (w : Vt) (t : CsiState) : stash (w.csiDispatch t 0x67) = stash w := by
  rw [frame_csiDispatch_tbc]; rfl

theorem stash_stbm (w : Vt) (t : CsiState) : stash (w.csiDispatch t 0x72) = stash w := by
  rw [frame_csiDispatch_stbm]; rfl

theorem stash_print (w : Vt) (c : Char) : stash (w.print c) = stash w := by
  have h := off_print w c
  exact Prod.ext (congrArg OffScreen.alt h) (congrArg OffScreen.saved h)

/-- `ESC =`, `ESC H`, `ESC >` and `ESC \` write a mode flag, the tab ruler or nothing. -/
theorem stays_escSeq (b : UInt8) (hb : b = 0x3D ∨ b = 0x48 ∨ b = 0x3E ∨ b = 0x5C) :
    Stays (escSeq b) := by
  intro v hg hu
  rw [show escSeq b = [0x1B] ++ [b] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [b]) = (w.step 0x1B).step b from fun w => by
      simp [Vt.feed]]
  rw [esc_step_eq hg hu, step_of_esc_quiet b rfl (by simpa using hu)]
  rcases hb with h | h | h | h <;> subst h <;> show _ ∧ _ ∧ _ <;> unfold Vt.stepEsc <;>
    exact ⟨rfl, by simpa using hu, rfl⟩

/-- `ESC ( x` / `ESC ) x` set a charset flag. -/
theorem stays_escCharset (i x : UInt8) (hi : i = 0x28 ∨ i = 0x29) (hlo : 0x30 ≤ x)
    (hhi : x ≤ 0x7E) : Stays (escCharset i x) := by
  intro v hg hu
  rw [show escCharset i x = [0x1B] ++ [i, x] from rfl]
  rw [show ∀ (w : Vt), w.feed ([0x1B] ++ [i, x]) = ((w.step 0x1B).step i).step x from fun w => by
      simp [Vt.feed]]
  rw [esc_step_eq hg hu]
  have hinter : (Vt.step { v with pstate := .esc }) i = { v with pstate := .escInter i } := by
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

/-- `SO` sets the shift flag. -/
theorem stays_shiftOut : Stays [0x0E] := by
  intro v hg hu
  rw [show ∀ (w : Vt), w.feed [(0x0E : UInt8)] = w.step 0x0E from fun _ => rfl]
  rw [step_of_ground_quiet (0x0E : UInt8) hg hu]
  show _ ∧ _ ∧ _
  unfold Vt.stepGround
  rw [ite_eq_right (by decide), ite_eq_left (by decide)]
  unfold Vt.ctl
  exact ⟨hg, by simpa using hu, rfl⟩

theorem stays_penSgr (p : Pen) : Stays (penSgr p) := fixes_penSgr psBlind_stash p stash_sgr

theorem stays_cup (a b : Nat) : Stays (csiNum2 a b 0x48) :=
  fixes_csiNum2 psBlind_stash a b 0x48 (by decide) (by decide) stash_cup

theorem stays_cha (n : Nat) : Stays (csiNum n 0x47) :=
  fixes_csiNum psBlind_stash n 0x47 (by decide) (by decide) stash_cha

theorem stays_cursorAnsi (v : Vt) : Stays (cursorAnsi v) := Stays.streamPred.cursorAnsi stays_cup v

theorem stays_regionAnsi (v : Vt) : Stays (regionAnsi v) :=
  Stays.streamPred.regionAnsi
    (fun a b => fixes_csiNum2 psBlind_stash a b 0x72 (by decide) (by decide) stash_stbm) v

theorem stays_tabsAnsi (v : Vt) : Stays (tabsAnsi v) :=
  Stays.streamPred.tabsAnsi (fixes_csiNum psBlind_stash 3 0x67 (by decide) (by decide) stash_tbc)
    stays_cha (stays_escSeq 0x48 (by decide)) v

theorem stays_titleAnsi (v : Vt) : Stays (titleAnsi v) := by
  unfold titleAnsi
  exact
    fixes_osc psBlind_stash _ fun w acc => by
      rw [frame_oscFinish]; rfl

theorem stays_charsetAnsi (v : Vt) : Stays (charsetAnsi v) :=
  Stays.streamPred.charsetAnsi
    (fun _ _ hi hx =>
      stays_escCharset _ _ hi (by rcases hx with h | h <;> subst h <;> decide)
        (by rcases hx with h | h <;> subst h <;> decide))
    stays_shiftOut v

/-- A mode other than the screen switches and the DECSC slot's leaves the stash and the slot. -/
theorem stash_setMode (v : Vt) (priv : Bool) (n : Nat) (on : Bool) (h47 : n ≠ 47) (h1047 : n ≠ 1047)
    (h1048 : n ≠ 1048) (h1049 : n ≠ 1049) : stash (v.setMode priv n on) = stash v := by
  unfold Vt.setMode
  split
  · split
    all_goals
      first
      | rfl
      | rw [frame_moveTo]
      | exact absurd rfl h47
      | exact absurd rfl h1047
      | exact absurd rfl h1048
      | exact absurd rfl h1049
  · split
    all_goals rfl

theorem stash_csiDispatch_mode (v : Vt) (s : CsiState) (final : UInt8) (n : Nat) (sub : Bool)
    (hf : final = 0x68 ∨ final = 0x6C) (hp : s.params = #[(n, sub)]) (h47 : n ≠ 47)
    (h1047 : n ≠ 1047) (h1048 : n ≠ 1048) (h1049 : n ≠ 1049) :
    stash (v.csiDispatch s final) = stash v := by
  by_cases hi : s.ignore = true
  · rw [csiDispatch_ignored v _ hi]
  · rcases hf with rfl | rfl
    · rw [csiDispatch_sm_one v s n sub (by simpa using hi) hp]
      exact stash_setMode v _ n true h47 h1047 h1048 h1049
    · rw [csiDispatch_rm_one v s n sub (by simpa using hi) hp]
      exact stash_setMode v _ n false h47 h1047 h1048 h1049

/-- `CSI ? n h` / `CSI ? n l` for a mode `stash_setMode` names. -/
theorem stays_modeSet (n : Nat) (on : Bool) (hlt : n < 65535) (h47 : n ≠ 47) (h1047 : n ≠ 1047)
    (h1048 : n ≠ 1048) (h1049 : n ≠ 1049) : Stays (modeSet n on) := by
  have hf :
    (if on then (0x68 : UInt8) else 0x6C) = 0x68 ∨
      (if on then (0x68 : UInt8) else 0x6C) = 0x6C := by
    cases on <;> simp
  have h1 : (0x40 : UInt8) ≤ (if on then 0x68 else 0x6C) := by cases on <;> decide
  have h2 : (if on then (0x68 : UInt8) else 0x6C) ≤ 0x7E := by cases on <;> decide
  intro v hg hu
  rw [show
      modeSet n on = [0x1B, 0x5B] ++ ([(0x3F : UInt8)] ++ (digits n ++ [if on then 0x68 else 0x6C]))
      from by
      unfold modeSet csiPriv csiB; cases on <;> simp]
  rw [feed_append, feed_append]
  rw [keeps_csi_open hg hu]
  rw [show ∀ (w : Vt), w.feed [(0x3F : UInt8)] = w.step 0x3F from fun _ => rfl]
  rw [step_of_csi_quiet (0x3F : UInt8) (v := { v with pstate := .csi {} }) (s := {}) rfl
      (by simpa using hu)]
  unfold Vt.stepCsi
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_left (by decide)]
  exact
    fixes_csi_digits_tail psBlind_stash n _ h1 h2 hlt
      (fun w t sub ha => stash_csiDispatch_mode w t _ n sub hf ha h47 h1047 h1048 h1049) rfl
      (by simpa using hu) rfl rfl rfl

theorem stays_irm (on : Bool) : Stays (csiNum 4 (if on then 0x68 else 0x6C)) := by
  cases on
  · exact
      fixes_csiNum_arg psBlind_stash 4 0x6C (by decide) (by decide) (by omega)
        (fun w t sub ha =>
          stash_csiDispatch_mode w t _ 4 sub (Or.inr rfl) ha (by omega) (by omega) (by omega)
            (by omega))
  · exact
      fixes_csiNum_arg psBlind_stash 4 0x68 (by decide) (by decide) (by omega)
        (fun w t sub ha =>
          stash_csiDispatch_mode w t _ 4 sub (Or.inl rfl) ha (by omega) (by omega) (by omega)
            (by omega))

theorem stays_modesAnsi (v : Vt) : Stays (modesAnsi v) :=
  Stays.streamPred.modesAnsi v
    (fun n on h => stays_modeSet n on (by omega) (by omega) (by omega) (by omega) (by omega))
    (fun h => by
      simp only [Bool.or_eq_true, beq_iff_eq] at h
      exact stays_modeSet _ _ (by omega) (by omega) (by omega) (by omega) (by omega))
    (stays_modeSet 6 _ (by omega) (by omega) (by omega) (by omega) (by omega))
    (stays_escSeq 0x3D (by decide)) (stays_escSeq 0x3E (by decide)) stays_irm
    (fixes_shapeAnsi (fun _ _ => rfl) _)

theorem stays_utf8_safe (ch : Char) : Stays (utf8 (safeChar ch)) := by
  intro w hg hu
  obtain ⟨hg', hu'⟩ :=
    utf8_feed_ground_need (safeChar ch) ⟨(safeChar_ge ch).1, (safeChar_ge ch).2⟩ hg hu
  exact
    ⟨hg', hu',
      proj_glyph_run stash_print (fun _ _ _ => rfl) _ _ hg fun b hb =>
        (utf8_no_ctl _ (safeChar_ge ch).1 (safeChar_ge ch).2 b hb).1⟩

theorem stays_utf8s (cs : List Char) : Stays (utf8s cs) := by
  intro w hg hu
  obtain ⟨hg', hu'⟩ := utf8s_feed_ground_need cs hg hu
  exact
    ⟨hg', hu',
      proj_glyph_run stash_print (fun _ _ _ => rfl) _ _ hg fun b hb => (utf8s_no_ctl cs b hb).1⟩

/-- A C0 control from ground executes. -/
theorem step_ctl_of_ground {w : Vt} (b : UInt8) (hg : w.pstate = .ground) (hu : w.u8need = 0)
    (hb : b < 0x20) (he : b ≠ 0x1B) : w.step b = w.ctl b := by
  rw [step_of_ground_quiet b hg hu]
  unfold Vt.stepGround
  rw [ite_eq_right (by simpa using he), ite_eq_left hb]

theorem stays_crlf : Stays [0x0D, 0x0A] := by
  intro w hg hu
  have e : w.feed [0x0D, 0x0A] = w.carriageReturn.lineFeed := by
    rw [show w.feed [0x0D, 0x0A] = (w.step 0x0D).step 0x0A from rfl,
      step_ctl_of_ground 0x0D hg hu (by decide) (by decide)]
    exact step_ctl_of_ground (w := w.carriageReturn) 0x0A hg hu (by decide) (by decide)
  rw [e]
  refine
    ⟨by
      rw [ps_lineFeed]; exact hg, by
      rw [un_lineFeed]; exact hu, ?_⟩
  rw [frame_lineFeed]; rfl

theorem stays_home : Stays (csiB ++ [0x48]) := by
  have h := fixes_csi_seq psBlind_stash [] 0x48 ParamBytes.nil (by decide) (by decide) stash_cup
  rwa [List.append_nil] at h

theorem stays_gridAnsi (g : Array Row) : Stays (gridAnsi g) :=
  Stays.streamPred.gridAnsi (fixes_csiNum psBlind_stash 0 0x6D (by decide) (by decide) stash_sgr)
    stays_home stays_crlf
    (fun row p => Stays.streamPred.rowAnsi stays_penSgr stays_utf8_safe stays_utf8s stays_cha row p)
    g

/-- **The paint leaves the session's stash**: nothing on the main screen, and on the alternate
screen the main screen with its cursor, pen and origin mode, parked and switched with `?1049h`. -/
theorem screens_stash (v w : Vt) (hgood : Good w) (hren : Renderable w) (hcols : w.cols = v.cols)
    (hrows : w.rows = v.rows) (hua : w.u8acc = 0) (hun : w.u8need = 0) (hgv : Good v)
    (hvren : Renderable v) :
    (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).altGrid =
      v.altGrid := by
  have hpos : 0 < v.cols := by
    rw [← hcols]; exact hgood.colsPos
  have hub : v.cols < 65533 := by
    have := hgood.colsLe; rw [hcols] at this; omega
  obtain ⟨e1, e2, -, -, e5, -, e7, -, -, -, -, -, -, -, -, est⟩ :=
    paint_entry v w hgood hren hcols hrows hua hun
  match halt : v.altGrid with
  | none =>
    have hs := (smap_screensAnsi v _ e5).2
    rw [est, halt] at hs
    have hns :
      (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).altGrid.isSome =
        false := by
      rw [← stick_alt, feed_append, hs]; rfl
    exact
      Option.not_isSome_iff_eq_none.mp
        (by
          rw [hns]; simp)
  | some (mainGrid, ms) =>
    obtain ⟨hmsz, hmok⟩ := hvren.alt mainGrid ms halt
    obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, f11, f12, f13, f14, falt, -⟩ :=
      scrollback_entry (u := w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)) (v := v)
        (Good.feed _ hgood) (renderable_feed hren _) e1 e2 e5 e7 est
    have hgz :
      Good ((w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)) :=
      Good.feed _ (Good.feed _ hgood)
    obtain ⟨sc, sr, st, sbt, salt, sg, sn, sa, sins, swrap, sorg, s0, s1, sgrid, -⟩ :=
      alt_pre_park (z :=
        (w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)) (mg :=
        mainGrid) (cols := v.cols) (rows := v.rows) f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14
        falt hgz hpos hub hmok hmsz
    have hgs := Good.feed (gridAnsi mainGrid) hgz
    have hrs :=
      renderable_feed
        (renderable_feed (renderable_feed hren (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A))
          (scrollbackAnsi v))
        (gridAnsi mainGrid)
    generalize hs :
      ((w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).feed (scrollbackAnsi v)).feed
        (gridAnsi mainGrid) =
      s at sc sr st sbt salt sg sn sa sins swrap sorg s0 s1 sgrid hgs hrs
    obtain ⟨hmx, hmy⟩ := hgv.altCur mainGrid ms halt
    -- the park, exactly
    have hpark :
      s.feed (parkAnsi v.cols mainGrid ms) =
        { s with
          cursor := ms.cur, pen := ms.pen,
          modes := if ms.origin then { s.modes with origin := true } else s.modes } := by
      rw [← sc, ← sgrid]
      exact
        parkAnsi_eq s ms hgs hrs s0 s1 swrap sins st (by rw [sbt, sr]) sg sn sa (by omega)
          (by omega) (fun h => (hgv.altPendX mainGrid ms halt h).trans sc.symm)
    -- the switch stashes the parked cursor with the painted main screen
    have hsw :
      ((s.feed (parkAnsi v.cols mainGrid ms)).feed (csiPriv 1049 0x68)).altGrid =
        some (mainGrid, ms) := by
      rw [show csiPriv 1049 0x68 = modeSet 1049 true from rfl,
        modeSet_feed_eq 1049 true (by decide) (by decide)
          (by
            rw [hpark]; exact sg)
          (by
            rw [hpark]; exact sn),
        show
          (s.feed (parkAnsi v.cols mainGrid ms)).setMode true 1049 true =
            (s.feed (parkAnsi v.cols mainGrid ms)).enterAlt true
          from rfl,
        hpark]
      unfold Vt.enterAlt Vt.cursorSaved
      dsimp only
      rw [ite_eq_right
          (show ¬(s.altGrid.isSome = true) from by
            rw [salt]; simp),
        sgrid]
      congr 2
      cases ms
      cases ho : ‹Bool› <;> simp_all
    -- the rest of the paint keeps it
    have hz := hsw
    generalize hzv : (s.feed (parkAnsi v.cols mainGrid ms)).feed (csiPriv 1049 0x68) = z at hz
    have hzg : z.pstate = .ground ∧ z.u8need = 0 := by
      rw [← hzv, show csiPriv 1049 0x68 = modeSet 1049 true from rfl,
        modeSet_feed_eq 1049 true (by decide) (by decide)
          (by
            rw [hpark]; exact sg)
          (by
            rw [hpark]; exact sn)]
      exact
        ⟨rfl,
          (un_setMode _ true 1049 true).trans
            (by
              rw [hpark]; exact sn)⟩
    have hk :=
      (Stays.streamPred.append
          (Stays.streamPred.originOffAnsi
            (stays_modeSet 6 false (by omega) (by omega) (by omega) (by omega) (by omega)) ms)
          (stays_gridAnsi v.grid))
        z hzg.1 hzg.2
    have hpeel :
      w.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) =
        z.feed (originOffAnsi ms ++ gridAnsi v.grid) := by
      rw [show
          screensAnsi v =
            scrollbackAnsi v ++ gridAnsi mainGrid ++ parkAnsi v.cols mainGrid ms ++
              csiPriv 1049 0x68 ++
              (originOffAnsi ms ++ gridAnsi v.grid)
          from by
          unfold screensAnsi; rw [halt]; simp only [List.append_assoc],
        ← hzv, ← hs]
      simp only [feed_append]
    rw [hpeel]
    exact congrArg Prod.fst hk.2.2 |>.trans hz

/-- **The tail establishes the rest exactly.** On a receiver in the state the paint leaves —
the session's grid and stash, the whole screen as the region, ASCII charsets with no shift,
autowrap on, replacement and origin mode off, the decoder quiet — the tail installs the
session's cursor with its deferred wrap, its region, its DECSC slot and its charsets, and keeps
the stash. -/
theorem tail_shows (v u : Vt) (hgv : Good v) (hvren : Renderable v) (hg : Good u)
    (hr : Renderable u) (hcols : u.cols = v.cols) (hrows : u.rows = v.rows)
    (hgrid : u.grid = v.grid) (ht : u.top = 0) (hb : u.bot = v.rows - 1) (h0 : u.g0Line = false)
    (h1 : u.g1Line = false) (hso : u.shiftOut = false) (hwrap : u.modes.wrap = true)
    (hins : u.modes.insert = false) (ho : u.modes.origin = false) (hp : u.pstate = .ground)
    (hn : u.u8need = 0) (ha : u.u8acc = 0) (halt : u.altGrid = v.altGrid) :
    let d :=
      u.feed
        (savedAnsi v ++ regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
          penSgr v.pen ++
          cursorAnsi v ++
          cursorPendingAnsi v)
    d.cursor = v.cursor ∧
      d.top = v.top ∧
      d.bot = v.bot ∧
      d.altGrid = v.altGrid ∧
      d.saved = v.saved ∧ d.g0Line = v.g0Line ∧ d.g1Line = v.g1Line ∧ d.shiftOut = v.shiftOut := by
  intro d
  have hrowsLe : v.rows ≤ 1000 := hrows ▸ hg.rowsLe
  have hcolsLe : v.cols ≤ 1000 := hcols ▸ hg.colsLe
  have hreg : (v.top = 0 ∧ v.bot = v.rows - 1) ∨ (v.top < v.bot ∧ v.bot < v.rows) := by
    rcases hgv.region with h | h
    · exact Or.inr ⟨h, hgv.botLt⟩
    · exact
        Or.inl
          ⟨by
            have := hgv.topLe; have := hgv.botLt; omega, by
            have := hgv.botLt; omega⟩
  -- the sticky fields after everything but the deferred wrap
  have hst :
    stick
        (u.feed
          (savedAnsi v ++ regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++
            charsetAnsi v ++
            penSgr v.pen ++
            cursorAnsi v)) =
      ⟨v.rows, v.top, v.bot, v.g0Line, v.g1Line, v.shiftOut, v.altGrid.isSome⟩ := by
    have htc : v.top + 1 < 65535 := by rcases hreg with h | h <;> omega
    have hbc : v.bot + 1 < 65535 := by rcases hreg with h | h <;> omega
    have hmid := ((smap_id_tabsAnsi v).append (smap_id_titleAnsi v)).append (smap_id_modesAnsi v)
    have hm :=
      (((smap_id_savedAnsi v).comp (smap_regionAnsi v htc hbc)).comp hmid).congr (fun _ => rfl)
    have hs :=
      (hm.comp (smap_charsetAnsi v)).comp ((smap_id_penSgr v.pen).append (smap_id_cursorAnsi v))
    have he := (hs u hp).2
    simp only [List.append_assoc, id_eq] at he
    simp only [List.append_assoc]
    rw [he]
    have hrg :
      (if v.top == 0 && v.bot == v.rows - 1 then id else stStbm v.top v.bot) (stick u) =
        { stick u with
          top := v.top, bot := v.bot } := by
      split
      · rename_i h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        show
          stick u =
            { stick u with
              top := v.top, bot := v.bot }
        unfold stick
        rw [ht, hb, h.1, h.2]
      · rename_i h
        have hh : v.top < v.bot ∧ v.bot < (stick u).rows := by
          rcases hreg with heq | hh
          · exact False.elim (h (by simp [heq.1, heq.2]))
          · exact
              ⟨hh.1, by
                rw [stick_rows, hrows]; exact hh.2⟩
        rw [stStbm_of hh.1 hh.2]
    rw [hrg]
    have hsu : stick u = ⟨v.rows, 0, v.rows - 1, false, false, false, v.altGrid.isSome⟩ := by
      show (⟨u.rows, u.top, u.bot, u.g0Line, u.g1Line, u.shiftOut, u.altGrid.isSome⟩ : Sticky) = _
      rw [hrows, ht, hb, h0, h1, hso, halt]
    rw [hsu]
    cases v.shiftOut <;> rfl
  -- the DECSC slot
  obtain ⟨c1, p1, hsa⟩ :=
    savedAnsi_eq v u hgv hg hr hcols hrows hgrid h0 h1 hwrap hins ho ht (hb.trans (by rw [hrows]))
      hp hn ha
  have hdeq :
    d =
      (((u.feed (savedAnsi v)).feed
                (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
                  penSgr v.pen)).feed
            (cursorAnsi v)).feed
        (cursorPendingAnsi v) := by
    simp only [d, feed_append]
  have hst' :
    stick
        (((u.feed (savedAnsi v)).feed
              (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
                penSgr v.pen)).feed
          (cursorAnsi v)) =
      ⟨v.rows, v.top, v.bot, v.g0Line, v.g1Line, v.shiftOut, v.altGrid.isSome⟩ := by
    simpa only [feed_append] using hst
  have hgood :
    Good
      ((u.feed (savedAnsi v)).feed
        (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
          penSgr v.pen)) :=
    Good.feed _ (Good.feed _ hg)
  have hren :
    Renderable
      ((u.feed (savedAnsi v)).feed
        (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
          penSgr v.pen)) :=
    renderable_feed (renderable_feed hr _) _
  have hdims :
    dims
        ((u.feed (savedAnsi v)).feed
          (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
            penSgr v.pen)) =
      dims u := by
    rw [dims_feed _ (Good.feed _ hg), dims_feed _ hg]
  have hua :
    U8Ok
      ((u.feed (savedAnsi v)).feed
        (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
          penSgr v.pen)) :=
    u8Ok_feed _ (u8Ok_feed _ fun _ => ha)
  generalize hav : u.feed (savedAnsi v) = a at hsa hdeq hst' hgood hren hdims hua
  have ap : a.pstate = .ground := by
    rw [hsa]; exact hp
  have an : a.u8need = 0 := by
    rw [hsa]; exact hn
  -- the metadata stages keep the grid and the stash and leave origin mode as the session's
  have hk :=
    (((((stays_regionAnsi v).append (stays_tabsAnsi v)).append (stays_titleAnsi v)).append
              (stays_modesAnsi v)).append
          (stays_charsetAnsi v)).append
      (stays_penSgr v.pen) a ap an
  have hkg :=
    (((((keeps_regionAnsi v).append (keeps_tabsAnsi v)).append (keeps_titleAnsi v)).append
              (keeps_modesAnsi v)).append
          (keeps_charsetAnsi v)).append
      (keeps_penSgr v.pen) a ap an
  have bo :
    (a.feed
          (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
            penSgr v.pen)).modes.origin =
      v.modes.origin := by
    have h3 := ((stays_regionAnsi v).append (stays_tabsAnsi v)).append (stays_titleAnsi v) a ap an
    have hor := modesAnsi_origin v (a.feed (regionAnsi v ++ tabsAnsi v ++ titleAnsi v)) h3.1 h3.2.1
    have h4 := stays_modesAnsi v (a.feed (regionAnsi v ++ tabsAnsi v ++ titleAnsi v)) h3.1 h3.2.1
    have he :=
      (mmap_id_append (mmap_id_charsetAnsi v) (mmap_id_penSgr v.pen)
          ((a.feed (regionAnsi v ++ tabsAnsi v ++ titleAnsi v)).feed (modesAnsi v)) h4.1 h4.2.1).2.2
    simp only [id_eq] at he
    rw [show
        a.feed
            (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
              penSgr v.pen) =
          ((a.feed (regionAnsi v ++ tabsAnsi v ++ titleAnsi v)).feed (modesAnsi v)).feed
            (charsetAnsi v ++ penSgr v.pen)
        from by simp only [feed_append],
      he, hor]
  generalize hbv :
    a.feed
      (regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++ penSgr v.pen) =
    b at hk hkg bo hdeq hst' hgood hren hdims hua
  obtain ⟨bp, bn, bstash⟩ := hk
  have bgrid : b.grid = v.grid := by
    have h := hkg.2.2
    dsimp only at h
    rw [h, hsa]
    exact hgrid
  have bcols : b.cols = v.cols := by rw [← dims_fst, hdims, dims_fst, hcols]
  have brows : b.rows = v.rows := by rw [← dims_snd, hdims, dims_snd, hrows]
  -- the final address writes only the cursor
  obtain ⟨cc, hcc⟩ : ∃ cc, b.feed (cursorAnsi v) = { b with cursor := cc } := by
    unfold cursorAnsi; split <;> exact cup_frame _ _ bp bn
  rw [hcc] at hst' hdeq
  have hbt : b.top = v.top := congrArg Sticky.top hst'
  have hbb : b.bot = v.bot := congrArg Sticky.bot hst'
  have hb0 : b.g0Line = v.g0Line := congrArg Sticky.g0 hst'
  have hb1 : b.g1Line = v.g1Line := congrArg Sticky.g1 hst'
  have hbso : b.shiftOut = v.shiftOut := congrArg Sticky.so hst'
  have hccv : cc = { x := v.cursor.x, y := v.cursor.y, pending := false } := by
    have hcx := hgv.curX
    have hcy := hgv.curY
    have hin := hgv.originIn
    have h := hcc
    unfold cursorAnsi at h
    split at h
    · rename_i hor
      rw [cup_feed_eq _ _ (by omega) (by omega) (by omega) (by omega) bp bn] at h
      have hcur : (b.moveTo (v.cursor.x + 1 - 1) (v.cursor.y - v.top + 1 - 1)).cursor = cc :=
        congrArg VtRec.cursor h
      rw [← hcur]
      have := hin hor
      simp only [Vt.moveTo, bo, hor, ↓reduceIte, hbt, hbb, bcols, Nat.add_sub_cancel]
      congr 1 <;> omega
    · rename_i hor
      rw [cup_feed_eq _ _ (by omega) (by omega) (by omega) (by omega) bp bn] at h
      have hcur : (b.moveTo (v.cursor.x + 1 - 1) (v.cursor.y + 1 - 1)).cursor = cc :=
        congrArg VtRec.cursor h
      rw [← hcur]
      simp only [Vt.moveTo, bo, hor, Bool.false_eq_true, ↓reduceIte, bcols, brows,
        Nat.add_sub_cancel, Nat.zero_add]
      congr 1 <;> omega
  subst hccv
  -- the deferred wrap
  have cgood : Good { b with cursor := { x := v.cursor.x, y := v.cursor.y, pending := false } } :=
    hcc ▸ Good.feed _ hgood
  have cren :
    Renderable { b with cursor := { x := v.cursor.x, y := v.cursor.y, pending := false } } :=
    renderable_congr hren rfl rfl rfl rfl
  have hpd :=
    cursorPendingAnsi_feed_eq v
      { b with cursor := { x := v.cursor.x, y := v.cursor.y, pending := false } } cgood cren bcols
      bgrid (fun hon hy => pending_row_active v _ cgood brows bo (fun _ => ⟨hbt, hbb⟩) hon hy) bp bn
      (hua bn)
  rw [hdeq, hpd]
  have hstash : (b.altGrid, b.saved) = (v.altGrid, v.saved) := by
    have : stash b = stash a := bstash
    rw [hsa] at this
    simpa [stash, halt] using this
  obtain ⟨balt, bsaved⟩ := Prod.ext_iff.mp hstash
  by_cases hpend : v.cursor.pending = true
  · have hcond :
      (v.cursor.pending &&
          (!v.modes.origin ||
            (((v.top == 0 && v.bot == v.rows - 1) || (v.top < v.bot && v.bot < v.rows)) &&
              v.top ≤ v.cursor.y &&
              v.cursor.y ≤ v.bot))) =
        true := by
      cases hor : v.modes.origin
      · simp [hpend]
      · obtain ⟨hy1, hy2⟩ := hgv.originIn hor
        have hcy := hgv.curY
        rcases hreg with h | h
        · simp [hpend, h]
          omega
        · simp [hpend, h, hy1, hy2]
    rw [ite_eq_left hcond,
      ite_eq_right (pendingAnsi_ne_nil _ _ hvren.main hgv.curY hpend (hgv.pendX hpend))]
    exact ⟨rfl, hbt, hbb, balt, bsaved, rfl, rfl, rfl⟩
  · rw [ite_eq_right (by simp [hpend])]
    refine ⟨?_, hbt, hbb, balt, bsaved, hb0, hb1, hbso⟩
    show ({ x := v.cursor.x, y := v.cursor.y, pending := false } : Cursor) = v.cursor
    revert hpend
    cases v.cursor
    simp

/-- **The repaint replays every mode but the mouse mode as the session holds it**, and the mouse
mode too unless it is one a decoded checkpoint holds that no program could set: `modesAnsi`
reads that field only through its allowlist. -/
theorem restore_modes_unmoused (v w : Vt) :
    ({ (w.feed (restore v)).modes with mouse := 0 } : Modes) = { v.modes with mouse := 0 } := by
  by_cases hm :
    v.modes.mouse = 0 ∨ v.modes.mouse = 1000 ∨ v.modes.mouse = 1002 ∨ v.modes.mouse = 1003
  · rw [restore_modes_any v w hm]
  · have hn : v.modes.mouse ≠ 1000 ∧ v.modes.mouse ≠ 1002 ∧ v.modes.mouse ≠ 1003 := by
      simp only [not_or] at hm
      exact hm.2
    have he : restore v = restore { v with modes := { v.modes with mouse := 0 } } := by
      have hma : modesAnsi v = modesAnsi { v with modes := { v.modes with mouse := 0 } } := by
        simp [modesAnsi, hn.1, hn.2.1, hn.2.2]
      unfold restore restoreBody
      rw [hma]
      rfl
    rw [he, restore_modes_any _ w (Or.inl rfl)]

/-- Two terminals read the same when they agree on every field `step` reads. -/
theorem readable_eq {r v : Vt} (hc : r.cols = v.cols) (hr : r.rows = v.rows) (hg : r.grid = v.grid)
    (hcur : r.cursor = v.cursor) (hp : r.pen = v.pen)
    (hm : ({ r.modes with mouse := 0 } : Modes) = { v.modes with mouse := 0 }) (ht : r.top = v.top)
    (hb : r.bot = v.bot) (htabs : r.tabs = v.tabs) (halt : r.altGrid = v.altGrid)
    (hs : r.saved = v.saved) (h0 : r.g0Line = v.g0Line) (h1 : r.g1Line = v.g1Line)
    (hso : r.shiftOut = v.shiftOut) (hps : r.pstate = v.pstate) (hun : r.u8need = v.u8need)
    (hua : r.u8acc = v.u8acc) : readable r = readable v := by
  unfold readable
  rw [hc, hr, hg, hcur, hp, hm, ht, hb, htabs, halt, hs, h0, h1, hso, hps, hun, hua]

/-- **The repaint reproduces everything later output reads but a partial sequence.** A live
receiver of a live terminal's size that has parsed the terminal's repaint reads the same as the
terminal with its partial parser state forgotten: the grid and the stashed main screen, the
cursor with its deferred wrap, the DECSC slot, the pen, the modes but the mouse mode, the scroll
region, the tab ruler, the charsets and shift state, and a quiet decoder. -/
theorem restore_readable_quiesce (v w : Vt) (hv : LiveReachableVt v) (hw : LiveReachableVt w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) :
    readable (w.feed (restore v)) = readable v.quiesce := by
  rw [feed_restore_zeroed v w (u8Ok_of_liveReachable hw)]
  have hgood :
    Good
      { w with
        u8need := 0, u8acc := 0 } :=
    Good.set_u8 0 0 (by omega) (good_of_liveReachable hw)
  have hren :
    Renderable
      { w with
        u8need := 0, u8acc := 0 } :=
    renderable_congr (renderable_of_liveReachable hw) rfl rfl rfl rfl
  generalize hw0 :
    ({ w with
        u8need := 0, u8acc := 0 } :
      Vt) =
    w0 at hgood hren
  have hc0 : w0.cols = v.cols := by
    rw [← hw0]; exact hcols
  have hr0 : w0.rows = v.rows := by
    rw [← hw0]; exact hrows
  have hua : w0.u8acc = 0 := by rw [← hw0]
  have hun : w0.u8need = 0 := by rw [← hw0]
  have hgv := good_of_liveReachable hv
  have hvren := renderable_of_liveReachable hv
  have hvtabs := tabsOk_of_liveReachable hv
  -- the paint
  obtain ⟨ups, un, ugrid, uins, uwrap, -⟩ := screens_paint v w0 hgood hren hc0 hr0 hua hun hvren
  obtain ⟨uc, ur, ut, ub, u0, u1, uo⟩ := restore_paint_canonical v w0 hgood hren hc0 hr0 hua hun
  have ualt := screens_stash v w0 hgood hren hc0 hr0 hua hun hgv hvren
  have uso :
    (Vt.feed w0 (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).shiftOut =
      false := by
    obtain ⟨-, -, -, -, ep, -, -, -, -, -, -, -, -, -, -, es⟩ :=
      paint_entry v w0 hgood hren hc0 hr0 hua hun
    have hs := (smap_screensAnsi v _ ep).2
    rw [es] at hs
    have h := congrArg Sticky.so hs
    rw [stick_so, ← feed_append] at h
    rw [h]
    split
    · unfold stAlt
      dsimp only
      split <;> rfl
    · rfl
  have ugood := Good.feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) hgood
  have uren :=
    renderable_feed hren (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)
  have uua :=
    u8Ok_feed (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v) (fun _ => hua) un
  obtain ⟨dcur, dtop, dbot, dalt, dsaved, d0, d1, dso⟩ :=
    tail_shows v _ hgv hvren ugood uren uc ur ugrid ut ub u0 u1 uso uwrap uins uo ups un uua ualt
  have hrest :
    Vt.feed w0 (restore v) =
      (Vt.feed w0 (prologueAnsi v ++ csiNum 0 0x6D ++ csiNum 2 0x4A ++ screensAnsi v)).feed
        (savedAnsi v ++ regionAnsi v ++ tabsAnsi v ++ titleAnsi v ++ modesAnsi v ++ charsetAnsi v ++
          penSgr v.pen ++
          cursorAnsi v ++
          cursorPendingAnsi v) := by
    rw [restore_split, feed_append]
  obtain ⟨qp, qn⟩ := restore_quiesced_any v w0
  apply readable_eq
  · rw [← dims_fst, dims_feed _ hgood, dims_fst]; exact hc0
  · rw [← dims_snd, dims_feed _ hgood, dims_snd]; exact hr0
  · exact restore_grid_any v w0 hgood hren hc0 hr0 hua hun hvren
  · rw [hrest]; exact dcur
  · exact restore_pen_any v w0
  · exact restore_modes_unmoused v w0
  · rw [hrest]; exact dtop
  · rw [hrest]; exact dbot
  · exact restore_tabs_any v w0 hgood hc0 hvtabs
  · rw [hrest]; exact dalt
  · rw [hrest]; exact dsaved
  · rw [hrest]; exact d0
  · rw [hrest]; exact d1
  · rw [hrest]; exact dso
  · exact qp
  · exact qn
  · exact u8Ok_feed (restore v) (fun _ => hua) qn

/-- A terminal between control sequences and characters, whose decoder keeps no bits once it
expects no byte, has no partial parser state to forget. -/
theorem quiesce_of_atBoundary {v : Vt} (hu : U8Ok v) (hb : v.atBoundary = true) :
    v.quiesce = v := by
  have hvb : v.pstate = .ground ∧ v.u8need = 0 := by
    unfold Vt.atBoundary at hb
    simpa using hb
  have ha := hu hvb.2
  cases v
  simp_all [Vt.quiesce]

/-- **The repaint reproduces everything later output reads.** Taken between control sequences
and characters, the terminal has no partial parser state, and its live receiver reads the same
as the terminal itself. -/
theorem restore_readable (v w : Vt) (hv : LiveReachableVt v) (hw : LiveReachableVt w)
    (hcols : w.cols = v.cols) (hrows : w.rows = v.rows) (hb : v.atBoundary = true) :
    readable (w.feed (restore v)) = readable v := by
  rw [restore_readable_quiesce v w hv hw hcols hrows,
    quiesce_of_atBoundary (u8Ok_of_liveReachable hv) hb]

/-- Two terminals later output reads the same of show the same screen. -/
theorem shows_readable {u v : Vt} (h : readable u = readable v) :
    Shows Vt.colCount Vt.rowCount Vt.getRow Vt.cursorPos stick v u :=
  ⟨(congrArg Vt.colCount h :), (congrArg Vt.rowCount h :), fun y _ =>
    (congrArg (Vt.getRow · y) h :), (congrArg Vt.cursorPos h :), (congrArg stick h :)⟩

/-- **A repaint restores its terminal.** Any receiver of the repaint of any terminal holds the
terminal's pen and every mode but the mouse mode (`restore_pen_any`, `restore_modes_unmoused`), the mouse mode too when a program could have set
it (`restore_modes_any`), and sits between control sequences and characters
(`restore_quiesced_any`); one as tall as the terminal holds its sticky fields when DECSTBM could
have set its region (`restore_sticky_any`). A live receiver of a live terminal's size shows the
terminal's screen, since it reads as the terminal does once the terminal's partial parser state
is forgotten (`restore_readable_quiesce`). When the terminal sits between control sequences and
characters too, the receiver reads the same as the terminal (`restore_readable`), and later
output cannot tell apart two terminals it reads the same of (`readable_feed`). -/
theorem restore_restores (v w : Vt) :
    Restores LiveReachableVt Vt.feed Vt.colCount Vt.rowCount Vt.getRow Vt.cursorPos Vt.getPen
      Vt.getModes stick Vt.atBoundary v w (w.feed (restore v)) := by
  refine
    ⟨restore_pen_any v w, ?_, fun mouse => congrArg Modes.mouse (restore_modes_any v w mouse), ?_,
      fun height region inside fits => restore_sticky_any v w height region inside fits,
      fun hv hw hcols hrows =>
      ⟨(shows_readable (restore_readable_quiesce v w hv hw hcols hrows) :), fun hb later => ?_⟩⟩
  · -- stated through `modes` itself, so no check unfolds the receiver's feed
    unfold Vt.getModes
    exact restore_modes_unmoused v w
  · obtain ⟨hp, hn⟩ := restore_quiesced_any v w
    simp [Vt.atBoundary, hp, hn]
  · have h := readable_feed (restore_readable v w hv hw hcols hrows hb) later
    exact
      ⟨shows_readable h, (congrArg Vt.getPen h :), (congrArg Vt.getModes h :),
        (congrArg Vt.atBoundary h :)⟩

/-- The repaint as one synchronized update: the closing bracket finds the receiver between
control sequences and characters, where it changes nothing (`feed_syncEnd`). -/
theorem feed_synced (v w : Vt) : w.feed (synced v) = (w.feed syncBegin).feed (restore v) := by
  unfold synced
  rw [feed_append, feed_append, feed_syncEnd]
  obtain ⟨hp, hn⟩ := restore_quiesced_any v (w.feed syncBegin)
  simp [Vt.atBoundary, hp, hn]

/-- The opening bracket keeps what `Restores` asks of the receiver: its size, and that a session
holds it. -/
theorem syncBegin_keeps (w : Vt) :
    (w.feed syncBegin).cols = w.cols ∧
      (w.feed syncBegin).rows = w.rows ∧
      (LiveReachableVt w → LiveReachableVt (w.feed syncBegin)) := by
  have h := dims_feed_ne_ris syncBegin (v := w) (by decide)
  simp only [dims, Prod.mk.injEq] at h
  exact ⟨h.1, h.2, fun hw => .feed hw syncBegin⟩

/-- **A repaint restores its terminal**, streamed at any positive budget as one synchronized
update: the receiver the repaint meets is the one the opening bracket left, of the same size and
held by a session when the first is (`syncBegin_keeps`), and the closing bracket changes nothing
(`feed_synced`), so `restore_restores` carries over. -/
theorem restores (budget : Nat) (positive : 0 < budget) (v w : Vt) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        Restores LiveReachableVt Vt.feed Vt.colCount Vt.rowCount Vt.getRow Vt.cursorPos Vt.getPen
          Vt.getModes stick Vt.atBoundary v w (w.feed bytes) := by
  refine ⟨synced v, ?_, ?_⟩
  · rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  · obtain ⟨hcols, hrows, hlive⟩ := syncBegin_keeps w
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := restore_restores v (w.feed syncBegin)
    rw [feed_synced]
    refine
      ⟨h1, h2, h3, h4, fun height => h5 (by simpa [stick, hrows] using height), fun hv hw hc hr =>
        h6 hv (hlive hw) ?_ ?_⟩
    · simpa [Vt.colCount, hcols] using hc
    · simpa [Vt.rowCount, hrows] using hr

end Terminal.Render
