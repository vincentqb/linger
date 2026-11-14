module

import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt.State

/-! # What later output reads of a terminal

`step` writes the history, the window title, the bell and the mouse mode and never reads them:
no cell, cursor, mode it acts on or parser state depends on them. `readable` blanks those four,
and `readable_feed` says that two terminals that read the same keep reading the same under any
output. A repaint that reproduces everything else therefore keeps showing what its source shows
(`Terminal.Proofs.Render.Shows`).

Each operation `f` is shown to `Respects` that cut, `readable (f v) = readable (f (readable v))`,
bottom up from the record updates to `step`. `readable` and `Respects` are reducible, so after
`unfold` the tests an operation makes of `readable v` reduce to the same tests of `v`, and one
`split` takes both sides down the same branch. -/

namespace Terminal.Vt

/-- What later output can read of a terminal: everything but its history, its title, its bell
and its mouse mode, which `step` only writes. -/
abbrev readable (v : Vt) : Vt :=
  { v with
    sb := {}, title := "", bell := false, modes := { v.modes with mouse := 0 } }

/-- `f` respects what later bytes read: what they read of its result depends only on what they
read of its argument. -/
abbrev Respects (f : Vt → Vt) : Prop := ∀ v, readable (f v) = readable (f (readable v))

theorem Respects.comp {f g : Vt → Vt} (hf : Respects f) (hg : Respects g) :
    Respects (fun v => g (f v)) := by
  intro v
  show readable (g (f v)) = readable (g (f (readable v)))
  rw [hg (f v), hf v, ← hg (f (readable v))]

theorem Respects.foldl {α : Type} {f : Vt → α → Vt} (hf : ∀ a, Respects (f · a)) :
    ∀ l : List α, Respects (l.foldl f ·)
  | [], _ => rfl
  | a :: l, v => by
    show readable (l.foldl f (f v a)) = readable (l.foldl f (f (readable v) a))
    rw [Respects.foldl hf l (f v a), hf a v, ← Respects.foldl hf l (f (readable v) a)]

theorem respects_repeatAtMost (cap count : Nat) {f : Vt → Vt} (hf : Respects f) :
    Respects (·.repeatAtMost cap count f) := Respects.foldl (f := fun w _ => f w) (fun _ => hf) _

theorem respects_clearPending : Respects Vt.clearPending := fun _ => rfl

theorem respects_carriageReturn : Respects Vt.carriageReturn := fun _ => rfl

theorem respects_moveTo (x y : Nat) : Respects (·.moveTo x y) := fun _ => rfl

theorem respects_moveRel (dx dy : Int) : Respects (·.moveRel dx dy) := fun _ => rfl

theorem respects_setCol (x : Nat) : Respects (·.setCol x) := fun _ => rfl

theorem respects_tab : Respects Vt.tab := fun _ => rfl

theorem respects_backTab : Respects Vt.backTab := fun _ => rfl

theorem respects_saveCursor : Respects Vt.saveCursor := fun _ => rfl

theorem respects_restoreCursor : Respects Vt.restoreCursor := fun _ => rfl

theorem respects_scrollDownIn (t b : Nat) : Respects (·.scrollDownIn t b) := fun _ => rfl

theorem respects_scrollDown : Respects Vt.scrollDown := fun _ => rfl

theorem respects_putCell (x y : Nat) (c : Cell) : Respects (·.putCell x y c) := fun _ => rfl

theorem respects_mendRow (x y : Nat) : Respects (·.mendRow x y) := fun _ => rfl

theorem respects_eraseRowSpan (y a b : Nat) : Respects (·.eraseRowSpan y a b) := fun _ => rfl

theorem respects_deleteChars (n : Nat) : Respects (·.deleteChars n) := fun _ => rfl

theorem respects_insertChars (n : Nat) : Respects (·.insertChars n) := fun _ => rfl

theorem respects_eraseChars (n : Nat) : Respects (·.eraseChars n) := fun _ => rfl

theorem respects_applySgr (ps : List (Nat × Bool)) : Respects (·.applySgr ps) := fun _ => rfl

theorem respects_scrollUpIn (t b : Nat) (a : Bool) : Respects (·.scrollUpIn t b a) := by
  intro v
  unfold Vt.scrollUpIn
  dsimp only
  split <;> rfl

theorem respects_scrollUp : Respects Vt.scrollUp := fun v => respects_scrollUpIn v.top v.bot true v

theorem respects_lineFeed : Respects Vt.lineFeed := by
  intro v
  unfold Vt.lineFeed Vt.clearPending
  dsimp only
  split
  · exact respects_scrollUp _
  · split <;> rfl

theorem respects_reverseIndex : Respects Vt.reverseIndex := by
  intro v
  unfold Vt.reverseIndex Vt.clearPending
  dsimp only
  split <;> rfl

theorem respects_backspace : Respects Vt.backspace := by
  intro v
  unfold Vt.backspace
  split <;> rfl

theorem respects_printWrap : Respects Vt.printWrap := by
  intro v
  unfold Vt.printWrap
  split
  · exact respects_carriageReturn.comp respects_lineFeed v
  · rfl

theorem respects_printWideWrap (w : Nat) : Respects (·.printWideWrap w) := by
  intro v
  unfold Vt.printWideWrap
  dsimp only
  split
  · exact respects_carriageReturn.comp respects_lineFeed v
  · rfl

theorem respects_printShift (w : Nat) : Respects (·.printShift w) := by
  intro v
  unfold Vt.printShift
  dsimp only
  split <;> rfl

theorem respects_printPut (ch : Char) (w : Nat) : Respects (·.printPut ch w) := by
  intro v
  unfold Vt.printPut
  dsimp only
  split
  · rfl
  · split <;> rfl

theorem respects_printAdvance (w : Nat) : Respects (·.printAdvance w) := by
  intro v
  unfold Vt.printAdvance
  dsimp only
  split <;> rfl

/-- The cells a mark reads are read through `getCell`, unfolded so the two sides' tests match. -/
theorem respects_printMark (ch : Char) : Respects (·.printMark ch) := by
  intro v
  unfold Vt.printMark Vt.getCell Vt.getRow
  dsimp only
  repeat' split
  all_goals rfl

theorem respects_print (ch : Char) : Respects (·.print ch) := by
  intro v
  unfold Vt.print Vt.printChar
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | exact respects_printMark _ v
      |
        exact
          ((((respects_printWrap.comp (respects_printWideWrap _)).comp (respects_printShift _)).comp
                  (respects_printPut _ _)).comp
              (respects_printAdvance _))
            v

theorem respects_setPstate (p : PState) : Respects ({ · with pstate := p }) := fun _ => rfl

theorem cursor_eraseLine (v : Vt) (m : Nat) : (v.eraseLine m).cursor = v.cursor := by
  rw [frame_eraseLine]

theorem rows_eraseLine (v : Vt) (m : Nat) : (v.eraseLine m).rows = v.rows := by rw [frame_eraseLine]

theorem respects_eraseLine (m : Nat) : Respects (·.eraseLine m) := by
  intro v
  unfold Vt.eraseLine
  dsimp only
  split <;> rfl

theorem respects_eraseCols (f : Nat → Nat) :
    Respects (fun (w : Vt) => w.eraseRowSpan (f 0) 0 w.cols) := fun _ => rfl

theorem respects_eraseScreen (m : Nat) : Respects (·.eraseScreen m) := by
  intro v
  unfold Vt.eraseScreen
  dsimp only
  simp only [cursor_eraseLine, rows_eraseLine]
  split
  · exact
      ((respects_eraseLine 0).comp
          (Respects.foldl (f := fun v' i => v'.eraseRowSpan (v.cursor.y + 1 + i) 0 v'.cols)
            (fun _ _ => rfl) _))
        v
  · exact
      ((respects_eraseLine 1).comp
          (Respects.foldl (f := fun v' y => v'.eraseRowSpan y 0 v'.cols) (fun _ _ => rfl) _))
        v
  · exact Respects.foldl (f := fun v' y => v'.eraseRowSpan y 0 v'.cols) (fun _ _ => rfl) _ v
  · exact Respects.foldl (f := fun v' y => v'.eraseRowSpan y 0 v'.cols) (fun _ _ => rfl) _ v

theorem respects_insertLines (n : Nat) : Respects (·.insertLines n) := by
  intro v
  unfold Vt.insertLines
  dsimp only
  split
  · rfl
  · exact respects_repeatAtMost _ _ (respects_scrollDownIn _ _) v

theorem respects_deleteLines (n : Nat) : Respects (·.deleteLines n) := by
  intro v
  unfold Vt.deleteLines
  dsimp only
  split
  · rfl
  · exact respects_repeatAtMost _ _ (respects_scrollUpIn _ _ _) v

theorem respects_enterAlt (s : Bool) : Respects (·.enterAlt s) := by
  intro v
  unfold Vt.enterAlt Vt.cursorSaved
  dsimp only
  split <;> rfl

theorem respects_leaveAlt (s : Bool) : Respects (·.leaveAlt s) := by
  intro v
  unfold Vt.leaveAlt
  dsimp only
  repeat' split
  all_goals rfl

theorem respects_setMode (priv : Bool) (n : Nat) (on : Bool) : Respects (·.setMode priv n on) := by
  intro v
  unfold Vt.setMode
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact respects_enterAlt _ v
      | exact respects_leaveAlt _ v
      | exact respects_saveCursor v
      | exact respects_restoreCursor v
      | exact respects_moveTo 0 0 _

theorem respects_setModes (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    Respects (·.setModes priv ps on) :=
  Respects.foldl (f := fun w (p : Nat × Bool) => w.setMode priv p.1 on)
    (fun _ => respects_setMode _ _ _) ps

theorem respects_csiDispatch (s : CsiState) (final : UInt8) : Respects (·.csiDispatch s final) := by
  intro v
  unfold Vt.csiDispatch
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact respects_insertChars _ v
      | exact respects_moveRel _ _ v
      | exact (respects_moveRel _ _).comp respects_carriageReturn v
      | exact respects_setCol _ v
      | exact respects_moveTo _ _ _
      | exact respects_repeatAtMost _ _ respects_tab v
      | exact respects_repeatAtMost _ _ respects_backTab v
      | exact respects_repeatAtMost _ _ respects_scrollUp v
      | exact respects_repeatAtMost _ _ respects_scrollDown v
      | exact respects_eraseScreen _ v
      | exact respects_eraseLine _ v
      | exact respects_insertLines _ v
      | exact respects_deleteLines _ v
      | exact respects_deleteChars _ v
      | exact respects_eraseChars _ v
      | exact respects_setModes _ _ _ v
      | exact respects_applySgr _ v
      | exact respects_saveCursor v
      | exact respects_restoreCursor v

theorem respects_csiFinish (s : CsiState) (final : UInt8) : Respects (·.csiFinish s final) := by
  intro v
  unfold Vt.csiFinish
  dsimp only
  exact (respects_csiDispatch _ _).comp (respects_setPstate _) v

theorem respects_oscFinish (acc : Array UInt8) : Respects (·.oscFinish acc) := by
  intro v
  unfold Vt.oscFinish
  dsimp only
  repeat' split
  all_goals rfl

theorem respects_ctl (b : UInt8) : Respects (·.ctl b) := by
  intro v
  unfold Vt.ctl
  split
  all_goals
    with_reducible
      first
      | rfl
      | exact respects_backspace v
      | exact respects_tab v
      | exact respects_lineFeed v
      | exact respects_carriageReturn v

theorem respects_acceptChar (n : Nat) : Respects (·.acceptChar n) := by
  intro v
  unfold Vt.acceptChar
  split <;> exact respects_print _ v

theorem respects_stepGround (b : UInt8) : Respects (·.stepGround b) := by
  intro v
  unfold Vt.stepGround
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact respects_ctl _ v
      | exact respects_acceptChar _ v
      | exact respects_acceptChar _ _

theorem respects_stepEsc (b : UInt8) : Respects (·.stepEsc b) := by
  intro v
  unfold Vt.stepEsc
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact respects_saveCursor.comp (respects_setPstate _) v
      | exact respects_restoreCursor.comp (respects_setPstate _) v
      | exact respects_lineFeed.comp (respects_setPstate _) v
      | exact (respects_carriageReturn.comp respects_lineFeed).comp (respects_setPstate _) v
      | exact respects_reverseIndex.comp (respects_setPstate _) v

theorem respects_stepEscInter (i b : UInt8) : Respects (·.stepEscInter i b) := by
  intro v
  unfold Vt.stepEscInter
  dsimp only
  repeat' split
  all_goals rfl

theorem respects_csiInterEnd (s : CsiState) (final : UInt8) :
    Respects (·.csiInterEnd s final) := fun _ => rfl

theorem respects_stepCsi (s : CsiState) (b : UInt8) : Respects (·.stepCsi s b) := by
  intro v
  unfold Vt.stepCsi
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact respects_csiFinish _ _ v
      | exact respects_csiInterEnd _ _ v
      | exact respects_ctl _ v

theorem respects_stepOsc (acc : Array UInt8) (e : Bool) (b : UInt8) :
    Respects (·.stepOsc acc e b) := by
  intro v
  unfold Vt.stepOsc
  dsimp only
  repeat' split
  all_goals
    with_reducible
      first
      | rfl
      | exact respects_oscFinish _ v

theorem respects_stepStr (e : Bool) (b : UInt8) : Respects (·.stepStr e b) := by
  intro v
  unfold Vt.stepStr
  dsimp only
  repeat' split
  all_goals rfl

theorem respects_abortUtf8 (b : UInt8) : Respects (·.abortUtf8 b) := by
  intro v
  unfold Vt.abortUtf8
  dsimp only
  split <;> rfl

theorem respects_step (b : UInt8) : Respects (·.step b) := by
  intro v
  unfold Vt.step
  dsimp only
  simp only [ps_abortUtf8]
  split
  all_goals
    with_reducible
      first
      | exact (respects_abortUtf8 b).comp (respects_stepGround b) v
      | exact (respects_abortUtf8 b).comp (respects_stepEsc b) v
      | exact (respects_abortUtf8 b).comp (respects_stepEscInter _ b) v
      | exact (respects_abortUtf8 b).comp (respects_stepCsi _ b) v
      | exact (respects_abortUtf8 b).comp (respects_stepOsc _ _ b) v
      | exact (respects_abortUtf8 b).comp (respects_stepStr _ b) v

theorem respects_feed (bs : List UInt8) : Respects (·.feed bs) :=
  Respects.foldl (f := Vt.step) respects_step bs

/-- **Later output cannot tell apart two terminals it reads the same of**: feeding the same
bytes to both leaves them reading the same, whatever their histories, titles, bells and
mouse modes. -/
theorem readable_feed {v w : Vt} (h : readable v = readable w) (bs : List UInt8) :
    readable (v.feed bs) = readable (w.feed bs) := by
  rw [respects_feed bs v, h, ← respects_feed bs w]

/-- …and every row shows what later output reads. -/
theorem readable_getRow (v : Vt) (y : Nat) : (readable v).getRow y = v.getRow y := rfl

end Terminal.Vt
