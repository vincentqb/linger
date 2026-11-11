module

import all Terminal.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.State
import all Terminal.Proofs.Vt.Renderable
import all Terminal.Proofs.Render.Keeps

/-! # History is the record of what left the screen

A terminal's history only gains rows at its end, keeping its newest `sbCap` rows, until output
asks to erase it. `Grows` is that relation between two states, and every operation of the
emulator but the erase of `CSI 3 J` moves along it. A scan of the output (`EraseScan`) keeps up
with the parser: whenever the parser could be completing `CSI 3 J`, the scan has seen a `[` and
a `3` since, so output in which the scan finds no such `J` (`mayErase`) keeps the history
(`history_feed`). A resize keeps it too, adding the main screen's rows that leave its top
(`history_resize`); `CSI 3 J` empties it (`history_erase`) and a reset (`ESC c`) keeps it
(`history_reset`). -/

namespace Terminal.Vt

/-! ## Lists that keep their newest rows -/

/-- Keeping the newest `n` of a list, adding `m` and keeping the newest `n` again keeps the newest
`n` of the list followed by `m`. -/
theorem newest_append {α : Type} (l m : List α) (n : Nat) :
    newest n (newest n l ++ m) = newest n (l ++ m) := by
  unfold newest
  by_cases hl : l.length ≤ n
  · have : l.length - n = 0 := by omega
    simp [this]
  · have hd : l.length - n ≤ l.length := by omega
    have hlen : (l.drop (l.length - n)).length = n := by
      simp; omega
    simp only [List.length_append, hlen]
    have h1 : n + m.length - n = m.length := by omega
    have h2 : l.length + m.length - n = (l.length - n) + m.length := by omega
    rw [h1, h2, ← List.drop_drop, List.drop_append_of_le_length hd]

/-- A list of at most `n` entries is its own newest `n`. -/
theorem newest_of_le {α : Type} {l : List α} {n : Nat} (h : l.length ≤ n) : newest n l = l := by
  unfold newest
  rw [Nat.sub_eq_zero_of_le h, List.drop_zero]

/-- A ring's history has one row per stored row. -/
theorem ring_toList_length (r : Ring) : r.toList.length = r.data.size := by
  simp only [Ring.toList, List.length_append, List.length_drop, List.length_take,
    Array.length_toList]
  omega

/-- Adding a row to a ring of at most `sbCap` rows adds it to the end of its history, of which
the newest `sbCap` rows stay. -/
theorem ring_toList_push (r : Ring) (row : Row) (h : r.data.size ≤ sbCap) :
    (r.push row).toList = newest sbCap (r.toList ++ [row]) := by
  unfold newest
  have hlen := ring_toList_length r
  unfold Ring.push
  split
  · rename_i hlt
    have hk : (r.toList ++ [row]).length - sbCap = 0 := by
      simp [hlen]; omega
    rw [hk, List.drop_zero]
    split
    · rename_i h0
      simp [Ring.toList, h0]
    · simp [Ring.toList]
  · rename_i hge
    have hsize : r.data.size = sbCap := by omega
    have hk : (r.toList ++ [row]).length - sbCap = 1 := by
      simp [hlen]; omega
    rw [hk]
    have heff :
      r.toList =
        r.data.toList.drop (if r.start < r.data.size then r.start else 0) ++
          r.data.toList.take (if r.start < r.data.size then r.start else 0) := by
      split
      · rfl
      · rename_i hs
        simp only [Ring.toList, List.drop_zero, List.take_zero, List.append_nil]
        rw [List.drop_eq_nil_of_le
            (by
              simp; omega),
          List.take_of_length_le
            (by
              simp; omega)]
        simp
    generalize hsdef : (if r.start < r.data.size then r.start else 0) = s at heff ⊢
    have hcap0 : 0 < sbCap := by decide
    have hs : s < r.data.size := by
      rw [← hsdef]; split <;> omega
    rw [heff]
    simp only [Ring.toList, Array.toList_setIfInBounds]
    rw [List.set_eq_take_append_cons_drop,
      ite_eq_left
        (by
          simp; omega)]
    have hdrop :
      r.data.toList.drop s =
        r.data.toList[s]'(by
              simp; omega) ::
          r.data.toList.drop (s + 1) := by
      rw [List.drop_eq_getElem_cons]
    have htake : (r.data.toList.take s).length = s := by
      simp; omega
    rw [hdrop, List.cons_append, List.cons_append, List.drop_one, List.tail_cons]
    by_cases hlast : s + 1 < sbCap
    · rw [Nat.mod_eq_of_lt hlast, List.drop_append, List.take_append, htake,
        List.drop_of_length_le (by omega), List.take_of_length_le (by omega)]
      simp
    · have hs1 : s + 1 = sbCap := by omega
      rw [hs1, Nat.mod_self, List.drop_zero, List.take_zero, List.append_nil,
        List.drop_eq_nil_of_le
          (by
            simp; omega)]
      simp

/-- Adding rows one by one adds them all to the end, and the newest `sbCap` stay. -/
theorem ring_toList_pushAll (r : Ring) (rows : List Row) (h : r.data.size ≤ sbCap) :
    (rows.foldl Ring.push r).toList = newest sbCap (r.toList ++ rows) := by
  induction rows generalizing r with
  | nil =>
    simp [newest_of_le
          (by
            rw [ring_toList_length]; omega : r.toList.length ≤ sbCap)]
  | cons row rows ih =>
    simp only [List.foldl_cons]
    rw [ih (r.push row) (ring_push_le row h), ring_toList_push r row h, newest_append]
    simp

/-! ## The relation every operation but an erase moves along -/

/-- `w`'s history is `v`'s with rows added at its end, of which the newest `sbCap` stay. -/
def Grows (v w : Vt) : Prop := ∃ added : List Row, w.sb.toList = newest sbCap (v.sb.toList ++ added)

/-- An operation that keeps the history moves along `Grows`. -/
theorem Grows.of_eq {v w : Vt} (h : v.sb.data.size ≤ sbCap) (hsb : w.sb = v.sb) : Grows v w :=
  ⟨[], by
    rw [hsb, List.append_nil,
      newest_of_le (l := v.sb.toList)
        (by
          rw [ring_toList_length]; exact h)]⟩

/-- `Grows` is reflexive. -/
theorem Grows.refl {v : Vt} (h : v.sb.data.size ≤ sbCap) : Grows v v := .of_eq h rfl

/-- `Grows` composes. -/
theorem Grows.trans {u v w : Vt} (h₁ : Grows u v) (h₂ : Grows v w) : Grows u w := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exact ⟨a ++ b, by rw [hb, ha, newest_append, List.append_assoc]⟩

/-- Adding one row moves along `Grows`. -/
theorem Grows.push {v w : Vt} (h : v.sb.data.size ≤ sbCap) (row : Row)
    (hsb : w.sb = v.sb.push row) : Grows v w := ⟨[row], by rw [hsb, ring_toList_push v.sb row h]⟩

/-! ## Each operation moves along it -/

namespace Grows

/-- An operation that keeps the history, from a state the emulator can reach. -/
theorem frame {v w : Vt} (h : Good v) (hsb : w.sb = v.sb) : Grows v w := .of_eq h.sbLe hsb

theorem clearPending {v : Vt} (h : Good v) : Grows v v.clearPending :=
  frame h (by rw [frame_clearPending])

theorem carriageReturn {v : Vt} (h : Good v) : Grows v v.carriageReturn :=
  frame h (by rw [frame_carriageReturn])

theorem moveTo {v : Vt} (h : Good v) (x y : Nat) : Grows v (v.moveTo x y) :=
  frame h (by rw [frame_moveTo])

theorem moveRel {v : Vt} (h : Good v) (dx dy : Int) : Grows v (v.moveRel dx dy) := frame h rfl

theorem setCol {v : Vt} (h : Good v) (x : Nat) : Grows v (v.setCol x) :=
  frame h (by rw [frame_setCol])

theorem backspace {v : Vt} (h : Good v) : Grows v v.backspace := frame h (by rw [frame_backspace])

theorem tab {v : Vt} (h : Good v) : Grows v v.tab := frame h (by rw [frame_tab])

theorem backTab {v : Vt} (h : Good v) : Grows v v.backTab := frame h (by rw [frame_backTab])

theorem scrollUpIn {v : Vt} (h : Good v) (t b : Nat) (a : Bool) : Grows v (v.scrollUpIn t b a) := by
  unfold Vt.scrollUpIn
  dsimp only
  split
  · exact .push h.sbLe _ rfl
  · exact frame h rfl

theorem scrollUp {v : Vt} (h : Good v) : Grows v v.scrollUp := scrollUpIn h _ _ _

theorem scrollDownIn {v : Vt} (h : Good v) (t b : Nat) : Grows v (v.scrollDownIn t b) :=
  frame h (by rw [frame_scrollDownIn])

theorem scrollDown {v : Vt} (h : Good v) : Grows v v.scrollDown := scrollDownIn h _ _

theorem lineFeed {v : Vt} (h : Good v) : Grows v v.lineFeed := by
  have hc := Good.clearPending h
  unfold Vt.lineFeed
  dsimp only
  refine (clearPending h).trans ?_
  split
  · exact scrollUp hc
  · split
    · exact frame hc rfl
    · exact refl hc.sbLe

theorem reverseIndex {v : Vt} (h : Good v) : Grows v v.reverseIndex :=
  frame h (by rw [frame_reverseIndex])

theorem eraseLine {v : Vt} (h : Good v) (m : Nat) : Grows v (v.eraseLine m) :=
  frame h (by rw [frame_eraseLine])

/-- Every erase of the screen but `ED 3` keeps the history. -/
theorem eraseScreen {v : Vt} (h : Good v) (m : Nat) (hm : m ≠ 3) : Grows v (v.eraseScreen m) :=
  frame h
    (by
      rw [frame_eraseScreen]; simp [hm])

theorem insertLines {v : Vt} (h : Good v) (n : Nat) : Grows v (v.insertLines n) :=
  frame h (by rw [frame_insertLines])

theorem deleteLines {v : Vt} (h : Good v) (n : Nat) : Grows v (v.deleteLines n) :=
  frame h (by rw [frame_deleteLines])

theorem deleteChars {v : Vt} (h : Good v) (n : Nat) : Grows v (v.deleteChars n) := frame h rfl

theorem insertChars {v : Vt} (h : Good v) (n : Nat) : Grows v (v.insertChars n) := frame h rfl

theorem eraseChars {v : Vt} (h : Good v) (n : Nat) : Grows v (v.eraseChars n) :=
  frame h
    (by
      unfold Vt.eraseChars; rw [frame_eraseRowSpan])

theorem applySgr {v : Vt} (h : Good v) (ps : List (Nat × Bool)) : Grows v (v.applySgr ps) :=
  frame h (by rw [frame_applySgr])

theorem enterAlt {v : Vt} (h : Good v) (s : Bool) : Grows v (v.enterAlt s) :=
  frame h (by rw [frame_enterAlt])

theorem leaveAlt {v : Vt} (h : Good v) (s : Bool) : Grows v (v.leaveAlt s) :=
  frame h (by rw [frame_leaveAlt])

theorem setMode {v : Vt} (h : Good v) (priv : Bool) (n : Nat) (on : Bool) :
    Grows v (v.setMode priv n on) := by
  unfold Vt.setMode
  repeat' split
  all_goals
    first
    | exact frame h rfl
    | exact moveTo (Good.set_modes _ h) _ _ |> (frame h rfl).trans
    | exact enterAlt h _
    | exact leaveAlt h _

theorem setModes {v : Vt} (h : Good v) (priv : Bool) (ps : List (Nat × Bool)) (on : Bool) :
    Grows v (v.setModes priv ps on) := by
  induction ps generalizing v with
  | nil =>
    rw [setModes_nil]; exact refl h.sbLe
  | cons p ps ih =>
    rw [setModes_cons]
    exact (setMode h priv p.1 on).trans (ih (Good.setMode priv p.1 on h))

theorem foldl {α : Type} {f : Vt → α → Vt} (hf : ∀ w a, Good w → Grows w (f w a))
    (hg : ∀ w a, Good w → Good (f w a)) (l : List α) {v : Vt} (h : Good v) :
    Grows v (l.foldl f v) := by
  induction l generalizing v with
  | nil => exact refl h.sbLe
  | cons a l ih => exact (hf v a h).trans (ih (hg v a h))

theorem repeatAtMost {v : Vt} (h : Good v) (cap count : Nat) {f : Vt → Vt}
    (hf : ∀ w, Good w → Grows w (f w)) (hg : ∀ w, Good w → Good (f w)) :
    Grows v (v.repeatAtMost cap count f) :=
  foldl (fun w _ hw => hf w hw) (fun w _ hw => hg w hw) _ h

/-- `CNL` and `CPL`: a relative move, then a carriage return. -/
theorem moveRelReturn {v : Vt} (h : Good v) (dx dy : Int) :
    Grows v (v.moveRel dx dy).carriageReturn :=
  (moveRel h dx dy).trans (carriageReturn (Good.moveRel dx dy h))

/-- A dispatch keeps the history unless it is an `ED` whose first parameter is 3. -/
theorem csiDispatch {v : Vt} (h : Good v) (s : CsiState) (final : UInt8)
    (hsafe : final = 0x4A → s.ignore = false → s.arg 0 0 ≠ 3) :
    Grows v (v.csiDispatch s final) := by
  unfold Vt.csiDispatch
  split
  · exact refl h.sbLe
  · next hi =>
      have hi' : s.ignore = false := by simpa using hi
      dsimp only
      split
      -- `ED`, the eleventh final, is the one dispatch that may erase the history
      case h_11 => exact eraseScreen h _ (hsafe rfl hi')
      all_goals
        repeat' split
        all_goals
          with_reducible
            first
            | exact insertChars h _
            | exact moveRel h _ _
            | exact moveRelReturn h _ _
            | exact setCol h _
            | exact moveTo h _ _
            | exact repeatAtMost h _ _ (fun _ hw => tab hw) (fun _ hw => Good.tab hw)
            | exact repeatAtMost h _ _ (fun _ hw => backTab hw) (fun _ hw => Good.backTab hw)
            | exact repeatAtMost h _ _ (fun _ hw => scrollUp hw) (fun _ hw => Good.scrollUp hw)
            | exact repeatAtMost h _ _ (fun _ hw => scrollDown hw) (fun _ hw => Good.scrollDown hw)
            | exact eraseLine h _
            | exact insertLines h _
            | exact deleteLines h _
            | exact deleteChars h _
            | exact eraseChars h _
            | exact setModes h _ _ _
            | exact applySgr h _
            | exact frame h (by rw [frame_moveTo])
            | exact frame h rfl

theorem putCell {v : Vt} (h : Good v) (x y : Nat) (c : Cell) : Grows v (v.putCell x y c) :=
  frame h (by rw [frame_putCell])

theorem mendRow {v : Vt} (h : Good v) (x y : Nat) : Grows v (v.mendRow x y) :=
  frame h (by rw [frame_mendRow])

theorem printWrap {v : Vt} (h : Good v) : Grows v v.printWrap := by
  unfold Vt.printWrap
  split
  · exact (carriageReturn h).trans (lineFeed (Good.carriageReturn h))
  · exact clearPending h

theorem printWideWrap {v : Vt} (h : Good v) (w : Nat) : Grows v (v.printWideWrap w) := by
  unfold Vt.printWideWrap
  split
  · exact (carriageReturn h).trans (lineFeed (Good.carriageReturn h))
  · exact refl h.sbLe

theorem printShift {v : Vt} (h : Good v) (w : Nat) : Grows v (v.printShift w) :=
  frame h (by rw [frame_printShift])

theorem printPut {v : Vt} (h : Good v) (ch : Char) (w : Nat) : Grows v (v.printPut ch w) :=
  frame h (by rw [frame_printPut])

theorem printMark {v : Vt} (h : Good v) (ch : Char) : Grows v (v.printMark ch) :=
  frame h (by rw [frame_printMark])

theorem printAdvance {v : Vt} (h : Good v) (w : Nat) : Grows v (v.printAdvance w) :=
  frame h (by rw [frame_printAdvance])

theorem print {v : Vt} (h : Good v) (ch : Char) : Grows v (v.print ch) := by
  unfold Vt.print
  dsimp only
  split
  · exact printMark h _
  · have h1 := Good.printWrap h
    have h2 := Good.printWideWrap (charWidth (v.printChar ch)) h1
    have h3 := Good.printShift (charWidth (v.printChar ch)) h2
    have h4 := Good.printPut (v.printChar ch) (charWidth (v.printChar ch)) h3
    exact
      (printWrap h).trans
        ((printWideWrap h1 _).trans
          ((printShift h2 _).trans ((printPut h3 _ _).trans (printAdvance h4 _))))

theorem acceptChar {v : Vt} (h : Good v) (n : Nat) : Grows v (v.acceptChar n) := by
  unfold Vt.acceptChar
  split <;> exact print h _

theorem ctl {v : Vt} (h : Good v) (b : UInt8) : Grows v (v.ctl b) := by
  unfold Vt.ctl
  split
  all_goals
    with_reducible
      first
      | exact backspace h
      | exact tab h
      | exact lineFeed h
      | exact carriageReturn h
      | exact frame h rfl

theorem oscFinish {v : Vt} (h : Good v) (acc : Array UInt8) : Grows v (v.oscFinish acc) :=
  frame h (by rw [frame_oscFinish])

/-- A collector whose first parameter may yet be 3: its first closed parameter is 3, or the one
being read is. -/
def Dangerous (s : CsiState) : Prop := (s.params.getD 0 (0, false)).1 = 3 ∨ s.cur = 3

/-- An `ED` asks for mode 3 only when its first parameter is 3. -/
theorem arg_three {s : CsiState} (h : s.arg 0 0 = 3) : (s.params.getD 0 (0, false)).1 = 3 := by
  unfold CsiState.arg at h
  split at h <;> omega

/-- The first entry of an array after a push: the pushed one when the array was empty. -/
theorem getD_push_zero (a : Array (Nat × Bool)) (x : Nat × Bool) :
    ((a.push x).getD 0 (0, false)).1 = 3 → (a.getD 0 (0, false)).1 = 3 ∨ x.1 = 3 := by
  intro h
  by_cases ha : a.size = 0
  · right
    rw [Array.eq_empty_of_size_eq_zero ha] at h
    simpa using h
  · left
    have hpos : 0 < a.size := Nat.pos_of_ne_zero ha
    simpa [Array.getD, hpos, Array.getElem_push_lt hpos] using h

/-- Closing the parameter being read keeps a collector whose first parameter is 3 dangerous. -/
theorem dangerous_csiPush {s : CsiState} (sub : Bool) (h : Dangerous (csiPush s sub)) :
    Dangerous s := by
  unfold csiPush at h
  unfold Dangerous at h ⊢
  split at h
  · simp only at h
    omega
  · simp only at h
    rcases h with h | h
    · rcases getD_push_zero _ _ h with h | h
      · exact Or.inl h
      · exact
          Or.inr
            (by
              simp at h; omega)
    · omega

/-- A final byte dispatches the first parameter its collector held. -/
theorem csiFinish {v : Vt} (h : Good v) (s : CsiState) (final : UInt8)
    (hsafe : final = 0x4A → ¬Dangerous s) : Grows v (v.csiFinish s final) := by
  unfold Vt.csiFinish
  dsimp only
  refine (csiDispatch h _ _ fun hf hi h3 => hsafe hf ?_).trans (frame (Good.csiDispatch _ _ h) rfl)
  have h3' := arg_three h3
  revert hi h3'
  split
  · split
    · intro hi; simp at hi
    · intro _ h3'
      unfold Dangerous
      rcases getD_push_zero _ _ h3' with h | h
      · exact Or.inl h
      · exact
          Or.inr
            (by
              simp at h; omega)
  · split
    · next hnil =>
        intro _ h3'
        have : s.params = #[] := by
          rw [← Array.toList_inj]; simpa using hnil
        simp [this] at h3'
    · intro _ h3'
      exact dangerous_csiPush false (Or.inl h3')

theorem stepGround {v : Vt} (h : Good v) (b : UInt8) : Grows v (v.stepGround b) := by
  -- Follow the dispatch, as `Good.stepGround` does: a mismatched alternative unfolds `print`.
  unfold Vt.stepGround
  have u8 := h.u8Le
  split
  · exact frame h rfl
  split
  · exact ctl h _
  split
  · exact refl h.sbLe
  split
  · exact acceptChar h _
  split
  · split
    · exact refl h.sbLe
    split
    · exact
        (frame (w :=
              { v with
                u8need := 0, u8acc := 0 })
              h rfl).trans
          (acceptChar (Good.set_u8 0 0 (by omega) h) _)
    · exact frame h rfl
  split
  · exact frame h rfl
  split
  · exact frame h rfl
  split
  · exact frame h rfl
  · exact refl h.sbLe

theorem stepEsc {v : Vt} (h : Good v) (b : UInt8) : Grows v (v.stepEsc b) := by
  unfold Vt.stepEsc
  repeat' split
  all_goals
    with_reducible
      first
      | exact (lineFeed h).trans (frame (Good.lineFeed h) rfl)
      |
        exact
          (carriageReturn h).trans
            ((lineFeed (Good.carriageReturn h)).trans
              (frame (Good.lineFeed (Good.carriageReturn h)) rfl))
      | exact (reverseIndex h).trans (frame (Good.reverseIndex h) rfl)
      | exact frame h rfl

theorem stepEscInter {v : Vt} (h : Good v) (i b : UInt8) : Grows v (v.stepEscInter i b) :=
  frame h (by rw [frame_stepEscInter])

theorem stepCsi {v : Vt} (h : Good v) (s : CsiState) (b : UInt8) (hsafe : b = 0x4A → ¬Dangerous s) :
    Grows v (v.stepCsi s b) := by
  unfold Vt.stepCsi
  repeat' split
  all_goals
    with_reducible
      first
      | exact csiFinish h _ _ hsafe
      | exact ctl h _
      | exact refl h.sbLe
      | exact frame h rfl

theorem stepOsc {v : Vt} (h : Good v) (acc : Array UInt8) (e : Bool) (b : UInt8) :
    Grows v (v.stepOsc acc e b) := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    first
    | exact oscFinish h _
    | exact frame h rfl

theorem stepStr {v : Vt} (h : Good v) (e : Bool) (b : UInt8) : Grows v (v.stepStr e b) :=
  frame h (by rw [frame_stepStr])

theorem abortUtf8 {v : Vt} (h : Good v) (b : UInt8) : Grows v (v.abortUtf8 b) := by
  unfold Vt.abortUtf8
  split
  · exact frame h rfl
  · exact refl h.sbLe

/-- **One byte moves along `Grows`** unless it is the `J` of a collector whose first parameter
may be 3. -/
theorem step {v : Vt} (h : Good v) (b : UInt8)
    (hsafe : ∀ s, v.pstate = .csi s → b = 0x4A → ¬Dangerous s) : Grows v (v.step b) := by
  have ha : Good (v.abortUtf8 b) := by
    unfold Vt.abortUtf8
    split
    · exact Good.set_u8 0 0 (by omega) h
    · exact h
  refine (abortUtf8 h b).trans ?_
  cases hp : v.pstate with
  | ground =>
    rw [step_of_ground b hp]; exact stepGround ha b
  | esc =>
    rw [step_of_esc b hp]; exact stepEsc ha b
  | escInter i =>
    rw [step_of_escInter b hp]; exact stepEscInter ha i b
  | csi s =>
    rw [step_of_csi b hp]; exact stepCsi ha s b (hsafe s hp)
  | osc acc e =>
    rw [step_of_osc b hp]; exact stepOsc ha acc e b
  | str e =>
    rw [step_of_str b hp]; exact stepStr ha e b

end Grows

/-! ## The scan keeps up with the parser -/

/-- The scan keeps up with the parser `v`: inside a control sequence, the scan is inside one too,
and has seen a `3` whenever the sequence's first parameter may be 3. -/
def Tracks (scan : EraseScan) (v : Vt) : Prop :=
  ∀ s, v.pstate = .csi s → ∃ three, scan = .inside three ∧ (Grows.Dangerous s → three = true)

/-- Between sequences the parser collects nothing, so any scan keeps up with it. -/
theorem tracks_ground {v : Vt} (hg : v.pstate = .ground) (scan : EraseScan) : Tracks scan v := by
  intro s hs
  rw [hg] at hs
  cases hs

theorem stepGround_ne_csi {v : Vt} (hg : v.pstate = .ground) (b : UInt8) (s : CsiState) :
    (v.stepGround b).pstate ≠ .csi s := by
  by_cases hb : b = 0x1B
  · subst hb
    unfold Vt.stepGround
    rw [ite_eq_left (by decide)]
    simp
  · rw [ps_stepGround v b hb, hg]
    simp

/-- After ESC only `[` begins a control sequence, with nothing collected. -/
theorem csi_of_stepEsc {v : Vt} (hp : v.pstate = .esc) {b : UInt8} {s : CsiState}
    (h : (v.stepEsc b).pstate = .csi s) : b = 0x5B ∧ s = {} := by
  unfold Vt.stepEsc at h
  split at h
  all_goals
    first
    | exact ⟨rfl, (PState.csi.inj h).symm⟩
    | ( split at h
        · simp at h
        · split at h <;> simp [hp] at h)
    | (simp [hp, Vt.init] at h; done)

theorem stepEscInter_ne_csi (v : Vt) (i b : UInt8) (s : CsiState) :
    (v.stepEscInter i b).pstate ≠ .csi s := by
  unfold Vt.stepEscInter
  repeat' split
  all_goals simp

theorem stepOsc_ne_csi (v : Vt) (acc : Array UInt8) (e : Bool) (b : UInt8) (s : CsiState) :
    (v.stepOsc acc e b).pstate ≠ .csi s := by
  unfold Vt.stepOsc
  repeat' split
  all_goals
    first
    | (rw [Render.ps_oscFinish]; simp)
    | simp

theorem stepStr_ne_csi (v : Vt) (e : Bool) (b : UInt8) (s : CsiState) :
    (v.stepStr e b).pstate ≠ .csi s := by
  unfold Vt.stepStr
  repeat' split
  all_goals simp

/-- A byte's value, compared in `Nat`. -/
theorem u8_le {a b : UInt8} : a ≤ b ↔ a.toNat ≤ b.toNat := UInt8.le_iff_toNat_le

/-- Inside a control sequence, the parser stays inside only on a byte below `@` or DEL, other
than `[`, and a first parameter of 3 appears only on the byte `3`. -/
theorem csi_of_stepCsi {v : Vt} {s s' : CsiState} (hp : v.pstate = .csi s) {b : UInt8}
    (h : (v.stepCsi s b).pstate = .csi s') :
    (b < 0x40 ∨ b = 0x7F) ∧ b ≠ 0x5B ∧ (Grows.Dangerous s' → Grows.Dangerous s ∨ b = 0x33) := by
  have low : b.toNat < 0x40 → b < 0x40 ∧ b ≠ 0x5B := fun hb =>
    ⟨UInt8.lt_iff_toNat_lt.mpr (by simpa using hb), by
      rintro rfl; simp at hb⟩
  unfold Vt.stepCsi at h
  split at h
  · rename_i hd
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, u8_le, UInt8.reduceToNat] at hd
    have hs := PState.csi.inj h
    subst hs
    obtain ⟨hlt, hne⟩ := low (by omega)
    refine ⟨Or.inl hlt, hne, fun hd' => ?_⟩
    unfold Grows.Dangerous at hd' ⊢
    rcases hd' with hd' | hd'
    · exact Or.inl (Or.inl hd')
    · right
      simp only at hd'
      apply UInt8.toNat_inj.mp
      simp only [UInt8.reduceToNat]
      omega
  split at h
  · rename_i hsemi
    have hs := PState.csi.inj h
    subst hs
    simp only [beq_iff_eq] at hsemi
    subst hsemi
    exact ⟨Or.inl (by decide), by decide, fun hd => Or.inl (Grows.dangerous_csiPush false hd)⟩
  split at h
  · rename_i hcolon
    have hs := PState.csi.inj h
    subst hs
    simp only [beq_iff_eq] at hcolon
    subst hcolon
    exact ⟨Or.inl (by decide), by decide, fun hd => Or.inl (Grows.dangerous_csiPush true hd)⟩
  split at h
  · rename_i hpriv
    have hs := PState.csi.inj h
    subst hs
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, u8_le, UInt8.reduceToNat] at hpriv
    obtain ⟨hlt, hne⟩ := low (by omega)
    exact ⟨Or.inl hlt, hne, fun hd => Or.inl hd⟩
  split at h
  · rename_i hinter
    have hs := PState.csi.inj h
    subst hs
    simp only [Bool.and_eq_true, decide_eq_true_eq, ge_iff_le, u8_le, UInt8.reduceToNat] at hinter
    obtain ⟨hlt, hne⟩ := low (by omega)
    exact ⟨Or.inl hlt, hne, fun hd => Or.inl hd⟩
  split at h
  · split at h
    · simp at h
    · simp [Vt.csiFinish] at h
  split at h
  · simp at h
  split at h
  · rename_i hdel
    rw [hp] at h
    have hs := PState.csi.inj h
    subst hs
    simp only [beq_iff_eq] at hdel
    exact
      ⟨Or.inr hdel, by
        rw [hdel]; decide, fun hd => Or.inl hd⟩
  split at h
  · rename_i hc0
    rw [ps_ctl, hp] at h
    have hs := PState.csi.inj h
    subst hs
    obtain ⟨hlt, hne⟩ :=
      low
        (by
          rw [UInt8.lt_iff_toNat_lt] at hc0; simp at hc0; omega)
    exact ⟨Or.inl hlt, hne, fun hd => Or.inl hd⟩
  · simp at h

/-- **The scan keeps up with the parser** across one byte. -/
theorem tracks_step {v : Vt} {scan : EraseScan} (ht : Tracks scan v) (b : UInt8) :
    Tracks (scan.next b) (v.step b) := by
  intro s' hs'
  have hab : ∀ p, v.pstate = p → (v.abortUtf8 b).pstate = p := fun p hp => by rw [ps_abortUtf8, hp]
  cases hp : v.pstate with
  | ground =>
    rw [step_of_ground b hp] at hs'
    exact absurd hs' (stepGround_ne_csi (hab _ hp) b s')
  | esc =>
    rw [step_of_esc b hp] at hs'
    obtain ⟨rfl, rfl⟩ := csi_of_stepEsc (hab _ hp) hs'
    refine ⟨false, by simp [EraseScan.next], fun hd => ?_⟩
    simp [Grows.Dangerous] at hd
  | escInter i =>
    rw [step_of_escInter b hp] at hs'
    exact absurd hs' (stepEscInter_ne_csi _ i b s')
  | csi s =>
    rw [step_of_csi b hp] at hs'
    obtain ⟨hlow, hne, hd⟩ := csi_of_stepCsi (hab _ hp) hs'
    obtain ⟨three, hscan, hthree⟩ := ht s hp
    refine ⟨three || b == 0x33, ?_, fun hd' => ?_⟩
    · rw [hscan]
      simp [EraseScan.next, hne, hlow]
    · rcases hd hd' with hd | h3
      · simp [hthree hd]
      · simp [h3]
  | osc acc e =>
    rw [step_of_osc b hp] at hs'
    exact absurd hs' (stepOsc_ne_csi _ acc e b s')
  | str e =>
    rw [step_of_str b hp] at hs'
    exact absurd hs' (stepStr_ne_csi _ e b s')

/-- **Output in which the scan finds no erase request keeps the history.** -/
theorem feed_grows {v : Vt} (h : Good v) {scan : EraseScan} (ht : Tracks scan v)
    (bytes : List UInt8) (hb : scan.finds bytes = false) : Grows v (v.feed bytes) := by
  induction bytes generalizing v scan with
  | nil => exact Grows.refl h.sbLe
  | cons b bs
    ih =>
    simp only [EraseScan.finds, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hb
    obtain ⟨hnot, hrest⟩ := hb
    rw [feed_cons]
    refine
      (Grows.step h b fun s hs hJ hd => hnot ?_).trans (ih (Good.step b h) (tracks_step ht b) hrest)
    obtain ⟨three, hscan, hthree⟩ := ht s hs
    exact ⟨by rw [hscan, hthree hd], hJ⟩

/-! ## What a terminal's history does -/

/-- **Output only adds to history, unless it may ask to erase it.** Output fed between control
sequences and characters, in which no `J` follows a `[` and bytes below `@` or DEL among which a
`3`, keeps the history of a terminal the emulator can reach: its history is then the newest
`sbCap` rows of the old one followed by rows added at its end. -/
theorem history_feed {v : Vt} (h : Good v) (hb : v.atBoundary = true) (bytes : List UInt8)
    (he : mayErase bytes = false) :
    ∃ added : List Row, (v.feed bytes).scrollback = newest sbCap (v.scrollback ++ added) :=
  feed_grows h (tracks_ground ((atBoundary_iff v).mp hb).1 .outside) bytes he

/-- **A shrink moves the rows that leave the top of the main screen into history.** A resize's
history is the newest `sbCap` rows of the old history followed by the main screen's rows above
the new height, oldest first; on the main screen, those are the screen's own top rows. -/
theorem history_resize {v : Vt} (h : Good v) (hr : Renderable v) (cols rows : Nat) :
    ∃ added : List Row,
      (v.resize cols rows).scrollback = newest sbCap (v.scrollback ++ added) ∧
        (v.inAlt = false →
          added = (List.range (v.rowCount - (v.resize cols rows).rowCount)).map v.getRow) := by
  refine ⟨_, ring_toList_pushAll v.sb _ h.sbLe, fun halt => ?_⟩
  have hnone : v.altGrid = none := by
    cases hg : v.altGrid with
    | none => rfl
    | some _ => simp [Vt.inAlt, hg] at halt
  have hsize : v.grid.size = v.rows := hr.main.1
  simp only [hnone]
  show
    v.grid.toList.take (v.grid.size - clampDim rows) =
      (List.range (v.rows - clampDim rows)).map v.getRow
  apply List.ext_getElem
  · simp [hsize]
  · intro i h1 h2
    simp only [List.length_take, Array.length_toList] at h1
    simp only [List.getElem_take, Array.getElem_toList, List.getElem_map, List.getElem_range,
      Vt.getRow]
    simp [Array.getD, show i < v.grid.size by omega]

/-- **A reset keeps history**: `ESC c` between control sequences and characters leaves the
history as it was. -/
theorem history_reset {v : Vt} (hb : v.atBoundary = true) :
    (v.feed [0x1B, 0x63]).scrollback = v.scrollback := by
  obtain ⟨hg, hu⟩ := (atBoundary_iff v).mp hb
  rw [show v.feed [(0x1B : UInt8), 0x63] = (v.step 0x1B).step 0x63 from rfl,
    Render.esc_step_eq hg hu, step_of_esc (v := { v with pstate := .esc }) 0x63 rfl,
    Render.abortUtf8_of_uz (v := { v with pstate := .esc }) 0x63 hu]
  rfl

/-- **An erase request empties history**: `CSI 3 J` between control sequences and characters
leaves none. -/
theorem history_erase {v : Vt} (hb : v.atBoundary = true) :
    (v.feed [0x1B, 0x5B, 0x33, 0x4A]).scrollback = [] := by
  obtain ⟨hg, hu⟩ := (atBoundary_iff v).mp hb
  rw [show ([0x1B, 0x5B, 0x33, 0x4A] : List UInt8) = [0x1B, 0x5B] ++ (Render.digits 3 ++ [0x4A])
      from by simp [Render.digits],
    feed_append, Render.keeps_csi_open hg hu,
    Render.csi_digits_tail_eq 3 0x4A (by decide) (by decide) (v := { v with pstate := .csi {} }) rfl
      hu rfl rfl (by decide)]
  rfl

end Terminal.Vt
