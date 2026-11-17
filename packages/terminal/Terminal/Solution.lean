module

meta import SoftwareChallenge
public import Terminal.CoreCode.Render
public import Terminal.CoreCode.Replay
public import Terminal.CoreCode.Mediation
public import Terminal.CoreSpec
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.State
import all Terminal.Proofs.Vt.History
import all Terminal.Proofs.Vt.Renderable
import all Terminal.Proofs.Render.Ends
import all Terminal.Proofs.Render.Pen
import all Terminal.Proofs.Render.Modes
import all Terminal.Proofs.Render.Sticky
import all Terminal.Proofs.Render.History
import all Terminal.Proofs.Render.Grid
import all Terminal.Proofs.Render.PendingWrap
import all Terminal.Proofs.Render.Scrollback
import all Terminal.Proofs.Render.Shows
import all Terminal.Proofs.Replay
import all Terminal.Proofs.Conform
import all Terminal.Proofs.Stream

/-! The VT toolkit's headline theorems, proved of the toolkit: `lake comparator` checks that
these are exactly the statements of `Challenge.lean`. -/

public section

namespace Terminal

theorem replay_restores (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        Vt.Restores (Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable)
          Vt.Vt.feed Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
          Vt.Vt.getModes Vt.stick Vt.Vt.atBoundary v w (w.feed bytes) :=
  Render.restores budget positive v w

theorem replay_restores_rejects_resaved :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            ∃ bytes,
              Replay.Emits Replay.next budget
                  ((fun (v : Vt.Vt) => Replay.start (v.feed [0x1B, 0x37])) v) bytes ∧
                Vt.Restores
                  (Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable)
                  Vt.Vt.feed Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
                  Vt.Vt.getModes Vt.stick Vt.Vt.atBoundary v w (w.feed bytes) := by
  intro h
  -- DECSC at the start of a row, then `A`: a repaint that saves the cursor with DECSC itself, as
  -- the repaint of the terminal after another DECSC does, shows the same row and cursor, and DECRC
  -- then puts `B` over the `A` on the terminal but beside it on the receiver
  obtain ⟨bytes, emits, -, -, -, -, -, live⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 2 1).feed [0x1B, 0x37, 0x41]) (Vt.Vt.init 2 1)
  have streamed :
    Replay.Emits Replay.next 1
      (Replay.start (((Vt.Vt.init 2 1).feed [0x1B, 0x37, 0x41]).feed [0x1B, 0x37]))
      (Render.synced (((Vt.Vt.init 2 1).feed [0x1B, 0x37, 0x41]).feed [0x1B, 0x37])) := by
    rw [← Replay.start_faithful]
    exact Replay.emits_remaining 1 Nat.one_pos _
  have same := Replay.Emits.unique emits streamed
  subst same
  have row :=
    ((live (.feed (.init 2 1) _) (.init 2 1) (by decide +kernel) (by decide +kernel)).2
          (by decide +kernel) [0x1B, 0x38, 0x42]).1.2.2.1
      0 (by decide +kernel)
  exact absurd (congrArg (fun r : Vt.Row => (r.getD 0 {}).base) row) (by decide +kernel)

theorem replay_history (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (retained : (Render.sbRows v).isEmpty = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  obtain ⟨hc, hr, hlive⟩ := Render.syncBegin_keeps w
  refine ⟨Render.synced v, ?_, ?_⟩
  · rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  · rw [Render.feed_synced]
    exact
      Render.restore_sb_reachable v (w.feed Render.syncBegin) (hlive hw) hv (hc.trans hcols)
        (hr.trans hrows) retained

theorem replay_history_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w →
              w.colCount = v.colCount →
              w.rowCount = v.rowCount →
              (Render.sbRows v).isEmpty = false →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  intro h
  obtain ⟨bytes, emits, history⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 2 1).feed [0x41, 0x0A]) (Vt.Vt.init 2 1)
      (.feed (.init 2 1) [0x41, 0x0A]) (.init 2 1) (by decide +kernel) (by decide +kernel)
      (by
        rw [Render.sbRows_observed]; rfl)
  cases emits with
  | step next => cases next
  | done =>
    rw [Render.sbRows_observed] at history
    exact absurd (congrArg List.length history) (by decide +kernel)

theorem replay_synchronized (budget : Nat) (positive : 0 < budget) (v : Vt.Vt)
    (bytes : Render.Bytes) (emits : Replay.Emits Replay.next budget (Replay.start v) bytes) :
    ∃ body,
      bytes = Render.syncBegin ++ body ++ Render.syncEnd ∧
        ¬Render.syncBegin <:+: body ∧ ¬Render.syncEnd <:+: body := by
  have streamed : Replay.Emits Replay.next budget (Replay.start v) (Render.synced v) := by
    rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  rw [Replay.Emits.unique emits streamed]
  exact ⟨Render.restore v, rfl, (Render.restore_noBracket v).1, (Render.restore_noBracket v).2.1⟩

theorem replay_synchronized_rejects_bare :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v : Vt.Vt),
            ∀ (bytes : Render.Bytes),
              Replay.Emits Replay.next budget (Replay.unbracketed Replay.start Replay.next v)
                  bytes →
                ∃ body,
                  bytes = Render.syncBegin ++ body ++ Render.syncEnd ∧
                    ¬Render.syncBegin <:+: body ∧ ¬Render.syncEnd <:+: body := by
  intro h
  -- past its first step, the opening bracket, a repaint starts with the ST that grounds its
  -- receiver, `ESC \`, where a synchronized update has `ESC [`
  obtain ⟨body, eq, -, -⟩ :=
    h 1 Nat.one_pos (Vt.Vt.init 1 1) _
      (Replay.emits_remaining 1 Nat.one_pos
        (Replay.unbracketed Replay.start Replay.next (Vt.Vt.init 1 1)))
  have lead := congrArg (List.take 2) eq
  have bare :
    (Replay.remaining (Replay.unbracketed Replay.start Replay.next (Vt.Vt.init 1 1))).take 2 =
      [0x1B, 0x5C] := by
    decide +kernel
  rw [bare] at lead
  simp [Render.syncBegin] at lead

theorem history_grows (v : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) :
    (∀ bytes : List UInt8,
        v.atBoundary = true →
          Vt.mayErase bytes = false →
          ∃ added, (v.feed bytes).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added)) ∧
      ∀ cols rows : Nat,
        ∃ added,
          (v.resize cols rows).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added) ∧
            ((Vt.stick v).alt = false →
              added = (List.range (v.rowCount - (v.resize cols rows).rowCount)).map v.getRow) := by
  have good := Vt.good_of_liveReachable hv
  exact
    ⟨fun bytes hb he => Vt.history_feed good hb bytes he, fun cols rows =>
      Vt.history_resize good (Vt.renderable_of_liveReachable hv) cols rows⟩

theorem history_grows_rejects_lost :
    ¬∀ (v : Vt.Vt),
        Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
            Vt.Vt.quiesce Vt.Vt.Decodable v →
          (∀ bytes : List UInt8,
              v.atBoundary = true →
                Vt.mayErase bytes = false →
                ∃ added,
                  ((fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) v bytes).scrollback =
                    Vt.newest Vt.sbCap (v.scrollback ++ added)) ∧
            ∀ cols rows : Nat,
              ∃ added,
                (v.resize cols rows).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added) ∧
                  ((Vt.stick v).alt = false →
                    added =
                      (List.range (v.rowCount - (v.resize cols rows).rowCount)).map v.getRow) := by
  intro h
  -- A shrink from two rows to one leaves one row of history, which the lost output drops.
  obtain ⟨added, history⟩ :=
    (h ((Vt.Vt.init 1 2).resize 1 1) (.resize (.init 1 2) 1 1)).1 [] (by decide +kernel) rfl
  have lengths := congrArg List.length history
  have none : (Vt.Vt.init 1 1).scrollback.length = 0 := by decide +kernel
  have one : ((Vt.Vt.init 1 2).resize 1 1).scrollback.length = 1 := by decide +kernel
  have cap : Vt.sbCap = 10000 := rfl
  simp only [Vt.newest, List.length_drop, List.length_append, none, one, cap] at lengths
  omega

theorem live_shape (v : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) :
    1 ≤ v.colCount ∧
      v.colCount ≤ 1000 ∧
      1 ≤ v.rowCount ∧
      v.rowCount ≤ 1000 ∧
      (∀ y < v.rowCount, (v.getRow y).size = v.colCount) ∧
      v.cursorPos.1 < v.colCount ∧ v.cursorPos.2 < v.rowCount ∧ v.scrollback.length ≤ Vt.sbCap := by
  have good := Vt.good_of_liveReachable hv
  have shaped := Vt.renderable_of_liveReachable hv
  refine
    ⟨good.colsPos, good.colsLe, good.rowsPos, good.rowsLe, fun y hy => ?_, good.curX, good.curY, ?_⟩
  · have row := (shaped.main.2 y).size
    have inside : y < v.grid.size := by
      rw [shaped.main.1]; exact hy
    simp only [Vt.Vt.getRow, Vt.Vt.colCount, Array.getD, inside, dite_true] at row ⊢
    exact row
  · simp only [Vt.Vt.scrollback, Vt.Ring.toList, List.length_append, List.length_drop,
      List.length_take, Array.length_toList]
    have := good.sbLe
    simp only [Vt.Ring.size] at this
    omega

theorem live_shape_rejects_empty :
    ¬∀ (v : Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
          1 ≤ v.colCount ∧
            v.colCount ≤ 1000 ∧
            1 ≤ v.rowCount ∧
            v.rowCount ≤ 1000 ∧
            (∀ y < v.rowCount,
              ((fun (_ : Vt.Vt) (_ : Nat) => (#[] : Vt.Row)) v y).size = v.colCount) ∧
            v.cursorPos.1 < v.colCount ∧
            v.cursorPos.2 < v.rowCount ∧ v.scrollback.length ≤ Vt.sbCap := by
  intro h
  have empty := (h (Vt.Vt.init 1 1) (.init 1 1)).2.2.2.2.1 0 (by decide +kernel)
  exact absurd empty (by decide +kernel)

theorem feed_inert (v : Vt.Vt) (bytes : List UInt8) (between : v.atBoundary = true)
    (inert : ∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) :
    v.feed bytes = v := by
  have ground : v.pstate = .ground ∧ v.u8need = 0 := by simpa [Vt.Vt.atBoundary] using between
  have hosc : ∀ acc e, v.pstate ≠ .osc acc e := by
    intro acc e
    rw [ground.1]
    simp
  have hstr : v.pstate ≠ .str true := by
    rw [ground.1]
    simp
  have step (b : UInt8) (hb : b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) :
    v.step b = v := by
    rcases hb with del | low | ⟨above, below, notEsc⟩
    · subst del
      exact Vt.step_del_inert ground.2 hosc hstr
    · have below : b < 0x20 := by
        simp only [UInt8.lt_iff_toNat_lt] at low ⊢
        simp only [UInt8.reduceToNat] at low ⊢
        omega
      have notEsc : b ≠ 0x1B := by
        rintro rfl
        exact absurd low (by decide)
      exact Vt.step_c0_inert below (.inl low) notEsc ground.2 hosc hstr
    · exact Vt.step_c0_inert below (.inr above) notEsc ground.2 hosc hstr
  show bytes.foldl Vt.Vt.step v = v
  induction bytes with
  | nil => rfl
  | cons b rest ih =>
    rw [List.foldl_cons, step b (inert b (by simp))]
    exact ih (fun b hb => inert b (by simp [hb]))

theorem feed_inert_rejects_print :
    ¬∀ (v : Vt.Vt) (bytes : List UInt8),
        v.atBoundary = true →
          (∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) →
          (fun (v : Vt.Vt) (bytes : List UInt8) =>
                v.feed (bytes.map fun b => if b = 0x7F then 0x3F else b))
              v bytes =
            v := by
  intro h
  have same := congrArg Vt.Vt.cursorPos (h (Vt.Vt.init 2 2) [0x7F] (by decide +kernel) (by simp))
  exact absurd same (by decide +kernel)

theorem repeatAtMost_eq_repeat (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt) :
    v.repeatAtMost cap count f = Nat.repeat f (min count cap) v :=
  Vt.repeatAtMost_eq_repeat v cap count f

theorem repeatAtMost_eq_repeat_rejects_uncapped :
    ¬∀ (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt),
        (fun (v : Vt.Vt) (_ count : Nat) (f : Vt.Vt → Vt.Vt) => Nat.repeat f count v) v cap count
            f =
          Nat.repeat f (min count cap) v := by
  intro h
  have same := congrArg Vt.Vt.colCount (h (Vt.Vt.init 1 1) 0 1 (fun _ => Vt.Vt.init 2 1))
  exact absurd same (by decide +kernel)

theorem next_bounded {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes}
    (h : Replay.next budget p = some (bytes, q)) : bytes.length ≤ budget := Replay.next_bounded h

theorem next_bounded_rejects_overrun :
    ¬∀ {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes},
        Replay.overrun budget p = some (bytes, q) → bytes.length ≤ budget := by
  intro h
  exact
    absurd (@h 0 (Replay.start (Vt.Vt.init 1 1)) (Replay.start (Vt.Vt.init 1 1)) [0] rfl)
      (by decide)

theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Render.screenText_text v
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

theorem screenText_text_rejects_escape :
    ¬∀ (v : Vt.Vt),
        ∃ cs : List Char,
          Render.escape v = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  intro h
  obtain ⟨cs, text, safe⟩ := h (Vt.Vt.init 1 1)
  have escape : (0x1B : UInt8) ∈ cs.flatMap String.utf8EncodeChar := by
    rw [← text]
    exact List.mem_singleton_self _
  obtain ⟨c, member, byte⟩ := List.mem_flatMap.mp escape
  rcases safe c member with newline | ⟨printable, notDel, -⟩
  · subst newline
    revert byte
    decide
  · rw [← Render.utf8_eq_utf8EncodeChar] at byte
    exact absurd (Render.utf8_no_ctl c printable notDel _ byte).1 (by decide)

theorem history_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.history v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Render.history_text v
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

theorem history_text_rejects_escape :
    ¬∀ (v : Vt.Vt),
        ∃ cs : List Char,
          Render.escape v = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  intro h
  obtain ⟨cs, text, safe⟩ := h (Vt.Vt.init 1 1)
  have escape : (0x1B : UInt8) ∈ cs.flatMap String.utf8EncodeChar := by
    rw [← text]
    exact List.mem_singleton_self _
  obtain ⟨c, member, byte⟩ := List.mem_flatMap.mp escape
  rcases safe c member with newline | ⟨printable, notDel, -⟩
  · subst newline
    revert byte
    decide
  · rw [← Render.utf8_eq_utf8EncodeChar] at byte
    exact absurd (Render.utf8_no_ctl c printable notDel _ byte).1 (by decide)

theorem leave_canonical_all (w : Vt.Vt) (h2 : 2 ≤ w.rowCount) :
    (w.feed Render.leaveAnsi).atBoundary = true ∧
      (w.feed Render.leaveAnsi).getModes = ({} : Vt.Modes) ∧
      Vt.stick (w.feed Render.leaveAnsi) =
        { rows := w.rowCount, top := 0, bot := w.rowCount - 1, g0 := false, g1 := false,
          so := false, alt := false } ∧
      (w.feed Render.leaveAnsi).getPen = ({} : Vt.Pen) ∧
      (w.feed Render.leaveAnsi).windowTitle = "" := by
  obtain ⟨_, modes, sticky, pen, title⟩ := Render.leave_canonical_all w h2
  obtain ⟨ground, settled, _⟩ := Render.leave_boundary_title w
  exact ⟨by simp [Vt.Vt.atBoundary, ground, settled], modes, sticky, pen, title⟩

theorem leave_canonical_all_rejects_escape :
    ¬∀ (w : Vt.Vt),
        2 ≤ w.rowCount →
          (w.feed ([0x1B] : Render.Bytes)).atBoundary = true ∧
            (w.feed ([0x1B] : Render.Bytes)).getModes = ({} : Vt.Modes) ∧
            Vt.stick (w.feed ([0x1B] : Render.Bytes)) =
              { rows := w.rowCount, top := 0, bot := w.rowCount - 1, g0 := false, g1 := false,
                so := false, alt := false } ∧
            (w.feed ([0x1B] : Render.Bytes)).getPen = ({} : Vt.Pen) ∧
            (w.feed ([0x1B] : Render.Bytes)).windowTitle = "" := by
  intro h
  exact absurd (h (Vt.Vt.init 2 2) (by decide +kernel)).1 (by decide +kernel)

theorem vt_conforms :
    ∃ screen : Vt.Vt → Vt.Ref.Screen,
      (∀ v,
          Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
            Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
        ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
          Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
            v.atBoundary = true →
            Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
            s.Ok → Vt.Ref.Same (screen (v.feed s.bytes)) (Vt.Ref.Seq.apply (screen v) s) :=
  ⟨Vt.Conform.screenOf, Vt.Conform.reads_screenOf, fun _ s hv hb hp hs =>
    Vt.Conform.conforms hv hb hp s hs⟩

theorem vt_conforms_rejects_elWhole :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.elWhole Vt.Vt.feed) Vt.Vt.resize Vt.Vt.quiesce
                Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.elWhole Vt.Vt.feed) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  -- EL 0 at column 2 of `ab` leaves the `a` that a whole-line erase blanks
  rintro ⟨scr, hR, hS⟩
  have h :=
    hS _ (.el 0) (.feed (.init 3 1) [0x61, 0x62]) (by decide +kernel)
      (by
        unfold Vt.Ref.Plain; decide +kernel)
      trivial
  have hc :=
    Vt.Conform.Same.cell_at h (x := 0) (y := 0)
      (by
        rw [(hR _).2.1]; decide +kernel)
      (by
        rw [(hR _).1]; decide +kernel)
  rw [Vt.Conform.Reads.cell_at (hR _) (by decide +kernel) (by decide +kernel)] at hc
  simp only [Vt.Ref.Seq.apply, Vt.Ref.Screen.erase, (hR _).2.2.2.1, (hR _).2.2.2.2.1,
    (hR _).2.2.2.2.2.1] at hc
  rw [Vt.Conform.Reads.cell_at (hR _) (by decide +kernel) (by decide +kernel)] at hc
  exact absurd (congrArg Vt.Cell.base hc) (by decide +kernel)

theorem vt_conforms_rejects_cupFromZero :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.cupFromZero Vt.Vt.feed) Vt.Vt.resize Vt.Vt.quiesce
                Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.cupFromZero Vt.Vt.feed) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  -- `CSI 1 ; 1 H` homes the cursor; read from 0 it lands on the second column
  rintro ⟨scr, hR, hS⟩
  have h :=
    (hS _ (.cup 1 1) (.init 3 3) (by decide +kernel)
        (by
          unfold Vt.Ref.Plain; decide +kernel)
        (by
          unfold Vt.Ref.Seq.Ok; decide)).2.2.2.1
  simp only [Vt.Ref.Seq.apply, (hR _).2.2.2.1, (hR _).1] at h
  exact absurd h (by decide +kernel)

theorem vt_conforms_rejects_eagerWrap :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.eagerWrap Vt.Vt.feed Vt.Vt.colCount Vt.Vt.cursorPos)
                Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same
                (screen ((Vt.Ref.eagerWrap Vt.Vt.feed Vt.Vt.colCount Vt.Vt.cursorPos) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  -- a print into the last column holds the cursor there; wrapping at once moves it
  rintro ⟨scr, hR, hS⟩
  have h :=
    (hS _ (.print 'b') (.feed (.init 2 2) [0x61]) (by decide +kernel)
        (by
          unfold Vt.Ref.Plain; decide +kernel)
        (by
          unfold Vt.Ref.Seq.Ok; decide)).2.2.2.1
  simp only [Vt.Ref.Seq.apply] at h
  rw [Vt.Conform.print_x _ _
      (by
        rw [(hR _).1]; decide +kernel)
      (by
        rw [(hR _).2.2.2.1]; decide +kernel),
    (hR _).2.2.2.1] at h
  exact absurd h (by decide +kernel)

theorem vt_conforms_rejects_resetKeepsBold :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.resetKeepsBold Vt.Vt.feed Vt.Vt.getPen) Vt.Vt.resize
                Vt.Vt.quiesce Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.resetKeepsBold Vt.Vt.feed Vt.Vt.getPen) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  -- SGR 0 turns bold off
  rintro ⟨scr, hR, hS⟩
  have h :=
    (hS _ (.sgr [.reset]) (.feed (.init 1 1) (Vt.Ref.Seq.sgr [.bold]).bytes) (by decide +kernel)
        (by
          unfold Vt.Ref.Plain; decide +kernel)
        (by
          unfold Vt.Ref.Seq.Ok; decide)).2.2.2.2.2.2.1
  simp only [Vt.Ref.Seq.apply, (hR _).2.2.2.2.2.1] at h
  exact absurd (congrArg Vt.Pen.bold h) (by decide +kernel)

theorem vt_conforms_rejects_ilKeepsColumn :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.ilKeepsColumn Vt.Vt.feed Vt.Vt.cursorPos) Vt.Vt.resize
                Vt.Vt.quiesce Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.ilKeepsColumn Vt.Vt.feed Vt.Vt.cursorPos) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  -- IL moves the cursor to the line home position
  rintro ⟨scr, hR, hS⟩
  have h :=
    (hS _ (.il 1) (.feed (.init 3 2) [0x61, 0x62]) (by decide +kernel)
        (by
          unfold Vt.Ref.Plain; decide +kernel)
        (by
          unfold Vt.Ref.Seq.Ok; decide)).2.2.2.1
  rw [Vt.Conform.il_x _ _
      (by
        rw [(hR _).2.2.2.2.1, (hR _).2.2.2.2.2.2.2.1, (hR _).2.2.2.2.2.2.2.2.1]
        decide +kernel),
    (hR _).2.2.2.1] at h
  exact absurd h (by decide +kernel)

theorem vt_keeps (v : Vt.Vt) (k : Vt.Ref.Kept) (between : v.atBoundary = true) (ok : k.Ok) :
    (∀ y, (v.feed k.bytes).getRow y = v.getRow y) ∧
      (v.feed k.bytes).cursorPos = v.cursorPos ∧
      (v.feed k.bytes).getPen = v.getPen ∧
      (v.feed k.bytes).getModes = Vt.Ref.Kept.modes v.getModes k ∧
      Vt.stick (v.feed k.bytes) = Vt.stick v ∧
      (v.feed k.bytes).windowTitle = v.windowTitle ∧
      (v.feed k.bytes).atBoundary = true := Vt.Conform.keeps_all between k ok

theorem vt_keeps_rejects_unescaped :
    ¬∀ (v : Vt.Vt) (k : Vt.Ref.Kept),
        v.atBoundary = true →
          k.Ok →
          (∀ y, ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).getRow y = v.getRow y) ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).cursorPos = v.cursorPos ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).getPen = v.getPen ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).getModes = Vt.Ref.Kept.modes v.getModes k ∧
            Vt.stick ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes) = Vt.stick v ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).windowTitle = v.windowTitle ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).atBoundary = true := by
  -- a sixel image's data prints once its ESCs are gone
  intro h
  have row :=
    (h (Vt.Vt.init 4 1) (.sixel [0x41]) (by decide +kernel)
          (by
            unfold Vt.Ref.Kept.Ok; decide)).1
      0
  exact absurd (congrArg (fun r : Vt.Row => (r.getD 0 {}).base) row) (by decide +kernel)

theorem title_source (v : Vt.Vt) (ts : List Stream.Token) (between : v.atBoundary = true)
    (ok : ∀ t ∈ ts, t.Ok) :
    (v.feed (ts.flatMap Stream.Token.bytes)).windowTitle =
        ts.foldl Stream.Token.retitle v.windowTitle ∧
      (v.feed (ts.flatMap Stream.Token.bytes)).atBoundary = true :=
  Vt.Conform.title_stream between ts ok

theorem title_source_rejects_icon :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        v.atBoundary = true →
          (∀ t ∈ ts, t.Ok) →
          ((Stream.iconAsTitle Vt.Vt.feed) v (ts.flatMap Stream.Token.bytes)).windowTitle =
              ts.foldl Stream.Token.retitle v.windowTitle ∧
            ((Stream.iconAsTitle Vt.Vt.feed) v (ts.flatMap Stream.Token.bytes)).atBoundary =
              true := by
  -- OSC 1 names the icon; taken for the title, it sets one
  intro h
  have :=
    (h (Vt.Vt.init 2 1) [.osc [0x31, 0x3B, 0x78] false] (by decide +kernel)
        (by
          intro t ht; simp at ht; subst ht; unfold Stream.Token.Ok; decide)).1
  exact absurd this (by decide +kernel)

theorem asks_exact (v : Vt.Vt) (ts : List Stream.Token) (ok : ∀ t ∈ ts, t.Ok) :
    (Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).vt =
        v.feed (ts.flatMap Stream.Token.bytes) ∧
      (Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).asks = ts.any Stream.Token.asks ∧
      (Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).notice = Stream.notice ts :=
  Mediation.heard_stream v ts ok

theorem asks_exact_rejects_ending :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        (∀ t ∈ ts, t.Ok) →
          ((Stream.endingRings Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).vt =
              v.feed (ts.flatMap Stream.Token.bytes) ∧
            ((Stream.endingRings Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).asks =
              ts.any Stream.Token.asks ∧
            ((Stream.endingRings Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).notice =
              Stream.notice ts := by
  -- the BEL that ends a title rings no bell
  intro h
  have :=
    (h (Vt.Vt.init 2 1) [.osc [0x32, 0x3B, 0x78] false]
        (by
          intro t ht; simp at ht; subst ht; unfold Stream.Token.Ok; decide)).2.1
  exact absurd this (by decide +kernel)

theorem asks_exact_rejects_progress :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        (∀ t ∈ ts, t.Ok) →
          ((Stream.progressAsks Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).vt =
              v.feed (ts.flatMap Stream.Token.bytes) ∧
            ((Stream.progressAsks Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).asks =
              ts.any Stream.Token.asks ∧
            ((Stream.progressAsks Mediation.feed) v .ground
                  (ts.flatMap Stream.Token.bytes)).notice =
              Stream.notice ts := by
  -- ConEmu's progress report posts no notification
  intro h
  have :=
    (h (Vt.Vt.init 2 1) [.osc [0x39, 0x3B, 0x34, 0x3B, 0x31] false]
        (by
          intro t ht; simp at ht; subst ht; unfold Stream.Token.Ok; decide)).2.1
  exact absurd this (by decide +kernel)

theorem progress_source (v : Vt.Vt) (ts : List Stream.Token) (ok : ∀ t ∈ ts, t.Ok)
    (p : Option Mediation.Progress) :
    ((Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).progress).getD p =
      ts.foldl Stream.Token.reprogress p := by
  rw [Mediation.progress_stream v ts ok, Mediation.reprogress_foldl]

theorem progress_source_rejects_title :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        (∀ t ∈ ts, t.Ok) →
          ∀ (p : Option Mediation.Progress),
            (((Stream.titleProgress Vt.Vt.windowTitle Mediation.feed) v .ground
                      (ts.flatMap Stream.Token.bytes)).progress).getD
                p =
              ts.foldl Stream.Token.reprogress p := by
  -- a title declares nothing; heard as work, it would
  intro h
  have :=
    h (Vt.Vt.init 2 1) [.osc [0x32, 0x3B, 0x78] false]
      (by
        intro t ht; simp at ht; subst ht; unfold Stream.Token.Ok; decide)
      none
  exact absurd this (by decide +kernel)

end Terminal
