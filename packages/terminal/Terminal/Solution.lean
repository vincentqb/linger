module

public import Terminal.Render
public import Terminal.Replay
public import Terminal.Spec
public import Terminal.Spec.Claims
import all Terminal.Vt
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
import all Terminal.Proofs.Replay

/-! The VT toolkit's headline theorems, proved of the toolkit: `lake comparator` checks that
these are exactly the statements of `TerminalChallenge.lean`. -/

public section

namespace Terminal

theorem replay_grid (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).colCount = v.colCount ∧
        (w.feed bytes).rowCount = v.rowCount ∧
        ∀ y < v.rowCount, (w.feed bytes).getRow y = v.getRow y := by
  refine ⟨Render.restore v, ?_, ?_⟩
  · rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  have dims := Vt.dims_feed (Render.restore v) (Vt.good_of_liveReachable hw)
  simp only [Vt.dims, Prod.mk.injEq] at dims
  have grid := Render.restore_grid_reachable v w hw hv hcols hrows
  have size := (Vt.renderable_of_liveReachable hv).main.1
  refine ⟨dims.1.trans hcols, dims.2.trans hrows, fun y below => ?_⟩
  have inside : y < v.grid.size := size ▸ below
  unfold Vt.Vt.getRow
  rw [grid]
  simp only [Array.getD, inside, dite_true]

theorem replay_grid_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w →
              w.colCount = v.colCount →
              w.rowCount = v.rowCount →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).colCount = v.colCount ∧
                  (w.feed bytes).rowCount = v.rowCount ∧
                  ∀ y < v.rowCount, (w.feed bytes).getRow y = v.getRow y := by
  intro h
  obtain ⟨bytes, emits, -, -, rows⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 2 1).feed [0x41]) (Vt.Vt.init 2 1) (.feed (.init 2 1) [0x41])
      (.init 2 1) (by decide +kernel) (by decide +kernel)
  cases emits with
  | step next => cases next
  | done =>
    have row := rows 0 (by decide +kernel)
    exact absurd (congrArg (fun r : Vt.Row => (r.getD 0 {}).base) row) (by decide +kernel)

theorem replay_keeps_showing
    (keeps :
      Replay.KeepsShowing (Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable)
        Vt.Vt.feed Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.atBoundary Replay.start
        Replay.next)
    (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (boundary : v.atBoundary = true) (later : List UInt8) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (∀ y < v.rowCount, (w.feed bytes).getRow y = v.getRow y) ∧
        ∀ y < (v.feed later).rowCount,
          ((w.feed bytes).feed later).getRow y = (v.feed later).getRow y := by
  obtain ⟨bytes, emits, -, -, rows⟩ := replay_grid budget positive v w hv hw hcols hrows
  obtain ⟨other, streamed, kept⟩ := keeps budget v w later positive hv hw hcols hrows boundary
  have same := Replay.Emits.unique emits streamed
  subst same
  exact ⟨bytes, emits, rows, kept⟩

theorem replay_keeps_showing_rejects_fixed :
    ¬(Replay.KeepsShowing
          (Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
            Vt.Vt.quiesce Vt.Vt.Decodable)
          (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.colCount Vt.Vt.rowCount
          Vt.Vt.getRow Vt.Vt.atBoundary Replay.start Replay.next →
        ∀ (budget : Nat),
          0 < budget →
            ∀ (v w : Vt.Vt),
              Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
                  Vt.Vt.quiesce Vt.Vt.Decodable v →
                Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
                  Vt.Vt.quiesce Vt.Vt.Decodable w →
                w.colCount = v.colCount →
                w.rowCount = v.rowCount →
                v.atBoundary = true →
                ∀ (later : List UInt8),
                  ∃ bytes,
                    Replay.Emits Replay.next budget (Replay.start v) bytes ∧
                      (∀ y < v.rowCount,
                        ((fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) w bytes).getRow y =
                          v.getRow y) ∧
                      ∀ y < ((fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) v later).rowCount,
                        ((fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1)
                                ((fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) w bytes)
                                later).getRow
                            y =
                          ((fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) v later).getRow
                            y) := by
  intro h
  have keeps :
    Replay.KeepsShowing
      (Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
        Vt.Vt.quiesce Vt.Vt.Decodable)
      (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.colCount Vt.Vt.rowCount
      Vt.Vt.getRow Vt.Vt.atBoundary Replay.start Replay.next := by
    intro budget v _ _ positive _ _ _ _ _
    exact ⟨_, Replay.emits_remaining budget positive (Replay.start v), fun _ _ => rfl⟩
  obtain ⟨_, -, rows, -⟩ :=
    h keeps 1 Nat.one_pos (Vt.Vt.init 2 1) (Vt.Vt.init 2 1) (.init 2 1) (.init 2 1) rfl rfl
      (by decide +kernel) []
  have row : (Vt.Vt.init 1 1).getRow 0 = (Vt.Vt.init 2 1).getRow 0 := rows 0 (by decide +kernel)
  exact absurd (congrArg (fun r : Vt.Row => r.size) row) (by decide +kernel)

theorem replay_history (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (retained : (Render.sbRows v).isEmpty = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  refine ⟨Render.restore v, ?_, Render.restore_sb_reachable v w (hw) (hv) hcols hrows retained⟩
  rw [← Replay.start_faithful v]
  exact Replay.emits_remaining budget positive (Replay.start v)

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

theorem replay_cursor (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (ho : v.getModes.origin = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).cursorPos = v.cursorPos := by
  refine ⟨Render.restore v, ?_, ?_⟩
  · rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  obtain ⟨x, y⟩ :=
    Render.restore_cursor_any v w (Vt.good_of_liveReachable (hv)) (Vt.good_of_liveReachable (hw))
      hcols hrows ho
  simp only [Vt.cursorPos_eq, x, y]

theorem replay_cursor_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w →
              w.colCount = v.colCount →
              w.rowCount = v.rowCount →
              v.getModes.origin = false →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).cursorPos = v.cursorPos := by
  intro h
  obtain ⟨bytes, emits, cursor⟩ :=
    h 1 Nat.one_pos (Vt.Vt.init 2 1) ((Vt.Vt.init 2 1).feed [0x41]) (.init 2 1)
      (.feed (.init 2 1) [0x41]) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  cases emits with
  | step next => cases next
  | done => exact absurd (congrArg Prod.fst cursor) (by decide +kernel)

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

theorem replay_pen (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).getPen = v.getPen := by
  refine ⟨Render.restore v, ?_, Render.restore_pen_any v w⟩
  rw [← Replay.start_faithful v]
  exact Replay.emits_remaining budget positive (Replay.start v)

theorem replay_pen_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            ∃ bytes,
              Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                (w.feed bytes).getPen = v.getPen := by
  intro h
  obtain ⟨bytes, emits, pen⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 1 1).feed [0x1B, 0x5B, 0x31, 0x6D]) (Vt.Vt.init 1 1)
  cases emits with
  | step next => cases next
  | done => exact absurd (congrArg Vt.Pen.bold pen) (by decide +kernel)

theorem replay_modes (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (mouse :
      v.getModes.mouse = 0 ∨
        v.getModes.mouse = 1000 ∨ v.getModes.mouse = 1002 ∨ v.getModes.mouse = 1003) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).getModes = v.getModes := by
  refine ⟨Render.restore v, ?_, Render.restore_modes_any v w mouse⟩
  rw [← Replay.start_faithful v]
  exact Replay.emits_remaining budget positive (Replay.start v)

theorem replay_modes_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            (v.getModes.mouse = 0 ∨
                v.getModes.mouse = 1000 ∨ v.getModes.mouse = 1002 ∨ v.getModes.mouse = 1003) →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).getModes = v.getModes := by
  intro h
  obtain ⟨bytes, emits, modes⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 1 1).feed [0x1B, 0x5B, 0x3F, 0x32, 0x30, 0x30, 0x34, 0x68])
      (Vt.Vt.init 1 1) (.inl (by decide +kernel))
  cases emits with
  | step next => cases next
  | done => exact absurd (congrArg Vt.Modes.bracketedPaste modes) (by decide +kernel)

theorem replay_sticky (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (height : (Vt.stick w).rows = (Vt.stick v).rows) (region : (Vt.stick v).top < (Vt.stick v).bot)
    (inside : (Vt.stick v).bot < (Vt.stick v).rows) (fits : (Vt.stick v).rows < 65535) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        Vt.stick (w.feed bytes) = Vt.stick v := by
  refine ⟨Render.restore v, ?_, Render.restore_sticky_any v w height region inside fits⟩
  rw [← Replay.start_faithful v]
  exact Replay.emits_remaining budget positive (Replay.start v)

theorem replay_sticky_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            (Vt.stick w).rows = (Vt.stick v).rows →
              (Vt.stick v).top < (Vt.stick v).bot →
              (Vt.stick v).bot < (Vt.stick v).rows →
              (Vt.stick v).rows < 65535 →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  Vt.stick (w.feed bytes) = Vt.stick v := by
  intro h
  obtain ⟨bytes, emits, sticky⟩ :=
    h 1 Nat.one_pos ((Vt.Vt.init 1 3).feed [0x1B, 0x5B, 0x32, 0x3B, 0x33, 0x72]) (Vt.Vt.init 1 3)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
  cases emits with
  | step next => cases next
  | done => exact absurd (congrArg Vt.Sticky.top sticky) (by decide +kernel)

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
        (fun (_ : Nat) (p : Replay.Plan) => some (([0] : Render.Bytes), p)) budget p =
            some (bytes, q) →
          bytes.length ≤ budget := by
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
          (fun (_ : Vt.Vt) => ([0x1B] : Render.Bytes)) v = cs.flatMap String.utf8EncodeChar ∧
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
          (fun (_ : Vt.Vt) => ([0x1B] : Render.Bytes)) v = cs.flatMap String.utf8EncodeChar ∧
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

end Terminal
