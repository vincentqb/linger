module

public import Linger.App.Commands
public import Linger.App.Entry
public import Linger.Display.Listing
public import Linger.Display.Status
public import Linger.Display.View
public import Linger.Import.Resurrect
public import Linger.Selector.Fuzzy
public import Linger.Selector.Input
public import Linger.Selector.Picker
public import Linger.Display.Title
public import Linger.Os.Env
public import Linger.Session
public import Linger.Session.Buf
public import Linger.Session.Checkpoint
public import Linger.Session.Claim
public import Linger.Session.Driver
public import Linger.Session.Spec
public import Linger.Target.Name
public import Linger.Target.Remote
public import Linger.Target.Spec
public import Linger.Terminal.Render
public import Linger.Terminal.Mediation
public import Linger.Terminal.Replay
public import Linger.Terminal.Spec
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Entry
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import all Linger.Selector.Proofs.Fuzzy
import all Linger.Selector.Proofs.Input
import all Linger.Selector.Proofs.Picker
import all Linger.Display.Proofs.Title
import all Linger.Os.Proofs.Env
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Record
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Start
import all Linger.Session.Proofs.Wire
public import Linger.Session.Record
public import Linger.Session.Wire
public import Linger.Session.Start
import all Linger.Terminal.Vt
import all Linger.Terminal.Proofs.Vt
import all Linger.Terminal.Proofs.Vt.Renderable
import all Linger.Terminal.Proofs.Render.Grid
import all Linger.Terminal.Proofs.Render.History
import all Linger.Terminal.Proofs.Render.PendingWrap
import all Linger.Terminal.Proofs.Render.Scrollback
import all Linger.Terminal.Proofs.Render.Sticky
import all Linger.Terminal.Proofs.Replay
import all Linger.Terminal.Proofs.Vt.State

/-! # Proofs of the headline theorems and their kills

`Challenge.lean` states these theorems; each proof here cites the component theorems it
restates. `./lake comparator` checks that the statements match. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Linger.Terminal

theorem replay_grid (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v)
    (hw :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).colCount = v.colCount ∧
        (w.feed bytes).rowCount = v.rowCount ∧
        ∀ y < v.rowCount, (w.feed bytes).getRow y = v.getRow y := by
  have hv := Checkpoint.live_of_decoded hv
  have hw := Checkpoint.live_of_decoded hw
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
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) w →
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
      KeepsShowing
        (Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
          (Checkpoint.Decoded Checkpoint.loadBytes))
        Vt.Vt.feed Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.atBoundary Replay.start
        Replay.next)
    (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v)
    (hw :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) w)
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
    ¬(KeepsShowing
          (Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
            Vt.Vt.quiesce (Checkpoint.Decoded Checkpoint.loadBytes))
          (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.colCount Vt.Vt.rowCount
          Vt.Vt.getRow Vt.Vt.atBoundary Replay.start Replay.next →
        ∀ (budget : Nat),
          0 < budget →
            ∀ (v w : Vt.Vt),
              Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
                  Vt.Vt.quiesce (Checkpoint.Decoded Checkpoint.loadBytes) v →
                Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
                  Vt.Vt.quiesce (Checkpoint.Decoded Checkpoint.loadBytes) w →
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
    KeepsShowing
      (Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
        Vt.Vt.quiesce (Checkpoint.Decoded Checkpoint.loadBytes))
      (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.colCount Vt.Vt.rowCount
      Vt.Vt.getRow Vt.Vt.atBoundary Replay.start Replay.next := by
    intro budget v _ _ positive _ _ _ _ _
    exact ⟨_, Replay.emits_remaining budget positive (Replay.start v), fun _ _ => rfl⟩
  obtain ⟨_, -, rows, -⟩ :=
    h keeps 1 Nat.one_pos (Vt.Vt.init 2 1) (Vt.Vt.init 2 1) (.init 2 1) (.init 2 1) rfl rfl
      (by decide +kernel) []
  have row : (Vt.Vt.init 1 1).getRow 0 = (Vt.Vt.init 2 1).getRow 0 := rows 0 (by decide +kernel)
  exact absurd (congrArg (fun r : Vt.Row => r.size) row) (by decide +kernel)

theorem step_input_exact (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {inputs : List (List UInt8)} (hc : s.client? id = some c)
    (typist : c.attached = false ∨ c.sizer = true)
    (read : c.decoder.feed chunk = (dec, inputs.map Wire.Msg.input))
    (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = inputs.map Effect.writePty :=
  Session.step_input_exact s id chunk hc typist read healthy

theorem step_input_exact_rejects_drop :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder}
        {inputs : List (List UInt8)},
        s.client? id = some c →
          (c.attached = false ∨ c.sizer = true) →
          c.decoder.feed chunk = (dec, inputs.map Wire.Msg.input) →
          dec.errored = false →
          ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                (.bytes id chunk)).2 =
            inputs.map Effect.writePty := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have wrote :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
      (Wire.encode (.input [0x61])) { id := 1 } {} [[0x61]] joined (.inl rfl)
      (Session.feed_encode_fresh (.input [0x61]) (by simp [Wire.Msg.Fits, Wire.maxPayload])) rfl
  simp at wrote

theorem input_exact (reads : ByteArray → ByteArray) (delivers : Pty.Delivers reads) {cap : Nat}
    {accepted written : ByteArray} {b : Buf.Buf}
    (life :
      Buf.InputLife Buf.Buf.empty Buf.bufOffer Buf.bufAdvance Buf.writeFrom cap accepted written
        b) :
    reads written ++ Buf.writeFrom b = accepted ∧
      ∀ more, (Buf.bufOffer cap b more).2 = true ↔ cap < Buf.owedLen b + more.size := by
  refine ⟨?_, fun more => Buf.bufOffer_refuses_iff cap b more⟩
  rw [delivers written]
  exact Buf.inputLife_exact life

theorem input_exact_rejects_lost :
    ¬∀ (reads : ByteArray → ByteArray),
        Pty.Delivers reads →
          ∀ {cap : Nat} {accepted written : ByteArray} {b : Buf.Buf},
            Buf.InputLife Buf.Buf.empty (fun (_ : Nat) (b : Buf.Buf) (_ : ByteArray) => (b, false))
                Buf.bufAdvance Buf.writeFrom cap accepted written b →
              reads written ++ Buf.writeFrom b = accepted ∧
                ∀ more,
                  ((fun (_ : Nat) (b : Buf.Buf) (_ : ByteArray) => (b, false)) cap b more).2 =
                      true ↔
                    cap < Buf.owedLen b + more.size := by
  intro h
  have life :=
    Buf.InputLife.offer (empty := Buf.Buf.empty) (offer :=
      fun (_ : Nat) (b : Buf.Buf) (_ : ByteArray) => (b, false)) (advance := Buf.bufAdvance)
      (pending := Buf.writeFrom) (cap := 1) ByteArray.empty ByteArray.empty Buf.Buf.empty ⟨#[0x61]⟩
      .empty
  have lost := congrArg ByteArray.size (h id (fun _ => rfl) life).1
  simp [Buf.writeFrom_empty] at lost
  exact absurd lost (by decide)

theorem replay_history (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v)
    (hw :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (retained : (Render.sbRows v).isEmpty = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  refine
    ⟨Render.restore v, ?_,
      Render.restore_sb_reachable v w (Checkpoint.live_of_decoded hw)
        (Checkpoint.live_of_decoded hv) hcols hrows retained⟩
  rw [← Replay.start_faithful v]
  exact Replay.emits_remaining budget positive (Replay.start v)

theorem replay_history_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) w →
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

theorem replay_cursor (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v)
    (hw :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (ho : v.getModes.origin = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).cursorPos = v.cursorPos := by
  refine ⟨Render.restore v, ?_, ?_⟩
  · rw [← Replay.start_faithful v]
    exact Replay.emits_remaining budget positive (Replay.start v)
  obtain ⟨x, y⟩ :=
    Render.restore_cursor_any v w (Vt.good_of_liveReachable (Checkpoint.live_of_decoded hv))
      (Vt.good_of_liveReachable (Checkpoint.live_of_decoded hw)) hcols hrows ho
  simp only [Vt.cursorPos_eq, x, y]

theorem replay_cursor_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) w →
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

theorem decode_encode_chunked (ms : List Wire.Msg) (fits : ∀ m ∈ ms, m.Fits)
    (chunks : List (List UInt8)) (cut : chunks.flatten = ms.flatMap Wire.encode) :
    Wire.feedAll Wire.Decoder.feed {} chunks = ({ buf := [], errored := false }, ms) := by
  rw [Wire.feedAll_feed]
  exact Wire.decode_encode_chunked ms (fun m hm => Wire.fits_wf m (fits m hm)) chunks cut

theorem decode_encode_chunked_rejects_silence :
    ¬∀ (ms : List Wire.Msg),
        (∀ m ∈ ms, m.Fits) →
          ∀ (chunks : List (List UInt8)),
            chunks.flatten = ms.flatMap (fun (_ : Wire.Msg) => ([] : List UInt8)) →
              Wire.feedAll Wire.Decoder.feed {} chunks = ({ buf := [], errored := false }, ms) := by
  intro h
  have read := h [.done] (by simp [Wire.Msg.Fits]) [] (by simp)
  exact absurd (congrArg Prod.snd read) (by simp [Wire.feedAll])

theorem step_attach_focus (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {cols rows : UInt32} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.attach cols rows])) (healthy : dec.errored = false)
    (bytes : List UInt8) :
    Effect.writePty bytes ∈ (Session.step s (.bytes id chunk)).2 ↔
      bytes = [0x1B, 0x5B, 0x49] ∧
        s.terminal.getModes.focusEvents = true ∧
        c.attached = false ∧
        cols ≠ 0 ∧
        rows ≠ 0 ∧ ∀ other ∈ s.roster, other.id ≠ id → (other.attached && other.sizer) = false :=
  Session.step_attach_focus s id chunk hc read healthy bytes

theorem step_attach_focus_rejects_eager :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder}
        {cols rows : UInt32},
        s.client? id = some c →
          c.decoder.feed chunk = (dec, [.attach cols rows]) →
          dec.errored = false →
          ∀ (bytes : List UInt8),
            Effect.writePty bytes ∈
                ((fun (s : State) (_ : Event) =>
                      (s, ([.writePty [0x1B, 0x5B, 0x49]] : List (Effect Replay.Plan))))
                    s (.bytes id chunk)).2 ↔
              bytes = [0x1B, 0x5B, 0x49] ∧
                s.terminal.getModes.focusEvents = true ∧
                c.attached = false ∧
                cols ≠ 0 ∧
                rows ≠ 0 ∧
                ∀ other ∈ s.roster, other.id ≠ id → (other.attached && other.sizer) = false := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have heard :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
          (Wire.encode (.attach 0 0)) { id := 1 } {} 0 0 joined
          (Session.feed_encode_fresh (.attach 0 0) trivial) rfl [0x1B, 0x5B, 0x49]).mp
      (by simp)
  exact heard.2.2.2.1 rfl

theorem step_closed_focus (s : State) (id : Nat) (bytes : List UInt8) :
    Effect.writePty bytes ∈ (Session.step s (.closed id)).2 ↔
      bytes = [0x1B, 0x5B, 0x4F] ∧
        s.terminal.getModes.focusEvents = true ∧
        (s.client? id).any (·.sizer) = true ∧
        s.roster.any (fun c => c.attached && c.sizer) = true ∧
        (Session.step s (.closed id)).1.roster.any (fun c => c.attached && c.sizer) = false :=
  Session.step_closed_focus s id bytes

theorem step_closed_focus_rejects_eager :
    ¬∀ (s : State) (id : Nat) (bytes : List UInt8),
        Effect.writePty bytes ∈
            ((fun (s : State) (_ : Event) =>
                  (s, ([.writePty [0x1B, 0x5B, 0x4F]] : List (Effect Replay.Plan))))
                s (.closed id)).2 ↔
          bytes = [0x1B, 0x5B, 0x4F] ∧
            s.terminal.getModes.focusEvents = true ∧
            (s.client? id).any (·.sizer) = true ∧
            s.roster.any (fun c => c.attached && c.sizer) = true ∧
            ((fun (s : State) (_ : Event) =>
                      (s, ([.writePty [0x1B, 0x5B, 0x4F]] : List (Effect Replay.Plan))))
                    s (.closed id)).1.roster.any
                (fun c => c.attached && c.sizer) =
              false := by
  intro h
  obtain ⟨-, none⟩ := Session.connected_client_witness
  have heard := (h (State.boot (Vt.Vt.init 1 1) [] []) 1 [0x1B, 0x5B, 0x4F]).mp (by simp)
  rw [none] at heard
  exact absurd heard.2.2.1 (by decide)

theorem one_owner (grant : Claim.State → Nat → Nat → Bool) (exclusive : Claim.Exclusive grant)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b :=
  Claim.at_most_one_owner exclusive reached ha hb leftUses rightUses

theorem one_owner_rejects_socket :
    ¬∀ (grant : Claim.State → Nat → Nat → Bool),
        Claim.Exclusive grant →
          ∀ {s : Claim.State},
            Claim.Reachable grant (fun (socket _ : Bool) => socket) s →
              ∀ {a b resource : Nat} {left right : Claim.Lease},
                s.active a = some left →
                  s.active b = some right → left.Uses resource → right.Uses resource → a = b := by
  intro h
  -- the operating system grants every free lock, and only a free one
  let grant : Claim.State → Nat → Nat → Bool := fun s _ resource => s.locks resource == none
  have exclusive : Claim.Exclusive grant := fun s _ resource granted => by
    simpa [grant] using granted
  -- process 1 takes socket 1 and acts on lease (1, 3); process 2 takes socket 2 and checkpoint 3
  let s1 : Claim.State := { Claim.initial with locks := Claim.put Claim.initial.locks 1 (some 1) }
  let s2 : Claim.State := { s1 with active := Claim.put s1.active 1 (some ⟨1, 3⟩) }
  let s3 : Claim.State := { s2 with locks := Claim.put s2.locks 2 (some 2) }
  let s4 : Claim.State := { s3 with locks := Claim.put s3.locks 3 (some 2) }
  let s5 : Claim.State := { s4 with active := Claim.put s4.active 2 (some ⟨2, 3⟩) }
  have reached : Claim.Reachable grant (fun (socket _ : Bool) => socket) s5 :=
    ((((Claim.Reachable.initial.next (.acquire _ 1 1 rfl)).next (.enter _ 1 ⟨1, 3⟩ rfl rfl)).next
              (.acquire _ 2 2 rfl)).next
          (.acquire _ 2 3 rfl)).next
      (.enter _ 2 ⟨2, 3⟩ rfl rfl)
  have same := @h grant exclusive s5 reached 1 2 3 ⟨1, 3⟩ ⟨2, 3⟩ rfl rfl (.inr rfl) (.inr rfl)
  exact absurd same (by decide)

theorem step_labels_requested (s : State) (ev : Event)
    (changed : (Session.step s ev).1.labelList ≠ s.labelList) :
    ∃ id chunk c,
      ev = .bytes id chunk ∧
        s.client? id = some c ∧
        (c.attached = false ∨ c.sizer = true) ∧
        ∃ m ∈ (c.decoder.feed chunk).2, m.ChangesLabels := Session.step_labels_sources s ev changed

theorem step_labels_requested_rejects_reset :
    ¬∀ (s : State) (ev : Event),
        ((fun (s : State) (_ : Event) =>
                  (State.boot s.terminal [] [], ([] : List (Effect Replay.Plan))))
                s ev).1.labelList ≠
            s.labelList →
          ∃ id chunk c,
            ev = .bytes id chunk ∧
              s.client? id = some c ∧
              (c.attached = false ∨ c.sizer = true) ∧
              ∃ m ∈ (c.decoder.feed chunk).2, m.ChangesLabels := by
  intro h
  obtain ⟨-, -, -, -, labelled, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [("a", "b")] []
  obtain ⟨-, -, -, -, emptied, -⟩ :=
    Session.boot_observed (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).terminal [] []
  have changed :
    (State.boot (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).terminal [] []).labelList ≠
      (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).labelList := by
    rw [emptied, labelled]
    simp [maxLabels]
  obtain ⟨_, _, _, ticked, -⟩ := h (State.boot (Vt.Vt.init 1 1) [("a", "b")] []) (.tick 0) changed
  cases ticked

theorem infoFields_boot (vt : Vt.Vt) (labels metadata : List (String × String)) (evs : List Event) :
    ∃ rest,
      Session.infoFields (Session.trace Session.step (State.boot vt labels metadata) evs).1 =
        metadata ++ rest := by
  rw [Session.trace_step]
  exact Session.run_boot_infoFields vt labels metadata evs

theorem infoFields_boot_rejects_reboot :
    ¬∀ (vt : Vt.Vt) (labels metadata : List (String × String)) (evs : List Event),
        ∃ rest,
          Session.infoFields
              (Session.trace
                  (fun (_ : State) (_ : Event) =>
                    (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  (State.boot vt labels metadata) evs).1 =
            metadata ++ rest := by
  intro h
  obtain ⟨rest, named⟩ := h (Vt.Vt.init 1 1) [] [("name", "a")] [.tick 0]
  obtain ⟨tail, counted⟩ := Session.infoFields_metaKv (State.boot (Vt.Vt.init 1 1) [] [])
  have booted :
    (Session.trace
          (fun (_ : State) (_ : Event) =>
            (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
          (State.boot (Vt.Vt.init 1 1) [] [("name", "a")]) [.tick 0]).1 =
      State.boot (Vt.Vt.init 1 1) [] [] :=
    rfl
  rw [booted, counted, Session.boot_metaKv] at named
  simp at named

theorem step_terminal_sources (s : State) (ev : Event) :
    (∃ chunk, ev = .ptyOut chunk ∧ (Session.step s ev).1.terminal = s.terminal.feed chunk) ∨
      ∃ sizes : List (Nat × Nat),
        (Session.step s ev).1.terminal =
          sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal :=
  Session.step_vt_sources s ev

theorem step_terminal_sources_rejects_print :
    ¬∀ (s : State) (ev : Event),
        (∃ chunk,
            ev = .ptyOut chunk ∧
              ((fun (s : State) (_ : Event) =>
                      (State.boot (s.terminal.feed [0x41]) [] [], ([] : List (Effect Replay.Plan))))
                    s ev).1.terminal =
                s.terminal.feed chunk) ∨
          ∃ sizes : List (Nat × Nat),
            ((fun (s : State) (_ : Event) =>
                    (State.boot (s.terminal.feed [0x41]) [] [], ([] : List (Effect Replay.Plan))))
                  s ev).1.terminal =
              sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal := by
  intro h
  obtain ⟨-, -, kept, -, -, -⟩ := Session.boot_observed (Vt.Vt.init 2 1) [] []
  obtain ⟨-, -, printed, -, -, -⟩ :=
    Session.boot_observed ((State.boot (Vt.Vt.init 2 1) [] []).terminal.feed [0x41]) [] []
  rcases h (State.boot (Vt.Vt.init 2 1) [] []) (.tick 0) with ⟨_, ticked, -⟩ | ⟨sizes, resized⟩
  · cases ticked
  · change
      (State.boot ((State.boot (Vt.Vt.init 2 1) [] []).terminal.feed [0x41]) [] []).terminal =
        _ at resized
    rw [printed, kept] at resized
    have moved : ((Vt.Vt.init 2 1).feed [0x41]).cursorPos = (1, 0) := by decide +kernel
    rw [resized, Session.foldl_resize_origin _ (by decide +kernel)] at moved
    simp at moved

theorem start_plan (live saved : Bool) :
    Start.plan live saved = if live then .running else if saved then .saved else .take :=
  Start.plan_eq live saved

theorem start_plan_rejects_take :
    ¬∀ (live saved : Bool),
        (fun (_ _ : Bool) => Start.Plan.take) live saved =
          if live then .running else if saved then .saved else .take := by
  intro h
  cases h true false

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.client? other =
      s.client? other := by
  rw [Session.trace_step]
  exact Session.run_bytes_isolates s id chunks h

theorem run_bytes_isolates_rejects_reset :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat},
        other ≠ id →
          (Session.trace
                  (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  s (chunks.map (Event.bytes id))).1.client?
              other =
            s.client? other := by
  intro h
  obtain ⟨joined, empty⟩ := Session.connected_client_witness
  have forgot :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 0 [[]] 1
      (by decide)
  have reset :
    (Session.trace
          (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
          (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1
          ([[]].map (Event.bytes 0))).1 =
      State.boot (Vt.Vt.init 1 1) [] [] :=
    rfl
  rw [reset, empty, joined] at forgot
  cases forgot

theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.labelList = s.labelList ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  rw [Session.trace_step]
  exact Session.run_readonly s id chunks hc attached watcher

theorem run_readonly_rejects_kill :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client},
        (fun (_ : State) (i : Nat) => some ({ id := i, attached := true } : Client)) s id = some c →
          c.attached = true →
          c.sizer = false →
          (Session.trace (fun s _ => (s, ([.killChild] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.terminal =
              s.terminal ∧
            (Session.trace (fun s _ => (s, ([.killChild] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.labelList =
              s.labelList ∧
            ∀
              eff ∈
                (Session.trace (fun s _ => (s, ([.killChild] : List (Effect Replay.Plan)))) s
                    (chunks.map (Event.bytes id))).2,
              (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  intro h
  obtain ⟨-, -, effects⟩ :=
    @h (State.boot (Vt.Vt.init 1 1) [] []) 0 [[]] { id := 0, attached := true } rfl rfl rfl
  rcases effects .killChild (by simp [Session.trace]) with ⟨_, sent⟩ | closed | saved
  · cases sent
  · cases closed
  · cases saved

theorem remotesFile_home (home : Option String) :
    Os.Env.remotesFile home = none ↔ home = none ∨ home = some "" :=
  Os.Env.remotesFile_eq_none_iff home

theorem remotesFile_home_rejects_shared :
    ¬∀ (home : Option String),
        (fun (_ : Option String) => some "remotes") home = none ↔ home = none ∨ home = some "" := by
  intro h
  exact absurd ((h none).mpr (.inl rfl)) (by simp)

theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (Listing.rowFields socketName info).lookup "name" = some socketName :=
  Listing.rowFields_name socketName info

theorem rowFields_name_rejects_reply :
    ¬∀ (socketName : String) (info : List (String × String)),
        ((fun (_ : String) (info : List (String × String)) => info) socketName info).lookup "name" =
          some socketName := by
  intro h
  exact absurd (h "s" []) (by simp)

theorem picker_attach_listed (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .attach target) : target ∈ s.candidates :=
  (Selector.Picker.step_attach_mem s key target h).1

theorem picker_attach_listed_rejects_fixed :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.attach "s") s
              key =
            .attach target →
          target ∈ s.candidates := by
  intro h
  exact absurd (h { candidates := [] } .accept "s" rfl) (by simp)

theorem picker_create_new (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .create target) :
    target ∉ s.candidates ∧ target ≠ "" ∧ Name.Valid ((target.splitOn "@").headD "") := by
  obtain ⟨-, absent, nonempty, -, valid, -⟩ := Selector.Picker.step_create_valid s key target h
  exact ⟨absent, nonempty, valid⟩

theorem picker_create_new_rejects_empty :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.create "") s
              key =
            .create target →
          target ∉ s.candidates ∧ target ≠ "" ∧ Name.Valid ((target.splitOn "@").headD "") := by
  intro h
  exact absurd (h { candidates := [] } .accept "" rfl).2.1 (by simp)

theorem route_exact (args : List String) :
    App.Entry.route args =
      if args = [] then .session ["help"]
      else
        if args = ["attach"] ∨ args = ["a"] then .selector false
        else
          if args = ["attach", "--read-only"] ∨ args = ["a", "--read-only"] then .selector true
          else
            if args.head? = some "tmux" then .tmux args.tail
            else .session args := App.Entry.route_eq args

theorem route_exact_rejects_selector :
    ¬∀ (args : List String),
        (fun (args : List String) => App.Entry.Route.session args) args =
          if args = [] then .session ["help"]
          else
            if args = ["attach"] ∨ args = ["a"] then .selector false
            else
              if args = ["attach", "--read-only"] ∨ args = ["a", "--read-only"] then .selector true
              else if args.head? = some "tmux" then .tmux args.tail else .session args := by
  intro h
  exact absurd (h ["attach"]) (by simp)

theorem lookup_table :
    (App.Commands.table.flatMap fun command => command.word :: command.aliases).Nodup ∧
      ∀ command ∈ App.Commands.table,
        App.Commands.lookup command.word = some command ∧
          ∀ word ∈ command.aliases, App.Commands.lookup word = some command :=
  ⟨App.Commands.table_words_nodup, fun command member =>
    ⟨App.Commands.lookup_word command member, App.Commands.lookup_alias command member⟩⟩

theorem lookup_table_rejects_none :
    ¬((App.Commands.table.flatMap fun command => command.word :: command.aliases).Nodup ∧
        ∀ command ∈ App.Commands.table,
          (fun (_ : String) => (none : Option App.Commands.Command)) command.word = some command ∧
            ∀ word ∈ command.aliases,
              (fun (_ : String) => (none : Option App.Commands.Command)) word = some command) := by
  intro h
  obtain ⟨command, member⟩ := List.exists_mem_of_ne_nil _ App.Commands.table_ne_nil
  exact absurd (h.2 command member).1 (by simp)

theorem retired_free : ∀ entry ∈ App.Commands.retired, App.Commands.lookup entry.1 = none :=
  App.Commands.retired_free

theorem retired_free_rejects_any :
    ¬∀ entry ∈ App.Commands.retired,
        (fun (_ : String) =>
              some ({ word := "run", args := "", summary := "" } : App.Commands.Command))
            entry.1 =
          none := by
  intro h
  obtain ⟨entry, member⟩ := List.exists_mem_of_ne_nil _ App.Commands.retired_ne_nil
  exact absurd (h entry member) (by simp)

theorem usageLine_exact (command : App.Commands.Command) :
    App.Commands.usageLine command =
      if command.args.isEmpty then s!"usage: linger {command.word}"
      else s!"usage: linger {command.word} {command.args}" := App.Commands.usageLine_eq command

theorem usageLine_exact_rejects_bare :
    ¬∀ (command : App.Commands.Command),
        (fun (_ : App.Commands.Command) => "usage: linger") command =
          if command.args.isEmpty then s!"usage: linger {command.word}"
          else s!"usage: linger {command.word} {command.args}" := by
  intro h
  exact absurd (h { word := "help", args := "", summary := "" }) (by decide)

theorem plan_exact (existing : List String) (panes : List Import.Resurrect.Pane)
    (pane : Import.Resurrect.Pane) :
    pane ∈ Import.Resurrect.plan existing panes ↔ pane ∈ panes ∧ pane.name ∉ existing :=
  Import.Resurrect.mem_plan existing panes pane

theorem plan_exact_rejects_all :
    ¬∀ (existing : List String) (panes : List Import.Resurrect.Pane) (pane : Import.Resurrect.Pane),
        pane ∈
            (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes) existing panes ↔
          pane ∈ panes ∧ pane.name ∉ existing := by
  intro h
  have kept :=
    (h ["a"] [{ name := "a", dir := "", line := 0 }] { name := "a", dir := "", line := 0 }).mp
      (by simp)
  exact absurd kept.2 (by simp)

theorem plan_again_empty (existing : List String) (panes made : List Import.Resurrect.Pane)
    (first : made = Import.Resurrect.plan existing panes) :
    Import.Resurrect.plan (existing ++ made.map (·.name)) panes = [] := by
  rw [first]
  exact Import.Resurrect.plan_sequential_idempotent existing panes

theorem plan_again_empty_rejects_all :
    ¬∀ (existing : List String) (panes made : List Import.Resurrect.Pane),
        made =
            (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes) existing panes →
          (fun (_ : List String) (panes : List Import.Resurrect.Pane) => panes)
              (existing ++ made.map (·.name)) panes =
            [] := by
  intro h
  exact absurd (h [] [{ name := "a", dir := "", line := 0 }] _ rfl) (by simp)

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := Name.check_eq_some_iff s result

theorem check_eq_some_iff_rejects_any :
    ¬∀ (s result : String), (fun s => some s) s = some result ↔ result = s ∧ Name.Valid s := by
  intro h
  exact absurd ((h "" "").mp rfl).2.1 (by simp)

theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := Remote.command_argv verb words

theorem command_argv_rejects_empty :
    ¬∀ (verb : String) (words : List String),
        Remote.Shell.Words ((fun (_ : String) (_ : List String) => "") verb words).toList
          (("linger" :: verb :: words).map String.toList) := by
  intro h
  have words := h "" []
  cases words
  simp_all [Remote.Shell.word]

theorem check_no_alias (a b name : String) (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := Name.check_no_alias ha hb

theorem check_no_alias_rejects_fold :
    ¬∀ (a b name : String),
        (fun (_ : String) => some "s") a = some name →
          (fun (_ : String) => some "s") b = some name → a = b := by
  intro h
  exact absurd (h "a" "b" "s" rfl rfl) (by decide)

theorem targetArgs_targetOperands (name : String) (rest : List String) :
    Remote.targetArgs (Remote.targetOperands name ++ rest) = some (name, rest) :=
  Remote.targetArgs_targetOperands name rest

theorem targetArgs_targetOperands_rejects_none :
    ¬∀ (name : String) (rest : List String),
        Remote.targetArgs ((fun (_ : String) => ([] : List String)) name ++ rest) =
          some (name, rest) := by
  intro h
  have read := h "s" []
  simp [Remote.targetArgs_nil] at read

theorem shellQuote_roundtrip (s : String) (tail : List Char)
    (boundary : tail = [] ∨ ∃ rest, tail = ' ' :: rest) :
    Remote.Shell.word ((Remote.shellQuote s).toList ++ tail) = some (s.toList, tail) :=
  Remote.shellQuote_roundtrip s tail boundary

theorem shellQuote_roundtrip_rejects_bare :
    ¬∀ (s : String) (tail : List Char),
        (tail = [] ∨ ∃ rest, tail = ' ' :: rest) →
          Remote.Shell.word (((fun (s : String) => s) s).toList ++ tail) =
            some (s.toList, tail) := by
  intro h
  have read := h "" [] (.inl rfl)
  simp [Remote.Shell.word] at read

theorem checkHosts_ok_iff (hosts result : List String) :
    Remote.checkHosts hosts = .ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true :=
  Remote.checkHosts_ok_iff hosts result

theorem checkHosts_ok_iff_rejects_any :
    ¬∀ (hosts result : List String),
        (fun (hosts : List String) => (.ok hosts : Except String (List String))) hosts =
            .ok result ↔
          result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, Remote.hostClean x = true := by
  intro h
  have twice := ((h ["a", "a"] ["a", "a"]).mp rfl).2.1
  simp at twice

theorem detach_key (flag : Option String) :
    Os.Env.detachEnabled true flag = true ∧ Os.Env.detachEnabled false flag = flag.isNone :=
  ⟨Os.Env.detachEnabled_readOnly flag, Os.Env.detachEnabled_writable flag⟩

theorem detach_key_rejects_never :
    ¬∀ (flag : Option String),
        (fun (_ : Bool) (_ : Option String) => false) true flag = true ∧
          (fun (_ : Bool) (_ : Option String) => false) false flag = flag.isNone := by
  intro h
  exact absurd (h none).1 (by decide)

theorem resumeDir_where (home : Option String) (saved dir : String) (set : dir ≠ "") :
    Os.Env.resumeDir home saved true = some saved ∧
      Os.Env.resumeDir (some dir) saved false = some dir ∧
      Os.Env.resumeDir none saved false = none ∧ Os.Env.resumeDir (some "") saved false = none :=
  ⟨Os.Env.resumeDir_saved home saved, Os.Env.resumeDir_home set saved,
    (Os.Env.resumeDir_absent saved).1, (Os.Env.resumeDir_absent saved).2⟩

theorem resumeDir_where_rejects_gone :
    ¬∀ (home : Option String) (saved dir : String),
        dir ≠ "" →
          (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) home saved true =
              some saved ∧
            (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) (some dir) saved
                false =
              some dir ∧
            (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) none saved false =
              none ∧
            (fun (_ : Option String) (saved : String) (_ : Bool) => some saved) (some "") saved
                false =
              none := by
  intro h
  exact absurd (h none "a" "b" (by decide)).2.1 (by decide)

theorem failureStatus_exact (why : String) :
    Start.failureStatus (.directory why) = 125 ∧
      Start.failureStatus (.notFound why) = 127 ∧
      Start.failureStatus (.notRunnable why) = 126 := Start.failureStatus_exact why

theorem failureStatus_exact_rejects_alike :
    ¬∀ (why : String),
        (fun (_ : Os.Spawn.Failure) => (1 : UInt8)) (.directory why) = 125 ∧
          (fun (_ : Os.Spawn.Failure) => (1 : UInt8)) (.notFound why) = 127 ∧
          (fun (_ : Os.Spawn.Failure) => (1 : UInt8)) (.notRunnable why) = 126 := by
  intro h
  exact absurd (h "").1 (by decide)

theorem metadata_dirs (name pid created cmd dir : String) (saved : Option String) :
    ("start_dir", dir) ∈ Start.metadata name pid created cmd dir saved ∧
      ∀ d,
        ("saved_dir", d) ∈ Start.metadata name pid created cmd dir saved ↔
          saved = some d ∧ d ≠ dir := Start.metadata_dirs name pid created cmd dir saved

theorem metadata_dirs_rejects_silent :
    ¬∀ (name pid created cmd dir : String) (saved : Option String),
        ("start_dir", dir) ∈
            (fun (_ _ _ _ dir : String) (_ : Option String) => [("start_dir", dir)]) name pid
              created cmd dir saved ∧
          ∀ d,
            ("saved_dir", d) ∈
                (fun (_ _ _ _ dir : String) (_ : Option String) => [("start_dir", dir)]) name pid
                  created cmd dir saved ↔
              saved = some d ∧ d ≠ dir := by
  intro h
  have moved := ((h "" "" "" "" "b" (some "a")).2 "a").2 ⟨rfl, by decide⟩
  simp at moved

theorem programOf_exact (shell : String) (argv : List String) :
    Start.programOf shell argv = (argv.headD shell, (argv.drop 1).toArray) :=
  Start.programOf_exact shell argv

theorem programOf_exact_rejects_shell :
    ¬∀ (shell : String) (argv : List String),
        (fun (shell : String) (argv : List String) => (shell, #["-c", String.intercalate " " argv]))
            shell argv =
          (argv.headD shell, (argv.drop 1).toArray) := by
  intro h
  exact absurd (congrArg Prod.fst (h "sh" ["ls"])) (by decide)

theorem shellOf_choice (shell : String) (set : shell ≠ "") :
    Os.Env.shellOf (some shell) = shell ∧
      Os.Env.shellOf none = "sh" ∧ Os.Env.shellOf (some "") = "sh" :=
  ⟨Os.Env.shellOf_set set, Os.Env.shellOf_absent.1, Os.Env.shellOf_absent.2⟩

theorem shellOf_choice_rejects_fixed :
    ¬∀ (shell : String),
        shell ≠ "" →
          (fun (_ : Option String) => "sh") (some shell) = shell ∧
            (fun (_ : Option String) => "sh") none = "sh" ∧
            (fun (_ : Option String) => "sh") (some "") = "sh" := by
  intro h
  exact absurd (h "fish" (by decide)).1 (by decide)

theorem start_runs (inherited : String → Option String)
    (start : String → String → Array String → List (String × String) → Option Os.Spawn.Started)
    (runs : Os.Spawn.Runs inherited start) (name dir shell : String) (argv : List String)
    {started : Os.Spawn.Started}
    (ok :
      start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
          (Start.environment name) =
        some started) :
    started.argv = argv.headD shell :: argv.drop 1 ∧
      started.dir = dir ∧
      started.env "LINGER_SESSION" = some name ∧
      started.env "TERM" = some "xterm-256color" ∧
      started.env "TERM_PROGRAM" = some "linger" ∧
      started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
      ∀ key,
        key ∉ ["LINGER_SESSION", "TERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION"] →
          started.env key = inherited key := by
  obtain ⟨hargv, hdir, henv⟩ := runs _ _ _ _ _ ok
  rw [Start.programOf_exact] at hargv
  refine ⟨by simpa using hargv, hdir, ?_, ?_, ?_, ?_, fun key hkey => ?_⟩
  all_goals rw [henv, Start.environment_lookup]
  · simp
  · simp
  · simp
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkey
    simp [hkey.1, hkey.2.1, hkey.2.2.1, hkey.2.2.2]

theorem start_runs_rejects_unnamed :
    ¬∀ (inherited : String → Option String)
        (start : String → String → Array String → List (String × String) → Option Os.Spawn.Started),
        Os.Spawn.Runs inherited start →
          ∀ (name dir shell : String) (argv : List String) {started : Os.Spawn.Started},
            start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
                  ((fun (_ : String) => ([] : List (String × String))) name) =
                some started →
              started.argv = argv.headD shell :: argv.drop 1 ∧
                started.dir = dir ∧
                started.env "LINGER_SESSION" = some name ∧
                started.env "TERM" = some "xterm-256color" ∧
                started.env "TERM_PROGRAM" = some "linger" ∧
                started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
                ∀ key,
                  key ∉ ["LINGER_SESSION", "TERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION"] →
                    started.env key = inherited key := by
  intro h
  have runs :
    Os.Spawn.Runs (fun _ => none) fun dir prog args extra =>
      some
        { argv := prog :: args.toList, dir,
          env := fun key => (extra.reverse.lookup key).orElse fun _ => none } := by
    intro dir prog args extra started hs
    cases hs
    exact ⟨rfl, rfl, fun _ => rfl⟩
  exact absurd (h _ _ runs "x" "" "sh" [] rfl).2.2.1 (by simp)

theorem step_ended_reports (s : State) (o : Outcome) {c : Client} (hc : c ∈ s.roster)
    (listening : c.attached = true ∨ c.waiting = true) :
    [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
        (Session.step s (.childExited o)).2 ∧
      (Session.step s (.childExited o)).2.getLast? = some .exit :=
  Session.step_ended_reports s o hc listening

theorem step_ended_reports_rejects_status :
    ¬∀ (s : State) (o : Outcome) {c : Client},
        c ∈ (fun (_ : State) => [({ id := 0, attached := true } : Client)]) s →
          c.attached = true ∨ c.waiting = true →
          [Effect.send c.id (.ended o), Effect.send c.id (.exited o.status)] <:+:
              ((fun s _ => (s, ([.send 0 (.exited 1), .exit] : List (Effect Replay.Plan)))) s
                  (Event.childExited o)).2 ∧
            ((fun s _ => (s, ([.send 0 (.exited 1), .exit] : List (Effect Replay.Plan)))) s
                  (Event.childExited o)).2.getLast? =
              some .exit := by
  intro h
  obtain ⟨heard, -⟩ :=
    @h (State.boot (Vt.Vt.init 1 1) [] []) .unknown { id := 0, attached := true } (by simp)
      (.inl rfl)
  have same := heard.eq_of_length rfl
  simp at same

theorem step_childExited_keeps (s : State) (o : Outcome) :
    (∃ front,
        (Session.step s (.childExited o)).2 = front ++ [.checkpoint, .exit] ∧
          Effect.dropCheckpoint ∉ front) ∧
      (Session.step s (.childExited o)).1.terminal = s.terminal :=
  Session.step_childExited_keeps s o

theorem step_childExited_keeps_rejects_drop :
    ¬∀ (s : State) (o : Outcome),
        (∃ front,
            ((fun (s : State) (_ : Event) =>
                      (s, ([.dropCheckpoint, .checkpoint, .exit] : List (Effect Replay.Plan))))
                    s (.childExited o)).2 =
                front ++ [.checkpoint, .exit] ∧
              Effect.dropCheckpoint ∉ front) ∧
          ((fun (s : State) (_ : Event) =>
                  (s, ([.dropCheckpoint, .checkpoint, .exit] : List (Effect Replay.Plan))))
                s (.childExited o)).1.terminal =
            s.terminal := by
  intro h
  obtain ⟨⟨front, effects, kept⟩, -⟩ := h (State.boot (Vt.Vt.init 1 1) [] []) .unknown
  have dropped : [Effect.dropCheckpoint] ++ [.checkpoint, .exit] = front ++ [.checkpoint, .exit] :=
    effects
  rw [← List.append_cancel_right dropped] at kept
  exact kept (List.mem_singleton_self _)

theorem record_answer (o : Outcome) (file : Option (List UInt8)) :
    Record.answer (some (Record.encode (.ended o))) = some o ∧
      (Record.answer file).isSome = file.isSome :=
  ⟨Record.answer_ended o, Record.answer_isSome file⟩

theorem record_answer_rejects_unknown :
    ¬∀ (o : Outcome) (file : Option (List UInt8)),
        (fun (_ : Option (List UInt8)) => some Outcome.unknown) (some (Record.encode (.ended o))) =
            some o ∧
          ((fun (_ : Option (List UInt8)) => some Outcome.unknown) file).isSome = file.isSome := by
  intro h
  exact absurd (h (.exited 0) none).1 (by simp)

theorem record_kept (afterSave : List UInt8 → Option (List UInt8)) (kept : Record.Kept afterSave)
    (o : Outcome) (seen : Option Seen) :
    Record.answer (afterSave (Record.encode (.ended o))) = some o ∧
      Record.answer (afterSave (Record.encode (.running seen))) = some .unknown := by
  rw [kept, kept]
  exact ⟨Record.answer_ended o, Record.answer_running seen⟩

theorem record_kept_rejects_blank :
    ¬∀ (afterSave : List UInt8 → Option (List UInt8)),
        Record.Kept afterSave →
          ∀ (o : Outcome) (seen : Option Seen),
            Record.answer (afterSave ((fun (_ : Record) => ([] : List UInt8)) (.ended o))) =
                some o ∧
              Record.answer (afterSave ((fun (_ : Record) => ([] : List UInt8)) (.running seen))) =
                some .unknown := by
  intro h
  have blank := (h some (fun _ => rfl) (.exited 0) none).1
  simp [Record.answer, Record.decode] at blank

theorem outcomeFields_injective (o₁ o₂ : Outcome)
    (h : Session.outcomeFields o₁ = Session.outcomeFields o₂) : o₁ = o₂ :=
  Session.outcomeFields_injective h

theorem outcomeFields_injective_rejects_silence :
    ¬∀ (o₁ o₂ : Outcome),
        (fun (_ : Outcome) => ([] : List (String × String))) o₁ =
            (fun (_ : Outcome) => ([] : List (String × String))) o₂ →
          o₁ = o₂ := by
  intro h
  exact absurd (h (.exited 0) .unknown rfl) (by simp)

theorem infoFields_protocol (s : State) :
    ("protocol", toString Wire.protocol) ∈ Session.infoFields s := (Session.infoFields_protocol s).1

theorem infoFields_protocol_rejects_empty :
    ¬∀ (s : State),
        ("protocol", toString Wire.protocol) ∈
          (fun (_ : State) => ([] : List (String × String))) s := by
  intro h
  exact absurd (h (State.boot (Vt.Vt.init 1 1) [] [])) (by simp)

theorem step_unknown_refused (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {tag : UInt8} {payload : List UInt8} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, [.unknown tag payload])) (healthy : dec.errored = false) :
    (Session.step s (.bytes id chunk)).2 = [.send id (.err "unknown message".toUTF8.toList)] ∧
      (Session.step s (.bytes id chunk)).1.terminal = s.terminal ∧
      (Session.step s (.bytes id chunk)).1.labelList = s.labelList :=
  Session.step_unknown_refused s id chunk hc read healthy

theorem step_unknown_refused_rejects_silence :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder} {tag : UInt8}
        {payload : List UInt8},
        s.client? id = some c →
          c.decoder.feed chunk = (dec, [.unknown tag payload]) →
          dec.errored = false →
          ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).2 =
              [.send id (.err "unknown message".toUTF8.toList)] ∧
            ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.terminal =
              s.terminal ∧
            ((fun (s : State) (_ : Event) => (s, ([] : List (Effect Replay.Plan)))) s
                  (.bytes id chunk)).1.labelList =
              s.labelList := by
  intro h
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  have refused :=
    (@h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
        (Wire.encode (.unknown 200 [])) { id := 1 } {} 200 [] joined
        (Session.feed_encode_fresh (.unknown 200 []) ⟨by simp, by decide⟩) rfl).1
  simp at refused

theorem run_total_safe {World ε : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result State World) (events : List Event)
    (hb : Bounds State.roster State.labelList State.scanner r.st)
    (hlive :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal) :
    ∃ out,
      Driver.run execute r events = .ok out ∧
        Bounds State.roster State.labelList State.scanner out.st ∧
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
          (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  have live : LiveVt r.st := (Session.liveVt_iff _).mpr (Checkpoint.live_decoded_iff.mp hlive)
  obtain ⟨out, ok, ⟨bounded, _⟩, kept⟩ :=
    Driver.run_total_safe execute hw r events
      ⟨(Session.bounded_iff_bounds _).mpr hb, Vt.good_of_liveReachable live⟩ live
  exact
    ⟨out, ok, (Session.bounded_iff_bounds _).mp bounded,
      Checkpoint.live_decoded_iff.mpr ((Session.liveVt_iff _).mp kept)⟩

theorem run_total_safe_rejects_jump :
    ¬∀ {World ε : Type}
        (execute :
          State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff)),
        Driver.Responds execute →
          ∀ (r : Driver.Result State World) (events : List Event),
            Bounds State.roster
                (fun st =>
                  if st.terminal.colCount = 80 then [] else List.replicate (maxLabels + 1) ("", ""))
                State.scanner r.st →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                (Checkpoint.Decoded Checkpoint.loadBytes) r.st.terminal →
              ∃ out,
                Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r events = .ok out ∧
                  Bounds State.roster
                    (fun st =>
                      if st.terminal.colCount = 80 then []
                      else List.replicate (maxLabels + 1) ("", ""))
                    State.scanner out.st ∧
                  Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
                    (Checkpoint.Decoded Checkpoint.loadBytes) out.st.terminal := by
  intro h
  obtain ⟨-, -, wide, roster, -, scanner⟩ := Session.boot_observed (Vt.Vt.init 80 24) [] []
  obtain ⟨-, -, narrow, -, -, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [] []
  let execute : State → Unit → (eff : Effect Replay.Plan) → Except Unit (Unit × Driver.Reply eff) :=
    fun _ world eff => .ok (world, Driver.success eff)
  obtain ⟨out, jumped, bounds, -⟩ :=
    @h Unit Unit execute (fun _ _ _ => ⟨_, rfl⟩)
      { st := State.boot (Vt.Vt.init 80 24) [] [], world := () } []
      ⟨by
        rw [roster]; decide, by
        rw [wide]; decide +kernel, fun c member =>
        absurd member
          (by
            rw [roster]; exact List.not_mem_nil),
        by
        rw [scanner]; trivial⟩
      (by
        rw [wide]; exact .init 80 24)
  cases jumped
  have overflow := bounds.labelsLe
  rw [narrow] at overflow
  exact absurd overflow (by decide +kernel)

theorem run_feedback_alive {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (running : r.exiting = false)
    (failures : ∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) :
    (Driver.run execute r events).exiting = false :=
  Driver.run_feedback_alive execute r events running failures

theorem run_feedback_alive_rejects_halt :
    ¬∀ {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = false →
          (∀ ev ∈ events, ev = .checkpointFailed ∨ ∃ id, ev = .closed id) →
          (Driver.halt execute r events).exiting = false := by
  intro h
  have stopped :=
    @h Unit (fun _ world eff => (world, Driver.success eff))
      { st := State.boot (Vt.Vt.init 1 1) [] [], world := () } [] rfl (by simp)
  exact absurd stopped (by decide)

theorem run_exited {m : Type → Type} [Monad m] {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff))
    (r : Driver.Result State World) (events : List Event) (exited : r.exiting = true) :
    Driver.run execute r events = pure r := Driver.run_exited execute r events exited

theorem run_exited_rejects_jump :
    ¬∀ {m : Type → Type} [Monad m] {World : Type}
        (execute : State → World → (eff : Effect Replay.Plan) → m (World × Driver.Reply eff))
        (r : Driver.Result State World) (events : List Event),
        r.exiting = true →
          Driver.jump (State.boot (Vt.Vt.init 1 1) [] []) execute r events = pure r := by
  intro h
  have moved :=
    @h Id _ Unit (fun _ world eff => (world, Driver.success eff))
      { st := State.boot (Vt.Vt.init 1 1) [("a", "b")] [], world := (), exiting := true } [] rfl
  have labels := congrArg (fun (out : Driver.Result State Unit) => out.st.labelList) moved
  change
    (State.boot (Vt.Vt.init 1 1) [] []).labelList =
      (State.boot (Vt.Vt.init 1 1) [("a", "b")] []).labelList at labels
  obtain ⟨-, -, -, -, empty, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [] []
  obtain ⟨-, -, -, -, labelled, -⟩ := Session.boot_observed (Vt.Vt.init 1 1) [("a", "b")] []
  rw [empty, labelled] at labels
  simp [maxLabels] at labels

theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap :=
  Buf.reachableIn_bound h

theorem reachableIn_bound_rejects_append :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.InputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b → Buf.owedLen b ≤ cap := by
  intro h
  have owed :=
    @h 0 (Buf.bufEnqueue 0 Buf.Buf.empty (ByteArray.mk #[0])).1
      (.offer Buf.Buf.empty (ByteArray.mk #[0]) .empty)
  obtain ⟨empty, -, -, -, appended, -⟩ := Buf.buf_observed 0 0 Buf.Buf.empty (ByteArray.mk #[0])
  rw [appended, empty] at owed
  exact absurd owed (by decide)

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := Buf.reachableOut_bound h

theorem reachableOut_bound_rejects_uncut :
    ¬∀ {cap : Nat} {b : Buf.Buf},
        Buf.OutputReach Buf.Buf.empty (fun cap b more => ((Buf.bufEnqueue cap b more).1, false))
            Buf.bufAdvance cap b →
          Buf.owedLen b ≤ cap := by
  intro h
  have owed :=
    @h 0 (Buf.bufEnqueue 0 Buf.Buf.empty (ByteArray.mk #[0])).1
      (.enqueue Buf.Buf.empty (ByteArray.mk #[0]) .empty rfl)
  obtain ⟨empty, -, -, -, appended, -⟩ := Buf.buf_observed 0 0 Buf.Buf.empty (ByteArray.mk #[0])
  rw [appended, empty] at owed
  exact absurd owed (by decide)

theorem live_shape (v : Vt.Vt)
    (hv :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) v) :
    1 ≤ v.colCount ∧
      v.colCount ≤ 1000 ∧
      1 ≤ v.rowCount ∧
      v.rowCount ≤ 1000 ∧
      (∀ y < v.rowCount, (v.getRow y).size = v.colCount) ∧
      v.cursorPos.1 < v.colCount ∧ v.cursorPos.2 < v.rowCount ∧ v.scrollback.length ≤ Vt.sbCap := by
  have live := Checkpoint.live_of_decoded hv
  have good := Vt.good_of_liveReachable live
  have shaped := Vt.renderable_of_liveReachable live
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
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded Checkpoint.loadBytes) v →
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

theorem step_bytes_one_reply (s : State) (id : Nat) (chunk : List UInt8) :
    ((Session.step s (.bytes id chunk)).2.all (!·.rendered) ∨
        ∃ pre frames post,
          (Session.step s (.bytes id chunk)).2 = pre ++ frames ++ Effect.send id .done :: post ∧
            frames.all (·.rendered) ∧ (pre ++ post).all (!·.rendered)) ∧
      (((Session.step s (.bytes id chunk)).1.client? id).all (!·.attached) →
        ((Session.step s (.bytes id chunk)).2.filter (·.resizes)).length ≤ 1) :=
  Session.step_bytes_one_reply_observed s id chunk

theorem step_bytes_one_reply_rejects_twice :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8),
        (((fun (s : State) (_ : Event) =>
                    (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                  s (.bytes id chunk)).2.all
              (!·.rendered) ∨
            ∃ pre frames post,
              ((fun (s : State) (_ : Event) =>
                        (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                      s (.bytes id chunk)).2 =
                  pre ++ frames ++ Effect.send id .done :: post ∧
                frames.all (·.rendered) ∧ (pre ++ post).all (!·.rendered)) ∧
          ((((fun (s : State) (_ : Event) =>
                        (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                      s (.bytes id chunk)).1.client?
                  id).all
              (!·.attached) →
            (((fun (s : State) (_ : Event) =>
                        (s, ([.resizePty 1 1, .resizePty 1 1] : List (Effect Replay.Plan))))
                      s (.bytes id chunk)).2.filter
                  (·.resizes)).length ≤
              1) := by
  intro h
  obtain ⟨-, none⟩ := Session.connected_client_witness
  have twice := (h (State.boot (Vt.Vt.init 1 1) [] []) 1 []).2 (by simp [none])
  exact absurd twice (by decide)

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

theorem captureBytes_bounded (contents : String) :
    (Import.Resurrect.captureBytes contents).length ≤ 2 * Import.Resurrect.captureLimit :=
  Import.Resurrect.captureBytes_bounded contents

theorem captureBytes_bounded_rejects_unbounded :
    ¬∀ (contents : String),
        ((fun (_ : String) => List.replicate (2 * Import.Resurrect.captureLimit + 1) (0 : UInt8))
              contents).length ≤
          2 * Import.Resurrect.captureLimit := by
  intro h
  exact absurd (h "") (by simp)

theorem ending_clean (after : UInt32 → Nat → List Nat → List Nat) (ends : Os.Signal.Ends after)
    (alive : List Nat) :
    (Session.ending.head?.map (·.1)) = some 1 ∧
      Session.ending.foldl (fun still (signal : UInt32 × Nat) => after signal.1 signal.2 still)
          alive =
        [] := by
  rw [Session.ending_eq]
  exact ⟨rfl, ends.2 1000 _ (Nat.le_refl _)⟩

theorem ending_clean_rejects_hangup :
    ¬∀ (after : UInt32 → Nat → List Nat → List Nat),
        Os.Signal.Ends after →
          ∀ (alive : List Nat),
            (([(1, 1000)] : List (UInt32 × Nat)).head?.map (·.1)) = some 1 ∧
              ([(1, 1000)] : List (UInt32 × Nat)).foldl
                  (fun still (signal : UInt32 × Nat) => after signal.1 signal.2 still) alive =
                [] := by
  intro h
  have ends : Os.Signal.Ends fun sig _ alive => if sig = 9 then [] else alive := by
    refine ⟨fun sig ms alive p hp => ?_, fun ms alive _ => by simp⟩
    by_cases h9 : sig = 9 <;> simp_all
  have survives := (h _ ends [1]).2
  simp at survives

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
  Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)

theorem loadBytes_saveBytes_live_rejects_refusal :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt))) c.vt →
          (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt)) (Checkpoint.saveBytes c) =
            some { c with vt := c.vt.quiesce } := by
  intro h
  cases h ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1)

theorem resume_restores (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt)
    (metaKv : List (String × String)) :
    let saved := Checkpoint.loadBytes (Checkpoint.saveBytes c)
    let booted := State.boot (bootVt (saved.map (·.vt))) ((saved.map (·.labels)).getD []) metaKv
    booted.terminal = c.vt.quiesce ∧ booted.labelList = c.labels.take maxLabels := by
  intro saved booted
  have loaded : saved = some { c with vt := c.vt.quiesce } :=
    Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)
  obtain ⟨_, restored, terminal, -, labels, -⟩ := Session.boot_observed c.vt.quiesce c.labels metaKv
  simp only [booted, loaded, Option.map_some, Option.getD_some, restored]
  exact ⟨terminal, labels⟩

theorem resume_restores_rejects_fresh :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded Checkpoint.loadBytes) c.vt →
          ∀ (metaKv : List (String × String)),
            let saved := Checkpoint.loadBytes (Checkpoint.saveBytes c)
            let booted :=
              State.boot ((fun (_ : Option Vt.Vt) => Vt.Vt.init 1 1) (saved.map (·.vt)))
                ((saved.map (·.labels)).getD []) metaKv
            booted.terminal = c.vt.quiesce ∧ booted.labelList = c.labels.take maxLabels := by
  intro h
  have fresh := (h ⟨Vt.Vt.init 2 1, "", []⟩ (.init 2 1) []).1
  obtain ⟨-, -, terminal, -, -, -⟩ :=
    Session.boot_observed (Vt.Vt.init 1 1)
      (((Checkpoint.loadBytes (Checkpoint.saveBytes ⟨Vt.Vt.init 2 1, "", []⟩)).map (·.labels)).getD
        [])
      []
  rw [terminal] at fresh
  exact absurd (congrArg Vt.Vt.colCount fresh) (by decide +kernel)

theorem loadBytes_resave {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.loadBytes b = some c) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some c := Checkpoint.loadBytes_resave h

theorem loadBytes_resave_rejects_fixed :
    ¬∀ {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt},
        Checkpoint.loadBytes b = some c →
          Checkpoint.loadBytes
              ((fun (_ : Checkpoint.Ckpt Vt.Vt) => Checkpoint.saveBytes ⟨Vt.Vt.init 1 1, "x", []⟩)
                c) =
            some c := by
  intro h
  have empty := loadBytes_saveBytes_live ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1)
  have other := loadBytes_saveBytes_live ⟨Vt.Vt.init 1 1, "x", []⟩ (.init 1 1)
  have same := (h empty).symm.trans other
  exact absurd (congrArg (Option.map Checkpoint.Ckpt.cwd) same) (by decide)

theorem checkpoint_metadata (pane : Import.Resurrect.Pane) (contents : Option String) :
    (Import.Resurrect.checkpoint pane contents).cwd = pane.dir ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.command" =
        some pane.details.command ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.saved-command" =
        some pane.details.savedCommand ∧
      (Import.Resurrect.checkpoint pane contents).labels.lookup "tmux.capture" =
        some (if contents.isSome then "saved" else "none") :=
  Import.Resurrect.checkpoint_metadata pane contents

theorem checkpoint_metadata_rejects_blank :
    ¬∀ (pane : Import.Resurrect.Pane) (contents : Option String),
        ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                  (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                pane contents).cwd =
            pane.dir ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).labels.lookup
              "tmux.command" =
            some pane.details.command ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).labels.lookup
              "tmux.saved-command" =
            some pane.details.savedCommand ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).labels.lookup
              "tmux.capture" =
            some (if contents.isSome then "saved" else "none") := by
  intro h
  exact absurd (h { name := "a", dir := "x", line := 0 } none).1 (by decide)

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

theorem infoText_text (s : State) :
    ∃ cs : List Char,
      Session.infoText s = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Session.infoText_text s
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

theorem infoText_text_rejects_escape :
    ¬∀ (s : State),
        ∃ cs : List Char,
          (fun (_ : State) => ([0x1B] : List UInt8)) s = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\t' ∨
                c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  intro h
  obtain ⟨cs, text, safe⟩ := h (State.boot (Vt.Vt.init 1 1) [] [])
  have escape : (0x1B : UInt8) ∈ cs.flatMap String.utf8EncodeChar := by
    rw [← text]
    exact List.mem_singleton_self _
  obtain ⟨c, member, byte⟩ := List.mem_flatMap.mp escape
  rcases safe c member with tab | newline | ⟨printable, notDel, -⟩
  · subst tab
    revert byte
    decide
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

theorem ticks_settle (s : State) (now t₁ t₂ : Nat)
    (h₁ : (Session.trace Session.step s [.tick now]).1.nextTick = some t₁)
    (h₂ : (Session.trace Session.step s [.tick now, .tick t₁]).1.nextTick = some t₂) :
    (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1.nextTick = none :=
  Session.ticks_settle s now t₁ t₂ h₁ h₂

theorem ticks_settle_rejects_poll :
    ¬∀ (s : State) (now t₁ t₂ : Nat),
        (fun (_ : State) => (some 0 : Option Nat)) (Session.trace Session.step s [.tick now]).1 =
            some t₁ →
          (fun (_ : State) => (some 0 : Option Nat))
              (Session.trace Session.step s [.tick now, .tick t₁]).1 =
            some t₂ →
          (fun (_ : State) => (some 0 : Option Nat))
              (Session.trace Session.step s [.tick now, .tick t₁, .tick t₂]).1 =
            none := by
  intro h
  exact absurd (h (State.boot (Vt.Vt.init 1 1) [] []) 0 0 0 rfl rfl) (by simp)

theorem poll_wakes (returns : Int32 → Option Nat) (sleeps : Os.Poll.Sleeps returns) (now : Nat)
    (deadlines : List Nat) (fit : ∀ d ∈ deadlines, d - now ≤ 2147483647) :
    returns (Session.pollTimeout now deadlines) = deadlines.min?.map (· - now) := by
  rw [Session.pollTimeout_eq]
  cases h : deadlines.min? with
  | none => simpa using sleeps.1
  | some due =>
    have near : due - now ≤ 2147483647 := fit due (List.min?_mem h)
    simp only [Option.map_some, Option.getD_some, Nat.min_eq_left near]
    exact sleeps.2 _ near

theorem poll_wakes_rejects_polling :
    ¬∀ (returns : Int32 → Option Nat),
        Os.Poll.Sleeps returns →
          ∀ (now : Nat) (deadlines : List Nat),
            (∀ d ∈ deadlines, d - now ≤ 2147483647) →
              returns ((fun (_ : Nat) (_ : List Nat) => (100 : Int32)) now deadlines) =
                deadlines.min?.map (· - now) := by
  intro h
  have sleeps :
    Os.Poll.Sleeps fun (t : Int32) => if t.toInt < 0 then none else some t.toNatClampNeg := by
    refine ⟨by decide, fun ms near => ?_⟩
    have small : ms < 2 ^ 31 := by omega
    simp [Int32.toInt_ofNat_of_lt small, Int32.toNatClampNeg_ofNat_of_lt small]
  exact absurd (h _ sleeps 0 [] (by simp)) (by decide)

theorem step_output_audience (s : State) (chunk : List UInt8) :
    ∀ eff ∈ (Session.step s (.ptyOut chunk)).2,
      (∃ bytes, eff = .writePty bytes) ∨
        ∃ c ∈ s.roster,
          c.attached = true ∧
            ∃ payload, eff = .send c.id (.output payload) ∧ payload.length ≤ 65536 :=
  Session.step_ptyOut_audience s chunk

theorem step_output_audience_rejects_stranger :
    ¬∀ (s : State) (chunk : List UInt8),
        ∀
          eff ∈
            ((fun (s : State) (_ : Event) =>
                  (s, ([.send 0 (.output [])] : List (Effect Replay.Plan))))
                s (.ptyOut chunk)).2,
          (∃ bytes, eff = .writePty bytes) ∨
            ∃ c ∈ s.roster,
              c.attached = true ∧
                ∃ payload, eff = .send c.id (.output payload) ∧ payload.length ≤ 65536 := by
  intro h
  have sent := h (State.boot (Vt.Vt.init 1 1) [] []) [] (.send 0 (.output [])) (by simp)
  simp [Session.boot_roster] at sent

theorem start_answer_true (r : Start.Request) (h : Start.Reachable Start.proceeds Start.answer r) :
    (r.answer = some .started → r.runs = true) ∧ (r.answer = some .notStarted → r.runs = false) :=
  Start.answer_true h

theorem start_answer_true_rejects_started :
    ¬∀ (r : Start.Request),
        Start.Reachable Start.proceeds (fun _ _ => Start.Answer.started) r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  intro h
  have taken :=
    Start.Reachable.step (proceeds := Start.proceeds) (answer := fun _ _ => Start.Answer.started)
      .init (.commandTakes {} rfl rfl)
  exact absurd ((h _ taken).1 rfl) (by decide)

theorem start_answer_true_rejects_proceed :
    ¬∀ (r : Start.Request),
        Start.Reachable (fun _ => true) Start.answer r →
          (r.answer = some .started → r.runs = true) ∧
            (r.answer = some .notStarted → r.runs = false) := by
  intro h
  have taken :=
    Start.Reachable.step (proceeds := fun _ => true) (answer := Start.answer) .init
      (.commandTakes {} rfl rfl)
  have ran := Start.Reachable.step taken (.daemonDecides _ rfl rfl true)
  exact absurd ((h _ ran).2 (by simp [Start.answer_command])) (by decide)

theorem classify_iff (o : Status.Obs) (s : Status.Status) : Status.classify o = s ↔ Status.Is s o :=
  Status.classify_iff o s

theorem classify_iff_rejects_idle :
    ¬∀ (o : Status.Obs) (s : Status.Status),
        (fun (_ : Status.Obs) => Status.Status.idle) o = s ↔ Status.Is s o := by
  intro h
  exact absurd ((h { known := false } .unknown).mpr rfl) (by decide)

theorem icon_glyphs :
    Status.icon .working = '⣷' ∧
      Status.icon .wantsYou = '⣿' ∧
      Status.icon .idle = '⣀' ∧
      Status.icon .exitedOk = '✓' ∧
      Status.icon .exitedBad = '!' ∧
      Status.icon .resumable = '~' ∧
      Status.icon .unknown = '?' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem icon_glyphs_rejects_unknown :
    ¬((fun (_ : Status.Status) => '?') .working = '⣷' ∧
        (fun (_ : Status.Status) => '?') .wantsYou = '⣿' ∧
        (fun (_ : Status.Status) => '?') .idle = '⣀' ∧
        (fun (_ : Status.Status) => '?') .exitedOk = '✓' ∧
        (fun (_ : Status.Status) => '?') .exitedBad = '!' ∧
        (fun (_ : Status.Status) => '?') .resumable = '~' ∧
        (fun (_ : Status.Status) => '?') .unknown = '?') := by
  intro h
  exact absurd h.1 (by decide)

theorem summary_exact (statuses : List Status.Status) :
    Status.summary statuses =
      String.intercalate " "
        ((if statuses.count .wantsYou = 0 then []
          else [(toString (statuses.count .wantsYou)).push (Status.icon .wantsYou)]) ++
          (if statuses.count .exitedBad = 0 then []
          else [(toString (statuses.count .exitedBad)).push (Status.icon .exitedBad)]) ++
          (if statuses.count .unknown = 0 then []
          else [(toString (statuses.count .unknown)).push (Status.icon .unknown)])) :=
  Status.summary_exact statuses

theorem summary_exact_rejects_count :
    ¬∀ (statuses : List Status.Status),
        (fun (all : List Status.Status) => toString all.length) statuses =
          String.intercalate " "
            ((if statuses.count .wantsYou = 0 then []
              else [(toString (statuses.count .wantsYou)).push (Status.icon .wantsYou)]) ++
              (if statuses.count .exitedBad = 0 then []
              else [(toString (statuses.count .exitedBad)).push (Status.icon .exitedBad)]) ++
              (if statuses.count .unknown = 0 then []
              else [(toString (statuses.count .unknown)).push (Status.icon .unknown)])) := by
  intro h
  exact absurd (h []) (by simp)

theorem rowStatus_saved (status : Nat) (st : Status.Status) :
    Listing.rowStatus (.ended status) = (if status = 0 then .exitedOk else .exitedBad) ∧
      Listing.rowStatus (.remote false (Status.name st)) =
        if st = .exitedOk ∨ st = .exitedBad then st else .resumable :=
  ⟨Listing.rowStatus_ended status, Listing.rowStatus_remote_saved st⟩

theorem rowStatus_saved_rejects_unknown :
    ¬∀ (status : Nat) (st : Status.Status),
        (fun (_ : Listing.Row) => Status.Status.unknown) (.ended status) =
            (if status = 0 then .exitedOk else .exitedBad) ∧
          (fun (_ : Listing.Row) => Status.Status.unknown) (.remote false (Status.name st)) =
            if st = .exitedOk ∨ st = .exitedBad then st else .resumable := by
  intro h
  exact absurd (h 0 .unknown).1 (by decide)

theorem compose_attention_last (session application summary : String) (capacity : Nat) :
    Title.compose session application summary capacity =
      Title.compose session application ""
          (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
        (if summary.isEmpty then "" else " · " ++ summary) :=
  Title.compose_attention_last session application summary capacity

theorem compose_attention_last_rejects_first :
    ¬∀ (session application summary : String) (capacity : Nat),
        (fun (session application summary : String) (_ : Nat) => summary ++ session ++ application)
            session application summary capacity =
          (fun (session application summary : String) (_ : Nat) =>
                summary ++ session ++ application)
              session application ""
              (capacity - (if summary.isEmpty then "" else " · " ++ summary).length) ++
            (if summary.isEmpty then "" else " · " ++ summary) := by
  intro h
  exact absurd (h "" "" "x" 0) (by decide)

theorem sort_attention_first {α : Type} (status : α → Status.Status) (rows : List α) :
    (View.sort status rows).Perm rows ∧
      ∃ first rest,
        View.sort status rows = first ++ rest ∧
          (∀ x ∈ first, status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
          ∀ x ∈ rest, ¬(status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  obtain ⟨first, rest, split, front, back⟩ := View.sort_attention_first status rows
  exact
    ⟨View.sort_perm status rows, first, rest, split, fun x hx =>
      (View.mem_attention _).mp (front x hx), fun x hx => fun h =>
      back x hx ((View.mem_attention _).mpr h)⟩

theorem sort_attention_first_rejects_arrival :
    ¬∀ {α : Type} (status : α → Status.Status) (rows : List α),
        ((fun (_ : α → Status.Status) (rows : List α) => rows) status rows).Perm rows ∧
          ∃ first rest,
            (fun (_ : α → Status.Status) (rows : List α) => rows) status rows = first ++ rest ∧
              (∀ x ∈ first, status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) ∧
              ∀ x ∈ rest,
                ¬(status x = .wantsYou ∨ status x = .exitedBad ∨ status x = .unknown) := by
  intro h
  obtain ⟨-, first, rest, split, front, back⟩ := h id [Status.Status.idle, .wantsYou]
  match first, split with
  | [], split =>
    have whole : rest = [.idle, .wantsYou] := by simpa using split.symm
    exact back .wantsYou (by simp [whole]) (by simp)
  | a :: _, split =>
    have head : a = .idle := (List.cons.inj split).1.symm
    exact absurd (front a (by simp)) (by simp [head])

theorem groups_exact (keys : List String) :
    ((View.groups keys).map (·.2)).sum = keys.length ∧
      ∀ (k : String) (n : Nat), (k, n) ∈ View.groups keys → n = keys.count k :=
  ⟨View.groups_sum keys, View.groups_count keys⟩

theorem groups_exact_rejects_fixed :
    ¬∀ (keys : List String),
        (((fun (_ : List String) => [("", 1)]) keys).map (·.2)).sum = keys.length ∧
          ∀ (k : String) (n : Nat),
            (k, n) ∈ (fun (_ : List String) => [("", 1)]) keys → n = keys.count k := by
  intro h
  exact absurd (h []).1 (by simp)

theorem hidden_adds_up (targets : List String) :
    (View.hidden targets).2 = [] ∨
      ((View.hidden targets).2.map (·.2)).sum = (View.hidden targets).1 :=
  View.hidden_adds_up targets

theorem hidden_adds_up_rejects_short :
    ¬∀ (targets : List String),
        ((fun (_ : List String) => (1, [("a", 0)])) targets).2 = [] ∨
          (((fun (_ : List String) => (1, [("a", 0)])) targets).2.map (·.2)).sum =
            ((fun (_ : List String) => (1, [("a", 0)])) targets).1 := by
  intro h
  exact absurd (h []) (by simp)

theorem matchCount_push (s typed : Selector.Picker.State) (c : Char)
    (push : typed = { s with query := s.query.push c }) :
    Selector.Picker.matchCount typed ≤ Selector.Picker.matchCount s := by
  rw [push]
  exact Selector.Picker.matchCount_push s c

theorem matchCount_push_rejects_length :
    ¬∀ (s typed : Selector.Picker.State) (c : Char),
        typed = { s with query := s.query.push c } →
          (fun (s : Selector.Picker.State) => s.query.length) typed ≤
            (fun (s : Selector.Picker.State) => s.query.length) s := by
  intro h
  exact absurd (h { candidates := [] } _ 'a' rfl) (by simp)

theorem paste_only_text (state : Selector.Input.State) (byte : UInt8)
    (pasting : state.paste = true) :
    ∀ key ∈ (Selector.Input.feed state byte).2, ∃ c, key = .text c := fun key member =>
  Selector.Input.feed_paste_only_text state byte key pasting member

theorem paste_only_text_rejects_enter :
    ¬∀ (state : Selector.Input.State) (byte : UInt8),
        state.paste = true →
          ∀
            key ∈
              ((fun (state : Selector.Input.State) (_ : UInt8) =>
                    (state, [Selector.Input.Key.enter]))
                  state byte).2,
            ∃ c, key = .text c := by
  intro h
  obtain ⟨c, same⟩ := h { paste := true } 0 rfl .enter (by simp)
  cases same

theorem align_exact (query target : String) :
    ((Selector.Fuzzy.align query target).isSome = true ↔
        (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower)) ∧
      ∀ a,
        Selector.Fuzzy.align query target = some a →
          a.marks.length = target.length ∧
            ((target.toList.zip a.marks).filterMap fun (c, marked) =>
                if marked then some c.toLower else none) =
              query.toList.map Char.toLower :=
  ⟨Selector.Fuzzy.align_isSome_iff_sublist query target, fun a found =>
    ⟨Selector.Fuzzy.align_marks_length query target a found,
      Selector.Fuzzy.align_spells query target a found⟩⟩

theorem align_exact_rejects_none :
    ¬∀ (query target : String),
        (((fun (_ _ : String) => (none : Option Selector.Fuzzy.Alignment)) query target).isSome =
              true ↔
            (query.toList.map Char.toLower).Sublist (target.toList.map Char.toLower)) ∧
          ∀ a,
            (fun (_ _ : String) => (none : Option Selector.Fuzzy.Alignment)) query target = some a →
              a.marks.length = target.length ∧
                ((target.toList.zip a.marks).filterMap fun (c, marked) =>
                    if marked then some c.toLower else none) =
                  query.toList.map Char.toLower := by
  intro h
  exact absurd ((h "" "").1.mpr (by simp)) (by simp)

end Linger
