module

public import Linger.Session
public import Linger.Session.Buf
public import Linger.Session.Checkpoint
public import Linger.Session.Driver
public import Linger.Session.Spec
public import Linger.Target.Name
public import Linger.Target.Remote
public import Linger.Target.Spec
public import Linger.Terminal.Render
public import Linger.Terminal.Replay
public import Linger.Terminal.Spec
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Session
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

/-! # Proofs of the headline theorems

`Manifest.lean` states these theorems; each proof here cites the component theorems it
restates. `./lake comparator` checks that the statements match. -/

public section

namespace Linger.Claims

open Linger.Session Linger.Target Linger.Terminal

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

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.client? other =
      s.client? other := by
  rw [Session.trace_step]
  exact Session.run_bytes_isolates s id chunks h

theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∀ bytes, eff ≠ .writePty bytes) ∧ ∀ cols rows, eff ≠ .resizePty cols rows := by
  rw [Session.trace_step]
  exact Session.run_readonly s id chunks hc attached watcher

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := Name.check_eq_some_iff s result

theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := Remote.command_argv verb words

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

theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap :=
  Buf.reachableIn_bound h

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := Buf.reachableOut_bound h

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
  Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)

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

theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Render.screenText_text v
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

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

end Linger.Claims
