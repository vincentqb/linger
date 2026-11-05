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
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Session
import all Linger.Terminal.Vt
import all Linger.Terminal.Proofs.Vt
import all Linger.Terminal.Proofs.Vt.Parser
import all Linger.Terminal.Proofs.Vt.Renderable
import all Linger.Terminal.Proofs.Render.Grid
import all Linger.Terminal.Proofs.Render.History
import all Linger.Terminal.Proofs.Render.Modes
import all Linger.Terminal.Proofs.Render.PendingWrap
import all Linger.Terminal.Proofs.Render.Pen
import all Linger.Terminal.Proofs.Render.Scrollback
import all Linger.Terminal.Proofs.Render.Sticky
import all Linger.Terminal.Proofs.Replay
import all Linger.Terminal.Proofs.Vt.State

/-! # Proofs of the headline theorems

`Manifest.lean` states these theorems; each proof here cites the component theorem it
restates. `./lake comparator` checks that the statements match. -/

public section

namespace Linger.Claims

open Linger.Session Linger.Target Linger.Terminal

theorem check_eq_some_iff (s result : String) :
    Name.check s = some result ↔ result = s ∧ Name.Valid s := Name.check_eq_some_iff s result

theorem check_no_alias {a b name : String} (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := Name.check_no_alias ha hb

theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := Remote.command_argv verb words

theorem restore_grid_reachable (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount) :
    (w.feed (Render.restore v)).colCount = v.colCount ∧
      (w.feed (Render.restore v)).rowCount = v.rowCount ∧
      ∀ y < v.rowCount, (w.feed (Render.restore v)).getRow y = v.getRow y := by
  have dims := Vt.dims_feed (Render.restore v) (Vt.good_of_liveReachable hw)
  simp only [Vt.dims, Prod.mk.injEq] at dims
  have grid := Render.restore_grid_reachable v w hw hv hcols hrows
  have size := (Vt.renderable_of_liveReachable hv).main.1
  refine ⟨dims.1.trans hcols, dims.2.trans hrows, fun y below => ?_⟩
  have inside : y < v.grid.size := size ▸ below
  unfold Vt.Vt.getRow
  rw [grid]
  simp only [Array.getD, inside, dite_true]

theorem restore_sb_reachable (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (hne : (Render.sbRows v).isEmpty = false) :
    (w.feed (Render.restore v)).scrollback = (Render.sbRows v).toList :=
  Render.restore_sb_reachable v w hw hv hcols hrows hne

theorem restore_cursor_reachable (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (ho : v.getModes.origin = false) : (w.feed (Render.restore v)).cursorPos = v.cursorPos := by
  obtain ⟨x, y⟩ :=
    Render.restore_cursor_any v w (Vt.good_of_liveReachable hv) (Vt.good_of_liveReachable hw) hcols
      hrows ho
  simp only [Vt.cursorPos_eq, x, y]

theorem start_faithful (budget : Nat) (positive : 0 < budget) (v : Vt.Vt) :
    Replay.Emits Replay.next budget (Replay.start v) (Render.restore v) := by
  rw [← Replay.start_faithful v]
  exact Replay.emits_remaining budget positive (Replay.start v)

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

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
  Checkpoint.loadBytes_saveBytes_live c h

theorem liveReachableVt_resumeVt (b : ByteArray) :
    Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable
      (bootVt ((Checkpoint.loadBytes b).map (·.vt))) := Session.liveReachableVt_resumeVt b

theorem run_total_safe {World ε : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result State World) (events : List Event)
    (hb : Bounds State.roster State.labelList State.scanner r.st)
    (hlive :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable r.st.terminal) :
    ∃ out,
      Driver.run execute r events = .ok out ∧
        Bounds State.roster State.labelList State.scanner out.st ∧
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable
          out.st.terminal := by
  have live : LiveVt r.st := (Session.liveVt_iff _).mpr hlive
  obtain ⟨out, ok, ⟨bounded, _⟩, kept⟩ :=
    Driver.run_total_safe execute hw r events
      ⟨(Session.bounded_iff_bounds _).mpr hb, Vt.good_of_liveReachable live⟩ live
  exact ⟨out, ok, (Session.bounded_iff_bounds _).mp bounded, (Session.liveVt_iff _).mp kept⟩

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other :=
  Session.run_bytes_isolates s id chunks h

theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.sizer = false) :
    (run s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      ∀ eff ∈ (run s (chunks.map (Event.bytes id))).2,
        (∀ bytes, eff ≠ .writePty bytes) ∧ ∀ cols rows, eff ≠ .resizePty cols rows :=
  Session.run_readonly s id chunks hc attached watcher

theorem reachableIn_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.InputReach Buf.Buf.empty Buf.bufOffer Buf.bufAdvance cap b) : Buf.owedLen b ≤ cap :=
  Buf.reachableIn_bound h

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf}
    (h : Buf.OutputReach Buf.Buf.empty Buf.bufEnqueue Buf.bufAdvance cap b) :
    Buf.owedLen b ≤ cap := Buf.reachableOut_bound h

theorem at_most_one_owner {s : Claim.State} (reached : Claim.Reachable s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b :=
  Claim.at_most_one_owner reached ha hb leftUses rightUses

theorem init_observed (cols rows : Nat) :
    (Vt.Vt.init cols rows).colCount = Vt.clampDim cols ∧
      (Vt.Vt.init cols rows).rowCount = Vt.clampDim rows ∧
      (∀ y < Vt.clampDim rows,
        (Vt.Vt.init cols rows).getRow y = Array.replicate (Vt.clampDim cols) ({} : Vt.Cell)) ∧
      (Vt.Vt.init cols rows).cursorPos = (0, 0) ∧
      (Vt.Vt.init cols rows).getModes = {} ∧
      (Vt.Vt.init cols rows).getPen = {} ∧
      (Vt.Vt.init cols rows).scrollback = [] ∧
      Vt.stick (Vt.Vt.init cols rows) =
        { rows := Vt.clampDim rows, top := 0, bot := Vt.clampDim rows - 1, g0 := false, g1 := false,
          so := false, alt := false } ∧
      (Vt.Vt.init cols rows).windowTitle = "" ∧
      (Vt.Vt.init cols rows).atBoundary = true := Vt.init_observed cols rows

theorem resize_observed (v : Vt.Vt) (cols rows : Nat) :
    (v.resize cols rows).colCount = Vt.clampDim cols ∧
      (v.resize cols rows).rowCount = Vt.clampDim rows ∧
      (v.resize cols rows).cursorPos =
        (min v.cursorPos.1 (Vt.clampDim cols - 1), min v.cursorPos.2 (Vt.clampDim rows - 1)) ∧
      Vt.stick (v.resize cols rows) =
        { Vt.stick v with
          rows := Vt.clampDim rows, top := 0, bot := Vt.clampDim rows - 1 } ∧
      (v.resize cols rows).scrollback = v.scrollback ∧
      (v.resize cols rows).getModes = v.getModes ∧
      (v.resize cols rows).getPen = v.getPen ∧
      (v.resize cols rows).windowTitle = v.windowTitle ∧
      (v.resize cols rows).atBoundary = v.atBoundary := Vt.resize_observed v cols rows

theorem quiesce_observed (v : Vt.Vt) :
    v.quiesce.atBoundary = true ∧
      v.quiesce.colCount = v.colCount ∧
      v.quiesce.rowCount = v.rowCount ∧
      (∀ y, v.quiesce.getRow y = v.getRow y) ∧
      v.quiesce.cursorPos = v.cursorPos ∧
      v.quiesce.getModes = v.getModes ∧
      v.quiesce.getPen = v.getPen ∧
      v.quiesce.scrollback = v.scrollback ∧
      Vt.stick v.quiesce = Vt.stick v ∧
      v.quiesce.windowTitle = v.windowTitle := Vt.quiesce_observed v

theorem quiesce_decodable (v : Vt.Vt)
    (h : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) :
    v.quiesce.Decodable := Vt.quiesce_decodable h

theorem print_observed :
    ((Vt.Vt.init 2 1).feed [0x41]).getRow 0 = #[{ base := 'A' }, {}] ∧
      ((Vt.Vt.init 2 1).feed [0x41]).cursorPos = (1, 0) ∧
      Render.screenText ((Vt.Vt.init 2 1).feed [0x41]) = [0x41, 0x0A] ∧
      ((Vt.Vt.init 2 1).feed [0x41, 0x0A]).scrollback = [#[{ base := 'A' }, {}]] ∧
      Render.sbRows ((Vt.Vt.init 2 1).feed [0x41, 0x0A]) = #[#[{ base := 'A' }, {}]] :=
  ⟨Vt.print_observed.1, Vt.print_observed.2.1, Render.screenText_observed, Vt.print_observed.2.2,
    Render.sbRows_observed⟩

theorem controls_observed :
    ((Vt.Vt.init 2 1).feed [0x1B, 0x5B, 0x31, 0x6D]).getPen = { bold := true } ∧
      ((Vt.Vt.init 2 1).feed [0x1B, 0x5B, 0x3F, 0x36, 0x68]).getModes = { origin := true } ∧
      ((Vt.Vt.init 2 1).feed [0x1B, 0x5D, 0x32, 0x3B, 0x74, 0x07]).windowTitle = "t" ∧
      Vt.stick ((Vt.Vt.init 1 3).feed [0x1B, 0x5B, 0x32, 0x3B, 0x33, 0x72]) =
        { rows := 3, top := 1, bot := 2, g0 := false, g1 := false, so := false, alt := false } ∧
      Vt.stick ((Vt.Vt.init 1 3).feed [0x1B, 0x28, 0x30, 0x1B, 0x29, 0x30, 0x0E]) =
        { rows := 3, top := 0, bot := 2, g0 := true, g1 := true, so := true, alt := false } ∧
      Vt.stick ((Vt.Vt.init 1 3).feed [0x1B, 0x5B, 0x3F, 0x31, 0x30, 0x34, 0x39, 0x68]) =
        { rows := 3, top := 0, bot := 2, g0 := false, g1 := false, so := false, alt := true } ∧
      ((Vt.Vt.init 2 1).feed [0x1B]).atBoundary = false :=
  let ⟨pen, modes, region, charsets, alt, escape⟩ := Vt.controls_observed
  ⟨pen, modes, Render.title_observed, region, charsets, alt, escape⟩

theorem boot_observed (vt : Vt.Vt) (labels metaKv : List (String × String)) :
    bootVt none = Vt.Vt.init 80 24 ∧
      bootVt (some vt) = vt ∧
      (State.boot vt labels metaKv).terminal = vt ∧
      (State.boot vt labels metaKv).roster = [] ∧
      (State.boot vt labels metaKv).labelList = labels.take maxLabels ∧
      (State.boot vt labels metaKv).scanner = .ground := Session.boot_observed vt labels metaKv

theorem run_observed (s : State) (ev : Event) (evs : List Event) (id : Nat) :
    run s [] = (s, []) ∧
      run s (ev :: evs) =
        ((run (run s [ev]).1 evs).1, (run s [ev]).2 ++ (run (run s [ev]).1 evs).2) ∧
      s.client? id = s.roster.find? (·.id == id) := Session.run_observed s ev evs id

theorem events_observed (s : State) (id : Nat) (chunk : List UInt8) :
    (s.roster.length < maxClients → (run s [.connected id]).1.roster = s.roster ++ [{ id }]) ∧
      (maxClients ≤ s.roster.length →
        (run s [.connected id]).1.roster = s.roster ∧ Effect.close id ∈ (run s [.connected id]).2) ∧
      (run s [.closed id]).1.client? id = none ∧
      (run s [.ptyOut chunk]).1.terminal = s.terminal.feed chunk ∧
      (s.scanner = .ground → (run s [.ptyOut [0x1B]]).1.scanner = .esc) :=
  Session.events_observed s id chunk

theorem driver_observed {World : Type}
    (execute : State → World → (eff : Effect Replay.Plan) → Id (World × Driver.Reply eff))
    (succeeds : ∀ st w eff, (execute st w eff).run.2 = Driver.success eff)
    (r : Driver.Result State World) (events : List Event) (active : r.exiting = false)
    (stays : Effect.exit ∉ (run r.st events).2) :
    (Driver.run execute r events).run.st = (run r.st events).1 ∧
      (Driver.run execute r events).run.exiting = false :=
  Driver.run_success execute succeeds r events active stays

theorem buf_observed (cap n : Nat) (b : Buf.Buf) (more : ByteArray) :
    Buf.owedLen Buf.Buf.empty = 0 ∧
      (Buf.bufOffer cap b more).2 = decide (Buf.owedLen b + more.size > cap) ∧
      Buf.owedLen (Buf.bufOffer cap b more).1 =
        (if Buf.owedLen b + more.size > cap then Buf.owedLen b else Buf.owedLen b + more.size) ∧
      (Buf.bufEnqueue cap b more).2 = decide (Buf.owedLen b + more.size > cap) ∧
      Buf.owedLen (Buf.bufEnqueue cap b more).1 = Buf.owedLen b + more.size ∧
      Buf.owedLen (Buf.bufAdvance b n) = Buf.owedLen b - n := Buf.buf_observed cap n b more

end Linger.Claims
