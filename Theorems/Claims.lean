module

public import Linger.Session
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

theorem check_no_alias {a b name : String} (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := Name.check_no_alias ha hb

theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := Remote.command_argv verb words

theorem restore_grid_reachable (v w : Vt.Vt) (hv : Vt.LiveReachableVt v) (hw : Vt.LiveReachableVt w)
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

theorem restore_sb_reachable (v w : Vt.Vt) (hv : Vt.LiveReachableVt v) (hw : Vt.LiveReachableVt w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (hne : (Render.sbRows v).isEmpty = false) :
    (w.feed (Render.restore v)).scrollback = (Render.sbRows v).toList :=
  Render.restore_sb_reachable v w hw hv hcols hrows hne

theorem restore_cursor_reachable (v w : Vt.Vt) (hv : Vt.LiveReachableVt v)
    (hw : Vt.LiveReachableVt w) (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (ho : v.getModes.origin = false) : (w.feed (Render.restore v)).cursorPos = v.cursorPos := by
  obtain ⟨x, y⟩ :=
    Render.restore_cursor_any v w (Vt.good_of_liveReachable hv) (Vt.good_of_liveReachable hw) hcols
      hrows ho
  simp only [Vt.cursorPos_eq, x, y]

theorem start_faithful (budget : Nat) (positive : 0 < budget) (v : Vt.Vt) :
    Replay.Emits budget (Replay.start v) (Render.restore v) := by
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

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt) (h : Vt.LiveReachableVt c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
  Checkpoint.loadBytes_saveBytes_live c h

theorem liveReachableVt_resumeVt (b : ByteArray) :
    Vt.LiveReachableVt (bootVt ((Checkpoint.loadBytes b).map (·.vt))) :=
  Session.liveReachableVt_resumeVt b

theorem run_total_safe {World ε : Type}
    (execute : State → World → (eff : Effect) → Except ε (World × Driver.Reply eff))
    (hw : Driver.Responds execute) (r : Driver.Result World) (events : List Event)
    (hb : Bounded r.st) (hlive : LiveVt r.st) :
    ∃ out, Driver.run execute r events = .ok out ∧ Bounded out.st ∧ LiveVt out.st := by
  obtain ⟨out, ok, ⟨bounded, _⟩, live⟩ :=
    Driver.run_total_safe execute hw r events ⟨hb, Vt.good_of_liveReachable hlive⟩ hlive
  exact ⟨out, ok, bounded, live⟩

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other :=
  Session.run_bytes_isolates s id chunks h

theorem reachableIn_bound {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableIn cap b) :
    Buf.owedLen b ≤ cap := Buf.reachableIn_bound h

theorem reachableOut_bound {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableOut cap b) :
    Buf.owedLen b ≤ cap := Buf.reachableOut_bound h

theorem at_most_one_owner {s : Claim.State} (reached : Claim.Reachable s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b :=
  Claim.at_most_one_owner reached ha hb leftUses rightUses

end Linger.Claims
