module

public import Linger.Session
public import Linger.Session.Checkpoint
public import Linger.Session.Spec
public import Linger.Target.Name
public import Linger.Target.Remote
public import Linger.Target.Spec
public import Linger.Terminal.Render
public import Linger.Terminal.Replay
public import Linger.Terminal.Spec

/-! # Headline theorems

The guarantees linger must keep, stated over the components' public interfaces and the
definitions in their `Spec` modules. Each proof is `sorry` here: `Theorems/Claims.lean` proves
the same statements, and `./lake comparator` checks that it proves exactly these with no axiom
beyond `propext`, `Quot.sound` and `Classical.choice`. Changing a statement here changes what
linger claims.

Not claimed: anything about the IO executors, the C shim or the operating system, which suites
test instead. -/

public section

namespace Linger.Claims

open Linger.Session Linger.Target Linger.Terminal

/-! ## Session targets -/

/-- Distinct accepted session names cannot alias: validation never maps two different names to
the same one. -/
theorem check_no_alias {a b name : String} (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := by sorry

/-- The command linger runs on a remote host parses, in the literal POSIX shell model, as
exactly `linger`, the verb and every supplied word, with no other shell action. -/
theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := by
  sorry

/-! ## Terminal -/

/-- Repainting a terminal a session can hold into any other such terminal of the same size
reproduces its screen: the receiver ends with the same dimensions and every row. -/
theorem restore_grid_reachable (v w : Vt.Vt) (hv : Vt.LiveReachableVt v) (hw : Vt.LiveReachableVt w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount) :
    (w.feed (Render.restore v)).colCount = v.colCount ∧
      (w.feed (Render.restore v)).rowCount = v.rowCount ∧
      ∀ y < v.rowCount, (w.feed (Render.restore v)).getRow y = v.getRow y := by
  sorry

/-- Streaming a repaint with any positive byte budget per step ends, and its chunks, each within
the budget, concatenate to exactly the complete repaint `Render.restore v`. -/
theorem start_faithful (budget : Nat) (positive : 0 < budget) (v : Vt.Vt) :
    Replay.Emits budget (Replay.start v) (Render.restore v) := by sorry

/-- `linger capture` prints UTF-8 text with no C0 control, DEL or C1 control character other
than its line terminators. -/
theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

/-! ## Sessions -/

/-- Saving a checkpoint of a terminal a session can hold and loading it back returns the same
checkpoint, with the terminal's partial parser state forgotten. -/
theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt) (h : Vt.LiveReachableVt c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } := by sorry

/-- A daemon resumed from any bytes on disk boots a terminal a live session can hold. -/
theorem liveReachableVt_resumeVt (b : ByteArray) :
    Vt.LiveReachableVt (bootVt ((Checkpoint.loadBytes b).map (·.vt))) := by sorry

/-- One client's input bytes, however chunked, leave every other client's record unchanged. -/
theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other := by
  sorry

/-- The pty input queue never owes more than its cap, through any offers and flushes. -/
theorem reachableIn_bound {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableIn cap b) :
    Buf.owedLen b ≤ cap := by sorry

/-- A client output queue the daemon keeps never owes more than its cap, through any appends
and flushes. -/
theorem reachableOut_bound {cap : Nat} {b : Buf.Buf} (h : Buf.ReachableOut cap b) :
    Buf.owedLen b ≤ cap := by sorry

/-- In the lock-protocol model, two daemons or offline readers that share a socket or checkpoint
resource are never active at once, across any interleaving of acquisition, release and reuse. -/
theorem at_most_one_owner {s : Claim.State} (reached : Claim.Reachable s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b := by sorry

end Linger.Claims
