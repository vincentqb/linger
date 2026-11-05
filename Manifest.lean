module

public import Linger.Session
public import Linger.Session.Checkpoint
public import Linger.Target.Name
public import Linger.Target.Remote
public import Linger.Target.Spec
public import Linger.Terminal.Render
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

end Linger.Claims
