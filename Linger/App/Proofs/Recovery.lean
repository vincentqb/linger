module

import all Linger.App.CoreCode.Recovery
import all Linger.Session.Proofs.Record

/-! # What a command does with a saved session

No checkpoint starts a new session when the command may start one, and is no session otherwise;
bytes that decode resume the session they saved; and bytes that do not are never taken for no
checkpoint: the command starts nothing and answers `notDone`. -/

namespace Linger.App.Recovery

/-- **A checkpoint that does not decode is not a missing one**: what a command does, from the
bytes at the name's checkpoint path, or `none` for no file. -/
theorem recovery_exact (create : Bool) (file : Option ByteArray) :
    decide create file =
      (file.map fun bytes =>
            ((Linger.Session.Checkpoint.loadBytes bytes).map Recovery.resume).getD
              (.refuse .notDone)).getD
        (if create then .fresh else .refuse .notFound) := by
  cases file <;> rfl

/-- **A result is shown once, then discarded**: an attach to a saved session whose end record says
its program ended this way, typist or watcher alike, shows its last screen, tells how the program
ended and discards it. -/
theorem visit_ended (readOnly : Bool) (o : Linger.Session.Outcome) :
    visit readOnly (some (Linger.Session.Record.encode (.ended o))) =
      [.show, .tell o, .discard] := by
  simp [visit, Linger.Session.Record.decode_encode]

/-- **Any other saved session is resumed, or viewed**: one a signal to its daemon saved, or one
whose daemon ended without saying how its program ended. -/
theorem visit_saved (readOnly : Bool) (n : UInt8) :
    visit readOnly (some (Linger.Session.Record.encode (.saved n))) =
      if readOnly then [.show] else [.resume] := by
  simp [visit, Linger.Session.Record.decode_encode]

/-- …and so is one whose record its daemon left while the program still ran. -/
theorem visit_running (readOnly : Bool) (seen : Option Linger.Session.Seen) :
    visit readOnly (some (Linger.Session.Record.encode (.running seen))) =
      if readOnly then [.show] else [.resume] := by
  simp [visit, Linger.Session.Record.decode_encode]

/-- …and one with no end record. -/
theorem visit_none (readOnly : Bool) : visit readOnly none = if readOnly then [.show] else [.resume] :=
  rfl

end Linger.App.Recovery
