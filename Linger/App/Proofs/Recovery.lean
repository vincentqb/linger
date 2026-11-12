module

import all Linger.App.Recovery

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

end Linger.App.Recovery
