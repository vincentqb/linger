module

public import Linger.Session.CoreSpec
import all Linger.Session.CoreCode

/-! # What `info` reports of the session's present

Once the daemon reads the world (`Event.observed`), `info` reports the terminal's foreground as
the operating system reported it: its words, its process and its directory. -/

namespace Linger.Session

/-- A reading of the world is what `info` then reports of the present, and changes nothing else. -/
theorem step_observed (s : State) (o : Observation) :
    (step s (.observed o)).1 = { s with observed := some o } := rfl

/-- **`info` names the foreground it was told**: its words, its process and its directory. -/
theorem infoFields_foreground (s : State) (o : Observation) {fg : Foreground}
    (h : o.foreground = some fg) :
    ("fg", String.intercalate " " fg.argv) ∈ infoFields (step s (.observed o)).1 ∧
      ("fgpid", toString fg.pid) ∈ infoFields (step s (.observed o)).1 ∧
      ("fgdir", fg.dir) ∈ infoFields (step s (.observed o)).1 := by
  rw [step_observed]
  simp [infoFields, presentFields, h]

end Linger.Session
