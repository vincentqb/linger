module

public import Linger.Core.Name

public section

/-! Session title composition. Sampling belongs to the runtime and safe OSC 2
emission belongs to the VT toolkit's `Terminal.Title`. -/

namespace Linger.Core.Title

/-- Shared display order: session, application title, then attention.
Empty optional parts contribute neither text nor a separator. Clip the
application to the encoder's budget after reserving the session and attention. -/
def compose (session application summary : String) (capacity : Nat) : String :=
  let session := Name.sanitize session
  let suffix := if summary.isEmpty then "" else " · " ++ summary
  let application := (application.take (capacity - session.length - suffix.length - 3)).copy
  session ++ (if application.isEmpty then "" else " · " ++ application) ++ suffix

end Linger.Core.Title
