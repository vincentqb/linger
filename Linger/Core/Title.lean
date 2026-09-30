module

public import Linger.Core.Name

public section

/-! Session title composition. Sampling belongs to the runtime and safe OSC 2
emission belongs to the VT toolkit's `Terminal.Title`. -/

namespace Linger.Core.Title

/-- Session identity first, then attention and application title when present. -/
def compose (session summary application : String) : String :=
  String.intercalate " · " (Name.sanitize session :: [summary, application].filter (!·.isEmpty))

end Linger.Core.Title
