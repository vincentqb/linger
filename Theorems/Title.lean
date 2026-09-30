module

import all Linger.Core.Title

namespace Linger.Core.Title

theorem compose_quiet (session : String) : compose session "" "" = Name.sanitize session := by
  simp [compose]

theorem compose_parts (session summary application : String) :
    compose session summary application =
      String.intercalate " · "
        (Name.sanitize session :: [summary, application].filter (!·.isEmpty)) := rfl

end Linger.Core.Title
