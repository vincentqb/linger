import Linger.Core.Title

namespace Linger.Core.Title.Tests

open Linger.Core.Title

example : compose "work" "" "" = "work" := by native_decide

example : compose "work" "2⣿ 1!" "" = "work · 2⣿ 1!" := by native_decide

example : compose "work" "" "editor" = "work · editor" := by native_decide

example : compose "work" "2⣿" "editor" = "work · 2⣿ · editor" := by native_decide

example : compose "../bad" "" "" = "_._bad" := by native_decide

end Linger.Core.Title.Tests
