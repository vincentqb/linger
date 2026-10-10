import Linger.Core.Title
import Linger.Core.Terminal

namespace Linger.Core.Title.Tests

open Linger.Core.Terminal.Title (maxChars)

example : compose "work" "" "" maxChars = "work" := by native_decide

example : compose "work" "" "2⣿ 1!" maxChars = "work · 2⣿ 1!" := by native_decide

example : compose "work" "editor" "" maxChars = "work · editor" := by native_decide

example : compose "work" "editor" "2⣿" maxChars = "work · editor · 2⣿" := by native_decide

example : compose "../bad" "" "" maxChars = "_._bad" := by native_decide

example :
    String.ofList
        (Linger.Core.Terminal.Title.payload
          (compose "work" (String.ofList (List.replicate 500 'x')) "1!" maxChars)) =
      "work · " ++ String.ofList (List.replicate 488 'x') ++ " · 1!" := by
  native_decide

example : compose "work" "editor" "1!" 9 = "work · 1!" := by native_decide

end Linger.Core.Title.Tests
