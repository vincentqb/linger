import Linger.Core.Title

namespace Linger.Core.Title.Tests

open Linger.Core.Vt (Vt)
open Linger.Core.Title

example : compose "work" "" "" = "work" := by native_decide

example : compose "work" "2⣿ 1!" "" = "work · 2⣿ 1!" := by native_decide

example : compose "work" "" "editor" = "work · editor" := by native_decide

example : compose "work" "2⣿" "editor" = "work · 2⣿ · editor" := by native_decide

example : compose "../bad" "" "" = "_._bad" := by native_decide

example :
    payload "a\x1b]2;forged\x07\u009Cb" =
      ['a', '\uFFFD', ']', '2', ';', 'f', 'o', 'r', 'g', 'e', 'd', '\uFFFD', '\uFFFD', 'b'] := by
  native_decide

example : (payload (String.ofList (List.replicate 700 '😀'))).length = 500 := by native_decide

example : update ((Vt.init 1 1).observe "\x1b]2;half".toUTF8.toList) "linger" = [] := by
  native_decide

example : update ((Vt.init 1 1).observe "\x1bPgraphics".toUTF8.toList) "linger" = [] := by
  native_decide

example : update ((Vt.init 1 1).observe [0xE2, 0x82]) "linger" = [] := by native_decide

example : update ((Vt.init 1 1).observe [0xE2, 0x82, 0xAC]) "linger" = ansi "linger" := by
  native_decide

example :
    (((Vt.init 1 1).observe "\x1b]2;half".toUTF8.toList).observe
          " title\x1b\\".toUTF8.toList).windowTitle =
      "half title" := by
  native_decide

end Linger.Core.Title.Tests
