module

public import Linger.Terminal.Vt
import Linger.Terminal.Render

public section

/-! # Linger.Terminal.Title — safe title updates

`Title` emits bounded OSC 2 updates at complete parser boundaries. It accepts
arbitrary text; application-specific title composition stays with its caller. -/

namespace Linger.Terminal.Title

open Linger.Terminal.Vt (Vt)
open Linger.Terminal.Render

/-- Unicode scalar budget shared with callers that reserve parts of a title. -/
def maxChars : Nat := 500

/-- Bound an OSC payload without splitting a Unicode scalar. Five hundred
characters occupy at most 2000 UTF-8 bytes, below the parser's OSC limit even
with its `2;` prefix. C1 controls are replaced as well as C0 and DEL. -/
def payload (title : String) : List Char := title.toList.take maxChars |>.map Render.textChar

/-- Set the title, with all externally supplied content confined to the payload. -/
def ansi (title : String) : Bytes := [0x1B, 0x5D, 0x32, 0x3B] ++ utf8s (payload title) ++ [0x07]

/-- A refresh must not interrupt an application's OSC, DCS or UTF-8 character. -/
def update (observer : Vt) (title : String) : Bytes :=
  if observer.atBoundary then ansi title else []

end Linger.Terminal.Title
