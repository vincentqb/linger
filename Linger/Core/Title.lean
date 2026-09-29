module

public import Linger.Core.Name
public import Linger.Core.Render

public section

/-! Attached window titles use the terminal's OSC 2 interface. Composition is
independent of sampling, and emission is permitted only at a complete parser
boundary. No terminal query or title stack is needed. -/

namespace Linger.Core.Title

open Linger.Core.Vt (Vt)
open Linger.Core.Render (Bytes utf8s)

/-- Session identity first, then attention and application title when present. -/
def compose (session summary application : String) : String :=
  String.intercalate " · " (Name.sanitize session :: [summary, application].filter (!·.isEmpty))

/-- Bound an OSC payload without splitting a Unicode scalar. Five hundred
characters occupy at most 2000 UTF-8 bytes, below the parser's OSC limit even
with its `2;` prefix. C1 controls are replaced as well as C0 and DEL. -/
def payload (title : String) : List Char :=
  title.toList.take 500 |>.map fun c =>
    if 0x80 ≤ c.toNat && c.toNat < 0xA0 then '\uFFFD' else Render.safeChar c

/-- Set the title, with all externally supplied content confined to the payload. -/
def ansi (title : String) : Bytes := [0x1B, 0x5D, 0x32, 0x3B] ++ utf8s (payload title) ++ [0x07]

/-- A refresh must not interrupt an application's OSC, DCS or UTF-8 character. -/
def update (observer : Vt) (title : String) : Bytes :=
  if observer.atBoundary then ansi title else []

end Linger.Core.Title
