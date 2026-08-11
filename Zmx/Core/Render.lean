import Zmx.Core.Vt
/-! # Zmx.Core.Render — Vt state → ANSI bytes

Pure functions from a `Vt` snapshot to the byte stream that reproduces
it on a real terminal: `restore` (what a re-attaching client is sent),
`history` (scrollback dump for `lzmx history`), and `previewLines`
(plain rows for the TUI's preview pane).

Everything is `String`-assembled then UTF-8'd once at the end; the
runtime writes the bytes verbatim. No IO, no state.
-/

namespace Zmx.Core.Render

open Zmx.Core.Vt

def esc : String := "\x1b"
def csi : String := "\x1b["

/-- SGR for a pen, from a clean slate (always starts with reset — we
diff by "pen changed at all", not by attribute; simpler and correct). -/
def penSgr (p : Pen) : String :=
  let attr := fun (b : Bool) (code : String) => if b then ";" ++ code else ""
  let color := fun (c : Color) (isFg : Bool) =>
    match c with
    | .default => ""
    | .idx i =>
      let n := i.toNat
      if n < 8 then s!";{(if isFg then 30 else 40) + n}"
      else if n < 16 then s!";{(if isFg then 90 else 100) + n - 8}"
      else s!";{if isFg then 38 else 48};5;{n}"
    | .rgb r g b => s!";{if isFg then 38 else 48};2;{r.toNat};{g.toNat};{b.toNat}"
  csi ++ "0"
    ++ attr p.bold "1" ++ attr p.dim "2" ++ attr p.italic "3"
    ++ attr p.underline "4" ++ attr p.blink "5" ++ attr p.reverse "7"
    ++ attr p.strike "9"
    ++ color p.fg true ++ color p.bg false
    ++ "m"

def cellText (c : Cell) : String :=
  c.base.toString ++ String.ofList c.marks

/-- One row as SGR-colored text. Skips width-0 continuation cells (the
wide char to their left already covers them). -/
def rowAnsi (row : Row) (startPen : Pen) : String × Pen :=
  row.foldl
    (fun (acc : String × Pen) c =>
      if c.width == 0 then acc
      else
        let (s, pen) := acc
        let s := if c.pen == pen then s ++ cellText c
                 else s ++ penSgr c.pen ++ cellText c
        (s, c.pen))
    ("", startPen)

/-- Paint a full grid: home, then each row; CR+LF between rows (safe
under any terminal state since we repaint everything). -/
def gridAnsi (grid : Array Row) : String :=
  let (body, _) := grid.foldl
    (fun (acc : String × Pen) row =>
      let (s, pen) := acc
      let (line, pen') := rowAnsi row pen
      (s ++ line ++ "\r\n", pen'))
    ("", ({} : Pen))
  -- drop the trailing \r\n so the last row doesn't scroll
  csi ++ "H" ++ (body.dropEnd 2 |>.toString)

/-- Mode replay: what a fresh terminal must be told so the application
keeps working after reattach. -/
def modesAnsi (v : Vt) : String :=
  let set := fun (n : Nat) (on : Bool) =>
    if on then s!"{csi}?{n}h" else s!"{csi}?{n}l"
  (if v.modes.wrap then "" else set 7 false)
    ++ (if v.modes.appCursor then set 1 true else "")
    ++ (if v.modes.appKeypad then esc ++ "=" else "")
    ++ (if v.modes.cursorVisible then "" else set 25 false)
    ++ (if v.modes.bracketedPaste then set 2004 true else "")
    ++ (if v.modes.mouse != 0 then set v.modes.mouse true else "")
    ++ (if v.modes.mouseSgr then set 1006 true else "")
    ++ (if v.modes.focusEvents then set 1004 true else "")

/-- Everything a re-attaching client's terminal needs: reset, repaint
(both screens if in alt), scroll region, cursor, pen, modes, title. -/
def restore (v : Vt) : ByteArray :=
  let paintCurrent := gridAnsi v.grid
  let screens :=
    match v.altGrid with
    | none => paintCurrent
    | some (mainGrid, _, _) =>
      -- paint main, switch to alt, paint alt: a later 1049l then shows
      -- the right main screen underneath
      gridAnsi mainGrid ++ csi ++ "?1049h" ++ paintCurrent
  let region :=
    if v.top == 0 && v.bot == v.rows - 1 then ""
    else s!"{csi}{v.top + 1};{v.bot + 1}r"
  let cursor := s!"{csi}{v.cursor.y + 1};{v.cursor.x + 1}H"
  let title := if v.title.isEmpty then "" else s!"{esc}]2;{v.title}\x07"
  String.toUTF8 <|
    csi ++ "0m" ++ csi ++ "2J"          -- clean slate
    ++ screens
    ++ region
    ++ title
    ++ modesAnsi v
    ++ penSgr v.pen
    ++ cursor

/-- Row as plain text (no SGR), trailing blanks trimmed. -/
def rowText (row : Row) : String :=
  let s := row.foldl
    (fun (acc : String) c => if c.width == 0 then acc else acc ++ cellText c) ""
  (s.dropEndWhile (· == ' ')).toString

/-- Scrollback + screen as text, oldest first; for `lzmx history`. -/
def history (v : Vt) (withAnsi : Bool) : ByteArray :=
  let rows := v.sb.toList ++ v.grid.toList
  if withAnsi then
    let (body, _) := rows.foldl
      (fun (acc : String × Pen) row =>
        let (s, pen) := acc
        let (line, pen') := rowAnsi row pen
        (((s ++ line).dropEndWhile (· == ' ')).toString ++ "\n", pen'))
      ("", ({} : Pen))
    String.toUTF8 body
  else
    String.toUTF8 <| String.intercalate "\n" (rows.map rowText) ++ "\n"

/-- Last `n` non-empty-suffix rows as plain text, for the TUI preview. -/
def previewLines (v : Vt) (n : Nat) : List String :=
  let all := (v.sb.toList ++ v.grid.toList).map rowText
  let trimmed := (all.reverse.dropWhile (·.isEmpty)).reverse
  trimmed.drop (trimmed.length - n)

end Zmx.Core.Render
