import Zmx.Core.Vt
/-! # Zmx.Core.Render — Vt state → ANSI bytes

Pure functions from a `Vt` snapshot to the byte stream that reproduces
it on a real terminal: `restore` (what a re-attaching client is sent)
and `history` (scrollback dump for `linger history`).

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

/-- One row as SGR-colored text. A width-0 cell is the shadow of the
wide char to its left: its base is not re-emitted, but combining marks
parked on it are (a mark typed after a wide char lands on the shadow
cell, and on replay re-attaches there — dropping them would lose the
mark; §Replay fix 1). -/
def rowAnsi (row : Row) (startPen : Pen) : String × Pen :=
  row.foldl
    (fun (acc : String × Pen) c =>
      if c.width == 0 then (acc.1 ++ String.ofList c.marks, acc.2)
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
keeps working after reattach. DECOM and IRM are included (§Replay
fixes 4): origin mode changes how the final cursor address must be
computed, and insert mode would corrupt the *next* app output if lost.
Emitted after the repaint (insert mode during the repaint would shift
cells) and before the final cursor (setting DECOM homes the cursor). -/
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
    ++ (if v.modes.origin then set 6 true else "")
    ++ (if v.modes.insert then s!"{csi}4h" else "")

/-- Everything a re-attaching client's terminal needs: reset, repaint
(both screens if in alt), scroll region, tab stops, saved cursor,
title, modes, charset, pen, cursor. Emission order is load-bearing —
each comment names the §Replay constraint (specs/bigger-theorems.md):

1. repaint before modes (IRM would shift cells; charset would
   re-translate ASCII glyphs);
2. in alt, park the stash cursor/pen *before* `?1049h` — the switch is
   what stashes them, so painting first and switching after would stash
   wherever the main repaint happened to end (fix 7);
3. the saved-cursor replay comes *after* the alt switch (which
   clobbers `saved`) and *before* DECOM is set (its address is
   absolute) (fix 3);
4. the final cursor address is region-relative iff DECOM is on
   (fix 5). -/
def restore (v : Vt) : ByteArray :=
  let paintCurrent := gridAnsi v.grid
  let screens :=
    match v.altGrid with
    | none => paintCurrent
    | some (mainGrid, mcur, mpen) =>
      gridAnsi mainGrid
        ++ penSgr mpen ++ s!"{csi}{mcur.y + 1};{mcur.x + 1}H"
        ++ csi ++ "?1049h" ++ paintCurrent
  let region :=
    if v.top == 0 && v.bot == v.rows - 1 then ""
    else s!"{csi}{v.top + 1};{v.bot + 1}r"
  -- custom tab ruler only (the default is what a reset terminal has)
  let tabs :=
    if v.tabs == defaultTabs v.cols then ""
    else csi ++ "3g" ++ String.join
      (((List.range v.cols).filter (fun i => v.tabs.getD i false)).map
        (fun i => s!"{csi}{i + 1}G" ++ esc ++ "H"))
  let saved := penSgr v.saved.pen
    ++ s!"{csi}{v.saved.cur.y + 1};{v.saved.cur.x + 1}H" ++ esc ++ "7"
  let charset :=
    (if v.g0Line then esc ++ "(0" else esc ++ "(B")
    ++ (if v.g1Line then esc ++ ")0" else esc ++ ")B")
    ++ (if v.shiftOut then "\x0e" else "")
  let cursor :=
    if v.modes.origin then s!"{csi}{v.cursor.y - v.top + 1};{v.cursor.x + 1}H"
    else s!"{csi}{v.cursor.y + 1};{v.cursor.x + 1}H"
  let title := if v.title.isEmpty then "" else s!"{esc}]2;{v.title}\x07"
  String.toUTF8 <|
    csi ++ "0m" ++ csi ++ "2J"          -- clean slate
    ++ screens
    ++ region
    ++ tabs
    ++ saved
    ++ title
    ++ modesAnsi v
    ++ charset
    ++ penSgr v.pen
    ++ cursor

/-- Row as plain text (no SGR), trailing blanks trimmed. -/
def rowText (row : Row) : String :=
  let s := row.foldl
    (fun (acc : String) c => if c.width == 0 then acc else acc ++ cellText c) ""
  (s.dropEndWhile (· == ' ')).toString

/-- Scrollback + screen as text, oldest first; for `linger history`. -/
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

end Zmx.Core.Render
