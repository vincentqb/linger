import Zmx.Core.Vt
/-! # Zmx.Core.Render — Vt state → ANSI bytes

Pure functions from a `Vt` snapshot to the byte stream that reproduces
it on a real terminal: `restore` (what a re-attaching client is sent)
and `history` (scrollback dump for `linger history`).

**Bytes, not Strings** (§Replay, specs/bigger-theorems.md). This module
used to assemble `String`s and UTF-8 them at the end, which made the
output unprovable: a `String` literal does not reduce in the kernel, so
no theorem could see that `csi` is `[0x1B, 0x5B]` (`decide` gets stuck
on `"\x1b[".toUTF8`). Everything here now builds `List UInt8` through
named stages — `digits`, `utf8`, `csiNum`, `penSgr`, `rowAnsi` — each of
which the §Replay ladder in `Theorems/Render.lean` can state a lemma
about. Only `rowText` (plain text for `history`) still produces a
`String`, because there its output *is* text.

Emitted characters pass `safeChar`: a C0/DEL codepoint is replaced by
U+FFFD. That makes the emitter's output provably free of control bytes
for ANY `Vt` — no invariant hypothesis needed — and it is genuinely
defensive, since a control byte written into a repaint (or into an OSC
title payload) would be re-parsed as a command and desync the replay.
-/

namespace Zmx.Core.Render

open Zmx.Core.Vt

abbrev Bytes := List UInt8

/-! ## Byte primitives -/

def escB : Bytes := [0x1B]
def csiB : Bytes := [0x1B, 0x5B]

/-- Decimal, most significant digit first (`0` → `"0"`). Our own, so
the ladder can prove every emitted digit is in `0x30…0x39`. -/
def digits (n : Nat) : Bytes :=
  if n < 10 then [UInt8.ofNat (0x30 + n)]
  else digits (n / 10) ++ [UInt8.ofNat (0x30 + n % 10)]
termination_by n
decreasing_by omega

/-- A codepoint safe to emit inside a repaint or an OSC payload: never a
C0 control or DEL (which the parser would execute rather than print).
Cells can legitimately hold such a codepoint — an overlong UTF-8
sequence decodes to one — so the guard is on the emit side, where it
needs no hypothesis about the state. -/
def safeChar (c : Char) : Char :=
  if c.toNat < 0x20 || c.toNat == 0x7F then '\uFFFD' else c

/-- UTF-8 encode one codepoint. Ours rather than `String.toUTF8` so the
bytes are visible to the kernel and to proofs. The `min` is a local
clamp for provability (the AGENTS.md idiom): it is the identity on every
`Char` — scalar values are ≤ 0x10FFFF — and it makes each emitted byte's
range an arithmetic fact rather than a `Char.valid` derivation. -/
def utf8 (c : Char) : Bytes :=
  let n := min c.toNat 0x10FFFF
  if n < 0x80 then [UInt8.ofNat n]
  else if n < 0x800 then
    [UInt8.ofNat (0xC0 + n / 64), UInt8.ofNat (0x80 + n % 64)]
  else if n < 0x10000 then
    [UInt8.ofNat (0xE0 + n / 4096), UInt8.ofNat (0x80 + n / 64 % 64),
     UInt8.ofNat (0x80 + n % 64)]
  else
    [UInt8.ofNat (0xF0 + n / 262144), UInt8.ofNat (0x80 + n / 4096 % 64),
     UInt8.ofNat (0x80 + n / 64 % 64), UInt8.ofNat (0x80 + n % 64)]

/-- Encode a char list, control codepoints neutralized. -/
def utf8s (cs : List Char) : Bytes := cs.flatMap (fun c => utf8 (safeChar c))

/-- `CSI <n> <final>`. -/
def csiNum (n : Nat) (final : UInt8) : Bytes := csiB ++ digits n ++ [final]

/-- `CSI <a> ; <b> <final>`. -/
def csiNum2 (a b : Nat) (final : UInt8) : Bytes :=
  csiB ++ digits a ++ [0x3B] ++ digits b ++ [final]

/-- `CSI ? <n> <final>` (private mode set/reset). -/
def csiPriv (n : Nat) (final : UInt8) : Bytes :=
  csiB ++ [0x3F] ++ digits n ++ [final]

/-! ## Pen -/

/-- SGR for a pen, from a clean slate (always starts with reset — we
diff by "pen changed at all", not by attribute; simpler and correct). -/
def penSgr (p : Pen) : Bytes :=
  let attr := fun (b : Bool) (code : Nat) => if b then 0x3B :: digits code else ([] : Bytes)
  let color := fun (c : Color) (isFg : Bool) =>
    match c with
    | .default => ([] : Bytes)
    | .idx i =>
      let n := i.toNat
      if n < 8 then 0x3B :: digits ((if isFg then 30 else 40) + n)
      else if n < 16 then 0x3B :: digits ((if isFg then 90 else 100) + n - 8)
      else 0x3B :: digits (if isFg then 38 else 48)
             ++ 0x3B :: digits 5 ++ 0x3B :: digits n
    | .rgb r g b =>
      0x3B :: digits (if isFg then 38 else 48) ++ 0x3B :: digits 2
        ++ 0x3B :: digits r.toNat ++ 0x3B :: digits g.toNat ++ 0x3B :: digits b.toNat
  csiB ++ digits 0
    ++ attr p.bold 1 ++ attr p.dim 2 ++ attr p.italic 3
    ++ attr p.underline 4 ++ attr p.blink 5 ++ attr p.reverse 7
    ++ attr p.strike 9
    ++ color p.fg true ++ color p.bg false
    ++ [0x6D]

/-! ## Grid -/

def cellText (c : Cell) : Bytes := utf8 (safeChar c.base) ++ utf8s c.marks

/-- One row as SGR-colored bytes. A width-0 cell is the shadow of the
wide char to its left: its base is not re-emitted, but combining marks
parked on it are (a mark typed after a wide char lands on the shadow
cell, and on replay re-attaches there — dropping them would lose the
mark; §Replay fix 1). -/
def rowAnsi (row : Row) (startPen : Pen) : Bytes × Pen :=
  row.foldl
    (fun (acc : Bytes × Pen) c =>
      if c.width == 0 then (acc.1 ++ utf8s c.marks, acc.2)
      else
        let (s, pen) := acc
        let s := if c.pen == pen then s ++ cellText c
                 else s ++ penSgr c.pen ++ cellText c
        (s, c.pen))
    ([], startPen)

/-- Join painted rows with CR+LF, no trailing separator (a trailing
CRLF on the last row would scroll the screen). -/
def joinCRLF : List Bytes → Bytes
  | [] => []
  | [b] => b
  | b :: bs => b ++ [0x0D, 0x0A] ++ joinCRLF bs

/-- Paint a full grid: home, then each row. Safe under any terminal
state since we repaint everything. -/
def gridAnsi (grid : Array Row) : Bytes :=
  let (rows, _) := grid.foldl
    (fun (acc : List Bytes × Pen) row =>
      let (line, pen') := rowAnsi row acc.2
      (acc.1 ++ [line], pen'))
    (([], ({} : Pen)))
  csiB ++ [0x48] ++ joinCRLF rows

/-! ## Modes -/

/-- Mode replay: what a fresh terminal must be told so the application
keeps working after reattach. DECOM and IRM are included (§Replay
fix 4): origin mode changes how the final cursor address must be
computed, and insert mode would corrupt the *next* app output if lost.
Emitted after the repaint (insert mode during the repaint would shift
cells) and before the final cursor (setting DECOM homes the cursor). -/
def modesAnsi (v : Vt) : Bytes :=
  let set := fun (n : Nat) (on : Bool) => csiPriv n (if on then 0x68 else 0x6C)
  (if v.modes.wrap then [] else set 7 false)
    ++ (if v.modes.appCursor then set 1 true else [])
    ++ (if v.modes.appKeypad then escB ++ [0x3D] else [])
    ++ (if v.modes.cursorVisible then [] else set 25 false)
    ++ (if v.modes.bracketedPaste then set 2004 true else [])
    ++ (if v.modes.mouse != 0 then set v.modes.mouse true else [])
    ++ (if v.modes.mouseSgr then set 1006 true else [])
    ++ (if v.modes.focusEvents then set 1004 true else [])
    ++ (if v.modes.origin then set 6 true else [])
    ++ (if v.modes.insert then csiNum 4 0x68 else [])

/-! ## Restore -/

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
def restore (v : Vt) : Bytes :=
  let paintCurrent := gridAnsi v.grid
  let screens :=
    match v.altGrid with
    | none => paintCurrent
    | some (mainGrid, mcur, mpen) =>
      gridAnsi mainGrid
        ++ penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48
        ++ csiPriv 1049 0x68 ++ paintCurrent
  let region :=
    if v.top == 0 && v.bot == v.rows - 1 then []
    else csiNum2 (v.top + 1) (v.bot + 1) 0x72
  -- custom tab ruler only (the default is what a reset terminal has)
  let tabs :=
    if v.tabs == defaultTabs v.cols then []
    else csiNum 3 0x67 ++ (((List.range v.cols).filter (fun i => v.tabs.getD i false)).flatMap
      (fun i => csiNum (i + 1) 0x47 ++ escB ++ [0x48]))
  let saved := penSgr v.saved.pen
    ++ csiNum2 (v.saved.cur.y + 1) (v.saved.cur.x + 1) 0x48 ++ escB ++ [0x37]
  let charset :=
    (if v.g0Line then escB ++ [0x28, 0x30] else escB ++ [0x28, 0x42])
    ++ (if v.g1Line then escB ++ [0x29, 0x30] else escB ++ [0x29, 0x42])
    ++ (if v.shiftOut then [0x0E] else [])
  let cursor :=
    if v.modes.origin then csiNum2 (v.cursor.y - v.top + 1) (v.cursor.x + 1) 0x48
    else csiNum2 (v.cursor.y + 1) (v.cursor.x + 1) 0x48
  let title :=
    if v.title.isEmpty then []
    else escB ++ [0x5D, 0x32, 0x3B] ++ utf8s v.title.toList ++ [0x07]
  csiNum 0 0x6D ++ csiNum 2 0x4A          -- clean slate
    ++ screens
    ++ region
    ++ tabs
    ++ saved
    ++ title
    ++ modesAnsi v
    ++ charset
    ++ penSgr v.pen
    ++ cursor

/-! ## History (text) -/

/-- Row as plain text (no SGR), trailing blanks trimmed. -/
def rowText (row : Row) : String :=
  let s := row.foldl
    (fun (acc : String) c =>
      if c.width == 0 then acc
      else acc ++ (safeChar c.base).toString ++ String.ofList (c.marks.map safeChar)) ""
  (s.dropEndWhile (· == ' ')).toString

/-- Scrollback + screen, oldest first; for `linger history`. -/
def history (v : Vt) (withAnsi : Bool) : Bytes :=
  let rows := v.sb.toList ++ v.grid.toList
  if withAnsi then
    let (body, _) := rows.foldl
      (fun (acc : Bytes × Pen) row =>
        let (line, pen') := rowAnsi row acc.2
        (acc.1 ++ line ++ [0x0A], pen'))
      ([], ({} : Pen))
    body
  else
    (String.intercalate "\n" (rows.map rowText) ++ "\n").toUTF8.toList

end Zmx.Core.Render
