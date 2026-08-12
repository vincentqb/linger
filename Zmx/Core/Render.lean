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

/-- A two-byte `ESC <final>` sequence (DECSC, HTS, app-keypad…). Named so
its bytes stay one syntactic unit: `a ++ escB ++ [b]` would associate as
`(a ++ escB) ++ [b]` and split the sequence in two. -/
def escSeq (final : UInt8) : Bytes := escB ++ [final]

/-- A charset designation, `ESC ( x` / `ESC ) x`. -/
def escCharset (i x : UInt8) : Bytes := escB ++ [i, x]

/-! ## Pen -/

/-- One SGR attribute, as a sub-parameter. -/
def sgrAttr (on : Bool) (code : Nat) : Bytes :=
  if on then 0x3B :: digits code else []

/-- One colour, as sub-parameters (16-colour, 256-colour and truecolour
forms). -/
def sgrColor (c : Color) (isFg : Bool) : Bytes :=
  match c with
  | .default => []
  | .idx i =>
    let n := i.toNat
    if n < 8 then 0x3B :: digits ((if isFg then 30 else 40) + n)
    else if n < 16 then 0x3B :: digits ((if isFg then 90 else 100) + n - 8)
    else 0x3B :: digits (if isFg then 38 else 48)
           ++ 0x3B :: digits 5 ++ 0x3B :: digits n
  | .rgb r g b =>
    0x3B :: digits (if isFg then 38 else 48) ++ 0x3B :: digits 2
      ++ 0x3B :: digits r.toNat ++ 0x3B :: digits g.toNat ++ 0x3B :: digits b.toNat

/-- The parameter string of a pen's SGR. A named stage so §Replay can
say "this chunk is all parameter bytes" once (`Theorems/Render.lean`). -/
def penSgrBody (p : Pen) : Bytes :=
  digits 0
    ++ sgrAttr p.bold 1 ++ sgrAttr p.dim 2 ++ sgrAttr p.italic 3
    ++ sgrAttr p.underline 4 ++ sgrAttr p.blink 5 ++ sgrAttr p.reverse 7
    ++ sgrAttr p.strike 9
    ++ sgrColor p.fg true ++ sgrColor p.bg false

/-- SGR for a pen, from a clean slate (always starts with reset — we
diff by "pen changed at all", not by attribute; simpler and correct). -/
def penSgr (p : Pen) : Bytes := csiB ++ penSgrBody p ++ [0x6D]

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
cells) and before the final cursor (setting DECOM homes the cursor).

The `mouse != 6` guard looks redundant — `setMode` only ever stores
1000/1002/1003 in that field — but it is what makes §Replay's DECOM claim
(`quiet_modesAnsi`) provable *from the emitter alone*: private mode 6 is
DECOM, so replaying a `mouse` of 6 would silently turn origin mode on.
The alternative was a reachability invariant on `Vt`; one guarded emit is
cheaper than a field every constructor must maintain. -/
def modesAnsi (v : Vt) : Bytes :=
  let set := fun (n : Nat) (on : Bool) => csiPriv n (if on then 0x68 else 0x6C)
  (if v.modes.wrap then [] else set 7 false)
    ++ (if v.modes.appCursor then set 1 true else [])
    ++ (if v.modes.appKeypad then escSeq 0x3D else [])
    ++ (if v.modes.cursorVisible then [] else set 25 false)
    ++ (if v.modes.bracketedPaste then set 2004 true else [])
    ++ (if v.modes.mouse != 0 && v.modes.mouse != 6 then set v.modes.mouse true else [])
    ++ (if v.modes.mouseSgr then set 1006 true else [])
    ++ (if v.modes.focusEvents then set 1004 true else [])
    ++ (if v.modes.origin then set 6 true else [])
    ++ (if v.modes.insert then csiNum 4 0x68 else [])

/-! ## Restore

Named stages throughout, so §Replay can discharge one at a time and the
top theorem is their composition (`Theorems/Render.lean`).
-/

/-- The two screens: in alt, paint main, park the stashed cursor/pen,
switch, then paint alt (§Replay fix 7). -/
def screensAnsi (v : Vt) : Bytes :=
  match v.altGrid with
  | none => gridAnsi v.grid
  | some (mainGrid, mcur, mpen) =>
    gridAnsi mainGrid
      ++ penSgr mpen ++ csiNum2 (mcur.y + 1) (mcur.x + 1) 0x48
      ++ csiPriv 1049 0x68 ++ gridAnsi v.grid

/-- Scroll region, when it is not the whole screen. -/
def regionAnsi (v : Vt) : Bytes :=
  if v.top == 0 && v.bot == v.rows - 1 then []
  else csiNum2 (v.top + 1) (v.bot + 1) 0x72

/-- Custom tab ruler only (the default is what a reset terminal has). -/
def tabsAnsi (v : Vt) : Bytes :=
  if v.tabs == defaultTabs v.cols then []
  else csiNum 3 0x67 ++ (((List.range v.cols).filter (fun i => v.tabs.getD i false)).flatMap
    (fun i => csiNum (i + 1) 0x47 ++ escSeq 0x48))

/-- Replay the DECSC slot (§Replay fix 3). -/
def savedAnsi (v : Vt) : Bytes :=
  penSgr v.saved.pen
    ++ csiNum2 (v.saved.cur.y + 1) (v.saved.cur.x + 1) 0x48 ++ escSeq 0x37

/-- Charset designations and the shift state (§Replay fix 2). -/
def charsetAnsi (v : Vt) : Bytes :=
  (if v.g0Line then escCharset 0x28 0x30 else escCharset 0x28 0x42)
    ++ (if v.g1Line then escCharset 0x29 0x30 else escCharset 0x29 0x42)
    ++ (if v.shiftOut then [0x0E] else [])

/-- Window title as an OSC 2, BEL-terminated. The payload is scrubbed
(`utf8s`), so it can contain neither ESC nor BEL and cannot terminate or
extend its own sequence. -/
def titleAnsi (v : Vt) : Bytes :=
  if v.title.isEmpty then []
  else escB ++ [0x5D, 0x32, 0x3B] ++ utf8s v.title.toList ++ [0x07]

/-- Final cursor placement — region-relative under DECOM (§Replay fix 5).
`restore` ends with this, which is also what makes the parser provably
quiesced: it is ESC-initiated, and ESC clears any pending UTF-8. -/
def cursorAnsi (v : Vt) : Bytes :=
  if v.modes.origin then csiNum2 (v.cursor.y - v.top + 1) (v.cursor.x + 1) 0x48
  else csiNum2 (v.cursor.y + 1) (v.cursor.x + 1) 0x48

/-- Everything a re-attaching client's terminal needs except the final
cursor placement. Emission order is load-bearing — each comment names
the §Replay constraint (specs/bigger-theorems.md):

1. repaint before modes (IRM would shift cells; charset would
   re-translate ASCII glyphs);
2. in alt, park the stash cursor/pen *before* `?1049h` — the switch is
   what stashes them, so painting first and switching after would stash
   wherever the main repaint happened to end (fix 7);
3. the saved-cursor replay comes *after* the alt switch (which
   clobbers `saved`) and *before* DECOM is set (its address is
   absolute) (fix 3);
4. the final cursor address is region-relative iff DECOM is on (fix 5,
   in `cursorAnsi`). -/
def restoreBody (v : Vt) : Bytes :=
  csiNum 0 0x6D ++ csiNum 2 0x4A          -- clean slate
    ++ screensAnsi v
    ++ regionAnsi v
    ++ tabsAnsi v
    ++ savedAnsi v
    ++ titleAnsi v
    ++ modesAnsi v
    ++ charsetAnsi v
    ++ penSgr v.pen

/-- The reattach byte stream. -/
def restore (v : Vt) : Bytes := restoreBody v ++ cursorAnsi v

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
