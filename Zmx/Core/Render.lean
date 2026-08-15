import Zmx.Core.Vt
/-! # Zmx.Core.Render — Vt state → ANSI bytes

Pure functions from a `Vt` snapshot to the byte stream that reproduces
it on a real terminal: `restore` (what a re-attaching client is sent)
and `history` (scrollback dump for `linger history`).

**Bytes, not Strings** (§Replay, specs/archive/bigger-theorems.md). This module
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

/-- One colour as SGR parameter *numbers* (16-colour, 256-colour and
truecolour forms). Numbers rather than bytes, so the same list can be
emitted either as its own sequence or joined into a longer one. -/
def colorCodes (c : Color) (isFg : Bool) : List Nat :=
  match c with
  | .default => []
  | .idx i =>
    let n := i.toNat
    if n < 8 then [(if isFg then 30 else 40) + n]
    else if n < 16 then [(if isFg then 90 else 100) + n - 8]
    else [if isFg then 38 else 48, 5, n]
  | .rgb r g b => [if isFg then 38 else 48, 2, r.toNat, g.toNat, b.toNat]

/-- The attribute half of a pen, as parameter numbers. Leads with `0`, so
the sequence starts from a clean slate: we diff by "pen changed at all",
not per attribute. -/
def penAttrCodes (p : Pen) : List Nat :=
  0 :: ((if p.bold then [1] else []) ++ (if p.dim then [2] else [])
    ++ (if p.italic then [3] else []) ++ (if p.underline then [4] else [])
    ++ (if p.blink then [5] else []) ++ (if p.reverse then [7] else [])
    ++ (if p.strike then [9] else []))

/-- `<n1>;<n2>;…` — parameters joined by `;`, with no leading separator (a
leading `;` would mean an empty first parameter, which SGR reads as a
*reset*). -/
def joinSemi : List Nat → Bytes
  | [] => []
  | [n] => digits n
  | n :: ns => digits n ++ [0x3B] ++ joinSemi ns

/-- `CSI <codes> m`. -/
def sgrOf (codes : List Nat) : Bytes := csiB ++ joinSemi codes ++ [0x6D]

/-- A colour as its own SGR, or nothing when the colour is the default —
`CSI m` with no parameters is a *reset*, which would wipe the attributes
the previous sequence just set. -/
def sgrColorSeq (c : Color) (isFg : Bool) : Bytes :=
  match colorCodes c isFg with
  | [] => []
  | codes => sgrOf codes

/-- SGR for a pen, as up to three sequences: attributes, then foreground,
then background.

**Why three and not one.** The parser honours at most 16 parameters and
sets `ignore` on the 17th, dropping the whole sequence. A single combined
SGR for a pen with all seven attributes and truecolour foreground *and*
background carries 18 (`0` + 7 + 5 + 5), so such a pen replayed as one
sequence comes back **entirely default** — every attribute and both
colours lost. That pen is reachable: an application sets attributes and
colours in separate SGRs, and nothing merges them.

Split this way each sequence carries at most 8, and no colour triplet can
straddle a boundary. Found by proving §Replay, not by testing (the
`heavyPen` fixture in `Tests/Render.lean` now pins it). -/
def penSgr (p : Pen) : Bytes :=
  sgrOf (penAttrCodes p) ++ sgrColorSeq p.fg true ++ sgrColorSeq p.bg false

/-! ## Grid -/

def cellText (c : Cell) : Bytes := utf8 (safeChar c.base) ++ utf8s c.marks

/-- One row as SGR-colored bytes. A width-0 cell is the shadow of the wide char
to its left: for a grid the emulator produced it paints nothing, because
`Vt.printMark` keeps marks off shadows and `Row.mend` canonicalizes them, so a
repaint of the base re-creates it (`Vt.Cell.shadow`). The branch still emits any
marks it finds there, which is dead code for a live grid and the defensive path
for a decoded checkpoint, whose rows carry no such guarantee.

A wide cell's **own** marks need the cursor parked *between* the glyph and
its shadow, or they attach to the shadow instead: `print` puts a mark at
`cursor.x - 1`, and a 2-column advance leaves the cursor two past the glyph
(§Replay fix 8). `CHA` puts it there by absolute column, which is why the fold
carries the column.

The fold's column is a **cell index**, so every cell advances it by one. A
width-2 base advancing it by two double-counted the pair — its shadow advances
it as well — and the emitted `CHA` for the *second* marked wide glyph in a row
then addressed one column too far right, which drifted the rest of the row and
wrapped its last cell into a spurious line feed that scrolled the whole grid.
Latent until marks were normalized onto the base (`Vt.print`), which is what
made this branch fire for an ordinary `漢` plus a combining mark; the fuzzer
found it in the same pass. -/
def rowAnsi (row : Row) (startPen : Pen) : Bytes × Pen :=
  let (bs, pen, _) := row.foldl
    (fun (acc : Bytes × Pen × Nat) c =>
      let (s, pen, x) := acc
      if c.width == 0 then (s ++ utf8s c.marks, pen, x + 1)
      else
        let s := if c.pen == pen then s else s ++ penSgr c.pen
        let body :=
          if c.width == 2 && !c.marks.isEmpty then
            utf8 (safeChar c.base) ++ csiNum (x + 2) 0x47 ++ utf8s c.marks
              ++ csiNum (x + 3) 0x47
          else cellText c
        (s ++ body, c.pen, x + 1))
    ([], startPen, 0)
  (bs, pen)

/-- Join painted rows with CR+LF, no trailing separator (a trailing
CRLF on the last row would scroll the screen). -/
def joinCRLF : List Bytes → Bytes
  | [] => []
  | [b] => b
  | b :: bs => b ++ [0x0D, 0x0A] ++ joinCRLF bs

/-- Paint a full grid: reset the pen, home, then each row.

The leading `CSI 0 m` is load-bearing, not decoration. The fold below seeds
its "pen already in effect" accumulator with the *default* pen, and
`rowAnsi` emits an `SGR` only when a cell's pen differs from that — so a
leading run of default-pen cells emits no `SGR` at all and inherits whatever
pen the terminal happened to be carrying. `screensAnsi` is exactly such a
caller: it sets the stashed main pen immediately before painting the alt
grid, and without this reset the whole leading run of the alt screen came
back in that pen (§Replay fix 9). Establishing the assumption here rather
than trusting each call site is what makes `gridAnsi` self-contained. -/
def gridAnsi (grid : Array Row) : Bytes :=
  let (rows, _) := grid.foldl
    (fun (acc : List Bytes × Pen) row =>
      let (line, pen') := rowAnsi row acc.2
      (acc.1 ++ [line], pen'))
    (([], ({} : Pen)))
  csiNum 0 0x6D ++ (csiB ++ [0x48] ++ joinCRLF rows)

/-! ## Modes -/

/-- Mode replay: what a fresh terminal must be told so the application
keeps working after reattach. DECOM and IRM are included (§Replay
fix 4): origin mode changes how the final cursor address must be
computed, and insert mode would corrupt the *next* app output if lost.
Emitted after the repaint (insert mode during the repaint would shift
cells) and before the final cursor (setting DECOM homes the cursor).

The mouse guard is an **allowlist**, not a denylist, and that is the whole point.
`setMode` only ever stores 1000/1002/1003 in that field, but a `Vt` does not only
come from `setMode`: `Checkpoint.load` reads `mouse` as an arbitrary `Nat` and is
deliberately total on arbitrary bytes, so a corrupt or foreign checkpoint can put
anything there — and this line replays it verbatim. A denylist got the first case
right and the rest wrong: `!= 6` was there because private mode 6 is DECOM, so
replaying a `mouse` of 6 would silently turn origin mode on (§Replay's
`quiet_modesAnsi`), but 47, 1047 and 1049 **switch screens**, which would corrupt
the very grid the restore is rebuilding. Naming the three modes the emulator can
legitimately hold closes both holes at once and cannot grow a third.

The alternative was a reachability invariant on `Vt`; one guarded emit is still
cheaper than a field every constructor must maintain. -/
def modesAnsi (v : Vt) : Bytes :=
  let set := fun (n : Nat) (on : Bool) => csiPriv n (if on then 0x68 else 0x6C)
  set 7 v.modes.wrap
    ++ (if v.modes.appCursor then set 1 true else [])
    ++ (if v.modes.appKeypad then escSeq 0x3D else [])
    ++ (if v.modes.cursorVisible then [] else set 25 false)
    ++ (if v.modes.bracketedPaste then set 2004 true else [])
    ++ (if v.modes.mouse == 1000 || v.modes.mouse == 1002 || v.modes.mouse == 1003
        then set v.modes.mouse true else [])
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
the §Replay constraint (specs/archive/bigger-theorems.md):

1. repaint before modes (IRM would shift cells; charset would
   re-translate ASCII glyphs);
2. in alt, park the stash cursor/pen *before* `?1049h` — the switch is
   what stashes them, so painting first and switching after would stash
   wherever the main repaint happened to end (fix 7);
3. the saved-cursor replay comes *after* the alt switch (which
   clobbers `saved`) and *before* DECOM is set (its address is
   absolute) (fix 3);
4. the final cursor address is region-relative iff DECOM is on (fix 5,
   in `cursorAnsi`).

Autowrap is deliberately **left on** across the repaint. Turning it off looks
attractive — it would delete the wrap-pending branches from the row-replay
induction — but it is wrong: `Vt.printMark` uses `cursor.pending` to tell
"parked on the margin cell just written" from "positioned before writing it",
and with wrap off both look identical, so a combining mark in the final column
attaches one cell to the left. Two fuzz seeds catch it (see SCRATCHPAD,
2026-08-15). The pending flag is load-bearing, and the replay proof has to
model it rather than legislate it away. -/
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
