module

public import Linger.Core.Render
-- Converted from legacy by the `Vt` seal (`specs/archive/vt-toolkit.md` Step 1): these
-- fixtures read the fields they assert about, so they are a friend of the emulator.
import all Linger.Core.Vt
import all Linger.Core.Render
-- `native_decide` compiles its goals, and a module's compiled code only sees
-- meta-imported modules — names alone arrive via the public import above.
public meta import Linger.Core.Vt
public meta import Linger.Core.Render

/-! # Vt behavior tests

The theorems say the emulator cannot crash or grow; these pin what it
actually *does* — golden semantics for the sequences real programs
emit. All `native_decide`: `Vt` ops are data-structure-heavy and the
kernel evaluator would crawl.
-/

namespace Linger.Core.Vt.Tests

open Linger.Core.Vt Linger.Core.Render

def feedStr (v : Vt) (s : String) : Vt := v.feedBytes s.toUTF8

def screen (cols rows : Nat) (s : String) : Vt := feedStr (Vt.init cols rows) s

def plain (row : Row) : String := (String.fromUTF8? ⟨(rowText row).toArray⟩).getD ""

/-- `rowText` builds bytes now (it was the last emitter assembled through `String`,
which is what made `linger history` unprovable — see `Render.history_lines`). The
fixtures still read better against string literals, so the decode lives here in the
harness rather than in the production path. -/
def rowStr (v : Vt) (y : Nat) : String := plain (v.getRow y)

/-- Plain echo with newline: CR+LF discipline. -/
example : (let v := screen 10 3 "hi\r\nyo"
           rowStr v 0 == "hi" && rowStr v 1 == "yo"
             && v.cursor.x == 2 && v.cursor.y == 1) = true := by native_decide

/-- LF alone moves down without resetting the column. -/
example :
          (let v := screen 10 3 "ab\nc"
           rowStr v 0 == "ab" && rowStr v 1 == "  c") =
      true := by
  native_decide

/-- Wrap at the right margin (DECAWM), wrap-pending style: the cursor
holds at the margin until the next glyph. -/
example : (let v := screen 3 2 "abcd"
           rowStr v 0 == "abc" && rowStr v 1 == "d"
             && v.cursor.x == 1 && v.cursor.y == 1) = true := by native_decide

/-- With wrap off, glyphs overwrite the last column. -/
example :
          (let v := screen 3 2 "\x1b[?7labcd"
           rowStr v 0 == "abd" && v.cursor.y == 0) =
      true := by
  native_decide

/-- RM applies both DECCKM and DECAWM, including the visible no-wrap effect. -/
example :
    (let v := screen 3 2 "\x1b[?1h\x1b[?1;7labcd"
     !v.modes.appCursor && !v.modes.wrap && rowStr v 0 == "abd" && v.cursor.y == 0) =
      true := by
  native_decide

/-- SM applies every private mode, even after an unknown or omitted parameter. -/
example :
    (let v := screen 10 6 "\x1b[2;5r\x1b[?7;25l\x1b[?9999;;1;7;25;1004;1006;2004;6h"
     v.modes.appCursor && v.modes.wrap && v.modes.cursorVisible &&
       v.modes.focusEvents && v.modes.mouseSgr && v.modes.bracketedPaste &&
       v.modes.origin && v.cursor.y == 1) = true := by
  native_decide

/-- Standard SM reaches IRM after an unknown parameter; insertion moves cells. -/
example :
    (let v := screen 5 2 "abc\r\x1b[9999;4hX"
     v.modes.insert && rowStr v 0 == "Xabc") =
      true := by
  native_decide

/-- Standard RM reaches IRM too, returning printing to replacement. -/
example :
    (let v := screen 5 2 "abc\r\x1b[4h\x1b[9999;4lX"
     !v.modes.insert && rowStr v 0 == "Xbc") =
      true := by
  native_decide

/-- Mode order is observable: the last requested mouse mode wins, and DECOM
homes the cursor before a following DECSC saves it. -/
example :
    (let v := screen 10 6 "\x1b[2;5r\x1b[4;4H\x1b[?1000;1003;1002;6;1048h"
     v.modes.mouse == 1002 && v.modes.origin &&
       v.cursor.x == 0 && v.cursor.y == 1 &&
       v.saved.cur.x == 0 && v.saved.cur.y == 1) = true := by
  native_decide

/-- A later screen switch takes effect; repeated 1049 still uses the existing
idempotent enter/leave behavior and preserves the original main screen. -/
example :
    (let v := screen 10 3 "main\x1b[?1;1049;1049halt"
     let w := feedStr v "\x1b[?1;1049;1049l"
     v.inAlt && rowStr v 0 == "alt" && !w.inAlt &&
       !w.modes.appCursor && rowStr w 0 == "main" && w.cursor.x == 4) = true := by
  native_decide

/-- CUP is 1-based; ED 2 clears. -/
example : (let v := screen 10 4 "xxxx\x1b[2J\x1b[3;2Hok"
           rowStr v 0 == "" && rowStr v 2 == " ok"
             && v.cursor.y == 2 && v.cursor.x == 3) = true := by native_decide

/-- VPA uses the scroll-region origin just as CUP does. The first row is `top`. -/
example :
    (let v := screen 10 6 "\x1b[2;5r\x1b[?6h\x1b[1d"
     v.modes.origin && v.top == 1 && v.bot == 4 && v.cursor.y == 1) = true := by
  native_decide

/-- VPA preserves the column, clears pending wrap, defaults omitted/zero to row
one, and clamps to the active origin's bottom. Without DECOM it uses the screen. -/
example :
    (let v := screen 10 6 "\x1b[2;5r\x1b[?6h0123456789"
     let omitted := feedStr v "\x1b[d"
      let zero := feedStr v "\x1b[0d"
      let clamped := feedStr v "\x1b[999d"
      let absolute := feedStr v "\x1b[?6l\x1b[4G\x1b[999d"
      v.cursor.pending && omitted.cursor.x == 9 && omitted.cursor.y == 1 &&
        !omitted.cursor.pending &&
        zero.cursor == omitted.cursor &&
        clamped.cursor.x == 9 &&
        clamped.cursor.y == 4 &&
        !clamped.cursor.pending &&
        absolute.cursor.x == 3 &&
        absolute.cursor.y == 5) =
      true := by
  native_decide

/-- SGR survives into cells: fg color + bold recorded, reset clears. -/
example :
          (let v := screen 10 2 "\x1b[1;31mA\x1b[0mB"
           let a := v.getCell 0 0
           let b := v.getCell 1 0
           a.pen.bold && a.pen.fg == .idx 1 && !b.pen.bold && b.pen.fg == .default) =
      true := by
  native_decide

/-- An omitted first CUP parameter keeps its position and uses the row default. -/
example :
    (let v := screen 10 6 "\x1b[;5HX"
     v.cursor.y == 0 && v.cursor.x == 5 && (v.getCell 4 0).base == 'X') = true := by
  native_decide

/-- An empty first SGR parameter resets the pen before the following color. -/
example :
    (let v := screen 10 2 "\x1b[1m\x1b[;31mA"
     let a := v.getCell 0 0
     !a.pen.bold && a.pen.fg == .idx 1) = true := by
  native_decide

/-- A trailing empty SGR parameter resets the pen too. -/
example :
    (let v := screen 10 2 "\x1b[31;mA"
     (v.getCell 0 0).pen == ({} : Pen)) =
      true := by
  native_decide

/-- Empty parameters consume slots too. Overflow ignores the whole SGR sequence;
the next sequence starts with a fresh accumulator. -/
example :
    (let v := screen 10 2 "\x1b[1m\x1b[;;;;;;;;;;;;;;;;mA\x1b[;31mB"
     let a := v.getCell 0 0
      let b := v.getCell 1 0
      a.pen.bold && !b.pen.bold && b.pen.fg == .idx 1) =
      true := by
  native_decide

/-- The sixteenth field still dispatches; only a seventeenth field overflows. -/
example :
    (let v := screen 10 2 "\x1b[1m\x1b[;;;;;;;;;;;;;;;mA"
     (v.getCell 0 0).pen == ({} : Pen)) =
      true := by
  native_decide

/-- Numeric saturation is observable while collecting, before the final-byte
dispatch discards the parser state. A separator clears the accumulated digits. -/
example :
    (let v := screen 10 2 "\x1b[999999999999999999999999"
     let w := feedStr v ";"
      match v.pstate, w.pstate with
      | .csi s, .csi t =>
        s.cur == 65535 && s.haveCur && t.params == #[(65535, false)] && t.cur == 0 && !t.haveCur
      | _, _ => false) =
      true := by
  native_decide

/-- 256-color and truecolor, both syntaxes. -/
example :
          (let v := screen 10 2 "\x1b[38;5;196mX\x1b[48:2::10:20:30mY"
           (v.getCell 0 0).pen.fg == .idx 196 && (v.getCell 1 0).pen.bg == .rgb 10 20 30) =
      true := by
  native_decide

/-- Alt screen: 1049 enter clears, leave restores the main screen. -/
example :
          (let v := screen 10 2 "main\x1b[?1049halt"
           let w := feedStr v "\x1b[?1049l"
           rowStr v 0 == "alt" && v.altGrid.isSome && rowStr w 0 == "main" && w.altGrid.isNone &&
        w.cursor.x == 4) =
      true := by
  native_decide

/-! ### The width tables, behaviourally (pin-the-gaps item 4)

`Theorems/Vt.lean` pins `isWide`/`isZeroWidth` at every clause edge as closed
`decide` propositions. These pin the **composite** — `charWidth`, which is what
the emulator, `CellOk` and the row painter actually call — at the boundaries
where the naive expectation is wrong: at the two places the tables *touch*,
"just outside a wide range" is width 0, not 1, and "just past a zero-width
range" is width 2, not 1. -/

/-- Every clause edge of both width tables, paired with the width `charWidth`
must give it. **One table, two consumers** — the claim below and its non-vacuity
check — so the probe list cannot drift between them, which is how a boundary
suite rots: a codepoint gets corrected in one fixture and not the other.

The entries that matter most are `0xFE2F → 0`, `0xFE30 → 2`, `0xFEFF → 0`,
`0xFF00 → 2`: those are the two places the tables touch, and a fixture assuming
"outside a wide range means width 1" is wrong at every one of them. -/
def widthProbes : List (Nat × Nat) :=
  [(0x10FF, 1), (0x1100, 2), (0x115F, 2), (0x1160, 1), (0x02FF, 1), (0x0300, 0), (0x036F, 0),
    (0x0370, 1), (0xFE2F, 0), (0xFE30, 2), (0xFE4F, 2), (0xFE50, 1), (0xFEFE, 1), (0xFEFF, 0),
    (0xFF00, 2), (0xFF60, 2), (0xFF61, 1), (0x200A, 1), (0x200B, 0), (0x200C, 0), (0x200D, 0),
    (0x200E, 1), (0x2E7F, 1), (0x2E80, 2), (0x303E, 2), (0x303F, 1), (0xABFF, 1), (0xAC00, 2),
    (0xD7A3, 2), (0xD7A4, 1), (0x1F2FF, 1), (0x1F300, 2), (0x1F64F, 2), (0x1F650, 1), (0x1FFFF, 1),
    (0x20000, 2), (0x2FFFD, 2), (0x2FFFE, 1)]

/-- The claim: `charWidth` — the composite the emulator, `CellOk` and the row
painter all call — agrees with the tables at every edge. -/
example : (widthProbes.all (fun p => charWidth (Char.ofNat p.1) == p.2)) = true := by native_decide

/-- **Non-vacuity for the probes above.** `Char.ofNat` silently yields `'\0'` on
an invalid scalar value, and `charWidth '\0' = 1` — so a typo'd probe (a
surrogate, or anything past U+10FFFF) would pass for the wrong reason wherever the
expected width is 1. Every codepoint round-trips, so none is `'\0'` in disguise. -/
example : (widthProbes.all (fun p => (Char.ofNat p.1).toNat == p.1)) = true := by native_decide

/-- Wide char occupies two columns; the shadow cell has width 0. -/
example : (let v := screen 10 2 "日x"
           (v.getCell 0 0).width == 2 && (v.getCell 1 0).width == 0
             && (v.getCell 2 0).base == 'x') = true := by native_decide

/-- A combining mark after a wide char attaches to the **base**, not to the
width-0 shadow: a shadow is a blank column re-created from its base, so a mark
parked there is invisible to `linger history` and unaddressable at the right
margin. -/
example :
          (let v := screen 10 2 "漢\u0301"
           (v.getCell 0 0).marks == ['\u0301'] && (v.getCell 1 0).marks == []) =
      true := by
  native_decide

/-- …including at the right margin, where the cursor sits on the shadow with
wrap pending. -/
example :
          (let v := screen 4 2 "ab漢\u0301"
           (v.getCell 2 0).marks == ['\u0301'] && (v.getCell 3 0).marks == []) =
      true := by
  native_decide

/-- No half wide pairs, whatever the mutation. A narrow glyph over a wide
base blanks the orphaned shadow; a wide glyph over a shadow blanks the
orphaned base; `ICH`/`DCH`/`ECH` and a truncating resize do the same. Half a
glyph is not displayable, and `Render.rowAnsi` cannot express it — so the
emulator does not reach it (`Row.mend`). -/
example : (let v := screen 6 2 "漢b\x1b[1;1HA"
           (v.getCell 0 0).width == 1 && (v.getCell 0 0).base == 'A'
             && (v.getCell 1 0).width == 1 && (v.getCell 1 0).base == ' ') = true := by
  native_decide

example : (let v := screen 6 2 "漢\x1b[1;2H漢"
           (v.getCell 0 0).width == 1 && (v.getCell 1 0).width == 2
             && (v.getCell 2 0).width == 0) = true := by native_decide

example : (let v := screen 6 2 "漢ab\x1b[1;1H\x1b[1P"
           (v.getCell 0 0).width == 1 && (v.getCell 0 0).base == ' '
             && (v.getCell 1 0).base == 'a') = true := by native_decide

example :
          (let v := screen 6 2 "ab漢cd\x1b[1;1H\x1b[3@"
           (List.range 6).all
        (fun x => (v.getCell x 0).width != 0 || ((v.getCell (x - 1) 0).width == 2 && x != 0))) =
      true := by
  native_decide

/-- Truncating resize through the middle of a pair leaves no orphan base in
the final column. -/
example :
          (let v := (screen 6 2 "ab漢cd").resize 3 2
           (v.getCell 2 0).width == 1) =
      true := by
  native_decide

/-- A stored DEL, and a C0 reached by an overlong UTF-8 sequence, become
U+FFFD on store: a cell holding a control codepoint cannot be repainted, since
the emitter would substitute one anyway. Fed as raw bytes — a Lean `"\xc0"`
literal is a *character*, which `toUTF8` re-encodes, so a string cannot
express an overlong sequence. -/
example : (let v := (Vt.init 6 2).feed [0x61, 0x7F, 0xC0, 0x80, 0x62]
           (v.getCell 1 0).base == '\uFFFD' && (v.getCell 2 0).base == '\uFFFD'
             && (v.getCell 3 0).base == 'b') = true := by native_decide

/-- UTF-8 split across feeds decodes identically (§Chunk in action). -/
example :
          (let bytes := "é".toUTF8.toList
           let v1 := (Vt.init 10 2).feed bytes
           let v2 := (Vt.init 10 2).feed [bytes[0]!] |>.feed [bytes[1]!]
           rowStr v1 0 == "é" && rowStr v2 0 == "é") =
      true := by
  native_decide

/-- Scroll region: lines outside [top,bot] stay put. -/
example : (let v := screen 10 4 "a\r\nb\r\nc\r\nd\x1b[2;3r\x1b[3;1H\nX"
           rowStr v 0 == "a" && rowStr v 3 == "d"
             && rowStr v 1 == "c" && rowStr v 2 == "X") = true := by native_decide

/-- Scrollback: lines pushed off the top are retained (ring, capped). -/
example :
          (let v := screen 5 2 "1\r\n2\r\n3\r\n4"
           v.sb.size == 2 && (v.sb.toList.map plain) == ["1", "2"]) =
      true := by
  native_decide

/-- **A reachable client can be mid-character.** This is the fixture behind dropping
`u8need = 0` from `Render.restore_grid_reachable`: being fed a UTF-8 lead byte is an
ordinary thing for a live terminal to have happened to it, so reachability does *not*
supply that hypothesis — and the claim holds anyway, because `restore` opens with `ESC`
and `abortUtf8` discards the pending sequence. -/
example : (((Vt.init 80 24).feed [0xC3]).u8need == 1) = true := by native_decide

/-- ED 3 wipes scrollback. -/
example :
          (let v := screen 5 2 "1\r\n2\r\n3\r\n4\x1b[3J"
           v.sb.size == 0) =
      true := by
  native_decide

/-- **Why `Render.OffRow` carries an `sb` field, at the one height that shows it.** With a
single row, a full-screen line feed pushes the evicted line to scrollback and rewrites row
0 — and there is no *other* row. So `OffRow.cells`, which quantifies over rows other than
the one being painted, is vacuous here while the ring grows underneath it: the two facts
are independent, and only a field can carry the second one. -/
example :
          (let v := screen 5 1 "1\r\n2"
           v.sb.size == 1 && (v.sb.toList.map plain) == ["1"] && rowStr v 0 == "2") =
      true := by
  native_decide

/-- ICH/DCH shift within the row. -/
example :
          (let v := screen 10 2 "abcdef\x1b[1;3H\x1b[2@XY"
           rowStr v 0 == "abXYcdef") =
      true := by
  native_decide

/-- DECSC/DECRC round-trips cursor and pen. -/
example : (let v := screen 10 3 "\x1b[31m\x1b7\x1b[0m\x1b[3;5Hzz\x1b8A"
           (v.getCell 0 0).base == 'A' && (v.getCell 0 0).pen.fg == .idx 1
             && v.cursor.x == 1 && v.cursor.y == 0) = true := by native_decide

/-- Kitty's private `CSI ? u` query is state-neutral; public ANSI `CSI u`
still performs DECRC. -/
example :
          (let v := screen 10 3 "\x1b[31m\x1b[s\x1b[0m\x1b[3;5H"
           let queried := feedStr v "\x1b[?u"
           let restored := feedStr v "\x1b[u"
           queried.cursor == v.cursor && queried.pen == v.pen && restored.cursor == v.saved.cur &&
        restored.pen == v.saved.pen) =
      true := by
  native_decide

/-- Resize clamps the cursor and keeps content (truncate/pad). -/
example : (let v := (screen 10 4 "hello\x1b[4;9H").resize 6 2
           v.cols == 6 && v.rows == 2
             && v.cursor.x == 5 && v.cursor.y == 1) = true := by native_decide

/-- DEC line-drawing charset maps q to ─. -/
example :
          (let v := screen 10 2 "\x1b(0qx\x1b(B"
           rowStr v 0 == "─│") =
      true := by
  native_decide

/-- OSC title (BEL-terminated) is captured, not printed. -/
example :
          (let v := screen 20 2 "\x1b]2;my title\x07ok"
           v.title == "my title" && rowStr v 0 == "ok") =
      true := by
  native_decide

/-- Bracketed paste + mouse modes recorded for restore. -/
example : (let v := screen 10 2 "\x1b[?2004h\x1b[?1002h\x1b[?1006h"
           v.modes.bracketedPaste && v.modes.mouse == 1002
             && v.modes.mouseSgr) = true := by native_decide

/-- Bell is sticky until cleared (the runtime's activity signal). -/
example :
          (let v := screen 10 2 "a\x07b"
           v.bell) =
      true := by
  native_decide

/-- Adversarial garbage: truncated CSI, orphan continuation bytes, junk
ESC — the screen still takes the next printable. (§Total, concretely.) -/
example :
          (let v := screen 10 2 "\x1b[999;999;999\xFF\x80\x80\x1b]\x07\x1b[<>=?zok"
           ((rowStr v 0).splitOn "ok").length ≥ 2) =
      true := by
  native_decide

/-- Restore render round-trip: feeding the restore bytes to a fresh Vt
reproduces the visible grid (the reattach guarantee, in miniature). -/
example :
          (let v := screen 12 3 "he\x1b[33mllo\r\n\x1b[44mworld\x1b[0m!"
           let w := (Vt.init 12 3).feed (restore v)
           (List.range 3).all (fun y => (v.getRow y) == (w.getRow y)) && w.cursor.x == v.cursor.x &&
        w.cursor.y == v.cursor.y) =
      true := by
  native_decide

/-- History dump contains scrollback plus screen, oldest first. -/
example :
          (let v := screen 5 2 "1\r\n2\r\n3\r\n4"
           String.fromUTF8! ⟨(history v).toArray⟩ == "1\n2\n3\n4\n") =
      true := by
  native_decide

/-- **`mend` is not the identity** (moved from `Theorems/Render/Keeps.lean` in
lean-modules Step 5 — a module-file kernel `decide` cannot reduce a derived
`DecidableEq` whose body is unexposed, and this check is an evaluation anyway):
a lone width-2 base is repaired away, so `mend_of_pairOk`'s hypothesis is
load-bearing rather than decorative. -/
example :
    (Row.mend #[{ base := 'x', marks := [], width := 2, pen := {} }] !=
        #[{ base := 'x', marks := [], width := 2, pen := {} }]) =
      true := by
  native_decide

/-- Every ESC intermediate keeps both the session and observer away from a
title-write boundary. The final is consumed without printing it. -/
example :
    ((List.range 16).all fun n =>
        let v := screen 10 2 "\x1b]2;application\x07"
        let bytes := [0x1B, UInt8.ofNat (0x20 + n)]
        let pending := v.feed bytes
        let observer := v.observe bytes
        let done := pending.feed [0x47, 0x6F, 0x6B]
        !pending.atBoundary && !observer.atBoundary && done.atBoundary &&
          done.windowTitle == "application" &&
          rowStr done 0 == "ok") =
      true := by
  native_decide

/-- The actual split ESC % G remains pending until G, including when observed
one chunk at a time. A following title is still parsed as an OSC. -/
example :
    (let v := Vt.init 10 2
     let pending := v.observe [0x1B, 0x25]
      let done := pending.observe [0x47]
      let titled := done.observe "\x1b]2;linger\x07".toUTF8.toList
      !pending.atBoundary && done.atBoundary && titled.atBoundary &&
        titled.windowTitle == "linger" &&
        rowStr titled 0 == "") =
      true := by
  native_decide

/-- Unknown compound ESC sequences must consume all intermediates and the
final without treating a trailing '(' or ')' as a single-byte designation. -/
example :
    ((List.range 16).all fun a =>
        (List.range 16).all fun b =>
          let v := screen 10 2 "\x1b(0\x1b)0"
          let pending := v.feed [0x1B, UInt8.ofNat (0x20 + a), UInt8.ofNat (0x20 + b)]
          let done := pending.feed [0x47]
          !pending.atBoundary && done.atBoundary && done.g0Line && done.g1Line &&
            rowStr done 0 == "") =
      true := by
  native_decide

/-- DEL does not finish CSI or discard its accumulated SGR parameters. -/
example :
    (let pending := screen 10 2 "\x1b[31"
     let ignored := pending.feed [0x7F]
      let done := feedStr ignored ";1mX"
      !ignored.atBoundary && done.atBoundary && done.pen.fg == .idx 1 && done.pen.bold &&
        rowStr done 0 == "X") =
      true := by
  native_decide

/-- DEL after a CSI intermediate remains inside that ignored control sequence;
its final must not leak onto the screen. -/
example :
    (let pending := screen 10 2 "\x1b[1 "
     let ignored := pending.observe [0x7F]
      let done := ignored.observe [0x71]
      !ignored.atBoundary && done.atBoundary && rowStr done 0 == "") =
      true := by
  native_decide

/-- DEL after ESC is ignored, so the next '[' still opens CSI. -/
example :
    (let pending := (Vt.init 10 2).feed [0x1B, 0x7F]
     let done := feedStr pending "[31mX"
     !pending.atBoundary && done.atBoundary && done.pen.fg == .idx 1 &&
       rowStr done 0 == "X") = true := by
  native_decide

/-- DEL within either charset designation preserves the pending bank and
allows its eventual final to select line drawing. -/
example :
    ([0x28, 0x29].all fun i =>
        let pending := (Vt.init 10 2).feed [0x1B, i, 0x7F]
        let done := pending.feed [0x30, if i == 0x29 then 0x0E else 0x0F, 0x71]
        !pending.atBoundary && done.atBoundary && rowStr done 0 == "─") =
      true := by
  native_decide

/-- A new ESC abandons an incomplete designation and starts a fresh OSC;
the boundary stays closed until that OSC's terminator. -/
example :
    (let pending := (Vt.init 10 2).observe "\x1b(\x1b]2;new".toUTF8.toList
     let done := pending.observe [0x07]
     !pending.atBoundary && done.atBoundary && done.windowTitle == "new" &&
       rowStr done 0 == "") = true := by
  native_decide

/-- Long runs of intermediates and DEL remain pending without a growing
accumulator; a final completes them even after thousands of chunks. -/
example :
    (let start := (Vt.init 1 1).observe [0x1B, 0x23]
     let result := (List.replicate 4096 [0x20, 0x7F, 0x2F]).foldl
       (fun (ok, v) bytes =>
         let w := v.observe bytes
         (ok && !w.atBoundary, w)) (true, start)
     result.1 && (result.2.observe [0x38]).atBoundary &&
       rowStr result.2 0 == "" && result.2.sb.size == 0) = true := by
  native_decide

/-- Every ESC final byte completes an intermediate sequence; nonfinal bytes
cannot publish a false boundary before it. -/
example :
    ((List.range (0x7F - 0x30)).all fun n =>
        let pending := (Vt.init 1 1).observe [0x1B, 0x25, 0x00, 0x7F, 0x80]
        !pending.atBoundary && (pending.observe [UInt8.ofNat (0x30 + n)]).atBoundary) =
      true := by
  native_decide

end Linger.Core.Vt.Tests
