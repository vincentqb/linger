import Zmx.Core.Vt
import Zmx.Core.Render
/-! # Vt behavior tests

The theorems say the emulator cannot crash or grow; these pin what it
actually *does* — golden semantics for the sequences real programs
emit. All `native_decide`: `Vt` ops are data-structure-heavy and the
kernel evaluator would crawl.
-/

namespace Zmx.Core.Vt.Tests

open Zmx.Core.Vt Zmx.Core.Render

def feedStr (v : Vt) (s : String) : Vt := v.feedBytes s.toUTF8

def screen (cols rows : Nat) (s : String) : Vt := feedStr (Vt.init cols rows) s

def rowStr (v : Vt) (y : Nat) : String := rowText (v.getRow y)

/-- Plain echo with newline: CR+LF discipline. -/
example : (let v := screen 10 3 "hi\r\nyo"
           rowStr v 0 == "hi" && rowStr v 1 == "yo"
             && v.cursor.x == 2 && v.cursor.y == 1) = true := by native_decide

/-- LF alone moves down without resetting the column. -/
example : (let v := screen 10 3 "ab\nc"
           rowStr v 0 == "ab" && rowStr v 1 == "  c") = true := by native_decide

/-- Wrap at the right margin (DECAWM), wrap-pending style: the cursor
holds at the margin until the next glyph. -/
example : (let v := screen 3 2 "abcd"
           rowStr v 0 == "abc" && rowStr v 1 == "d"
             && v.cursor.x == 1 && v.cursor.y == 1) = true := by native_decide

/-- With wrap off, glyphs overwrite the last column. -/
example : (let v := screen 3 2 "\x1b[?7labcd"
           rowStr v 0 == "abd" && v.cursor.y == 0) = true := by native_decide

/-- CUP is 1-based; ED 2 clears. -/
example : (let v := screen 10 4 "xxxx\x1b[2J\x1b[3;2Hok"
           rowStr v 0 == "" && rowStr v 2 == " ok"
             && v.cursor.y == 2 && v.cursor.x == 3) = true := by native_decide

/-- SGR survives into cells: fg color + bold recorded, reset clears. -/
example : (let v := screen 10 2 "\x1b[1;31mA\x1b[0mB"
           let a := v.getCell 0 0
           let b := v.getCell 1 0
           a.pen.bold && a.pen.fg == .idx 1
             && !b.pen.bold && b.pen.fg == .default) = true := by native_decide

/-- 256-color and truecolor, both syntaxes. -/
example : (let v := screen 10 2 "\x1b[38;5;196mX\x1b[48:2::10:20:30mY"
           (v.getCell 0 0).pen.fg == .idx 196
             && (v.getCell 1 0).pen.bg == .rgb 10 20 30) = true := by native_decide

/-- Alt screen: 1049 enter clears, leave restores the main screen. -/
example : (let v := screen 10 2 "main\x1b[?1049halt"
           let w := feedStr v "\x1b[?1049l"
           rowStr v 0 == "alt" && v.altGrid.isSome
             && rowStr w 0 == "main" && w.altGrid.isNone
             && w.cursor.x == 4) = true := by native_decide

/-- Wide char occupies two columns; the shadow cell has width 0. -/
example : (let v := screen 10 2 "日x"
           (v.getCell 0 0).width == 2 && (v.getCell 1 0).width == 0
             && (v.getCell 2 0).base == 'x') = true := by native_decide

/-- UTF-8 split across feeds decodes identically (§Chunk in action). -/
example : (let bytes := "é".toUTF8.toList
           let v1 := (Vt.init 10 2).feed bytes
           let v2 := (Vt.init 10 2).feed [bytes[0]!] |>.feed [bytes[1]!]
           rowStr v1 0 == "é" && rowStr v2 0 == "é") = true := by native_decide

/-- Scroll region: lines outside [top,bot] stay put. -/
example : (let v := screen 10 4 "a\r\nb\r\nc\r\nd\x1b[2;3r\x1b[3;1H\nX"
           rowStr v 0 == "a" && rowStr v 3 == "d"
             && rowStr v 1 == "c" && rowStr v 2 == "X") = true := by native_decide

/-- Scrollback: lines pushed off the top are retained (ring, capped). -/
example : (let v := screen 5 2 "1\r\n2\r\n3\r\n4"
           v.sb.size == 2
             && (v.sb.toList.map rowText) == ["1", "2"]) = true := by native_decide

/-- ED 3 wipes scrollback. -/
example : (let v := screen 5 2 "1\r\n2\r\n3\r\n4\x1b[3J"
           v.sb.size == 0) = true := by native_decide

/-- ICH/DCH shift within the row. -/
example : (let v := screen 10 2 "abcdef\x1b[1;3H\x1b[2@XY"
           rowStr v 0 == "abXYcdef") = true := by native_decide

/-- DECSC/DECRC round-trips cursor and pen. -/
example : (let v := screen 10 3 "\x1b[31m\x1b7\x1b[0m\x1b[3;5Hzz\x1b8A"
           (v.getCell 0 0).base == 'A' && (v.getCell 0 0).pen.fg == .idx 1
             && v.cursor.x == 1 && v.cursor.y == 0) = true := by native_decide

/-- Resize clamps the cursor and keeps content (truncate/pad). -/
example : (let v := (screen 10 4 "hello\x1b[4;9H").resize 6 2
           v.cols == 6 && v.rows == 2
             && v.cursor.x == 5 && v.cursor.y == 1) = true := by native_decide

/-- DEC line-drawing charset maps q to ─. -/
example : (let v := screen 10 2 "\x1b(0qx\x1b(B"
           rowStr v 0 == "─│") = true := by native_decide

/-- OSC title (BEL-terminated) is captured, not printed. -/
example : (let v := screen 20 2 "\x1b]2;my title\x07ok"
           v.title == "my title" && rowStr v 0 == "ok") = true := by native_decide

/-- Bracketed paste + mouse modes recorded for restore. -/
example : (let v := screen 10 2 "\x1b[?2004h\x1b[?1002h\x1b[?1006h"
           v.modes.bracketedPaste && v.modes.mouse == 1002
             && v.modes.mouseSgr) = true := by native_decide

/-- Bell is sticky until cleared (the runtime's activity signal). -/
example : (let v := screen 10 2 "a\x07b"
           v.bell) = true := by native_decide

/-- Adversarial garbage: truncated CSI, orphan continuation bytes, junk
ESC — the screen still takes the next printable. (§Total, concretely.) -/
example : (let v := screen 10 2 "\x1b[999;999;999\xFF\x80\x80\x1b]\x07\x1b[<>=?zok"
           ((rowStr v 0).splitOn "ok").length ≥ 2) = true := by native_decide

/-- Restore render round-trip: feeding the restore bytes to a fresh Vt
reproduces the visible grid (the reattach guarantee, in miniature). -/
example : (let v := screen 12 3 "he\x1b[33mllo\r\n\x1b[44mworld\x1b[0m!"
           let w := (Vt.init 12 3).feed (restore v)
           (List.range 3).all (fun y => (v.getRow y) == (w.getRow y))
             && w.cursor.x == v.cursor.x && w.cursor.y == v.cursor.y) = true := by
  native_decide

/-- History dump contains scrollback plus screen, oldest first. -/
example : (let v := screen 5 2 "1\r\n2\r\n3\r\n4"
           String.fromUTF8! ⟨(history v false).toArray⟩ == "1\n2\n3\n4\n") = true := by
  native_decide

end Zmx.Core.Vt.Tests
