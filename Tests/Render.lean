import Zmx.Core.Vt
import Zmx.Core.Render
/-! # §Replay round-trip tests — restore fidelity, executable form

The target theorem (specs/bigger-theorems.md step 3):

    (Vt.init v.cols v.rows).feed (Render.restore v) ≃ v

Until the proofs land (stages 3b–3d), this suite IS the fidelity
oracle: `replayEq` is the decidable `≃`, and every fixture exercises
one feature a reattaching client depends on. Each was verified to FAIL
against the pre-fix `Render.restore` (see SCRATCHPAD) — this is what
"the emitter forgot X" looks like when it can be caught at build time.
-/

namespace Zmx.Core.Render.Tests

open Zmx.Core.Vt Zmx.Core.Render

/-- The §Replay equivalence. Compared: grid, cursor position, pen,
scroll region, modes, title, tabs, charset, saved cursor/pen, the alt
stash, and that the replay ends parser-ground. Deliberately excluded:
`sb` (restore repaints the screen, not history), `bell` (a runtime
signal), and every wrap-`pending` flag (cursor addressing clears it on
any terminal — unrepresentable in a replay, harmless: the next glyph
decides). -/
def replayEq (r v : Vt) : Bool :=
  r.cols == v.cols && r.rows == v.rows
  && r.grid == v.grid
  && r.cursor.x == v.cursor.x && r.cursor.y == v.cursor.y
  && r.pen == v.pen
  && r.top == v.top && r.bot == v.bot
  && r.modes == v.modes
  && r.title == v.title
  && r.tabs == v.tabs
  && r.g0Line == v.g0Line && r.g1Line == v.g1Line && r.shiftOut == v.shiftOut
  && r.saved.cur.x == v.saved.cur.x && r.saved.cur.y == v.saved.cur.y
  && r.saved.pen == v.saved.pen
  && (match r.altGrid, v.altGrid with
      | none, none => true
      | some (g1, c1, p1), some (g2, c2, p2) =>
        g1 == g2 && c1.x == c2.x && c1.y == c2.y && p1 == p2
      | _, _ => false)
  && r.pstate == PState.ground && v.pstate == PState.ground
  && r.u8need == 0

def feedStr (v : Vt) (s : String) : Vt := v.feedBytes s.toUTF8

def screen (cols rows : Nat) (s : String) : Vt := feedStr (Vt.init cols rows) s

/-- The round trip under test. -/
def roundtrips (v : Vt) : Bool := replayEq ((Vt.init v.cols v.rows).feed (restore v)) v

/-- Text, 16-color SGR, attributes, cursor parked mid-screen. -/
example : roundtrips (screen 20 5
    "\x1b[31;1mred bold\x1b[0m\r\nplain \x1b[4munder\x1b[24m\x1b[2;3H")
    = true := by native_decide

/-- 256-color and RGB pens. -/
example : roundtrips (screen 12 3
    "\x1b[38;5;196mX\x1b[48;2;10;20;30mY")
    = true := by native_decide

/-- Erased-with-background cells (BCE): a full-screen app's canvas. -/
example : roundtrips (screen 10 4 "\x1b[44m\x1b[2J\x1b[1;1Hx")
    = true := by native_decide

/-- Scroll region set and content scrolled inside it; region must
survive the trip. -/
example : roundtrips (screen 10 6
    "\x1b[2;4r\x1b[2;1Haaa\r\nbbb\r\nccc\r\nddd")
    = true := by native_decide

/-- Wide chars, and a combining mark on a narrow char. -/
example : roundtrips (screen 12 3 "漢字e\u0301x")
    = true := by native_decide

/-- Spec fix 1: a combining mark on a WIDE char lives on the width-0
continuation cell; the emitter must not drop it. -/
example : roundtrips (screen 12 3 "漢\u0301x")
    = true := by native_decide

/-- Spec fix 2: charset state — G0 designated line-drawing (glyphs land
translated), G1 designated + SO active at detach time. -/
example : roundtrips (screen 12 3 "\x1b(0lqk\x1b(B ab\x1b)0\x0e")
    = true := by native_decide

/-- Spec fix 3: DECSC-saved cursor + pen must survive, or DECRC after
reattach jumps to 0,0 with the wrong pen. -/
example : roundtrips (screen 12 5 "\x1b[36m\x1b[3;7H\x1b7\x1b[0m\x1b[1;1Hz")
    = true := by native_decide

/-- Spec fixes 4+5: DECOM origin mode (with a region) and IRM insert
mode; the final cursor address is region-relative under DECOM. -/
example : roundtrips (screen 10 6 "\x1b[2;4r\x1b[?6h\x1b[4h\x1b[2;2H")
    = true := by native_decide

/-- Replayable modes: bracketed paste, mouse+SGR, app cursor, hidden
cursor, wrap off, focus events, app keypad. -/
example : roundtrips (screen 10 3
    "\x1b[?2004h\x1b[?1002h\x1b[?1006h\x1b[?1h\x1b[?25l\x1b[?7l\x1b[?1004h\x1b=")
    = true := by native_decide

/-- Spec fix 6: custom tab stops (TBC 3 then HTS at columns 6 and 10). -/
example : roundtrips (screen 20 3 "\x1b[3g\x1b[1;6H\x1bH\x1b[1;10H\x1bH\x1b[1;1H")
    = true := by native_decide

/-- Spec fix 7: alt screen — the stashed main cursor/pen (what ?1049l
will restore) and the `saved` slot must both survive; paint-then-switch
alone stashes wherever the main repaint happened to end. -/
example : roundtrips (screen 12 6
    "main1\r\nmain2\x1b[35m\x1b[5;3H\x1b[?1049h\x1b[33malt\x1b[3;2H")
    = true := by native_decide

/-- Title (OSC 2). -/
example : roundtrips (screen 10 3 "\x1b]2;my title\x07hey")
    = true := by native_decide

/-- Kitchen sink: region + modes + colors + wide + title + saved. -/
example : roundtrips (screen 24 8
    ("\x1b]0;sink\x07\x1b[2;7r\x1b[36m\x1b[3;7H\x1b7\x1b[38;5;40mok 漢字\r\n" ++
     "\x1b[?2004h\x1b[44mBCE\x1b[K\x1b[4;2H"))
    = true := by native_decide

end Zmx.Core.Render.Tests
