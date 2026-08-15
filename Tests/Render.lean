import Zmx.Core.Vt
import Zmx.Core.Render
/-! # §Replay round-trip tests — restore fidelity, executable form

The target theorem (specs/grid-fidelity.md):

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

/-- A combining mark on a WIDE char. It is stored on the **base**, never on
the width-0 continuation cell: a shadow is a blank column that a repaint
re-creates from its base, `Render.rowText` skips it outright (so a mark parked
there never appeared in `linger history`), and at the right margin only an
armed wrap-pending flag could address it — which no absolute cursor move
reproduces. `Vt.print` redirects there, so the emitter has one case instead of
a documented inexpressible one. -/
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

/-- Spec fix 8 — the **parameter cap**. Seven attributes plus truecolour
foreground *and* background, set by three separate SGRs the way a real
application does. Replayed as one combined sequence that would be 18
parameters, the parser sets `ignore` on the 17th and drops the lot: the
pen came back entirely default, every attribute and both colours lost.
Found by proving §Replay rather than by testing; `penSgr` now emits at
most 8 parameters per sequence. -/
example : roundtrips (screen 10 3
    "\x1b[1;2;3;4;5;7;9m\x1b[38;2;10;20;30m\x1b[48;2;40;50;60mX")
    = true := by native_decide

/-- The same cap, one rung down: 256-colour fg and bg (3 parameters each)
alongside every attribute — 14 combined, just under the cap, so this one
passed even before the fix. Kept as the boundary case. -/
example : roundtrips (screen 10 3
    "\x1b[1;2;3;4;5;7;9m\x1b[38;5;123m\x1b[48;5;200mY")
    = true := by native_decide

/-- Spec fix 8 — a combining mark on a **wide** cell's own position, not on
its shadow. Reachable: print 漢 (cursor lands past the shadow), step back
with `CSI 2 G`, print the mark — `print` attaches at `cursor.x - 1`, the
wide cell itself. `rowAnsi` emitted base-then-marks, and the 2-column
advance made the marks re-attach to the *shadow*: the mark moved one cell
right on every reattach. Found while designing the grid induction, not by
testing. -/
example : roundtrips (screen 12 3 "\u6f22\x1b[2G\u0301") = true := by native_decide

/-- The same path at the **right margin**: a wide char ending in the last
column leaves the cursor clamped there with wrap-pending, so the mark's target
is the shadow, which is exactly the case the redirect has to catch — a mark on
the final column is the one position an absolute `CHA` cannot reach. -/
example : roundtrips (screen 4 2 "ab\u6f22\u0301") = true := by native_decide

/-- Two marked wide glyphs in one row. The emitted `CHA` column is a **cell
index**, and a width-2 base used to advance it by two while its shadow advanced
it by one — so the second glyph's mark address was a column too far right, the
rest of the row drifted, and its last cell wrapped into a line feed that
scrolled the whole grid. Latent until marks were normalized onto the base made
this branch fire for an ordinary marked `漢`; the fuzzer found it in the same
pass, at two independent seeds. -/
example : roundtrips (screen 6 3 "\u6f22\u0301\u6f22\u0301") = true := by native_decide

/-- …and with a line-insert after it, which is how the fuzzer first showed the
drift: the spurious wrap moved every row down by one. -/
example : roundtrips (screen 6 3 "\x1b[?2004h\u6f22\u0301\u6f22\u0301\x1b[L")
    = true := by native_decide

/-- A **narrow glyph printed over a wide base** orphans that base's shadow: a
width-0 cell with no base to its left, which `rowAnsi` paints as nothing while
it still occupies a column, so the rest of the row lands one column left. This
needs no `ICH`/`DCH` — any redraw over CJK text does it — and it was both of
the deep fuzz seeds pinned as failing. `Vt.printPut` mends the two columns a
write can half-orphan. -/
example : roundtrips (screen 6 3 "\u6f22b\x1b[1;1HA") = true := by native_decide

/-- The same overprint where the orphaned shadow carries the wide glyph's
marks — the second pinned seed. Before the repair the mark re-attached to the
overprinting glyph. -/
example : roundtrips (screen 4 2 "\u6f22\u0301\x1b[1;1Hb") = true := by native_decide

/-- A **wide glyph printed over a shadow** orphans the shadow's base on the
left, the mirror of the case above. -/
example : roundtrips (screen 6 3 "\u6f22\x1b[1;2H\u6f22") = true := by native_decide

/-- `ICH` pushing a pair's shadow off the row end, and `DCH` deleting a wide
base out from under its shadow: the four mutations held out of the fuzz corpus
until now. Each leaves a half pair that the row painter cannot express, and
each is repaired where it happens. -/
example : roundtrips (screen 6 2 "ab\u6f22cd\x1b[1;1H\x1b[3@") = true := by native_decide

example : roundtrips (screen 6 2 "\u6f22ab\x1b[1;1H\x1b[1P") = true := by native_decide

example : roundtrips (screen 6 2 "a\u6f22b\x1b[1;2H\x1b[1@") = true := by native_decide

example : roundtrips (screen 6 2 "a\u6f22b\x1b[1;3H\x1b[2@") = true := by native_decide

/-- A partial erase that clears one half of a pair (`ECH` over the base, `EL`
from inside a pair). -/
example : roundtrips (screen 6 2 "a\u6f22b\x1b[1;2H\x1b[1X") = true := by native_decide

example : roundtrips (screen 6 2 "a\u6f22b\x1b[1;3H\x1b[K") = true := by native_decide

/-- Insert mode shifting a pair off the row end. -/
example : roundtrips (screen 6 2 "abc\u6f22\x1b[1;1H\x1b[4hxy") = true := by native_decide

/-- A stored **DEL**, and a C0 reached through an overlong UTF-8 sequence.
Either would be repainted as U+FFFD by `Render.safeChar` while the live cell
held the control codepoint, so the substitution happens on store instead
(`Vt.printableChar`) and the two agree. The overlong case is fed as raw bytes:
a Lean `"\xc0"` literal is a character, which `toUTF8` re-encodes. -/
example : roundtrips (screen 6 2 "a\x7fb") = true := by native_decide

example : roundtrips ((Vt.init 6 2).feed [0x61, 0xC0, 0x80, 0x62]) = true := by
  native_decide

/-- Resize truncating a row through the middle of a wide pair. -/
example : roundtrips ((screen 6 2 "ab\u6f22cd").resize 4 2) = true := by native_decide

/-- Spec fix 9 — the **stashed main pen leaked into the alt repaint**.
`screensAnsi` sets the stashed pen just before `?1049h` so the switch stashes
the right one; that left the terminal carrying it, and `gridAnsi`'s fold
assumes the *default* pen is in effect, emitting no SGR for a leading run of
default-pen cells. So a reattach repainted the whole leading run of the alt
screen in the shell's colour — every cell of it, for a blank alt screen.
Found by an alt-path bug hunt, not by the suite: the pre-existing alt fixture
happens to put a non-default pen on alt cell (0,0), whose `SGR` leads with a
reset and heals it. `gridAnsi` now establishes what it assumes. -/
example : roundtrips (screen 1 1 "\x1b[7m\x1b[?1049h") = true := by native_decide

/-- The same, with the leak visible across a row boundary and healing at the
first non-default cell — the shape that made it hard to notice. -/
example : roundtrips (screen 6 3 "\x1b[41mm\x1b[?1049h\x1b[0mA\x1b[32mB") = true := by
  native_decide

/-- A heavy pen at the switch over a blank alt screen: before the fix every
cell replayed bold+dim+italic+underline+blink+reverse+strike in truecolour. -/
example : roundtrips
    (screen 8 3 "\x1b[1;2;3;4;5;7;9m\x1b[38;2;10;20;30m\x1b[48;2;40;50;60mm\x1b[?1049h")
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

/-- A **decoded checkpoint** can carry a mouse mode the emulator would never
store: `Checkpoint.load` reads that field as an arbitrary `Nat` and is total on
arbitrary bytes by design. `modesAnsi` replays it, so a denylist that named only
DECOM would have emitted `CSI ? 1049 h` here — switching the client to the alt
screen in the middle of a restore, corrupting the very screen being restored.

Asserted on the **grid**, not `replayEq`: the allowlist deliberately does *not*
replay a mode the emulator cannot hold, so `modes` is expected to differ. What
must survive is the screen, and that no alt switch happened. -/
example : (let v := { screen 6 2 "ab" with
             modes := { (screen 6 2 "ab").modes with mouse := 1049 } }
           let w := (Vt.init v.cols v.rows).feed (restore v)
           w.grid == v.grid && w.altGrid.isNone) = true := by native_decide

example : (let v := { screen 6 2 "ab" with
             modes := { (screen 6 2 "ab").modes with mouse := 47 } }
           let w := (Vt.init v.cols v.rows).feed (restore v)
           w.grid == v.grid && w.altGrid.isNone) = true := by native_decide

/-- …and a legitimate mouse mode still round-trips in full. -/
example : roundtrips (screen 6 2 "\x1b[?1002h\x1b[?1006hab") = true := by native_decide

/-- Title (OSC 2). -/
example : roundtrips (screen 10 3 "\x1b]2;my title\x07hey")
    = true := by native_decide

/-- Kitchen sink: region + modes + colors + wide + title + saved. -/
example : roundtrips (screen 24 8
    ("\x1b]0;sink\x07\x1b[2;7r\x1b[36m\x1b[3;7H\x1b7\x1b[38;5;40mok 漢字\r\n" ++
     "\x1b[?2004h\x1b[44mBCE\x1b[K\x1b[4;2H"))
    = true := by native_decide

/-! ## Restoring into a client that is **not** pristine

`roundtrips` starts from `Vt.init`, which is the one receiver state in which every
mode the emitter depends on is already correct. A real client is whatever its
previous occupant left behind — `Session.onMsg` sends `restore` on attach with
nothing before it — so the interesting question is whether restore *establishes*
the state it needs rather than assuming it.

Before `prologueAnsi` and the both-ways `modesAnsi`, it did not: modes that the
emitter only ever *set* leaked the client's previous value, and IRM, DECOM, a stale
scroll region, a DEC line-drawing charset or the alt screen each corrupted the
repaint itself. -/

/-- Everything a previous occupant might have left on: insert mode, origin mode,
mouse reporting, bracketed paste, hidden cursor, application cursor and keypad, the
alt screen, line-drawing G0 with shift-out, and a scroll region. -/
def dirty (cols rows : Nat) : Vt :=
  feedStr (Vt.init cols rows)
    "\x1b[4h\x1b[?6h\x1b[?1000h\x1b[?1006h\x1b[?1004h\x1b[?2004h\x1b[?25l\x1b[?1h\x1b=\x1b[?1049h\x1b(0\x0e\x1b[2;3r"

/-- The round trip, from an arbitrary receiver rather than a fresh one. -/
def roundtripsFrom (start v : Vt) : Bool := replayEq (start.feed (restore v)) v

example : roundtripsFrom (dirty 6 3) (screen 6 3 "hi") = true := by native_decide

example : roundtripsFrom (dirty 8 4) (screen 8 4 "\x1b[31mab\r\ncd") = true := by
  native_decide

/-- The dirty client's own modes must not survive: this is the leak itself. -/
example : ((dirty 6 3).modes.insert && (dirty 6 3).modes.origin
    && (dirty 6 3).modes.mouse == 1000 && (dirty 6 3).shiftOut) = true := by native_decide

example : (let v := screen 6 3 "hi"
           let w := (dirty 6 3).feed (restore v)
           w.modes == v.modes && w.g0Line == v.g0Line && w.shiftOut == v.shiftOut
             && w.top == v.top && w.bot == v.bot && w.altGrid.isNone) = true := by
  native_decide

/-- A wide glyph and a combining mark, from a dirty start: the two shapes the
repaint is most sensitive to. -/
example : roundtripsFrom (dirty 6 3) (screen 6 3 "\u6f22e\u0301") = true := by native_decide

/-- And a session that *is* on the alt screen still restores into a dirty client. -/
example : roundtripsFrom (dirty 6 3) (screen 6 3 "ab\x1b[?1049hcd") = true := by
  native_decide

end Zmx.Core.Render.Tests
