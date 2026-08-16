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


/-! ### The tab ruler — the set-only field the `dirty` receiver missed

`tabsAnsi` used to emit nothing when the *session's* ruler was the default, on the
theory that a reset terminal already has it. A client is not a reset terminal, and
nothing else in a restore stream clears a tab stop, so the previous occupant's
ruler survived and a `\t` from the session landed on the wrong column. The `dirty`
receiver above never moves the ruler, which is exactly why sixteen fixtures and a
receiver-quantified modes proof all missed it; this one moves it. -/

/-- A previous occupant that cleared the ruler and set its own stops every four
columns: `CSI 3 g`, then `CHA` + `HTS` at columns 5, 9, 13 and 17. -/
def dirtyTabs (cols rows : Nat) : Vt :=
  feedStr (Vt.init cols rows) "\x1b[3g\x1b[5G\x1bH\x1b[9G\x1bH\x1b[13G\x1bH\x1b[17G\x1bH"

/-- The hazard itself: the receiver's ruler is not the default one. -/
example : ((dirtyTabs 20 3).tabs == defaultTabs 20) = false := by native_decide

/-- **The assertion that was false before the fix.** A default-ruler session
restored into that receiver used to come back holding the *receiver's* ruler. -/
example : (((dirtyTabs 20 3).feed (restore (screen 20 3 "hi"))).tabs
    == (screen 20 3 "hi").tabs) = true := by native_decide

example : roundtripsFrom (dirtyTabs 20 3) (screen 20 3 "hi") = true := by native_decide

/-- The other direction too: a session with its own custom ruler, into a receiver
with a different one. -/
example : roundtripsFrom (dirtyTabs 20 3) (screen 20 3 "\x1b[3g\x1b[7G\x1bHhi")
    = true := by native_decide

/-- Non-vacuity, part one: a default-ruler session now emits a ruler at all. This is
the byte range the old guard skipped. -/
example : (tabsAnsi (screen 20 3 "hi")).isEmpty = false := by native_decide

/-- Non-vacuity, part two: **nothing before `tabsAnsi` clears a tab stop** — no
`TBC` in the prologue, and `ED 2` does not touch the ruler — so the emit is the only
thing standing between a client's ruler and the session's. -/
example : (((dirtyTabs 20 3).feed (prologueAnsi (screen 20 3 "hi") ++ csiNum 0 0x6D
    ++ csiNum 2 0x4A)).tabs == (dirtyTabs 20 3).tabs) = true := by native_decide


/-! ### A receiver caught mid-sequence

The client's *parser* state is part of the state restore was assuming. A terminal
sitting in an unterminated OSC or DCS swallows every byte until its terminator, so
before `prologueAnsi` led with `ST` the entire restore stream vanished into a window
title. These starts cover one receiver per parser state. -/

def midOsc (cols rows : Nat) : Vt := feedStr (Vt.init cols rows) "\x1b]2;unfinished"

def midDcs (cols rows : Nat) : Vt := feedStr (Vt.init cols rows) "\x1bPq#0;2;0;0;0"

def midCsi (cols rows : Nat) : Vt := feedStr (Vt.init cols rows) "\x1b[38;5"

def midEscInter (cols rows : Nat) : Vt := feedStr (Vt.init cols rows) "\x1b("

def midUtf8 (cols rows : Nat) : Vt := (Vt.init cols rows).feedBytes ⟨#[0xE6, 0xBC]⟩

example : roundtripsFrom (midOsc 6 3) (screen 6 3 "hi") = true := by native_decide
example : roundtripsFrom (midDcs 6 3) (screen 6 3 "hi") = true := by native_decide
example : roundtripsFrom (midCsi 6 3) (screen 6 3 "hi") = true := by native_decide
example : roundtripsFrom (midEscInter 6 3) (screen 6 3 "hi") = true := by native_decide
example : roundtripsFrom (midUtf8 6 3) (screen 6 3 "hi") = true := by native_decide

/-- The mid-OSC receiver really is stuck: it has eaten the bytes and is still in an
OSC, so this is not a vacuous test. -/
example : ((midOsc 6 3).pstate == PState.ground) = false := by native_decide

/-- A session with **no** title clears the client's leftover one, rather than leaving
it on display: the last of the set-only emits. -/
example : (let v := screen 6 3 "hi"
           let w := (feedStr (Vt.init 6 3) "\x1b]2;stale\x07").feed (restore v)
           w.title == v.title && v.title.isEmpty) = true := by native_decide


/-! ### The hand-back (§Handback, anchor A5's outbound half)

The mirror image of everything above. `restore` establishes what the repaint needs in
whatever terminal it is given; `leaveAnsi` gives that terminal back to the user's
shell in a state the next program can use, whatever the session's last program left
behind. `leave_grounds` proves the parser half for every receiver; these pin the
values until the `Sets` instances land (`specs/restore-conformance.md` Step 1). -/

/-- The canonical state a detaching client owes the next program. `rows` is a
parameter because two of the fields are dimension-relative: the scroll region is the
whole screen, and the cursor is parked on the last row. -/
def sane (rows : Nat) (w : Vt) : Bool :=
  w.pstate == PState.ground
  && w.modes == ({} : Modes)
  && !w.g0Line && !w.g1Line && !w.shiftOut
  && w.top == 0 && w.bot == rows - 1
  && w.altGrid.isNone
  && w.pen == ({} : Pen)
  && w.cursor.x == 0 && w.cursor.y == rows - 1

/-- A dirty client is not sane, or the checks below would hold vacuously. -/
example : sane 3 (dirty 6 3) = false := by native_decide

example : sane 3 ((dirty 6 3).feed leaveAnsi) = true := by native_decide

/-- …from every parser state a dying program can leave, too. -/
example : sane 3 ((midOsc 6 3).feed leaveAnsi) = true := by native_decide
example : sane 3 ((midDcs 6 3).feed leaveAnsi) = true := by native_decide
example : sane 3 ((midCsi 6 3).feed leaveAnsi) = true := by native_decide
example : sane 3 ((midEscInter 6 3).feed leaveAnsi) = true := by native_decide
example : sane 3 ((midUtf8 6 3).feed leaveAnsi) = true := by native_decide

/-- The worst real case: a full-screen application that died mid-OSC. Both halves of
the hazard at once — dirty modes *and* a parser that eats what it is sent. -/
def dirtyMidOsc (cols rows : Nat) : Vt := feedStr (dirty cols rows) "\x1b]2;half"

example : sane 3 ((dirtyMidOsc 6 3).feed leaveAnsi) = true := by native_decide

/-- **The lead-in is load-bearing**, in the form a code break would show: drop the
two bytes of `ESC \` and the same receiver eats the entire hand-back, so the shell
inherits the application's terminal. This is `leave_grounds`'s non-vacuity — its
`∀ w` really does range over receivers that would otherwise swallow the stream. -/
example : sane 3 ((dirtyMidOsc 6 3).feed (leaveAnsi.drop 2)) = false := by native_decide

/-- And the hand-back is a *constant*: what linger gives back cannot depend on what
the session was doing, which is why it takes no `Vt`. Two very different sessions,
same result. -/
example : (((dirty 6 3).feed leaveAnsi).modes == ((midDcs 6 3).feed leaveAnsi).modes)
    = true := by native_decide

end Zmx.Core.Render.Tests
