module

public import Linger.Core.Render
-- Converted from legacy by the `Vt` seal (`specs/archive/vt-toolkit.md` Step 1): the
-- round-trip fixtures compare fields on both sides, so they are a friend of the
-- emulator.
import all Linger.Core.Vt
import all Linger.Core.Render
-- `native_decide` compiles its goals, and a module's compiled code only sees
-- meta-imported modules — names alone arrive via the public import above.
public meta import Linger.Core.Vt
public meta import Linger.Core.Render

/-! # §Replay round-trip tests — restore fidelity, executable form

The target theorem (specs/archive/grid-fidelity.md):

    (Vt.init v.cols v.rows).feed (Render.restore v) ≃ v

The grid, tab ruler, scrollback, pen, and mode proofs generalize beyond
these fixtures. Cursor restoration still has an origin-mode qualification,
and title and saved-state fidelity still depend on fixtures. `replayEq`
compares the listed observations, including all three deferred-wrap flags;
it is not equivalence under arbitrary future input. The fixtures complement
the proofs with concrete regressions and literal checks on the emitter's choices.
-/

namespace Linger.Core.Render.Tests

open Linger.Core.Vt Linger.Core.Render

/-- The §Replay equivalence. Compared: grid, cursor position, pen,
scroll region, modes, title, tabs, charset, saved cursor/pen, the alt
stash, all three deferred-wrap flags, the **scrollback** (against `sbRows v`, the fitted and
budget-trimmed history the emitter promises — not `v.sb`, since a
session's ring may have wrapped and the receiver's is built from index
zero, so the two agree as histories and differ as records), and that
the replay ends parser-ground. Deliberately excluded: `bell` (a runtime
signal). Deferred wrap is restored by reprinting the existing margin cell.
A pathological decoded flag without a representable margin cell can make
this comparison false; the oracle still compares the flag.

**One honest caveat on the `sb` conjunct.** `scrollbackAnsi` emits its
`ED 3` only when it has history to put there, so a receiver with a ring
of its own keeps it when the session has none. Pairing a dirty-ring
receiver with a no-history session therefore makes this `false` **by
design**; that combination is asserted separately, as non-interference,
below. -/
def replayEq (r v : Vt) : Bool :=
  r.cols == v.cols && r.rows == v.rows && r.grid == v.grid && r.cursor.x == v.cursor.x &&
    r.cursor.y == v.cursor.y &&
    r.cursor.pending == v.cursor.pending &&
    r.pen == v.pen &&
    r.top == v.top &&
    r.bot == v.bot &&
    r.modes == v.modes &&
    r.title == v.title &&
    r.tabs == v.tabs &&
    r.g0Line == v.g0Line &&
    r.g1Line == v.g1Line &&
    r.shiftOut == v.shiftOut &&
    r.saved.cur.x == v.saved.cur.x &&
    r.saved.cur.y == v.saved.cur.y &&
    r.saved.cur.pending == v.saved.cur.pending &&
    r.saved.pen == v.saved.pen &&
    (match r.altGrid, v.altGrid with
    | none, none => true
    | some (g1, c1, p1), some (g2, c2, p2) =>
      g1 == g2 && c1.x == c2.x && c1.y == c2.y && c1.pending == c2.pending && p1 == p2
    | _, _ => false) &&
    r.pstate == PState.ground &&
    v.pstate == PState.ground &&
    r.u8need == 0 &&
    r.sb.toList == (sbRows v).toList

def feedStr (v : Vt) (s : String) : Vt := v.feedBytes s.toUTF8

/-- A row as the text `linger history` would print for it. Used to pin the
emitter's view of the ring against **literals**: `replayEq`'s `sb` conjunct
compares the receiver's ring against `sbRows v`, i.e. against the emitter's own
view, so it cannot see a bug *inside* `sbRows` — only a bug in emitting it. The
fixtures anchored on literals below are the oracle for the fit and the order. -/
def rowStr (r : Row) : String := String.fromUTF8! ⟨(rowText r).toArray⟩

def screen (cols rows : Nat) (s : String) : Vt := feedStr (Vt.init cols rows) s

/-- The round trip under test. -/
def roundtrips (v : Vt) : Bool := replayEq ((Vt.init v.cols v.rows).feed (restore v)) v

/-- Geometry changes clear all three deferred-wrap slots. The main stash must
not resurrect an old margin after leaving the alternate screen. -/
example :
    let v := (screen 4 2 "abcd\x1b[?1049h").resize 6 2
    !v.cursor.pending && !v.saved.cur.pending &&
      !(feedStr v "\x1b[?1049l").cursor.pending = true := by
  native_decide

/-- A margin write is deferred until the next printable character. Address-only
replay loses that continuation even when every visible cell still agrees. -/
example :
    let v := screen 4 2 "abcd"
    let r := (Vt.init 4 2).feed (restore v)
    r.cursor.pending == v.cursor.pending &&
      (feedStr r "X").grid == (feedStr v "X").grid = true := by
  native_decide

/-- DECRC must recover the saved deferred wrap before printing. -/
example :
    let v := screen 4 2 "abcd\x1b7\r"
    let r := (Vt.init 4 2).feed (restore v)
    r.saved.cur.pending == v.saved.cur.pending &&
      (feedStr r "\x1b8X").grid == (feedStr v "\x1b8X").grid = true := by
  native_decide

/-- Leaving 1049 must recover the main screen's deferred wrap. -/
example :
    let v := screen 4 2 "abcd\x1b[?1049h"
    let r := (Vt.init 4 2).feed (restore v)
    (feedStr r "\x1b[?1049lX").grid == (feedStr v "\x1b[?1049lX").grid = true := by
  native_decide

/-- An invalid decoded origin region cannot redirect the extra repaint onto
another row. The existing grid guarantee does not require a live source. -/
example :
    let w := screen 4 2 "\r\nabcd"
    let v := { w with top := 1, bot := 1, modes := { w.modes with origin := true } }
    ((Vt.init 4 2).feed (restore v)).grid == v.grid = true := by
  native_decide

/-- Text, 16-color SGR, attributes, cursor parked mid-screen. -/
example :
    roundtrips (screen 20 5 "\x1b[31;1mred bold\x1b[0m\r\nplain \x1b[4munder\x1b[24m\x1b[2;3H") =
      true := by
  native_decide

/-- 256-color and RGB pens. -/
example : roundtrips (screen 12 3 "\x1b[38;5;196mX\x1b[48;2;10;20;30mY") = true := by native_decide

/-- Erased-with-background cells (BCE): a full-screen app's canvas. -/
example : roundtrips (screen 10 4 "\x1b[44m\x1b[2J\x1b[1;1Hx") = true := by native_decide

/-- Scroll region set and content scrolled inside it; region must
survive the trip. -/
example : roundtrips (screen 10 6 "\x1b[2;4r\x1b[2;1Haaa\r\nbbb\r\nccc\r\nddd") = true := by
  native_decide

/-- Wide chars, and a combining mark on a narrow char. -/
example : roundtrips (screen 12 3 "漢字e\u0301x") = true := by native_decide

/-- A combining mark on a WIDE char. It is stored on the **base**, never on
the width-0 continuation cell: a shadow is a blank column that a repaint
re-creates from its base, `Render.rowText` skips it outright (so a mark parked
there never appeared in `linger history`), and at the right margin only an
armed wrap-pending flag could address it — which no absolute cursor move
reproduces. `Vt.print` redirects there, so the emitter has one case instead of
a documented inexpressible one. -/
example : roundtrips (screen 12 3 "漢\u0301x") = true := by native_decide

/-- Spec fix 2: charset state — G0 designated line-drawing (glyphs land
translated), G1 designated + SO active at detach time. -/
example : roundtrips (screen 12 3 "\x1b(0lqk\x1b(B ab\x1b)0\x0e") = true := by native_decide

/-- Spec fix 3: DECSC-saved cursor + pen must survive, or DECRC after
reattach jumps to 0,0 with the wrong pen. -/
example : roundtrips (screen 12 5 "\x1b[36m\x1b[3;7H\x1b7\x1b[0m\x1b[1;1Hz") = true := by
  native_decide

/-- Spec fix 8 — the **parameter cap**. Seven attributes plus truecolour
foreground *and* background, set by three separate SGRs the way a real
application does. Replayed as one combined sequence that would be 18
parameters, the parser sets `ignore` on the 17th and drops the lot: the
pen came back entirely default, every attribute and both colours lost.
Found by proving §Replay rather than by testing; `penSgr` now emits at
most 8 parameters per sequence. -/
example :
    roundtrips (screen 10 3 "\x1b[1;2;3;4;5;7;9m\x1b[38;2;10;20;30m\x1b[48;2;40;50;60mX") =
      true := by
  native_decide

/-- The same cap, one rung down: 256-colour fg and bg (3 parameters each)
alongside every attribute — 14 combined, just under the cap, so this one
passed even before the fix. Kept as the boundary case. -/
example : roundtrips (screen 10 3 "\x1b[1;2;3;4;5;7;9m\x1b[38;5;123m\x1b[48;5;200mY") = true := by
  native_decide

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
example : roundtrips (screen 6 3 "\x1b[?2004h\u6f22\u0301\u6f22\u0301\x1b[L") = true := by
  native_decide

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

example : roundtrips ((Vt.init 6 2).feed [0x61, 0xC0, 0x80, 0x62]) = true := by native_decide

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
example : roundtrips (screen 6 3 "\x1b[41mm\x1b[?1049h\x1b[0mA\x1b[32mB") = true := by native_decide

/-- A heavy pen at the switch over a blank alt screen: before the fix every
cell replayed bold+dim+italic+underline+blink+reverse+strike in truecolour. -/
example :
    roundtrips
        (screen 8 3 "\x1b[1;2;3;4;5;7;9m\x1b[38;2;10;20;30m\x1b[48;2;40;50;60mm\x1b[?1049h") =
      true := by
  native_decide

/-- Spec fixes 4+5: DECOM origin mode (with a region) and IRM insert
mode; the final cursor address is region-relative under DECOM. -/
example : roundtrips (screen 10 6 "\x1b[2;4r\x1b[?6h\x1b[4h\x1b[2;2H") = true := by native_decide

/-- Replayable modes: bracketed paste, mouse+SGR, app cursor, hidden
cursor, wrap off, focus events, app keypad. -/
example :
    roundtrips
        (screen 10 3 "\x1b[?2004h\x1b[?1002h\x1b[?1006h\x1b[?1h\x1b[?25l\x1b[?7l\x1b[?1004h\x1b=") =
      true := by
  native_decide

/-- Spec fix 6: custom tab stops (TBC 3 then HTS at columns 6 and 10). -/
example : roundtrips (screen 20 3 "\x1b[3g\x1b[1;6H\x1bH\x1b[1;10H\x1bH\x1b[1;1H") = true := by
  native_decide

/-- Spec fix 7: alt screen — the stashed main cursor/pen (what ?1049l
will restore) and the `saved` slot must both survive; paint-then-switch
alone stashes wherever the main repaint happened to end. -/
example :
    roundtrips (screen 12 6 "main1\r\nmain2\x1b[35m\x1b[5;3H\x1b[?1049h\x1b[33malt\x1b[3;2H") =
      true := by
  native_decide

/-- A **decoded checkpoint** can carry a mouse mode the emulator would never
store: `Checkpoint.load` reads that field as an arbitrary `Nat` and is total on
arbitrary bytes by design. `modesAnsi` replays it, so a denylist that named only
DECOM would have emitted `CSI ? 1049 h` here — switching the client to the alt
screen in the middle of a restore, corrupting the very screen being restored.

Asserted on the **grid**, not `replayEq`: the allowlist deliberately does *not*
replay a mode the emulator cannot hold, so `modes` is expected to differ. What
must survive is the screen, and that no alt switch happened. -/
example :
          (let v := { screen 6 2 "ab" with modes := { (screen 6 2 "ab").modes with mouse := 1049 } }
           let w := (Vt.init v.cols v.rows).feed (restore v)
           w.grid == v.grid && w.altGrid.isNone) =
      true := by
  native_decide

example :
          (let v := { screen 6 2 "ab" with modes := { (screen 6 2 "ab").modes with mouse := 47 } }
           let w := (Vt.init v.cols v.rows).feed (restore v)
           w.grid == v.grid && w.altGrid.isNone) =
      true := by
  native_decide

/-- …and a legitimate mouse mode still round-trips in full. -/
example : roundtrips (screen 6 2 "\x1b[?1002h\x1b[?1006hab") = true := by native_decide

/-- Title (OSC 2). -/
example : roundtrips (screen 10 3 "\x1b]2;my title\x07hey") = true := by native_decide

/-- Kitchen sink: region + modes + colors + wide + title + saved. -/
example :
    roundtrips
        (screen 24 8
          ("\x1b]0;sink\x07\x1b[2;7r\x1b[36m\x1b[3;7H\x1b7\x1b[38;5;40mok 漢字\r\n" ++
            "\x1b[?2004h\x1b[44mBCE\x1b[K\x1b[4;2H")) =
      true := by
  native_decide

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

example : roundtripsFrom (dirty 8 4) (screen 8 4 "\x1b[31mab\r\ncd") = true := by native_decide

/-- The dirty client's own modes must not survive: this is the leak itself. -/
example :
    ((dirty 6 3).modes.insert && (dirty 6 3).modes.origin && (dirty 6 3).modes.mouse == 1000 &&
        (dirty 6 3).shiftOut) =
      true := by
  native_decide

example :
          (let v := screen 6 3 "hi"
           let w := (dirty 6 3).feed (restore v)
           w.modes == v.modes && w.g0Line == v.g0Line && w.shiftOut == v.shiftOut &&
        w.top == v.top &&
        w.bot == v.bot &&
        w.altGrid.isNone) =
      true := by
  native_decide

/-- A wide glyph and a combining mark, from a dirty start: the two shapes the
repaint is most sensitive to. -/
example : roundtripsFrom (dirty 6 3) (screen 6 3 "\u6f22e\u0301") = true := by native_decide

/-- And a session that *is* on the alt screen still restores into a dirty client. -/
example : roundtripsFrom (dirty 6 3) (screen 6 3 "ab\x1b[?1049hcd") = true := by native_decide

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
example :
    (((dirtyTabs 20 3).feed (restore (screen 20 3 "hi"))).tabs == (screen 20 3 "hi").tabs) =
      true := by
  native_decide

example : roundtripsFrom (dirtyTabs 20 3) (screen 20 3 "hi") = true := by native_decide

/-- The other direction too: a session with its own custom ruler, into a receiver
with a different one. -/
example : roundtripsFrom (dirtyTabs 20 3) (screen 20 3 "\x1b[3g\x1b[7G\x1bHhi") = true := by
  native_decide

/-- Non-vacuity, part one: a default-ruler session now emits a ruler at all. This is
the byte range the old guard skipped. -/
example : (tabsAnsi (screen 20 3 "hi")).isEmpty = false := by native_decide

/-- Non-vacuity, part two: **nothing before `tabsAnsi` clears a tab stop** — no
`TBC` in the prologue, and `ED 2` does not touch the ruler — so the emit is the only
thing standing between a client's ruler and the session's. -/
example :
    (((dirtyTabs 20 3).feed
            (prologueAnsi (screen 20 3 "hi") ++ csiNum 0 0x6D ++ csiNum 2 0x4A)).tabs ==
        (dirtyTabs 20 3).tabs) =
      true := by
  native_decide

/-! ### Non-vacuity of the receiver-quantified claims

`restore_sticky_any`'s hypotheses are all about the *session* — a region `DECSTBM`
will accept, parameters under the parser's clamp — plus one about the receiver's
height. **Nothing constrains the receiver's state**, so the claim is only worth
having if a receiver can actually differ from the session on every field in the
bundle. It can, and these are the witnesses; the theorem is that `∀ w`. -/

/-- Before: the `dirty` receiver differs from the session on the scroll region, the
G0 charset, the shift state and which screen is current — every group the bundle
names. -/
example :
          (let v := screen 20 3 "hi"
           let w := dirty 20 3
           (w.top != v.top) && (w.g0Line != v.g0Line) && (w.shiftOut != v.shiftOut) &&
        (w.altGrid.isSome != v.altGrid.isSome)) =
      true := by
  native_decide

/-- After: it agrees on all of them. -/
example :
          (let v := screen 20 3 "hi"
           let r := (dirty 20 3).feed (restore v)
           (r.top == v.top) && (r.bot == v.bot) && (r.g0Line == v.g0Line) &&
        (r.g1Line == v.g1Line) &&
        (r.shiftOut == v.shiftOut) &&
        (r.altGrid.isSome == v.altGrid.isSome)) =
      true := by
  native_decide

/-- The session-side hypotheses are met by an ordinary session, so the quantifier is
not empty. -/
example : (let v := screen 20 3 "hi"
           decide (v.top < v.bot) && decide (v.bot < v.rows)
             && decide (v.rows < 65535)) = true := by native_decide

/-- And the one case they exclude, named so it is not mistaken for an oversight: a
one-row session has `top = bot`, and `CSI 1 ; 1 r` is refused by this emulator and by
every real terminal, so there is no region to install. -/
example :
    (let v := screen 20 1 "hi";
      (v.top == v.bot)) =
      true := by
  native_decide

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
example :
          (let v := screen 6 3 "hi"
           let w := (feedStr (Vt.init 6 3) "\x1b]2;stale\x07").feed (restore v)
           w.title == v.title && v.title.isEmpty) =
      true := by
  native_decide

/-! ### The scrollback, in the receiver's own ring

`restore` used to repaint the screen and drop everything above it. It now paints
the session's ring into the *receiver's* scrollback — the only way a terminal
takes a line into its native history is to print it inside a whole-screen region
and let it scroll off — so wheel-scroll, search and selection find it.

Every receiver above has an **empty** ring, and so does every session above
(`Vt.scrollUpIn` pushes only from a whole-screen region on the main screen, which
none of them exercises, not even the `CSI 2;4r` one). So `replayEq`'s new conjunct
is vacuous for all thirty-seven of them, and the fixtures here are the whole
oracle. -/

/-- A session whose history really is in the ring: five lines through two rows
leaves `["aa", "bb", "cc"]` above the screen. -/
def scrolled : Vt := screen 6 2 "aa\r\nbb\r\ncc\r\ndd\r\nee"

/-- Non-vacuity, part one: the session's ring is not empty, and the emitter's view
of it is the same three rows. -/
example : (scrolled.sb.size == 3 && (sbRows scrolled).size == 3) = true := by native_decide

/-- **The emitter's view of the ring, against a literal.** Oldest first. Dropping
`sbRows`' outer `.reverse` plays the history backwards and `replayEq` does *not*
notice — it compares against `sbRows v`, which the same bug reverses — so this is
the fixture that catches it.  -/
example : ((sbRows scrolled).toList.map rowStr == ["aa", "bb", "cc"]) = true := by native_decide

/-- `fitRow_id_of_rowOk` in executable form: on the rows a live session stores the
fit is the identity, so comparing a receiver's ring against `sbRows v` is the
session's own history and not a weakened target. (A *decoded checkpoint's* ring is
where the fit has work to do — see `hostileRing` below.) -/
example : ((sbRows scrolled).toList == scrolled.sb.toList) = true := by native_decide

/-- **The trim drops the oldest first.** A fitted 6-column row costs 12, so a
budget of 27 admits two of the three: the survivors are the **newest** two, still
oldest-first. -/
example : ((sbTake 6 27 scrolled.sb.toList.reverse).reverse.map rowStr == ["bb", "cc"]) = true := by
  native_decide

/-- …and the wrong-order bug named as a fact, since it is the insidious one:
feeding `v.sb.toList` rather than its reverse keeps the **oldest** two under the
same budget. Both variants produce three rows whenever the whole ring fits, which
is why every fixture but this one would have passed. -/
example : ((sbTake 6 27 scrolled.sb.toList).map rowStr == ["aa", "bb"]) = true := by native_decide

/-- A previous occupant that left **its own** history in the window — the ring
analogue of `dirtyTabs`, and the receiver that makes the `ED 3` question real. -/
def dirtySb (cols rows : Nat) : Vt := feedStr (Vt.init cols rows) "OLD1\r\nOLD2\r\nOLD3\r\nJUNK"

/-- The hazard itself: the receiver's ring is non-empty and is *not* the
session's. -/
example : ((dirtySb 6 2).sb.size == 2) = true := by native_decide

example : (((dirtySb 6 2).sb.toList) == (sbRows scrolled).toList) = false := by native_decide

/-- **The headline.** `Render.history` is `v.sb.toList ++ v.grid.toList`, so this
one string spans the replayed history *and* the screen: a wrong flush count shows
up as a wrong string rather than a wrong length. The two off-by-one twins, for the
record: a flush of `rows - 1` gives `"aa\nbb\ndd\nee\n"` (the newest history row
never leaves the screen, and the screen paint overwrites it) and `rows + 1` gives
`"aa\nbb\ncc\n\ndd\nee\n"` (one spurious blank row, pushed *after* the newest
history row and carrying the pen the last painted row left in effect). -/
example :
    (String.fromUTF8! ⟨(history ((dirtySb 6 2).feed (restore scrolled))).toArray⟩ ==
        "aa\nbb\ncc\ndd\nee\n") =
      true := by
  native_decide

example : roundtripsFrom (dirtySb 6 2) scrolled = true := by native_decide

/-- Into a pristine client too, and into one caught mid-OSC — the push now sits
*inside* the byte range a swallowed stream would eat (`cd7c17b`), so this is not a
duplicate of the fixture above. -/
example : roundtrips scrolled = true := by native_decide

example : roundtripsFrom (midOsc 6 2) scrolled = true := by native_decide

example : roundtripsFrom (dirty 6 2) scrolled = true := by native_decide

/-- **Idempotent.** A second attach must not stack a second copy of the history —
that is what the `ED 3` is for, and without it this is `["OLD1", "OLD2", "aa",
"bb", "cc", "aa", "bb", "cc"]`. -/
example :
    ((((dirtySb 6 2).feed (restore scrolled)).feed (restore scrolled)).sb.toList ==
        (sbRows scrolled).toList) =
      true := by
  native_decide

/-- **The guard, stated as a promise.** `ED 3` erases the saved lines of the
window the client is running in, and that window's scrollback belongs to the
*user*, shared with their shell — session attachment uses the main screen. So it is
emitted only when there is history to put there: attaching a session that never
scrolled leaves the user's own history alone. (Unguarded, this is `[]`.) -/
example :
    (((dirtySb 6 2).feed (restore (screen 6 2 "hi"))).sb.toList == (dirtySb 6 2).sb.toList) =
      true := by
  native_decide

example : ((sbRows (screen 6 2 "hi")).isEmpty && (sbRows (screen 6 4 "hi")).isEmpty) = true := by
  native_decide

/-- …and the anti-stacking property survives the guard, because a session with no
ring pushes nothing that could stack. -/
example :
    ((((dirtySb 6 4).feed (restore (screen 6 4 "hi"))).feed
            (restore (screen 6 4 "hi"))).sb.toList ==
        (dirtySb 6 4).sb.toList) =
      true := by
  native_decide

/-- `ED 3` is emitted **after** the `ED 2`, which is the order ncurses `clear(1)`
sends (`CSI H CSI 2 J CSI 3 J`). Not decoration: our mode 3 erases the screen as
well as the saved lines (`Vt.eraseScreen`), and it is the `ED 2` four bytes
earlier that makes that surplus erase unobservable. -/
example : (let r := restore scrolled
           let idx := fun (needle : Bytes) =>
             (List.range (r.length + 1 - needle.length)).find?
               (fun i => (r.drop i).take needle.length == needle)
           match idx (csiNum 2 0x4A), idx (csiNum 3 0x4A) with
           | some a, some b => decide (a < b)
           | _, _ => false) = true := by native_decide

/-- A **wide glyph and a combining mark in the ring**, not on the screen: the two
shapes the row painter is most sensitive to, now replayed through `fitRow` as
well. -/
example : roundtripsFrom (dirtySb 8 2) (screen 8 2 "a漢b\r\néx\r\nzz\r\nq1\r\nq2") = true := by
  native_decide

/-- Colour through the ring, and the pen of the newest history row preserved
cell-for-cell — a history repainted in the wrong pen would still give the right
`history` string. -/
def colScrolled : Vt := screen 6 2 "\x1b[48;5;196mAA\r\nBB\r\nCC\r\nDD\r\nEE"

example : roundtripsFrom (dirtySb 6 2) colScrolled = true := by native_decide

example :
          (let r := (dirtySb 6 2).feed (restore colScrolled)
           (r.sb.toList.getLast!.at 0).pen == (colScrolled.sb.toList.getLast!.at 0).pen &&
        !((r.sb.toList.getLast!.at 0).pen == ({} : Pen))) =
      true := by
  native_decide

/-! #### The fit is mandatory, not hygiene

`Vt.resize` re-fits the grid and leaves `sb` alone, so a resized session's ring
rows are the *old* width. `fitRow` is what makes the replayed rows the session's
width, and `rowOk_fitRow` is unconditional — which is what keeps every hypothesis
about the ring out of the screen theorems. -/

def shrunk : Vt := (screen 8 2 "abcdefgh\r\n22\r\n33\r\n44").resize 4 2

/-- The hazard: the ring still holds 8-wide rows. -/
example : (shrunk.sb.toList.all (fun r => r.size == 4)) = false := by native_decide

/-- The fit: what the receiver is sent is 4 wide. -/
example : ((sbRows shrunk).toList.all (fun r => r.size == 4)) = true := by native_decide

example : roundtripsFrom (dirtySb 4 2) shrunk = true := by native_decide

/-- **A wide pair in the ring, against literals.** `cellFit`'s width-0 branch is
load-bearing: collapse a shadow to `charWidth ' ' = 1` and `Row.mend` sees a half
pair and blanks the base, so the glyph is *lost*. `replayEq` cannot see that
either — it compares against `sbRows`, which the same break rewrites. -/
def wideRing : Vt := screen 8 2 "a漢b\r\néx\r\nzz\r\nq1\r\nq2"

example : ((sbRows wideRing).toList.map rowStr == ["a漢b", "éx", "zz"]) = true := by native_decide

/-- …and the pair is still a pair: a width-2 base followed by its width-0 shadow. -/
example :
    (((sbRows wideRing).toList.head!.toList.map (fun c => c.width)).take 3 == [1, 2, 0]) =
      true := by
  native_decide

example : roundtripsFrom (dirtySb 8 2) wideRing = true := by native_decide

/-- **The ring is the one place no invariant covers**, which is what the fit is for
and why `rowOk_fitRow` may have no hypothesis. `Checkpoint.load` reads cells from
arbitrary bytes and is total by design, so a ring row can hold a C0 control
codepoint (unrepaintable — `Render.safeChar` would substitute it on emit, so the
replayed screen would differ from the live one) and a mark that is neither
zero-width nor printable. `cellFit` substitutes and filters; a bare
`Vt.resizeRow` copies both through, and **no other fixture notices** — a live
session's ring rows are already reproducible, so the two agree on every one of
them. -/
def hostileRing : Vt :=
  { screen 4 2 "hi" with
    sb :=
      {
        data :=
          #[#[{ base := '\x01', width := 1 }, { base := 'x', marks := ['A'], width := 1 },
              { base := 'y', width := 1 }, { base := 'z', width := 1 }]],
        start := 0 } }

example : (let r := (sbRows hostileRing).toList.head!
           (r.at 0).base == '�' && (r.at 1).marks.isEmpty && r.size == 4) = true := by
  native_decide

/-! #### The byte budget — a correctness requirement, not prudence

`outbufCap = 4194304` **disconnects** a client on undrained bytes
(`Linger/Runtime/Daemon.lean`), and a full `sbCap = 10000` ring of per-cell
truecolour rows is 32–46 MB at 80 columns. So the trim is what stands between a
reattach and an attach-then-instant-drop.

`sbTake_budget`/`sbRows_budget` bound the **counted** cost `sbRowCost`;
`scrollbackAnsi_le_cost` now proves the whole emitted stage is bounded by
`Σ sbRowCost (sbRows v) + 2 * v.rows + 19`, and `scrollbackAnsi_le` substitutes
`sbReplayBytes` for the sum. These fixtures additionally show the bound is
**sharp** — attained with zero slack by the adversarial ring below. They do not
bound the separate visible screen paints. -/

def ringOf (cols rows : Nat) (mk : Nat → Row) (n : Nat) : Vt :=
  { screen cols rows "" with sb := { data := (Array.range n).map mk, start := 0 } }

def costSum (v : Vt) : Nat := ((sbRows v).toList.map sbRowCost).sum

/-- The whole-stream bound, in the form that is actually true. -/
def stageInBudget (v : Vt) : Bool :=
  decide ((scrollbackAnsi v).length ≤ costSum v + 2 * v.rows + 19) &&
    decide (costSum v ≤ sbReplayBytes)

/-- 300 rows of per-cell truecolour through 40 columns: the pen changes at every
cell, so no `SGR` is shared. -/
def heavyRow (cols : Nat) (i : Nat) : Row :=
  (Array.range cols).map
    (fun j =>
      { base := 'x', width := 1,
        pen :=
          { fg := .rgb (UInt8.ofNat ((i + j) % 256)) 20 30,
            bg := .rgb 40 (UInt8.ofNat (j % 251)) 60 } })

def heavyRing : Vt := ringOf 40 24 (heavyRow 40) 300

/-- Non-vacuity: the trim actually bites — 174 of 300 rows survive the budget. -/
example :
    (decide ((sbRows heavyRing).size < heavyRing.sb.size) && (sbRows heavyRing).size == 174) =
      true := by
  native_decide

/-- A row's identity, for the fixture below: `heavyRow i` puts `i` in its first
cell's red channel, so a run of kept rows can be named. -/
def fstFg (r : Row) :
    Nat := match (r.at 0).pen.fg with
  | .rgb a _ _ => a.toNat
  | _ => 999

/-- **Which rows survived, asserted through `sbRows` itself.** The two `sbTake`
anchors above spell the `.reverse` out in the fixture, so they *document* the trim
rather than guard it: drop `sbRows`' own reverses and both still pass. This pins the
identity of the kept run — the **newest** 174 of 300 (`i = 126…299`, so red channel
126…43 after the `% 256` wrap), oldest-first. Dropping either reverse, or trimming
the oldest end instead of the newest, moves these four numbers. -/
example :
    (((sbRows heavyRing).toList.map fstFg).take 2 == [126, 127] &&
        ((sbRows heavyRing).toList.map fstFg).reverse.take 2 == [43, 42]) =
      true := by
  native_decide

/-- The counted cost, and the emitted length of the whole reattach burst. The
number is here rather than `sbReplayBytes` because the emitted stage is **not**
bounded by the budget — only by the budget plus `2 * rows + 19`. -/
example :
    (costSum heavyRing == 260844 && (scrollbackAnsi heavyRing).length == 260219 &&
        (restore heavyRing).length == 261417 &&
        stageInBudget heavyRing) =
      true := by
  native_decide

/-- 84 default-pen cells then one truecolour cell — a line of plain text ending in
a coloured token. Every row after the first therefore pays the full `penSgr {}`
that `sbRowCost`'s `+ 4` accounts for, which is what makes this the sharp case. -/
def advRow (cols : Nat) : Row :=
  (Array.range cols).map
    (fun i =>
      if i + 1 < cols then ({ base := 'a', width := 1 } : Cell)
      else { base := 'z', width := 1, pen := { fg := .rgb 1 2 3, bg := .rgb 4 5 6 } })

def advRing : Vt := ringOf 85 24 (fun _ => advRow 85) 3000

/-- **The overshoot, measured.** The stage emits 262153 bytes against a
`sbReplayBytes` of 262144 — nine bytes over. A bound stated against
`sbReplayBytes` alone would be false here, and no "budget to `1 <<< 30`" break
would catch it. The whole-stage bound is attained with **zero** slack.
Check these facts together to reuse the large fixture's computed lengths. -/
example :
    (decide ((scrollbackAnsi advRing).length > sbReplayBytes) &&
        (scrollbackAnsi advRing).length == 262153 &&
        costSum advRing == 262086 &&
        (scrollbackAnsi advRing).length == costSum advRing + 2 * advRing.rows + 19 &&
        stageInBudget advRing) =
      true := by
  unfold stageInBudget
  native_decide

/-- The remaining ring shapes: empty, blank and a realistic mixed row. The heavy
and adversarial cases check the same bound beside their exact lengths above. -/
example :
    (stageInBudget (screen 80 24 "hi") &&
        stageInBudget (ringOf 80 24 (fun _ => blankRow 80 {}) 10000) &&
        stageInBudget scrolled) =
      true := by
  native_decide

/-- The empty guard is load-bearing (`broadcast_empty`, one module over): with no
history the stage is twelve mode bytes and nothing else — no `ED 3`, no paint, no
flush. -/
example :
    ((scrollbackAnsi (screen 80 24 "hi")).length == 14 && (sbRows (screen 80 24 "hi")).isEmpty) =
      true := by
  native_decide

/-! ### The hand-back (§Handback, anchor A5's outbound half)

The mirror image of everything above. `restore` establishes what the repaint needs in
whatever terminal it is given; `leaveAnsi` gives that terminal back to the user's
shell in a state the next program can use, whatever the session's last program left
behind. `leave_grounds` proves the parser half for every receiver; these pin the
values until the `Sets` instances land (`specs/archive/restore-conformance.md` Step 1). -/

/-- The canonical state a detaching client owes the next program. `rows` is a
parameter because two of the fields are dimension-relative: the scroll region is the
whole screen, and the cursor is parked on the last row. -/
def sane (rows : Nat) (w : Vt) : Bool :=
  w.pstate == PState.ground && w.modes == ({} : Modes) && !w.g0Line && !w.g1Line && !w.shiftOut &&
    w.top == 0 &&
    w.bot == rows - 1 &&
    w.altGrid.isNone &&
    w.pen == ({} : Pen) &&
    w.cursor.x == 0 &&
    w.cursor.y == rows - 1

/-- A dirty client is not sane, or the checks below would hold vacuously. -/
example : sane 3 (dirty 6 3) = false := by native_decide

example : sane 3 ((dirty 6 3).feed leaveAnsi) = true := by native_decide

/-- …from every parser state a dying program can leave, too. -/
example : sane 3 ((midOsc 6 3).feed leaveAnsi) = true := by native_decide

/-- Step 2 at witnesses: a receiver caught mid-UTF-8, mid-OSC or mid-CSI is left
*quiesced* by `restore` — parser `ground`, nothing half-decoded — which is what
`restore_quiesced_any` says for all of them, and what `restore_quiesced` (fresh
`Vt.init` only) could not. -/
example : (let v := screen 6 3 "hi"
           ((midUtf8 6 3).feed (restore v)).pstate == PState.ground
             && ((midUtf8 6 3).feed (restore v)).u8need == 0
             && ((midOsc 6 3).feed (restore v)).pstate == PState.ground
             && ((midCsi 6 3).feed (restore v)).u8need == 0) = true := by native_decide

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
example : (((dirty 6 3).feed leaveAnsi).modes == ((midDcs 6 3).feed leaveAnsi).modes) = true := by
  native_decide

/-! ## `screenText` — the capture stream, exact bytes (specs/archive/agent-cli.md) -/

/-- The freeze: grid only, `rowText` per row (trailing blanks trimmed), one LF
each — a 4×2 screen holding "ab" is literally `a b LF LF`. -/
example : screenText (screen 4 2 "ab") = [0x61, 0x62, 0x0A, 0x0A] := by native_decide

/-- Grid-only, pinned against `history` on the same state: eight lines through
a five-row screen leave a capture of exactly five lines while the transcript
keeps all eight. -/
example :
    (let v := screen 20 5 (String.intercalate "\r\n" ((List.range 8).map (fun i => s!"l{i}")))
     (screenText v).count 0x0A == 5 && (history v).count 0x0A == 8) =
      true := by
  native_decide

/-- A control character smashed into a cell (unreachable live, but a decoded
checkpoint's grid is arbitrary) cannot forge a capture line: it emits as
U+FFFD and the line count stays the row count. -/
example :
    (let v := screen 10 2 "ab"
     let row := (v.grid.getD 0 #[]).setIfInBounds 1 { base := '\x0A' }
      let v2 := { v with grid := v.grid.setIfInBounds 0 row }
      (screenText v2).count 0x0A == 2) =
      true := by
  native_decide

/-- `linesLF`, the consumer-side splitter the parse contract is stated
against: one record per LF, an unterminated tail still counts (a parser does
not discard bytes for a missing terminator), and no trailing phantom record
after a final LF. -/
example : linesLF [0x61, 0x0A, 0x62, 0x63, 0x0A] = [[0x61], [0x62, 0x63]] := by native_decide

example : linesLF [0x61, 0x0A, 0x62] = [[0x61], [0x62]] := by native_decide

example : linesLF [0x0A, 0x0A] = [[], []] := by native_decide

example : linesLF [] = [] := by native_decide

/-- The parse contract on a concrete screen: splitting the capture gives the
rows, in order — `screenText_records`' shape, evaluated. -/
example :
    (linesLF (screenText (screen 20 3 "one\r\ntwo")) ==
          [(screen 20 3 "one\r\ntwo").grid.toList.map rowText].flatten &&
        (String.fromUTF8?
                (ByteArray.mk
                  (linesLF (screenText (screen 20 3 "one\r\ntwo")) |>.getD 1 []).toArray)).getD
            "" ==
          "two") =
      true := by
  native_decide

end Linger.Core.Render.Tests
