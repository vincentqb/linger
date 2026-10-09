module

public import E2E.Harness
public import Linger.Core.Terminal

public section

/-! # E2E.Graphics — kitty (APC) and sixel (DCS) image passthrough

Ported from `tests/graphics_test.py`. What linger promises here, and what it does
not:

* live, while attached: image bytes reach the client's terminal VERBATIM. The
  bounded terminal mediator recognizes only its owned query profile and emits every
  unowned APC/DCS byte unchanged; kitty/sixel enter payload-free passthrough
  states, so no opt-in switch is needed.
* the emulator IGNORES the payload (parser state `.str` until ST) and accumulates
  nothing, so a megabyte of base64 cannot grow the session or reach the checkpoint
  (§Bound).
* after detach/reattach: images are GONE. `restore` repaints from the cell grid,
  and cells hold no image data. The text screen comes back; the picture does not.

The third is the documented limitation (`linger help`, and the settled non-goal
in AGENTS.md). This suite exists so the first two cannot regress silently — a
future "render from the grid instead of broadcasting" optimization would break
images with no other test noticing.

BYTES, AND WHERE THEY COME FROM. The framing is the implementation's: ST is
`Render.escSeq Terminal.STFinal`, and the two introducers are `Render.escSeq` of
the finals `Vt.escFinal` routes into the payload-free `.str` state. The payload
bodies cannot be derived from anything — nothing in this repo emits kitty or sixel,
by design, since the emulator's whole job here is to skip them — so they stay
literals, which makes them fixture data rather than a stale copy of an emitter. -/

namespace E2E.Graphics

open E2E.Harness
open Linger.Core.Render (escSeq)
open Linger.Core.Terminal (STFinal)

/-- ST, the terminator both protocols end with, spelled as the mediator spells its
own byte. -/
def stB : List UInt8 := escSeq STFinal

/-- `ESC _`, the APC introducer (kitty). -/
def apcB : List UInt8 := escSeq 0x5F

/-- `ESC P`, the DCS introducer (sixel). -/
def dcsB : List UInt8 := escSeq 0x50

def kittyBytes : List UInt8 := apcB ++ "Gi=31,a=T,f=24,s=1,v=1;GFXPAYLOAD".toUTF8.toList ++ stB

def sixelBytes : List UInt8 := dcsB ++ "q#0;2;0;0;0#0~~@@vv@@~~$".toUTF8.toList ++ stB

/-- The commands that put those bytes on the wire, via `/bin/sh`'s `printf`.
The payload marker is octal-encoded because the shell ECHOES the command line: a
literal marker would appear in the text grid as echoed input and the `history`
check below would pass for the wrong reason (it did, the first time round). -/
def kittyCmd : String :=
  "printf '\\033_Gi=31,a=T,f=24,s=1,v=1;\\107\\106\\130\\120\\101\\131\\114\\117\\101\\104\\033\\134'"

def sixelCmd : String := "printf '\\033Pq#0;2;0;0;0#0~~@@vv@@~~$\\033\\134'"

/-- How many SIGWINCHes the reporter has logged. A missing file is none yet, the
honest reading before its first signal. -/
def winchCount (path : System.FilePath) : IO Nat := do
  try
    let s ← IO.FS.readFile path
    return (s.toList.filter (· == 'W')).length
  catch _ =>
    return 0

def run : IO UInt32 := do
  let e ← Env.make "gfx"
  let mut f := 0
  let c ← e.spawn #["attach", "gfx"] 80 24
  IO.sleep 800
  let _ ← drain c.fd 400
  -- 1+2. both protocols arrive verbatim at the attached client
  c.type (kittyCmd ++ "\r")
  IO.sleep 500
  let out ← drain c.fd 600
  f := f + (← expect (hasBytes out kittyBytes) "kitty APC graphics pass through verbatim")
  c.type (sixelCmd ++ "\r")
  IO.sleep 500
  let out ← drain c.fd 600
  f := f + (← expect (hasBytes out sixelBytes) "sixel DCS graphics pass through verbatim")
  -- 3. the session is not wedged by either payload. Assert on the EXPANSION, not
  -- the typed text: the shell echoes what it was given, and the arithmetic result
  -- is the discriminating string.
  c.type "echo gfx-alive-$((20+22))\r"
  IO.sleep 600
  let out ← drain c.fd 800
  f := f + (← expect (hasText out "gfx-alive-42") "session still live after image payloads")
  -- 4. the emulator ignored the payload rather than printing it
  f :=
    f +
      (←
        expect (!has (← e.out #["capture", "--history", "gfx"]) "GFXPAYLOAD")
            "image payload does not land in the text grid")
  -- 5. detach, reattach: the text screen restores and the parser is sane. The
  -- image is gone — the documented limitation, asserted here so the help and the
  -- behaviour cannot drift apart.
  c.bye
  let c2 ← e.spawn #["attach", "gfx"] 80 24
  IO.sleep 1000
  let restored ← drain c2.fd 800
  f := f + (← expect (hasText restored "gfx-alive-42") "text screen restores after reattach")
  f :=
    f +
      (←
        expect (!hasBytes restored kittyBytes)
            "images are NOT replayed on reattach (documented limitation)")
  c2.type "echo after-reattach-$((21+21))\r"
  IO.sleep 600
  let out ← drain c2.fd 800
  f := f + (← expect (hasText out "after-reattach-42") "parser sane after a restore")
  c2.bye
  e.killAll #["gfx"]
  -- 6+7. The repaint shortcut: an application that redraws brings its OWN images
  -- back, and what makes it redraw is SIGWINCH. We deliver that by resizing the pty
  -- for the size-owning client on attach, so a reattach at a NEW size nudges the
  -- program; at the same size the kernel suppresses the signal (`tty_do_resize`
  -- compares the winsize first) and nothing redraws.
  --
  -- Both halves are asserted because the ASYMMETRY is the user-visible rule. The
  -- reporter logs to a FILE — anything on stdout would be replayed by `restore` and
  -- could not be told apart from a fresh signal — and runs in the FOREGROUND, since
  -- a background process group gets no SIGWINCH at all.
  let wlog := (System.FilePath.mk e.dir) / "winch"
  -- `sleep` is not interruptible, so a bare `trap; while :; do sleep; done` never
  -- runs the handler — measured, it caught zero signals. POSIX `wait` IS
  -- interrupted by a trapped signal, so the sleep goes in the background and the
  -- shell blocks in `wait`: that catches every WINCH.
  let reporter := s!"trap 'printf W >> {wlog.toString}' WINCH; while :; do sleep 1 & wait; done\r"
  let w1 ← e.spawn #["attach", "winch"] 80 24
  IO.sleep 1200
  w1.type reporter
  IO.sleep 1000
  let _ ← drain w1.fd 400
  let base ← winchCount wlog
  w1.bye
  let w2 ← e.spawn #["attach", "winch"] 80 24
  IO.sleep 1600
  let _ ← drain w2.fd 400
  let same ← winchCount wlog
  f := f + (← expect (same == base) "same-size reattach delivers no SIGWINCH (no redraw)")
  w2.bye
  let w3 ← e.spawn #["attach", "winch"] 100 30
  IO.sleep 1600
  let _ ← drain w3.fd 400
  let grown ← winchCount wlog
  f := f + (← expect (grown > same) "reattach at a new size nudges the program (SIGWINCH)")
  w3.bye
  e.killAll #["winch"]
  verdict e f

end E2E.Graphics
