module

public import E2E.Harness

public section

/-! # E2E.Agent — the agent verbs: see and drive a session one-shot

Ported from `tests/agent_test.py`; the spec is `specs/archive/agent-cli.md`.

Step 1: `linger info <name>` and the observability fields — geometry + cursor
(what `capture` needs), `alt`, and `outseq` (the change cursor: "look again only
when it moved"). Step 2: `linger capture <name>` — the screen as plain text, one
line per row, and capturing marks the session seen. Step 3: `linger send <name> -`
— stdin to the pty byte-exact (the oracles assert on shell *expansions*: the tty
echoes typed input onto the screen, so a typed-text marker would pass even if the
bytes never ran; see SCRATCHPAD 2026-08-19). Step 4: `linger resize` — applies
detached (down to the child's own winsize, via `stty size`), refused while a
client is attached. All pinned against the rendered porcelain/bytes, end to end.

WHAT THE PORT TIGHTENED, and what it could not — read before adding a check:

* every geometry assertion compares against the number this suite *asked* for
  (the `let`s below), not against a second copy of it spelled out as a string;
* the oversize `resize` probe is derived from `Vt.clampDim` instead of the flat
  `5000` the Python used. `clampDim` saturates, so `clampDim n + 1` is the
  SMALLEST value the client must reject — the boundary, not a value well past
  it. If `Cli`'s own `1000` literal ever drifts from `clampDim`'s range, this
  is the check that fails;
* `alt` and `unseen` compare to `toString false` / `toString true`, because that
  is literally what `Session.infoFields` emits (`toString` of a `Bool`);
* the 80×24 default could NOT be tied to anything: it is a literal
  `Vt.init 80 24` inside `Daemon.serve`, so a Lean-side tie would restate the
  constant rather than derive it;
* "capture is exactly one line per row" could not be tied to
  `Render.screenText` either — the row count is a property of a `Vt` this
  process does not hold. `rows` comes from the session's own `info`, which is as
  close as the porcelain gets. -/

namespace E2E.Agent

open E2E.Harness

/-- Python's `.isdigit()` and `int(...)` in one move: `String.toNat?` is `none`
for the empty string and for anything carrying a non-digit, which is exactly what
`''.isdigit()` being False stood for at the two "is reported as a number" checks. -/
def num (o : Option String) : Option Nat := o.bind (·.toNat?)

/-- `linger send <name> -` with `payload` on its stdin, byte-exact.

`IO.Process.output`'s `input?` argument *is* the mechanism, so no new harness
primitive is needed: core spawns with `stdin := .piped`, `takeStdin`s the handle
away from the `Child`, writes, flushes, and then drops it — and dropping the last
reference is what closes the pipe. That close is load-bearing, not hygiene:
`Cli.cmdSendStdin` has **no timeout on purpose** ("a slow producer feeding a pipe
is legitimate, and EOF is the only exit"), so a port that kept the handle alive
would hang here instead of failing.

`putStr` writes the payload's UTF-8, and all three payloads below are ASCII or a
single C0 byte, so the bytes on the pipe are the Python's bytes exactly. A
payload that is not valid UTF-8 would need `spawn` + `takeStdin` + `Handle.write`
on a `ByteArray`; nothing here does. -/
def sendStdin (e : Env) (name payload : String) : IO UInt32 := do
  let out ← IO.Process.output
    { cmd := e.bin, args := #["send", name, "-"], env := e.procEnv } (some payload)
  return out.exitCode

def run : IO UInt32 := do
  let e ← Env.make "agent"
  let mut f := 0

  -- ── Step 1: info ──────────────────────────────────────────────────────────

  let _ ← e.cli #["run", "ag", "true"]      -- upsert a headless session (default shell)
  IO.sleep 1500

  f := f + (← expect ((← e.info "ag" "cols") == some "80"
                      && (← e.info "ag" "rows") == some "24")
    "headless session reports the 80x24 default size")
  f := f + (← expect ((← e.info "ag" "alt") == some (toString false))
    "alt is false outside a full-screen app")
  f := f + (← expect ((num (← e.info "ag" "cursorx")).isSome
                      && (num (← e.info "ag" "cursory")).isSome)
    "cursor position is reported as numbers")
  f := f + (← expect ((num (← e.info "ag" "outseq")).isSome)
    "outseq is reported as a number")

  -- outseq moves when output happens — the change cursor
  let before := (num (← e.info "ag" "outseq")).getD 0
  let _ ← e.cli #["run", "ag", "echo", "MOVED"]
  IO.sleep 1200
  let after := (num (← e.info "ag" "outseq")).getD 0
  f := f + (← expect (after > before) "outseq increases after output")

  -- geometry follows an attached terminal. `Env.spawn` sets the winsize BEFORE
  -- exec, so the `pty.fork()`-then-`ioctl(TIOCSWINSZ)` race the Python had
  -- against the client's own startup `winsizeGet` is gone — and this check is
  -- the one whose subject is precisely the size a client reported.
  let attCols : UInt32 := 100
  let attRows : UInt32 := 30
  let cl ← e.spawn #["attach", "ag"] attCols attRows
  IO.sleep 1500
  f := f + (← expect ((← e.info "ag" "cols") == some (toString attCols)
                      && (← e.info "ag" "rows") == some (toString attRows))
    "info reflects the attached terminal size")
  cl.bye                                    -- detach, close, reap

  -- info against a missing session fails cleanly. The quoted name is part of
  -- the message `requireLiveBounded` prints, so the port pins it: the Python
  -- accepted any "no session" text at all.
  let (irc, _, ierr) ← e.cli #["info", "nosuch"]
  f := f + (← expect (irc == 1 && has ierr "no session 'nosuch'")
    "info on a missing session exits 1 with a message")

  -- ── Step 2: capture ───────────────────────────────────────────────────────

  let _ ← e.cli #["run", "ag", "echo", "CAPTURED-MARKER"]
  IO.sleep 1200

  let (capRc, capOut, _) ← e.cli #["capture", "ag"]
  let lines := capOut.splitOn "\n"
  let rows := (num (← e.info "ag" "rows")).getD 0
  f := f + (← expect (capRc == 0 && has capOut "CAPTURED-MARKER")
    "capture shows what the session printed")
  -- screenText is LF-terminated per row: split yields rows + one trailing ''
  f := f + (← expect (lines.length == rows + 1 && lines.getLast? == some "")
    "capture is exactly one line per row")

  -- capture marks the session seen (the porcelain unseen flag flips)
  f := f + (← expect ((← e.info "ag" "unseen") == some (toString false)
                      && num (← e.info "ag" "behind") == some 0)
    "capture marks the session seen")
  let _ ← e.cli #["run", "ag", "echo", "again"]
  IO.sleep 1200
  f := f + (← expect ((← e.info "ag" "unseen") == some (toString true))
    "output after a capture reads unseen again")

  -- capture is the screen, not the transcript: flood past one screen and the
  -- capture stays `rows` lines while history grows beyond it
  let _ ← e.cli #["run", "ag", "seq", "1", "60"]
  IO.sleep 1500
  let cap2 := (← e.out #["capture", "ag"]).splitOn "\n"
  let hist := (← e.out #["history", "ag"]).splitOn "\n"
  f := f + (← expect (cap2.length == rows + 1 && hist.length > cap2.length)
    "capture stays screen-sized while history grows")

  f := f + (← expect ((← e.cli #["capture", "nosuch"]).1 == 1)
    "capture on a missing session exits 1")

  -- ── Step 3: send - (raw stdin) ────────────────────────────────────────────

  -- a full command line with its newline arrives verbatim and executes. The
  -- marker is asserted on the *expansion* (GOT-42), which the typed line does
  -- not contain — the tty echoes typed input onto the screen, so asserting on
  -- the typed text would pass even if the newline was lost and nothing ran.
  let src ← sendStdin e "ag" "echo \"GOT-$((40+2))\"\n"
  IO.sleep 1200
  f := f + (← expect (src == 0 && has (← e.out #["capture", "ag"]) "GOT-42")
    "send - delivers bytes verbatim (newline included: it ran)")

  -- a control byte works: ^C interrupts a foreground child, after which the
  -- queued next line is read and runs (same trick: the typed line says
  -- INTER""RUPTED-OK, only the executed output says INTERRUPTED-OK)
  let _ ← e.cli #["run", "ag", "sleep", "100"]
  IO.sleep 1000
  let _ ← sendStdin e "ag" "\x03"
  IO.sleep 500
  let _ ← e.cli #["run", "ag", "echo", "INTER\"\"RUPTED-OK"]
  IO.sleep 1200
  f := f + (← expect (has (← e.out #["capture", "ag"]) "INTERRUPTED-OK")
    "send - carries ^C (the sleep died, the shell came back)")

  -- empty stdin is a clean no-op
  f := f + (← expect ((← sendStdin e "ag" "") == 0)
    "send - with empty stdin exits 0")

  f := f + (← expect ((← sendStdin e "nosuch" "x") == 1)
    "send - on a missing session exits 1")

  e.killAll #["ag"]

  -- ── Step 4: resize ────────────────────────────────────────────────────────

  let _ ← e.cli #["run", "rz", "true"]
  IO.sleep 1500

  let rzCols : UInt32 := 120
  let rzRows : UInt32 := 40
  let (rrc, _, _) ← e.cli #["resize", "rz", toString rzCols, toString rzRows]
  IO.sleep 1000
  f := f + (← expect (rrc == 0
                      && (← e.info "rz" "cols") == some (toString rzCols)
                      && (← e.info "rz" "rows") == some (toString rzRows))
    "control resize applies to a detached session")

  -- the pty winsize followed too: the child's own stty sees it (SIGWINCH path).
  -- `stty size` prints rows then cols, so the expected string is built from the
  -- two numbers above rather than being a third copy of them.
  let _ ← e.cli #["run", "rz", "stty", "size"]
  IO.sleep 1200
  f := f + (← expect (has (← e.out #["capture", "rz"]) s!"{rzRows} {rzCols}")
    "the child observes the new winsize (stty size: 40 120)")

  -- an attached client owns the size: refused, loudly, and nothing moves
  let ownCols : UInt32 := 80
  let ownRows : UInt32 := 24
  let owner ← e.spawn #["attach", "rz"] ownCols ownRows
  IO.sleep 1500
  let newCols : UInt32 := 90
  let newRows : UInt32 := 25
  let (frc, _, ferr) ← e.cli #["resize", "rz", toString newCols, toString newRows]
  f := f + (← expect (frc == 1 && has ferr "owns the size")
    "resize is refused while a client is attached")
  f := f + (← expect ((← e.info "rz" "cols") == some (toString ownCols))
    "a refused resize moved nothing")
  owner.bye

  let (arc, _, _) ← e.cli #["resize", "rz", toString newCols, toString newRows]
  IO.sleep 800
  f := f + (← expect (arc == 0 && (← e.info "rz" "cols") == some (toString newCols))
    "resize applies again once the client detached")

  -- client-side validation: 1..1000 (clampDim's range). Both probes are the
  -- boundary itself: 0 is the largest rejected value below the range, and
  -- `clampDim` saturating means `clampDim 5000 + 1` is the smallest rejected
  -- value above it. The Python's flat 5000 could not tell "the CLI rejects
  -- 1001" from "the CLI rejects some number far outside".
  let tooBig := Linger.Core.Vt.clampDim 5000 + 1
  let (zrc, _, _) ← e.cli #["resize", "rz", "0", "10"]
  let (brc, _, _) ← e.cli #["resize", "rz", toString tooBig, "10"]
  f := f + (← expect (zrc == 2 && brc == 2)
    "zero and oversize are rejected client-side")
  f := f + (← expect ((← e.cli #["resize", "nosuch", "80", "24"]).1 == 1)
    "resize on a missing session exits 1")

  e.killAll #["rz"]
  verdict f

end E2E.Agent
