module

public import E2E.Harness
public import Linger.Core.Terminal

public section

/-! # E2E.Terminal — the bounded terminal mediator, with 0, 1 and 2 clients

Ported from `tests/terminal_query_test.py`.

The probe is an ordinary foreground pty program, not a shell detector. It puts its
tty in raw mode, emits one query, and records exactly what it reads back. The same
probe runs with zero, one and two presentation clients, which is what makes the
reply stream ROSTER-INDEPENDENT the thing under test: the mediator answers the
child, and a query is never a broadcast.

THE PROBE IS THIS BINARY. `e2e --probe <result> <ready> <trigger>` is dispatched by
`E2ETest.main` into `probe` below, so the same executable is both harness and pty
program. It has to run on the FAR side: the query leaves the session's own tty and
the reply arrives there; nothing outside the pty can observe either. `E2E.Resume`
reuses the same child-mode pattern for its winsize probe. The result file is
`k<TAB>v` records read by the harness's own parser, and the reply is encoded and
decoded by one pair of functions, so the two sides cannot drift.

WHAT IS DERIVED, AND WHAT CANNOT BE:

* the query is `Render.csiPlain 0x63` and the expected reply is what
  `Terminal.classifyCsi` ITSELF answers for it, not a copied byte literal. The
  tie cannot go vacuous: a query that stopped being owned collapses the
  expectation to `[]`, which the probe's non-empty reply then fails;
* the hostile XTGETTCAP request is built from the mediator's own framing, and its
  expected answer is `Terminal.xtgetcapReply` over that request's payload — the
  emitter performing its own filtering. The CR/LF check is deliberately NOT
  derived: it is about the bytes that actually reached the child, which is exactly
  the half `feed_replies_noNl` cannot see;
* the stable child profile's `TERM_PROGRAM_VERSION` is derived: `Daemon.serve` and
  this check both read `Terminal.versionNumber`. `TERM=xterm-256color` and
  `TERM_PROGRAM=linger` could NOT be tied to anything. They are literals inside
  `Daemon.serve`'s `spawnPty` call, not exported values, so a Lean-side tie would
  restate the constants rather than derive them. Same situation as `E2E.Agent`'s
  80×24 default, recorded for the same reason. -/

namespace E2E.Terminal

open E2E.Harness
open Linger.Posix
open Linger.Core.Render (csiPlain escSeq)
open Linger.Core.Terminal (STFinal classifyCsi xtgetcapReply)

/-! ## The queries, and what the mediator itself says they answer -/

/-- DA1, `CSI c`, spelled with the emitter's own CSI constructor. -/
def da1Query : List UInt8 := csiPlain 0x63

/-- The hostile XTGETTCAP request's payload: `54` (a hex capability name) CR
`;id>x` CR — the CRs are the injection primitive.

linger writes query replies into the child's OWN input (`Session.onMsg .ptyOut →
.writePty`), and the request is untrusted child output: a `cat` of a hostile file,
an ssh stream, a log tail. A raw echo of a payload carrying a CR let that output
run a command, because on a cooked-mode tty the CR commits the line. -/
def evilPayload : List UInt8 := "54\r;id>x\r".toUTF8.toList

/-- …and the request around it, framed the way the mediator frames its own: DCS,
the `+q` kind byte pair `Scan.dcsIntro`/`dcsKind` route into the buffered state,
the payload, ST. -/
def evilQuery : List UInt8 := escSeq 0x50 ++ [0x2B, 0x71] ++ evilPayload ++ escSeq STFinal

/-- What the mediator decides to answer for an owned CSI request, read out of
`classifyCsi` rather than copied from the test that used to spell it. The `Vt` is
only the cursor sampler for CPR and the geometry for `CSI 18 t`; DA1's row does not
look at it, so any well-formed one will do. -/
def csiAnswer (q : List UInt8) : List UInt8 :=
  match classifyCsi (Linger.Core.Vt.Vt.init 80 24) q with
  | .owned reply => reply
  | .unowned => []

def da1Expected : List UInt8 := csiAnswer da1Query

/-- The XTGETTCAP answer, from the emitter that does the filtering. Every
capability is answered negatively with the requested name echoed back, filtered to
the legal alphabet — so this value is `ESC P 0 + r 5 4 ; d ESC \`, and the dropped
bytes are precisely the CRs. -/
def evilExpected : List UInt8 := xtgetcapReply evilPayload

/-! ## The result file: bytes as hex, both directions -/

def nibble (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (0x30 + n.toNat) else Char.ofNat (0x61 + n.toNat - 10)

def toHex (bs : List UInt8) : String :=
  bs.foldl (fun s b => (s.push (nibble (b / 16))).push (nibble (b % 16))) ""

def unNibble (c : Char) : Option UInt8 :=
  let n := c.toNat
  if decide (0x30 ≤ n) && decide (n ≤ 0x39) then some (UInt8.ofNat (n - 0x30))
  else
    if decide (0x61 ≤ n) && decide (n ≤ 0x66) then some (UInt8.ofNat (n - 0x57))
    else if decide (0x41 ≤ n) && decide (n ≤ 0x46) then some (UInt8.ofNat (n - 0x37)) else none

/-- Hex pairs → bytes; `none` on a non-hex digit or an odd length, so a truncated
result file reads as "no reply" rather than as a short one. -/
def fromHexChars : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
    let hi ← unNibble a
    let lo ← unNibble b
    let tl ← fromHexChars rest
    return (hi * 16 + lo) :: tl

def fromHex (s : String) : Option (List UInt8) := fromHexChars s.toList

/-- The first `$PATH` entry holding `name`. Existence rather than `X_OK` — the only
caller is a "is fish installed at all" gate, and a non-executable file called
`fish` on `PATH` is not a case worth a syscall. -/
def whichBin (name : String) : IO (Option String) := do
  let path := (← IO.getEnv "PATH").getD ""
  for d in path.splitOn ":" do
    if d.isEmpty then
      continue
    let p := (System.FilePath.mk d) / name
    if ← p.pathExists then
      return some p.toString
  return none

/-! ## The child side -/

/-- Ask one terminal query and persist the observed reply.

Raw mode first, so nothing is echoed and the reply is not line-buffered; the query
goes out with `writeAll` on fd 1 rather than `IO.print`, because a buffered write
would not reach the pty until flush. Every failure is surfaced to the parent
through the result file — an exception here would otherwise look identical to a
mediator that never answered. -/
def probe (resultPath readyPath triggerPath : String) : IO UInt32 := do
  try
    let _ ← termRaw stdinFd
    IO.FS.writeFile (System.FilePath.mk readyPath) "ready"
    unless (← waitFor 8000 (System.FilePath.pathExists triggerPath)) do
      throw (IO.userError "trigger timeout")
    let hex ← IO.getEnv "PROBE_QUERY_HEX"
    let query := (hex.bind fromHex).getD da1Query
    writeAll stdoutFd (ByteArray.mk query.toArray)
    -- read until 2 s pass, or EOF, or ONE quiet interval after something arrived:
    -- the quiet interval is what would catch a DUPLICATE reply, which is the
    -- failure the exact-equality check upstairs is looking for
    let deadline := (← monotonicMs) + 2000
    let mut reply : List UInt8 := []
    let mut reading := true
    while reading && (← monotonicMs) < deadline do
      let revs ← poll #[stdinFd] #[POLLIN] 100
      if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        match ← read stdinFd 4096 with
        | none =>
          reading := false
        | some bs =>
          if bs.isEmpty then
            reading := false
          else
            reply := reply ++ bs.toList
      else if !reply.isEmpty then
        reading := false
    -- one `k<TAB>v` record per fact; an ABSENT variable writes no record
    let mut txt := s!"reply\t{toHex reply}\n"
    for k in ["TERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION"] do
      match ← IO.getEnv k with
      | some v =>
        txt := txt ++ s!"{k}\t{v}\n"
      | none =>
        pure ()
    IO.FS.writeFile (System.FilePath.mk resultPath) txt
    writeAll stdoutFd "\r\nPROBE-DONE\r\n".toUTF8
    IO.sleep 250
    return 0
  catch err =>
    IO.FS.writeFile (System.FilePath.mk resultPath) s!"error\t{err}\n"
    return 1

/-! ## The parent side -/

structure Case where
  reply : List UInt8 := []
  term : Option String := none
  termProgram : Option String := none
  termVersion : Option String := none
  clientOut : List ByteArray := []
  /-- Why the case produced nothing, if it did. It goes to stderr, which the suite
  log keeps without counting it as a check. -/
  err : Option String := none

/-- One case: a session whose child IS the probe, `clients` presentation clients
attached to it, and the query fired only once they are all in place. -/
def runCase (e : Env) (index clients : Nat) (inheritedTerm : Option String)
    (queryHex : Option String := none) : IO Case := do
  let name := s!"term-{index}-{clients}"
  let caseDir := (System.FilePath.mk e.dir) / name
  IO.FS.createDirAll caseDir
  let result := (caseDir / "result").toString
  let ready := (caseDir / "ready").toString
  let trigger := (caseDir / "trigger").toString
  -- The DAEMON's environment, which the child inherits and the mediator must
  -- override. In `("TERM", inheritedTerm)`, `some v` sets it and `none` REMOVES
  -- it, which is what case 0 needs.
  let mut env :=
    e.procEnv ++
      #[("TERM_PROGRAM", some "inherited-program"), ("TERM_PROGRAM_VERSION", some "9.9.9"),
        ("TERM", inheritedTerm)]
  if let some hex := queryHex then
    env := env.push ("PROBE_QUERY_HEX", some hex)
  -- `__daemon` directly rather than `attach`, because the child has to be the
  -- probe and not a shell; this is the argv `spawnDaemon` itself builds.
  let root ← IO.currentDir
  let probeBin ← IO.appPath
  let daemon ←
    IO.Process.spawn
        { cmd := e.bin, env := env,
          args :=
            #["__daemon", name, root.toString, probeBin.toString, "--probe", result, ready,
              trigger],
          stdout := .null, stderr := .null }
  let mut c : Case := {}
  let mut cls : Array Client := #[]
  if !(← waitFor 8000 (System.FilePath.pathExists ready)) then
    c := { c with err := some "probe did not become ready" }
  else
    for _ in [0:clients] do
      let cl ← e.spawn #["attach", name] 80 24
      cls := cls.push cl
      let _ ← waitFor 4000 (return (← e.info name "clients") == some (toString cls.size))
      let _ ← drain cl.fd 150 -- discard the initial restore
    IO.FS.writeFile (System.FilePath.mk trigger) "go"
    if !(← waitFor 8000 (System.FilePath.pathExists result)) then
      c := { c with err := some "probe did not answer" }
    else
      let txt ← IO.FS.readFile (System.FilePath.mk result)
      let recs := records txt
      let field := fun (k : String) => (recs.find? (·.1 == k)).map (·.2)
      let mut outs : List ByteArray := []
      for cl in cls do
        let o ← drain cl.fd 1200
        outs := outs ++ [o]
      c :=
        { reply := ((field "reply").bind fromHex).getD [], term := field "TERM",
          termProgram := field "TERM_PROGRAM", termVersion := field "TERM_PROGRAM_VERSION",
          clientOut := outs, err := field "error" }
      -- the daemon exits when its child does (`.childExited` → `.exit`), so this
      -- is a wait and not a kill
      if (← waitProcess daemon 5000).isNone then
        IO.eprintln s!"note: daemon '{name}' still running after the probe answered"
  -- cleanup, whatever happened above: reap the daemon, signalling it first if it
  -- is still running. The wait above may already have reaped it, which
  -- `reapOrKill` treats as finished rather than as an error.
  reapOrKill daemon 2000
  for cl in cls do
    cl.bye (sendDetach := false) -- close + reap; no detach key
  return c

def run : IO UInt32 :=
  Env.suite "terminal" fun e => do
    -- zero, one and two presentation clients — and a different inherited `TERM`
    -- each time, with none at all in the first, so the override is exercised from
    -- three different starting environments
    let plan : List (Nat × Nat × Option String) :=
      [(0, 0, none), (1, 1, some "xterm-kitty"), (2, 2, some "screen")]
    let mut cases : List (Nat × Case) := []
    for (index, clients, inherited) in plan do
      let c ← runCase e index clients inherited
      cases := cases ++ [(clients, c)]
    for (clients, data) in cases do
      if let some err := data.err then
        IO.eprintln s!"note: probe case with {clients} client(s): {err}"
      -- equality, not "contains": a duplicate reply is the failure this is for
      expect (data.reply == da1Expected)
          s!"DA1 progresses with {clients} client(s), exactly one reply"
      -- `TERM` and `TERM_PROGRAM` are literals, because `Daemon.serve`'s profile array
      -- is not an exported value; the version is derived. See the module docstring
      expect
          (data.term == some "xterm-256color" && data.termProgram == some "linger" &&
            data.termVersion == some Linger.Core.Terminal.versionNumber)
          s!"stable child terminal profile with {clients} client(s)"
      if clients != 0 then
        -- nested a level deeper on purpose: with nobody attached there is no client
        -- stream to make a claim about. `scripts/e2e.sh`'s exact check count is what
        -- stops this arm silently going empty and still printing `FAILURES: 0`.
        let outs := data.clientOut
        expect
            (outs.length == clients && outs.all (fun o => hasText o "PROBE-DONE") &&
              outs.all (fun o => !hasBytes o da1Query))
            s!"owned query hidden while ordinary output reaches {clients} client(s)"
    expect (cases.map (·.2.reply) == List.replicate 3 da1Expected)
        "reply stream is roster-independent"
    -- XTGETTCAP reply injection: the reply must carry no line terminator. Payload:
    -- 54 (hex '5','4') CR ; i d > x CR — the CRs are the injection primitive.
    let inj ← runCase e 9 0 none (some (toHex evilQuery))
    let ir := inj.reply
    if let some err := inj.err then
      IO.eprintln s!"note: XTGETTCAP probe case: {err}"
    expect (!ir.isEmpty && !ir.contains 0x0D && !ir.contains 0x0A)
        "XTGETTCAP reply carries no CR/LF (no command injection)"
    -- non-vacuity: linger did answer the query, and with the exact filtered negative
    -- reply `xtgetcapReply` prescribes for this payload — a prefix rather than
    -- equality, so a trailing byte from elsewhere in the stream does not decide it.
    expect (ir.take evilExpected.length == evilExpected)
        "XTGETTCAP still answered (filtered negative reply reached the child)"
    -- The original regression: an interactive fish must consume a command before
    -- any client attaches. This is required coverage, so an environment without
    -- fish fails instead of converting the missing check into a counted pass.
    let some fish ←
      whichBin "fish" | throw (IO.userError "fish is required for the detached-command regression")
    let marker := ((System.FilePath.mk e.dir) / "fish-command-ran").toString
    let fishEnv : Array (String × Option String) :=
      #[("SHELL", some fish), ("TERM", some "inherited-fish-term")]
    let _ ← e.cliEnv fishEnv #["run", "fish-regression", "printf", "ok", ">", marker]
    expect (← waitFor 6000 (System.FilePath.pathExists marker))
        "fish regression: detached command executes before attach"
    let _ ← e.cliEnv fishEnv #["kill", "fish-regression"]

end E2E.Terminal
