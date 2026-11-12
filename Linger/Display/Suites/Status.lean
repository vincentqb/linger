module

public import Verify.Harness

public section

/-! # Linger.Display.Suites.Status — the status column, the unread mechanism end to end

Ported from `tests/status_test.py`.

`unseen` is a property of the SESSION — output arrived while nobody was watching —
so the two transitions that matter are: attaching marks a session seen, and output
while detached marks it unread again. Both go through the counter pair in
`Session.State` (`outSeq`/`lookSeq`), and this pins them against the rendered
porcelain rather than against the internals.

The comparisons are against the `Status` constructors (through `Env.status`, which
reads `ofName`) and against `Status.icon` itself, so renaming a state is a compile
error rather than an assertion passing against a column that no longer exists.
`Linger.Session.Suites.Watch` covers the one transition this suite never exercises:
`linger attach --read-only` also marks a session seen. -/

namespace Linger.Display.Suites.Status

open Verify.Harness
open Linger.Display.Status (Status)

/-- `linger ls --summary` against `waiting`'s state dir, under `hangMs`, which only a hang
outlasts: the exit code (`none` once it had to be killed), elapsed milliseconds and stdout. -/
private def summaryWithin (waiting : Env) : IO (Option UInt32 × Nat × String) := do
  let start ← Os.Shell.monotonicMs
  let command ←
    IO.Process.spawn
        { cmd := waiting.bin, args := #["ls", "--summary"], env := waiting.procEnv,
          stdout := .piped, stderr := .null }
  let code ← waitOrKill command hangMs
  return (code, (← Os.Shell.monotonicMs) - start, ← command.stdout.readToEnd)

/-- The reply window `ls --summary` gives its peers, in milliseconds: `summaryText` in
`Linger.App.Shell`. -/
def summaryWindowMs : Nat := 250

/-- How many peers never answer in `checkDeadline`: enough that waiting out the reply window
once per peer would take ten seconds. -/
def stalledPeers : Nat := 40

/-- Stalled sockets precede a responsive peer and follow it. One sampling window covers the
entire snapshot; incomplete and unqueried peers stay unknown. Four stalled peers are fake
daemons that send a plausible partial reply and never finish it; the rest are listeners that
never accept, whose connections the kernel queues. The responsive peer sorts after the four, so
a summary that waited for each peer in turn would reach it only after a second, and would end
only after `stalledPeers` reply windows, ten seconds. The bound is half that: no load makes
waiting in turn quicker, and one shared window would have to stretch twentyfold to reach it. -/
def checkDeadline (e : Env) : IO Unit := do
  let waiting := { e with dir := s!"{e.dir}/waiting" }
  IO.FS.createDirAll waiting.dir
  let unfinished := #["first", "second", "third", "fourth"]
  let ready := "zz-ready"
  -- `zz-ready` sorts before `zzz-…`, and after the four unfinished peers.
  let quiet :=
    (List.range (stalledPeers - unfinished.size)).toArray.map fun i =>
      s!"zzz-{if i < 10 then "0" else ""}{i}"
  let self ← IO.appPath
  let listeners ← IO.mkRef (#[] : Array UInt32)
  let servers : Array (IO.Process.Child { stdout := .null, stderr := .null }) ←
    (unfinished.push ready).mapM fun name =>
        IO.Process.spawn
          { cmd := self.toString,
            args :=
              #["--info-server", s!"{waiting.dir}/{name}.sock", s!"{waiting.dir}/{name}.ready",
                if name == ready then "failed-info" else "timeout"],
            stdout := .null, stderr := .null }
  try
    for name in quiet do
      listeners.modify (·.push (← Os.Shell.unixListen s!"{waiting.dir}/{name}.sock"))
    for name in unfinished.push ready do
      unless ← waitFor patienceMs (System.FilePath.pathExists s!"{waiting.dir}/{name}.ready") do
        throw (IO.userError s!"status info server {name} did not become ready")
    let (code, elapsed, output) ← summaryWithin waiting
    let serialMs := stalledPeers * summaryWindowMs
    expect (code == some 0 && elapsed < serialMs / 2)
        s!"prompt shares one reply deadline across {stalledPeers} stalled peers ({elapsed} ms; \
          one window per peer would take {serialMs} ms)"
    expect
        (output ==
          s!"1{Linger.Display.Status.icon .exitedBad} {stalledPeers}{Linger.Display.Status.icon .unknown}\n")
        s!"a responsive peer behind stalled peers completes within the shared deadline ({output.trimAscii})"
    let retained ←
      (unfinished.push ready ++ quiet).allM fun name =>
          System.FilePath.pathExists s!"{waiting.dir}/{name}.sock"
    expect retained "prompt leaves unanswered peers' sockets in place"
  finally
    for server in servers do
      reapOrKill server 0
    for listener in ← listeners.get do
      Os.Shell.close listener

/-- Fill a listener without accepting. A reply timeout cannot help a blocking
connect here; the sampling command must decline the connection promptly. Nonblocking
connects fill the queue without timing: each one is queued until the queue is full, and the
next is refused at once, so the fixture knows it is full rather than guessing from a connect
that is slow. A summary that connected blocking would wait until this check closes the
listener, past `hangMs`. -/
def checkBacklog (e : Env) : IO Unit := do
  let waiting := { e with dir := s!"{e.dir}/backlog" }
  IO.FS.createDirAll waiting.dir
  let path := s!"{waiting.dir}/full.sock"
  let listener ← Os.Shell.unixListen path
  let queued ← IO.mkRef (#[] : Array UInt32)
  try
    let mut refused := false
    for _ in List.range 1024 do
      let fd ← Os.Shell.unixConnect path true
      if fd < 0 then
        refused := true
        break
      queued.modify (·.push fd.toUInt64.toUInt32)
    let held := (← queued.get).size
    let (code, elapsed, output) ← summaryWithin waiting
    expect (refused && held > 0)
        s!"fixture fills the pending Unix connection queue ({held} queued, then refused)"
    expect (code == some 0) s!"prompt does not wait for a full Unix connection queue ({elapsed} ms)"
    expect (output == s!"1{Linger.Display.Status.icon .unknown}\n")
        "busy connection counts as unknown"
    expect (← System.FilePath.pathExists path)
        "prompt retains a busy listener without claiming its name lock"
  finally
    Os.Shell.close listener
    for fd in ← queued.get do
      Os.Shell.close fd

/-- Whether `linger ls --summary` comes to print `expected` within `patienceMs`: a daemon writes
what it sees to its name's end record on a thread of its own, a moment after it sees it. -/
private def summaryBecomes (e : Env) (expected : String) : IO Bool :=
  waitFor patienceMs do
    let (code, text, _) ← e.cli #["ls", "--summary"]
    return code == 0 && text == expected

/-- The status suite: attaching marks a session seen and detached output marks it unread. -/
def run : IO UInt32 :=
  Env.suite "status" fun e => do
    let (emptyCode, empty, _) ← e.cli #["ls", "--summary"]
    expect (emptyCode == 0 && empty.isEmpty) "empty attention summary prints nothing"
    -- a long-lived child, so nothing exits under us and the row stays classifiable
    -- as idle/wants-you rather than exited-ok
    let _ ← e.typeIn "st" #["sh", "-c", "sleep 60"]
    -- a settling time, so that `behind` below counts all the output the shell will print
    IO.sleep 1500
    -- 1. a session nobody has watched, that has produced output, is unread
    expect (← waitFor patienceMs (return (← e.status "st") == Status.wantsYou))
        "unwatched output reads wants-you"
    let unread := s!"1{Linger.Display.Status.icon Status.wantsYou}\n"
    let before ← e.field "st" "behind"
    expect (← summaryBecomes e unread) "summary counts unread with the shared glyph"
    expect ((← e.field "st" "behind") == before) "summary does not acknowledge unread output"
    -- 2. attaching marks it seen: detach with no further output and it is idle.
    let c ← e.spawn #["attach", "st"] 80 24
    let _ ← waitFor patienceMs (return (← e.info "st" "clients") == some "1")
    c.detach
    let _ ← waitFor patienceMs (return (← e.info "st" "clients") == some "0")
    c.bye (sendDetach := false)
    expect ((← e.status "st") == Status.idle) "attach marks the session seen"
    expect (← summaryBecomes e "") "idle session does not clutter the summary"
    -- 3. output while detached makes it unread again
    let _ ← e.cli #["send", "st", "echo", "later"]
    expect (← waitFor patienceMs (return (← e.status "st") == Status.wantsYou))
        "output while away reads wants-you"
    -- `behind` is `toString (Session.behind s)`, a decimal `Nat`, so parse it
    -- rather than compare the string to "0": `!= "0"` also passes on a field that
    -- stopped being a number at all.
    let behind := ((← e.field "st" "behind").getD "0").toNat?.getD 0
    expect (behind > 0) "behind counts unseen output"
    -- 4. the human column renders one glyph for it — `Status.icon`'s own glyph,
    -- which is what `Listing.humanRow` puts at the head of the row.
    let human ← e.out #["ls"]
    expect (has human (String.singleton (Linger.Display.Status.icon Status.wantsYou)))
        "human listing shows the wants-you glyph"
    -- A real daemon retires when its child exits. Exercise a completed info
    -- reply carrying that exit field without racing the daemon's retirement.
    let self ← IO.appPath
    let failedServer ←
      IO.Process.spawn
          { cmd := self.toString,
            args :=
              #["--info-server", s!"{e.dir}/failed.sock", s!"{e.dir}/failed.ready", "failed-info"],
            stdout := .null, stderr := .null }
    try
      unless ← waitFor patienceMs (System.FilePath.pathExists s!"{e.dir}/failed.ready") do
        throw (IO.userError "failed info server did not become ready")
      let failed := (← e.status "failed") == Status.exitedBad
      let mixed :=
        s!"1{Linger.Display.Status.icon Status.wantsYou} 1{Linger.Display.Status.icon Status.exitedBad}\n"
      expect (failed && (← summaryBecomes e mixed))
          "summary keeps unread output and a reported failed exit distinct"
    finally
      reapOrKill failedServer 0
      -- a daemon removes its socket when it ends; the fixture's own is removed here
      try
        IO.FS.removeFile s!"{e.dir}/failed.sock"
      catch _ =>
        pure ()
    -- a record is read only while its daemon holds the name: a daemon killed before it could say
    -- how its program ended is counted as not answering, not from what it last wrote
    let program := ((← e.info "st" "pid").bind (·.toNat?)).map UInt32.ofNat
    let daemon ← e.daemonPid "st"
    for pid in [daemon, program] do
      if let some pid := pid then
        try
          Os.Shell.kill pid 9
        catch _ =>
          pure ()
    let unanswered := s!"1{Linger.Display.Status.icon Status.unknown}\n"
    expect (daemon.isSome && program.isSome && (← summaryBecomes e unanswered))
        "a summary counts a killed daemon as not answering, not from what it last wrote"
    e.killAll #["st"]
    checkDeadline e
    checkBacklog e

end Linger.Display.Suites.Status
