module

public import E2E.Harness

public section

/-! # E2E.Status — the status column, the unread mechanism end to end

Ported from `tests/status_test.py`.

`unseen` is a property of the SESSION — output arrived while nobody was watching —
so the two transitions that matter are: attaching marks a session seen, and output
while detached marks it unread again. Both go through the counter pair in
`Session.State` (`outSeq`/`lookSeq`), and this pins them against the rendered
porcelain rather than against the internals.

WHAT THE PORT STRENGTHENS. The Python compared the porcelain column against the
string literals `'wants-you'` and `'idle'`, and the human column against a
hardcoded braille glyph. All three are `Linger.Core.Status`' own output, so
renaming a state would have left the assertions passing against a column that no
longer exists. Here the comparison is against the `Status` constructors (through
`Env.status`, which reads `ofName`) and against `Status.icon` itself, so the same
rename is a compile error. `E2E.Watch` covers the one transition this suite never
exercised: `linger attach --read-only` also marks a session seen. -/

namespace E2E.Status

open E2E.Harness
open Linger.Core.Status (Status)

/-- Several stalled sockets precede a responsive peer. One sampling window
covers the entire snapshot; incomplete and unqueried peers stay unknown. -/
def checkDeadline (e : Env) : IO Nat := do
  let waiting := { e with dir := s!"{e.dir}/waiting" }
  IO.FS.createDirAll waiting.dir
  let names := #["first", "second", "third", "fourth", "zz-ready"]
  let self ← IO.appPath
  let servers : Array (IO.Process.Child { stdout := .null, stderr := .null }) ←
    names.mapM fun name =>
        IO.Process.spawn
          { cmd := self.toString,
            args :=
              #["--info-server", s!"{waiting.dir}/{name}.sock", s!"{waiting.dir}/{name}.ready",
                if name == "zz-ready" then "failed-info" else "timeout"],
            stdout := .null, stderr := .null }
  try
    for name in names do
      unless ← waitFor 5000 (System.FilePath.pathExists s!"{waiting.dir}/{name}.ready") do
        throw (IO.userError s!"status info server {name} did not become ready")
    let start ← Linger.Posix.monotonicMs
    let command ←
      IO.Process.spawn
          { cmd := e.bin, args := #["ls", "--summary"], env := waiting.procEnv, stdout := .piped,
            stderr := .null }
    let code ← waitProcess command 1500
    let elapsed := (← Linger.Posix.monotonicMs) - start
    if code.isNone then
      command.kill
      discard command.wait
    let output ← command.stdout.readToEnd
    let mut f := 0
    f :=
      f +
        (←
          expect (code == some 0 && elapsed < 900)
              "prompt shares one reply deadline across stalled peers")
    f :=
      f +
        (←
          expect
              (output ==
                s!"1{Linger.Core.Status.icon .exitedBad} {names.size - 1}{Linger.Core.Status.icon .unknown}\n")
              "a responsive peer behind stalled peers completes within the shared deadline")
    let retained ← names.allM fun name => System.FilePath.pathExists s!"{waiting.dir}/{name}.sock"
    f := f + (← expect retained "prompt leaves unanswered peers' sockets in place")
    return f
  finally
    for server in servers do
      try
        server.kill
      finally
        discard server.wait

/-- Fill a listener without accepting. A reply timeout cannot help a blocking
connect here; the sampling command must decline the connection promptly. -/
def checkBacklog (e : Env) : IO Nat := do
  let waiting := { e with dir := s!"{e.dir}/backlog" }
  IO.FS.createDirAll waiting.dir
  let path := s!"{waiting.dir}/full.sock"
  let listener ← Linger.Posix.unixListen path
  let attempts ← IO.mkRef (#[] : Array (Task (Except IO.Error Int64)))
  try
    let mut full := false
    for _ in List.range 128 do
      if full then
        break
      let attempt ← IO.asTask (Linger.Posix.unixConnect path) Task.Priority.dedicated
      attempts.modify (·.push attempt)
      if ← waitFor 100 (IO.hasFinished attempt) then
        full := (← IO.ofExcept (← IO.wait attempt)) < 0
      else
        full := true
    let start ← Linger.Posix.monotonicMs
    let command ←
      IO.Process.spawn
          { cmd := e.bin, args := #["ls", "--summary"], env := waiting.procEnv, stdout := .piped,
            stderr := .null }
    let code ← waitProcess command 1500
    let elapsed := (← Linger.Posix.monotonicMs) - start
    if code.isNone then
      command.kill
      discard command.wait
    let output ← command.stdout.readToEnd
    let mut f ← expect full "fixture fills the pending Unix connection queue"
    f :=
      f +
        (←
          expect (code == some 0 && elapsed < 900)
              "prompt does not wait for a full Unix connection queue")
    f :=
      f +
        (←
          expect (output == s!"1{Linger.Core.Status.icon .unknown}\n")
              "busy connection counts as unknown")
    f :=
      f +
        (←
          expect (← System.FilePath.pathExists path)
              "prompt retains a busy listener without claiming its name lock")
    return f
  finally
    -- Closing the listener releases the fixture's one blocked connect.
    Linger.Posix.close listener
    for attempt in ← attempts.get do
      if let .ok fd← IO.wait attempt then
        if fd ≥ 0 then
          Linger.Posix.close fd.toUInt64.toUInt32

def run : IO UInt32 := do
  let e ← Env.make "status"
  let mut f := 0
  let (emptyCode, empty, _) ← e.cli #["ls", "--summary"]
  f := f + (← expect (emptyCode == 0 && empty.isEmpty) "empty attention summary prints nothing")
  -- a long-lived child, so nothing exits under us and the row stays classifiable
  -- as idle/wants-you rather than exited-ok
  let _ ← e.cli #["run", "st", "sh", "-c", "sleep 60"]
  IO.sleep 1500
  -- 1. a session nobody has watched, that has produced output, is unread
  f := f + (← expect ((← e.status "st") == Status.wantsYou) "unwatched output reads wants-you")
  let unread := s!"1{Linger.Core.Status.icon Status.wantsYou}\n"
  let before ← e.field "st" "behind"
  let (summaryCode, summary, _) ← e.cli #["ls", "--summary"]
  f :=
    f +
      (←
        expect (summaryCode == 0 && summary == unread)
            "summary counts unread with the shared glyph")
  f :=
    f +
      (← expect ((← e.field "st" "behind") == before) "summary does not acknowledge unread output")
  -- 2. attaching marks it seen: detach with no further output and it is idle.
  let c ← e.spawn #["attach", "st"] 80 24
  IO.sleep 1500
  c.detach
  IO.sleep 800
  c.bye (sendDetach := false)
  f := f + (← expect ((← e.status "st") == Status.idle) "attach marks the session seen")
  let (quietCode, quiet, _) ← e.cli #["ls", "--summary"]
  f := f + (← expect (quietCode == 0 && quiet.isEmpty) "idle session does not clutter the summary")
  -- 3. output while detached makes it unread again
  let _ ← e.cli #["send", "st", "echo", "later"]
  IO.sleep 1200
  f := f + (← expect ((← e.status "st") == Status.wantsYou) "output while away reads wants-you")
  -- `behind` is `toString (Session.behind s)`, a decimal `Nat`, so parse it
  -- rather than compare the string to "0" as the Python did: `!= "0"` also
  -- passes on a field that stopped being a number at all.
  let behind := ((← e.field "st" "behind").getD "0").toNat?.getD 0
  f := f + (← expect (behind > 0) "behind counts unseen output")
  -- 4. the human column renders one glyph for it — `Status.icon`'s own glyph,
  -- which is what `Listing.humanRow` puts at the head of the row.
  let human ← e.out #["ls"]
  f :=
    f +
      (←
        expect (has human (String.singleton (Linger.Core.Status.icon Status.wantsYou)))
            "human listing shows the wants-you glyph")
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
    unless ← waitFor 5000 (System.FilePath.pathExists s!"{e.dir}/failed.ready") do
      throw (IO.userError "failed info server did not become ready")
    let failed := (← e.status "failed") == Status.exitedBad
    let (mixedCode, mixed, _) ← e.cli #["ls", "--summary"]
    f :=
      f +
        (←
          expect
              (failed && mixedCode == 0 &&
                mixed ==
                  s!"1{Linger.Core.Status.icon Status.wantsYou} 1{Linger.Core.Status.icon Status.exitedBad}\n")
              "summary keeps unread output and a reported failed exit distinct")
  finally
    failedServer.kill
    discard failedServer.wait
  e.killAll #["st"]
  f := f + (← checkDeadline e)
  f := f + (← checkBacklog e)
  verdict e f

end E2E.Status
