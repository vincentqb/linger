module

public import Verify.Harness
import Linger.Session.CoreCode.Checkpoint
import Linger.Session.CoreCode.Wire
import Linger.Display.CoreCode.Status

public section

/-! # Rename: a session keeps its ID and changes its name

A rename of a live, an attached, a saved and an ended session reaches each by its new name alone,
with its program, terminal, clients and status as they were and every file where it was; the
refusals change nothing; a rename and a start of one name at once leave one session with it; a
session the old layout keyed by its name lists, is captured, attaches and is killed as before,
and one whose daemon an older linger started is not renamed; `LINGER_SESSION` holds the ID,
which the rename keeps, and a `wait` begun before a rename answers. -/

namespace Linger.Session.Suites.Rename

open Verify.Harness
open Os.Shell
open Linger.Display.Status (Status)

/-- The names the local listing shows, each once per row. -/
private def listed (e : Env) : IO (List String) := do
  return (records (← e.out #["ls", "--porcelain"])).filterMap fun (k, v) =>
      if k == "name" then some v else none

/-- What the file at `path` holds, or `none` when there is none. -/
private def contents (path : String) : IO (Option String) := do
  if ← System.FilePath.pathExists path then
    return some (← IO.FS.readFile path)
  return none

/-- A daemon an older linger started, at `socket`: it answers each `info` with the fields of a
level-4 daemon, which name no `renames`, until `stop` is set. -/
private def olderDaemon (socket : String) (stop : IO.Ref Bool) : IO Unit := do
  let lfd ← unixListen socket
  try
    setNonblock lfd
    while !(← stop.get) do
      let some fd ← acceptWithin lfd 100 | continue
      try
        discard <| poll #[fd] #[POLLIN] 2000
        if let some request← read fd 65536 then
          if !request.isEmpty then
            let reply := "pid\t1\ncmd\tolder\nprotocol\t4\nversion\t0.1.0\nhandoff\t1\n"
            writeAll fd
                (ByteArray.mk (Linger.Session.Wire.encode (.infoReply reply.toUTF8.toList)).toArray)
            writeAll fd (ByteArray.mk (Linger.Session.Wire.encode .done).toArray)
      catch _ =>
        pure ()
      finally
        close fd
  finally
    close lfd
    try
      IO.FS.removeFile socket
    catch _ =>
      pure ()

/-- Stop the daemon of `name` with SIGTERM, which saves it, and wait until it is gone. -/
private def save (e : Env) (name : String) : IO Bool := do
  let some pid ← e.daemonPid name | return false
  kill pid 15
  waitFor patienceMs (return !(← alive pid))

/-- A live, an attached, a saved and an ended session, each renamed. -/
private def renameChecks (e : Env) : IO Unit := do
  let (aRc, _, _) ← e.cli #["start", "a", "/bin/cat"]
  let pid ← e.info "a" "pid"
  let (rc, _, err) ← e.cli #["rename", "a", "b"]
  let (oldRc, _, _) ← e.cli #["ls", "--porcelain", "--", "a"]
  let names ← listed e
  expect
      (aRc == 0 && rc == 0 && pid.isSome && (← e.info "b" "pid") == pid && oldRc == 127 &&
        names.contains "b" &&
        !names.contains "a" &&
        (← e.info "b" "name") == some "b" &&
        (← e.info "b" "renames") == some "true")
      s!"a live session renamed is reached and listed by its new name alone, its program as it \
        was, and its listing says its daemon renames ({rc} {err.trimAscii} {names})"
  expect
      ((← System.FilePath.pathExists s!"{e.dir}/a.sock") &&
        !(← System.FilePath.pathExists s!"{e.dir}/b.sock") &&
        (← contents s!"{e.dir}/names/b") == some "a")
      "a rename moves no file: the session keeps its ID, which the new name's entry holds"
  -- an attached client stays attached, and what it types still reaches the program
  let _ ← e.cli #["start", "c", "/bin/cat"]
  let client ← e.spawn #["attach", "c"]
  let attached ← waitFor patienceMs (return (← e.info "c" "clients") == some "1")
  let (cRc, _, _) ← e.cli #["rename", "c", "d"]
  client.type "after-rename\r"
  let typed ← waitFor patienceMs (return has (← e.out #["capture", "d"]) "after-rename")
  expect (attached && cRc == 0 && typed && (← e.info "d" "clients") == some "1")
      "an attached client stays attached through a rename, and its input reaches the program"
  client.bye
  -- a saved session keeps its screen under its new name
  let _ ← e.cli #["start", "s", "/bin/sh", "-c", "echo saved-$((40+2)); exec sleep 1000"]
  let shown ← waitFor patienceMs (return has (← e.out #["capture", "s"]) "saved-42")
  let saved ← save e "s"
  let (sRc, _, _) ← e.cli #["rename", "s", "t"]
  let (oldCapture, _, _) ← e.cli #["capture", "s"]
  expect
      (shown && saved && sRc == 0 && (← e.state "t") == .resumable &&
        has (← e.out #["capture", "t"]) "saved-42" &&
        oldCapture == 127)
      "a saved session renamed keeps its screen and lists as resumable under its new name alone"
  -- an ended session still listed keeps how it ended
  let _ ← e.cli #["start", "x", "/bin/sh", "-c", "exit 3"]
  let ended ← waitFor patienceMs (return (← e.state "x") == .exitedBad)
  let (xRc, _, _) ← e.cli #["rename", "x", "y"]
  let (waitRc, _, _) ← e.cli #["wait", "y"]
  let (oldWait, _, _) ← e.cli #["wait", "x"]
  expect (ended && xRc == 0 && (← e.state "y") == .exitedBad && waitRc == 3 && oldWait == 127)
      s!"an ended session renamed keeps how it ended under its new name alone ({waitRc})"

/-- Each refusal changes nothing, and nothing is ever replaced. -/
private def refusalChecks (e : Env) : IO Unit := do
  let pid ← e.info "b" "pid"
  let (invalidRc, _, _) ← e.cli #["rename", "b", "   "]
  expect (invalidRc == 2 && (← e.info "b" "pid") == pid)
      "rename refuses an invalid new name as a usage error"
  let (missingRc, _, _) ← e.cli #["rename", "nosuch", "z"]
  let (renamedRc, _, _) ← e.cli #["rename", "a", "z"]
  expect
      (missingRc == 127 && renamedRc == 127 && !(← System.FilePath.pathExists s!"{e.dir}/names/z"))
      "rename refuses an old name no session has, a renamed session's old name among them"
  let dPid ← e.info "d" "pid"
  let mut refused := true
  for taken in ["d", "t", "y", "b"] do
    let (rc, _, err) ← e.cli #["rename", "b", taken]
    refused := refused && rc == 1 && has err "replaces no session"
  expect
      (refused && (← e.info "b" "pid") == pid && (← e.info "d" "pid") == dPid &&
        (← e.state "t") == .resumable &&
        (← e.state "y") == .exitedBad &&
        (← contents s!"{e.dir}/names/d") == some "c")
      "rename refuses a new name a live, saved or ended session has, itself included, and \
        replaces nothing"
  -- a daemon an older linger started keeps no name but its ID
  let stop ← IO.mkRef false
  let older ← IO.asTask (olderDaemon s!"{e.dir}/old.sock" stop) Task.Priority.dedicated
  let up ← waitFor patienceMs (System.FilePath.pathExists s!"{e.dir}/old.sock")
  let (olderRc, _, olderErr) ← e.cli #["rename", "old", "new"]
  let names ← listed e
  stop.set true
  discard <| IO.wait older
  expect
      (up && olderRc == 1 && has olderErr "started by an older linger" &&
        has olderErr "linger upgrade old" &&
        names.contains "old" &&
        !(← System.FilePath.pathExists s!"{e.dir}/names/new"))
      s!"rename refuses a session whose daemon an older linger started, saying how to move it \
        onto this linger, and changes nothing ({olderErr.trimAscii})"

/-- A rename and a start of one name at once leave exactly one session with it. -/
private def raceChecks (e : Env) : IO Unit := do
  let mut one := true
  let mut seen := #[]
  for round in [0:6] do
    let old := s!"p{round}"
    let new := s!"q{round}"
    let _ ← e.cli #["start", old, "/bin/cat"]
    let oldPid ← e.info old "pid"
    -- in odd rounds the rename sets out once the start has begun its daemon, whose log it makes
    -- first, so that the start comes first and its daemon may still hold the name's ID
    let starter ← IO.asTask (e.cli #["start", new, "/bin/cat"]) Task.Priority.dedicated
    if round % 2 == 1 then
      discard <| waitFor patienceMs (System.FilePath.pathExists s!"{e.dir}/logs/{new}.log")
    let renamer ← IO.asTask (e.cli #["rename", old, new]) Task.Priority.dedicated
    let (renameRc, _, _) ← IO.ofExcept (← IO.wait renamer)
    let (startRc, _, _) ← IO.ofExcept (← IO.wait starter)
    let names ← listed e
    let newPid ← e.info new "pid"
    let count := (names.filter (· == new)).length
    let winner := if renameRc == 0 then "rename" else "start"
    seen := seen.push (winner, renameRc, startRc)
    one :=
      one && count == 1 && (renameRc == 0) != (startRc == 0) &&
        (if renameRc == 0 then newPid == oldPid && !names.contains old
        else newPid != oldPid && names.contains old)
  expect one
      s!"a rename onto a name and a start of it at once leave exactly one session with it ({seen})"

/-- The old layout keeps its meaning, and `LINGER_SESSION` and `wait` follow the ID. -/
private def layoutChecks (e : Env) : IO Unit := do
  -- a checkpoint keyed by its name, as every linger before names could change saved one
  let vt := (Terminal.Vt.Vt.init 30 3).feedBytes "old-layout screen".toUTF8
  IO.FS.writeBinFile s!"{e.dir}/legacy.ckpt" (Linger.Session.Checkpoint.saveBytes ⟨vt, e.dir, []⟩)
  IO.FS.writeBinFile s!"{e.dir}/kept.ckpt" (Linger.Session.Checkpoint.saveBytes ⟨vt, e.dir, []⟩)
  let names ← listed e
  let status ← e.state "legacy"
  let capture ← e.out #["capture", "legacy"]
  let (killRc, _, _) ← e.cli #["kill", "legacy"]
  expect
      (names.contains "legacy" && status == .resumable && has capture "old-layout screen" &&
        killRc == 0 &&
        !(← System.FilePath.pathExists s!"{e.dir}/legacy.ckpt"))
      s!"a saved session in the old layout lists, is captured and is killed as before ({names} \
        {Linger.Display.Status.name status} {capture.trimAscii} {killRc})"
  let client ← e.spawn #["attach", "kept"]
  let resumed ← waitFor patienceMs (return (← e.info "kept" "clients") == some "1")
  client.bye
  expect
      (resumed && (← System.FilePath.pathExists s!"{e.dir}/kept.sock") &&
        !(← System.FilePath.pathExists s!"{e.dir}/names/kept"))
      "a saved session in the old layout attaches and resumes under its name for its ID, \
        writing no entry"
  -- LINGER_SESSION holds the ID, which a rename keeps; a name whose ID a renamed session holds
  -- gets a fresh one
  let script := fun file => s!"printf %s \"$LINGER_SESSION\" > {e.dir}/{file}; exec cat"
  let _ ← e.cli #["start", "g", "/bin/sh", "-c", script "g.id"]
  let first ← waitFor patienceMs (return (← contents s!"{e.dir}/g.id").isSome)
  let (gRc, _, _) ← e.cli #["rename", "g", "h"]
  let _ ← e.cli #["start", "g", "/bin/sh", "-c", script "g2.id"]
  let second ← waitFor patienceMs (return (← contents s!"{e.dir}/g2.id").isSome)
  let freshId := (← contents s!"{e.dir}/g2.id").getD ""
  let porcelain ← e.out #["ls", "--porcelain"]
  expect
      (first && second && gRc == 0 && (← contents s!"{e.dir}/g.id") == some "g" &&
        freshId.startsWith "." &&
        freshId.length == 17 &&
        (← e.info "g" "pid") != (← e.info "h" "pid") &&
        (← e.info "g" "name") == some "g" &&
        !has porcelain s!"\"{freshId}\"" &&
        (← contents s!"{e.dir}/names/g") == some freshId)
      s!"LINGER_SESSION holds the session's ID, which a rename keeps; a name a renamed session's \
        ID holds gets a fresh one, which no listing shows ({freshId})"
  -- a wait begun before a rename answers with the program's status
  let _ ← e.cli #["start", "w", "/bin/sh", "-c", "read line; exit 7"]
  let waiter ←
    IO.Process.spawn
        { cmd := e.bin, args := #["wait", "w"], env := e.procEnv, stdin := .null, stdout := .null,
          stderr := .null }
  -- nothing reports a wait under way: give the waiter the time to look the name up
  IO.sleep 300
  let (wRc, _, _) ← e.cli #["rename", "w", "v"]
  let _ ← e.cli #["send", "v", "go\n"]
  let waited ← waitProcess waiter patienceMs
  expect (wRc == 0 && waited == some 7)
      s!"a wait begun before a rename answers with the program's status ({waited})"

/-- A name is clean text, spaces and Unicode included: a session renamed to one is listed under
it and reached by it, as one argument, by every command, here an attach and a kill; and a session
started under one is too, its files keyed by a fresh ID. -/
private def textNameChecks (e : Env) : IO Unit := do
  let name := "my build · ✓ 世界"
  let _ ← e.typeIn "plain" #["true"]
  let (rc, _, _) ← e.cli #["rename", "plain", name]
  let shown := (← listed e).contains name
  let c ← e.spawn #["attach", name]
  let attached ← waitFor patienceMs (return (← e.info name "clients") == some "1")
  c.type "echo text-$((40+2))\r"
  let typed ← c.awaitNeedle "text-42"
  c.detach
  let _ ← waitFor patienceMs (return (← e.info name "clients") == some "0")
  c.bye (sendDetach := false)
  let (killRc, _, _) ← e.cli #["kill", name]
  let gone ← waitFor patienceMs (return !(← listed e).contains name)
  expect (rc == 0 && shown && attached && typed && killRc == 0 && gone)
      "a session renamed to a name with spaces and Unicode is listed, attached and killed by it"
  let started := "two words ✓"
  let (startRc, _, _) ← e.cli #["start", started, "/bin/cat"]
  let live := (← e.info started "state") == some "live"
  let sockets ← e.dirNames ".sock"
  let keyed := sockets.all fun file => !has file " " && !has file "✓"
  let (endRc, _, _) ← e.cli #["kill", started]
  expect (startRc == 0 && live && keyed && endRc == 0)
      s!"a session started under a name with spaces is reached by it, its files keyed by an ID: \
        {sockets}"

/-- The rename suite. -/
def run : IO UInt32 :=
  Env.suite "rename" fun e => do
    try
      renameChecks e
      refusalChecks e
      raceChecks e
      layoutChecks e
      textNameChecks e
    finally
      e.endSessions

end Linger.Session.Suites.Rename
