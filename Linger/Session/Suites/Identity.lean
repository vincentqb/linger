module

public import Verify.Harness
import Linger.Session.CoreCode.Checkpoint
import Linger.Session.WorldCode.Daemon
import Linger.Target.CoreCode.Name
import Linger.Os.CoreCode.Answer

public section

/-! Exact command targets and exclusive ownership of sockets and saved state. -/

namespace Linger.Session.Suites.Identity

open Verify.Harness
open Os.Shell

private def splitEnv (e : Env) (runtime : Nat) : Array (String × Option String) :=
  #[("LINGER_DIR", none), ("XDG_RUNTIME_DIR", some s!"{e.dir}/r{runtime}"),
    ("XDG_STATE_HOME", some s!"{e.dir}/state")]

/-- A third runtime directory with its own state directory. -/
def isolatedEnv (e : Env) : Array (String × Option String) :=
  (splitEnv e 3).push ("XDG_STATE_HOME", some s!"{e.dir}/state-other")

/-- Whether the name's lock files, in the runtime directory and in the state directory's
`.locks`, are absent from the suite's directory, which is both. -/
private def locksGone (e : Env) (name : String) : IO Bool := do
  return !(← System.FilePath.pathExists s!"{e.dir}/{name}.lock") &&
      !(← System.FilePath.pathExists s!"{e.dir}/.locks/{name}.lock")

/-- One round of the start race on `name`, which no record names: this check holds the name's two
locks, as an offline reader does, while four `start`s of it race reads and listings, which try its
locks, and then deletes the lock files holding them, as a holder that no record names does, and
lets them go while more reads race the starts' daemons. It gives how many starts took the name
while it held the locks, how many daemons logged that they found the locks held, and how many
starts took the name in all. -/
private def startRace (e : Env) (name : String) : IO (Nat × Nat × Nat) := do
  let spawn := fun (args : Array String) =>
    IO.Process.spawn
      { cmd := e.bin, args, env := e.procEnv, stdin := .null, stdout := .null, stderr := .null }
  -- each starting daemon logs once that it found the name's locks held
  let logged := Linger.Session.Shell.Daemon.claimWaitLine name
  let before := ((← e.log name).splitOn logged).length - 1
  let waiting : IO Nat := do
    return ((← e.log name).splitOn logged).length - 1 - before
  -- the socket's lock and then the checkpoint's, as every owner takes them, let go in reverse
  let paths := [s!"{e.dir}/{name}.lock", s!"{e.dir}/.locks/{name}.lock"]
  let held ← paths.mapM flock
  let released ← IO.mkRef false
  let release : IO Unit := do
    unless ← released.get do
      released.set true
      for (fd, path) in (held.zip paths).reverse do
        if fd ≥ 0 then
          try
            unlinkHeld fd.toUInt64.toUInt32 path
          finally
            close fd.toUInt64.toUInt32
  try
    unless held.all (· ≥ 0) do
      throw (IO.userError s!"fixture locks unavailable: {name}")
    let starters ← (List.range 4).mapM fun _ => spawn #["start", name, "/bin/sh"]
    let exits ← starters.mapM fun _ => IO.mkRef (none : Option UInt32)
    let taken : IO Nat := do
      let mut n := 0
      for (k, exit) in starters.zip exits do
        if (← exit.get).isNone then
          exit.set (← k.tryWait)
        if (← exit.get) == some 0 then
          n := n + 1
      return n
    let early ← (List.range 6).mapM fun _ => spawn #["capture", name]
    let listers ← (List.range 4).mapM fun _ => spawn #["ls", "--porcelain"]
    -- let go once every daemon waits, or 400 ms after the first did, well within the second a
    -- starting daemon waits for the locks, so that one still waits when they go
    let first ← IO.mkRef (none : Option Nat)
    let _ ←
      waitFor patienceMs do
          let now ← monotonicMs
          let count ← waiting
          if count > 0 && (← first.get).isNone then
            first.set (some now)
          let since := ((← first.get).map (now - ·)).getD 0
          return count ≥ starters.length || since ≥ 400 || (← taken) > 0
    let takenHeld ← taken
    let waited ← waiting
    release
    let late ← (List.range 6).mapM fun _ => spawn #["capture", name]
    for k in early ++ listers ++ late do
      let _ ← k.wait
    let mut started := 0
    for (k, exit) in starters.zip exits do
      let code ←
        match ← exit.get with
        | some code =>
          pure code
        | none =>
          k.wait
      if code == 0 then
        started := started + 1
    return (takenHeld, waited, started)
  finally
    release

/-- State is bounded by what it means: after any command, every lock file names a session or
an ending. A command on a name no record names leaves no lock file of it, a kill that leaves its
name no record deletes them, a name with an ending keeps them, and a listing deletes the lock
files of names nothing names, but not one another process holds. -/
private def lockChecks (e : Env) : IO Unit := do
  let mut left : List String := []
  for args in
    [#["ls", "ghost", "--porcelain"], #["kill", "ghost"], #["resume", "ghost"],
      #["capture", "ghost"], #["capture", "--history", "ghost"], #["send", "ghost", "x"],
      #["detach", "ghost"], #["resize", "ghost", "80", "24"], #["wait", "ghost"],
      #["attach", "--read-only", "ghost"]] do
    let _ ← e.cli args
    unless ← locksGone e "ghost" do
      left := left ++ [String.intercalate " " args.toList]
  expect left.isEmpty s!"a command on a name no record names leaves no lock file of it: {left}"
  let ck : Linger.Session.Checkpoint.Ckpt Terminal.Vt.Vt :=
    { vt := Terminal.Vt.Vt.init 20 5, cwd := e.dir, fields := [] }
  IO.FS.writeBinFile s!"{e.dir}/orphan.ckpt" (Linger.Session.Checkpoint.saveBytes ck)
  let (_, listed, _) ← e.cli #["ls", "orphan", "--porcelain"]
  let kept := !(← locksGone e "orphan")
  let (killRc, _, _) ← e.cli #["kill", "orphan"]
  expect
      (has listed "name\torphan" && kept && killRc == 0 &&
        !(← System.FilePath.pathExists s!"{e.dir}/orphan.ckpt") &&
        (← locksGone e "orphan"))
      "a saved session's lock files stay while its checkpoint does, and go with the kill that discards it"
  let _ ← e.typeIn "ended" #["true"]
  let (endRc, _, _) ← e.cli #["kill", "ended"]
  let ended ←
    waitFor 3000 do
        return !(← System.FilePath.pathExists s!"{e.dir}/ended.sock")
  let _ ← e.cli #["ls", "--porcelain"]
  expect
      (endRc == 0 && ended && (← System.FilePath.pathExists s!"{e.dir}/ended.end") &&
        (← System.FilePath.pathExists s!"{e.dir}/ended.lock") &&
        (← System.FilePath.pathExists s!"{e.dir}/.locks/ended.lock"))
      "a name whose session ended keeps its lock files, which name its ending"
  IO.FS.createDirAll s!"{e.dir}/.locks"
  for name in ["stale", "held"] do
    IO.FS.writeFile s!"{e.dir}/{name}.lock" ""
    IO.FS.writeFile s!"{e.dir}/.locks/{name}.lock" ""
  let fd ← flock s!"{e.dir}/held.lock"
  unless fd ≥ 0 do
    throw (IO.userError "fixture lock unavailable: held")
  try
    let (lsRc, _, _) ← e.cli #["ls", "--porcelain"]
    expect
        (lsRc == 0 && (← locksGone e "stale") &&
          (← System.FilePath.pathExists s!"{e.dir}/held.lock"))
        "a listing deletes the lock files of names nothing names, but not one another process holds"
  finally
    close fd.toUInt64.toUInt32
  let _ ← e.cli #["ls", "--porcelain"]
  expect (← locksGone e "held") "a lock file nothing names goes once no process holds it"
  let _ ← e.typeIn "renamed" #["true"]
  let (renameRc, _, _) ← e.cli #["rename", "renamed", "renamed2"]
  let _ ← e.cli #["ls", "--porcelain"]
  expect
      (renameRc == 0 && (← System.FilePath.pathExists s!"{e.dir}/renamed.lock") &&
        !(← System.FilePath.pathExists s!"{e.dir}/names/.lock"))
      "a renamed session keeps its ID's lock files, which its entry names, and the names lock goes once let go"
  -- A check that starts a daemon ends it: the renamed session ends by its new name, and its daemon
  -- with it, so no run leaves one behind.
  let renamedDaemon ← e.daemonPid "renamed2"
  let (renamedRc, _, _) ← e.cli #["kill", "renamed2"]
  let renamedEnded ←
    match renamedDaemon with
    | some pid =>
      waitFor 5000 (return !(← alive pid))
    | none =>
      pure false
  expect
      (renamedRc == 0 && renamedEnded && !(← System.FilePath.pathExists s!"{e.dir}/renamed.sock"))
      "a renamed session ends by its new name, and its daemon ends with it"
  -- A name has one owner at a time, whatever deletes its lock files (`startRace`): no start
  -- takes the name while another process holds its locks, and once their holder deletes their
  -- files and lets them go, exactly one does. No racer ends a session, so a start that took the
  -- name while the locks were held, or a second one, would be a second owner at once. A `kill`
  -- among the racers could end the first owner within the round, and a later start would then
  -- take the name after it: two starts that took it, one owner after another, which counting
  -- them cannot tell from two at once.
  IO.FS.createDirAll s!"{e.dir}/.locks"
  let mut rounds : List (Nat × Nat × Nat) := []
  for round in [0:4] do
    rounds := rounds ++ [← startRace e s!"race{round}"]
    let _ ← e.cli #["kill", s!"race{round}"]
  expect
      (rounds.all fun (takenHeld, waited, started) => takenHeld == 0 && waited > 0 && started == 1)
      s!"no start takes a name while another process holds its locks, and once their holder \
        deletes their files and lets them go exactly one does, whatever reads race (taken while \
        held, daemons that waited, taken): {rounds}"

/-- The identity suite: exact command targets and exclusive ownership of sockets and saved
state. -/
def run : IO UInt32 :=
  Env.suite "identity" fun e => do
    try
      lockChecks e
      let _ ← e.typeIn "a_b" #["true"]
      let pid ← e.info "a_b" "pid"
      for name in ["", "   ", "a\tb", "a\u009bb", String.ofList (List.replicate 121 'a')] do
        let (rc, _, _) ← e.cli #["ls", name, "--porcelain"]
        expect (rc == 2) s!"invalid target {repr name} is a usage error"
      let (prefixRc, _, _) ← e.cli #["ls", "a", "--porcelain"]
      expect (prefixRc != 0) "command lookup never selects a name by prefix"
      let (killRc, _, _) ← e.cli #["kill", "a b"]
      expect
          (killRc == Linger.Os.Answer.code .notFound && (← e.info "a_b" "pid") == pid && pid.isSome)
          "a kill of a name no session has is never rewritten into a similar one's"
      let (waitRc, _, _) ← e.cli #["wait", "missing name"]
      expect (waitRc == Linger.Os.Answer.code .notFound)
          "wait of a clean name no session has answers that none has it"
      let (describeRc, _, _) ← e.cli #["describe", "a_b", "text"]
      expect (describeRc == 2 && (← e.info "a_b" "description").isNone)
          "describe is no command: a usage error that changes no session"
      let vt := (Terminal.Vt.Vt.init 20 2).feedBytes "old\r\nmiddle\r\nscreen".toUTF8
      let bytes := Linger.Session.Checkpoint.saveBytes ⟨vt, e.dir, [("saved", "yes")]⟩
      let path := s!"{e.dir}/saved.ckpt"
      IO.FS.writeBinFile path bytes
      for (args, expected) in
        [(#["capture", "--history", "saved"], Terminal.Render.history vt),
          (#["capture", "saved"], Terminal.Render.screenText vt)] do
        let (rc, out, _) ← e.cli args
        expect (rc == 0 && out.toUTF8.toList == expected)
            s!"offline {repr args} reads the saved terminal exactly"
      expect
          ((← IO.FS.readBinFile path).toList == bytes.toList &&
            !(← System.FilePath.pathExists s!"{e.dir}/saved.sock"))
          "offline reads preserve the checkpoint and do not start a daemon"
      let (caseLiveRc, _, _) ← e.cli #["ls", "A_B", "--porcelain"]
      let (caseSavedRc, caseSavedOut, _) ← e.cli #["capture", "--history", "SAVED"]
      expect (caseLiveRc != 0 && caseSavedRc != 0 && caseSavedOut.isEmpty)
          "case variants never resolve to an existing live or saved session"
      IO.FS.createDirAll s!"{e.dir}/.locks"
      for lock in [s!"{e.dir}/saved.lock", s!"{e.dir}/.locks/saved.lock"] do
        let fd ← flock lock
        unless fd ≥ 0 do
          throw (IO.userError s!"fixture lock unavailable: {lock}")
        try
          let (rc, out, _) ← e.cli #["capture", "--history", "saved"]
          expect (rc != 0 && out.isEmpty) s!"offline reads refuse an owned resource: {lock}"
        finally
          close fd.toUInt64.toUInt32
      IO.FS.writeBinFile s!"{e.dir}/bad.ckpt" ⟨#[1, 2, 3]⟩
      let (badRc, badOut, _) ← e.cli #["capture", "bad"]
      expect (badRc != 0 && badOut.isEmpty) "corrupt offline data fails without output"
      let host := Linger.Target.Name.sanitize (← gethostname)
      let checkpoint := s!"{e.dir}/state/linger/{host}/work.ckpt"
      let (firstRc, _, _) ← e.typeInEnv (splitEnv e 1) "work" #["true"]
      let saved ← waitFor 3000 (System.FilePath.pathExists checkpoint)
      let first := records (← e.cliEnv (splitEnv e 1) #["ls", "work", "--porcelain"]).2.1
      let firstPid := first.find? (·.1 == "pid")
      expect (firstRc == 0 && saved && firstPid.isSome)
          "first runtime owns a live session and its checkpoint"
      let (secondRc, _, _) ← e.cliEnv (splitEnv e 2) #["resume", "work"]
      expect (secondRc != 0) "another runtime directory cannot claim the same saved session"
      let (offlineRc, offlineOut, _) ← e.cliEnv (splitEnv e 2) #["capture", "--history", "work"]
      expect (offlineRc != 0 && offlineOut.isEmpty)
          "a session live in another runtime directory cannot masquerade as offline"
      let (_, otherListing, _) ← e.cliEnv (splitEnv e 2) #["ls", "--porcelain"]
      expect
          ((records otherListing).contains ("state", "live") &&
            (records otherListing).contains ("status", Linger.Display.Status.name .unknown))
          "listing does not offer another runtime's owned checkpoint as resumable"
      let (otherKillRc, _, _) ← e.cliEnv (splitEnv e 2) #["kill", "work"]
      IO.sleep 250
      let firstAfter := records (← e.cliEnv (splitEnv e 1) #["ls", "work", "--porcelain"]).2.1
      expect
          (otherKillRc != 0 && firstAfter.find? (·.1 == "pid") == firstPid &&
            (← System.FilePath.pathExists checkpoint))
          "commands in the other runtime cannot delete the live owner's saved state"
      let isolated := isolatedEnv e
      let (isolatedRc, _, _) ← e.typeInEnv isolated "work" #["true"]
      let separate := records (← e.cliEnv isolated #["ls", "work", "--porcelain"]).2.1
      let separatePid := separate.find? (·.1 == "pid")
      expect (isolatedRc == 0 && separatePid.isSome && separatePid != firstPid)
          "independent runtime and state directories allow the same session name"
      let _ ← e.cliEnv isolated #["kill", "work"]
      let original := records (← e.cliEnv (splitEnv e 1) #["ls", "work", "--porcelain"]).2.1
      expect (original.find? (·.1 == "pid") == firstPid)
          "ending an independent namesake leaves the original session intact"
      let _ ← e.cliEnv (splitEnv e 1) #["kill", "work"]
      let released ←
        waitFor 3000 do
            return !(← System.FilePath.pathExists s!"{e.dir}/r1/linger/work.sock")
      let (handoffRc, _, _) ← e.typeInEnv (splitEnv e 2) "work" #["true"]
      let successor := records (← e.cliEnv (splitEnv e 2) #["ls", "work", "--porcelain"]).2.1
      expect
          (released && handoffRc == 0 && (successor.find? (·.1 == "pid")).isSome &&
            successor.find? (·.1 == "pid") != firstPid)
          "ownership can transfer after cleanup, the lock files kept while a record names the name"
    finally
      e.killAll #["a_b", "saved", "ended", "race0", "race1", "race2", "race3"]
      for runtime in [1, 2] do
        let _ ← e.cliEnv (splitEnv e runtime) #["kill", "work"]
        pure ()
      let _ ← e.cliEnv (isolatedEnv e) #["kill", "work"]
      let _ ←
        waitFor 3000 do
            return !(← System.FilePath.pathExists s!"{e.dir}/a_b.sock") &&
                !(← System.FilePath.pathExists s!"{e.dir}/r1/linger/work.sock") &&
                !(← System.FilePath.pathExists s!"{e.dir}/r2/linger/work.sock") &&
                !(← System.FilePath.pathExists s!"{e.dir}/r3/linger/work.sock")

end Linger.Session.Suites.Identity
