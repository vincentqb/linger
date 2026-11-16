module

public import Verify.Harness
import Linger.Session.CoreCode.Checkpoint
import Linger.Target.CoreCode.Name

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

/-- State is bounded by what it means: after any command, every lock file names a session or
an ending. A command on a name no record names leaves no lock file of it, a kill that leaves its
name no record deletes them, a name with an ending keeps them, and a listing deletes the lock
files of names nothing names, but not one another process holds. -/
private def lockChecks (e : Env) : IO Unit := do
  let mut left : List String := []
  for args in
    [#["ls", "ghost", "--porcelain"], #["kill", "ghost"], #["resume", "ghost"],
      #["capture", "ghost"], #["capture", "--history", "ghost"], #["describe", "ghost", "x"],
      #["send", "ghost", "x"], #["detach", "ghost"], #["resize", "ghost", "80", "24"],
      #["wait", "--timeout", "0", "ghost"], #["attach", "--read-only", "ghost"]] do
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
  -- Deleting lock files keeps a name to one owner: while commands on a name no record names
  -- delete its lock files, as many `start`s of it race, exactly one takes the name.
  let mut owners : List Nat := []
  for round in [0:4] do
    let name := s!"race{round}"
    let spawn := fun (args : Array String) =>
      IO.Process.spawn
        { cmd := e.bin, args, env := e.procEnv, stdin := .null, stdout := .null, stderr := .null }
    let killers ← (List.range 6).mapM fun _ => spawn #["kill", name]
    let starters ← (List.range 4).mapM fun _ => spawn #["start", name, "/bin/sh"]
    let listers ← (List.range 4).mapM fun _ => spawn #["ls", "--porcelain"]
    for k in killers ++ listers do
      let _ ← k.wait
    let mut started := 0
    for k in starters do
      if (← k.wait) == 0 then
        started := started + 1
    owners := owners ++ [started]
    let _ ← e.cli #["kill", name]
  expect (owners.all (· == 1))
      s!"commands that delete a name's lock files leave racing starts one owner: {owners}"

/-- The identity suite: exact command targets and exclusive ownership of sockets and saved
state. -/
def run : IO UInt32 :=
  Env.suite "identity" fun e => do
    try
      lockChecks e
      let _ ← e.typeIn "a_b" #["true"]
      let pid ← e.info "a_b" "pid"
      for name in ["a b", "a/b", "", ".hidden", String.ofList (List.replicate 81 'a')] do
        let (rc, _, _) ← e.cli #["ls", name, "--porcelain"]
        expect (rc == 2) s!"invalid target {repr name} is a usage error"
      let (prefixRc, _, _) ← e.cli #["ls", "a", "--porcelain"]
      expect (prefixRc != 0) "command lookup never selects a name by prefix"
      let (killRc, _, _) ← e.cli #["kill", "a b"]
      expect (killRc == 2 && (← e.info "a_b" "pid") == pid && pid.isSome)
          "a malformed kill target cannot kill its sanitized alias"
      let (waitRc, _, _) ← e.cli #["wait", "missing name"]
      expect (waitRc == 2) "wait validates names even when no session exists"
      let (describeRc, _, _) ← e.cli #["describe", "a b", "text"]
      expect (describeRc == 2 && (← e.info "a_b" "description").isNone)
          "describe validates its target before changing any session"
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
