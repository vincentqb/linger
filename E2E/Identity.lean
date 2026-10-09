module

public import E2E.Harness
public import Linger.Core.Checkpoint
public import Linger.Core.Name

public section

/-! Exact command targets and exclusive ownership of sockets and saved state. -/

namespace E2E.Identity

open E2E.Harness
open Linger.Posix

def splitEnv (e : Env) (runtime : Nat) : Array (String × Option String) :=
  #[("LINGER_DIR", none), ("XDG_RUNTIME_DIR", some s!"{e.dir}/r{runtime}"),
    ("XDG_STATE_HOME", some s!"{e.dir}/state")]

/-- A third runtime directory with its own state directory. -/
def isolatedEnv (e : Env) : Array (String × Option String) :=
  (splitEnv e 3).push ("XDG_STATE_HOME", some s!"{e.dir}/state-other")

def run : IO UInt32 := do
  let e ← Env.make "identity"
  let mut f := 0
  try
    let _ ← e.cli #["run", "a_b", "true"]
    let pid ← e.info "a_b" "pid"
    for name in ["a b", "a/b", "", ".hidden", String.ofList (List.replicate 81 'a')] do
      let (rc, _, _) ← e.cli #["info", name]
      f := f + (← expect (rc == 2) s!"invalid target {repr name} is a usage error")
    let (prefixRc, _, _) ← e.cli #["info", "a"]
    f := f + (← expect (prefixRc != 0) "command lookup never selects a name by prefix")
    let (killRc, _, _) ← e.cli #["kill", "a b"]
    f :=
      f +
        (←
          expect (killRc == 2 && (← e.info "a_b" "pid") == pid && pid.isSome)
              "a malformed kill target cannot kill its sanitized alias")
    let (waitRc, _, _) ← e.cli #["wait", "missing name"]
    f := f + (← expect (waitRc == 2) "wait validates names even when no session exists")
    let (setRc, _, _) ← e.cli #["set", "a_b", "partial=bad", "=missing-key"]
    let (_, labels, _) ← e.cli #["get", "a_b"]
    f :=
      f +
        (←
          expect (setRc == 2 && !has labels "partial=")
              "set validates every argument before changing any label")
    let (bareSetRc, _, _) ← e.cli #["set", "a_b", "missing-equals"]
    let (emptyUnsetRc, _, _) ← e.cli #["unset", "a_b", ""]
    f :=
      f +
        (←
          expect (bareSetRc == 2 && emptyUnsetRc == 2)
              "label commands reject malformed arguments as usage errors")
    let vt := (Linger.Core.Vt.Vt.init 20 2).feedBytes "old\r\nmiddle\r\nscreen".toUTF8
    let bytes := ByteArray.mk (Linger.Core.Checkpoint.save ⟨vt, "/tmp", [("saved", "yes")]⟩).toArray
    let path := s!"{e.dir}/saved.ckpt"
    IO.FS.writeBinFile path bytes
    for (args, expected) in
      [(#["capture", "--history", "saved"], Linger.Core.Render.history vt),
        (#["capture", "saved"], Linger.Core.Render.screenText vt)] do
      let (rc, out, _) ← e.cli args
      f :=
        f +
          (←
            expect (rc == 0 && out.toUTF8.toList == expected)
                s!"offline {repr args} reads the saved terminal exactly")
    f :=
      f +
        (←
          expect
              ((← IO.FS.readBinFile path).toList == bytes.toList &&
                !(← System.FilePath.pathExists s!"{e.dir}/saved.sock"))
              "offline reads preserve the checkpoint and do not start a daemon")
    let (caseLiveRc, _, _) ← e.cli #["info", "A_B"]
    let (caseSavedRc, caseSavedOut, _) ← e.cli #["capture", "--history", "SAVED"]
    f :=
      f +
        (←
          expect (caseLiveRc != 0 && caseSavedRc != 0 && caseSavedOut.isEmpty)
              "case variants never resolve to an existing live or saved session")
    IO.FS.createDirAll s!"{e.dir}/.locks"
    for lock in [s!"{e.dir}/saved.lock", s!"{e.dir}/.locks/saved.lock"] do
      let fd ← flock lock
      unless fd ≥ 0 do
        throw (IO.userError s!"fixture lock unavailable: {lock}")
      try
        let (rc, out, _) ← e.cli #["capture", "--history", "saved"]
        f :=
          f + (← expect (rc != 0 && out.isEmpty) s!"offline reads refuse an owned resource: {lock}")
      finally
        close fd.toUInt64.toUInt32
    IO.FS.writeBinFile s!"{e.dir}/bad.ckpt" ⟨#[1, 2, 3]⟩
    let (badRc, badOut, _) ← e.cli #["capture", "bad"]
    f := f + (← expect (badRc != 0 && badOut.isEmpty) "corrupt offline data fails without output")
    let host := Linger.Core.Name.sanitize (← gethostname)
    let checkpoint := s!"{e.dir}/state/linger/{host}/work.ckpt"
    let (firstRc, _, _) ← e.cliEnv (splitEnv e 1) #["run", "work", "true"]
    let saved ← waitFor 3000 (System.FilePath.pathExists checkpoint)
    let first := records (← e.cliEnv (splitEnv e 1) #["info", "work"]).2.1
    let firstPid := first.find? (·.1 == "pid")
    f :=
      f +
        (←
          expect (firstRc == 0 && saved && firstPid.isSome)
              "first runtime owns a live session and its checkpoint")
    let (secondRc, _, _) ← e.cliEnv (splitEnv e 2) #["run", "work", "true"]
    f :=
      f + (← expect (secondRc != 0) "another runtime directory cannot claim the same saved session")
    let (offlineRc, offlineOut, _) ← e.cliEnv (splitEnv e 2) #["capture", "--history", "work"]
    f :=
      f +
        (←
          expect (offlineRc != 0 && offlineOut.isEmpty)
              "a session live in another runtime directory cannot masquerade as offline")
    let (_, otherListing, _) ← e.cliEnv (splitEnv e 2) #["ls", "--porcelain"]
    f :=
      f +
        (←
          expect
              ((records otherListing).contains ("state", "live") &&
                (records otherListing).contains ("status", Linger.Core.Status.name .unknown))
              "listing does not offer another runtime's owned checkpoint as resumable")
    let (otherKillRc, _, _) ← e.cliEnv (splitEnv e 2) #["kill", "work"]
    IO.sleep 250
    let firstAfter := records (← e.cliEnv (splitEnv e 1) #["info", "work"]).2.1
    f :=
      f +
        (←
          expect
              (otherKillRc != 0 && firstAfter.find? (·.1 == "pid") == firstPid &&
                (← System.FilePath.pathExists checkpoint))
              "commands in the other runtime cannot delete the live owner's saved state")
    let isolated := isolatedEnv e
    let (isolatedRc, _, _) ← e.cliEnv isolated #["run", "work", "true"]
    let separate := records (← e.cliEnv isolated #["info", "work"]).2.1
    let separatePid := separate.find? (·.1 == "pid")
    f :=
      f +
        (←
          expect (isolatedRc == 0 && separatePid.isSome && separatePid != firstPid)
              "independent runtime and state directories allow the same session name")
    let _ ← e.cliEnv isolated #["kill", "work"]
    let original := records (← e.cliEnv (splitEnv e 1) #["info", "work"]).2.1
    f :=
      f +
        (←
          expect (original.find? (·.1 == "pid") == firstPid)
              "ending an independent namesake leaves the original session intact")
    let _ ← e.cliEnv (splitEnv e 1) #["kill", "work"]
    let released ←
      waitFor 3000 do
          return !(← System.FilePath.pathExists s!"{e.dir}/r1/linger/work.sock")
    let (handoffRc, _, _) ← e.cliEnv (splitEnv e 2) #["run", "work", "true"]
    let successor := records (← e.cliEnv (splitEnv e 2) #["info", "work"]).2.1
    f :=
      f +
        (←
          expect
              (released && handoffRc == 0 && (successor.find? (·.1 == "pid")).isSome &&
                successor.find? (·.1 == "pid") != firstPid)
              "ownership can transfer after cleanup without deleting the lock files")
  finally
    e.killAll #["a_b", "saved"]
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
  verdict e f

end E2E.Identity
