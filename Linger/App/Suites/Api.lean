module

public import Verify.Harness
import Linger.App.WorldCode.Api

public section

/-! # The Lean API: linger as a library, its command line as a renderer

A Lean program calls the API in a namespace it names, whatever its environment's `LINGER_DIR`,
XDG variables and HOME say, with its standard output and standard error on pipes: it starts a
session, sends it input, captures its screen, lists it, waits for it, with a deadline and without,
and kills it, and gets typed results back, what each found and what it shows, while the API writes
nothing to either stream and tells what it says only to the caller. A remote target with no
transport passed is refused, and no transport runs. -/

namespace Linger.App.Suites.Api

open Verify.Harness
open Os.Shell

/-- What the probe found of each call, one `key<TAB>value` line each, in `report`. -/
private def tell (report : String) (key value : String) : IO Unit := do
  let h ← IO.FS.Handle.mk report .append
  h.putStrLn s!"{key}\t{value}"

/-- Whether `bytes`, as text, holds `text`. -/
private def shows (bytes : ByteArray) (text : String) : Bool :=
  (String.fromUTF8? bytes).any (·.contains text)

/-- The probe: the API's calls in the namespace `dir`, with the linger executable `bin`, telling
what each found in `report`; run with both standard streams on pipes and an environment that
names another namespace. -/
def probe (args : List String) : IO UInt32 := do
  let [dir, bin, report] := args | return 98
  let said ← IO.mkRef (#[] : Array String)
  let env : Linger.App.Api.Env :=
    { dirs := { sockets := dir, state := dir }, exe := bin,
      say := fun s => said.modify (·.push s.text) }
  let program := "printf 'api-ready\\n'; read line; printf 'got %s\\n' \"$line\"; exit 3"
  tell report "start" (reprStr (← Linger.App.Api.start env "api" "/bin/sh" ["-c", program]))
  let ready ←
    waitFor 3000 do
        return shows (← Linger.App.Api.capture env "api").2 "api-ready"
  tell report "ready" (toString ready)
  tell report "send" (reprStr (← Linger.App.Api.send env "api" (.text ["hello\r"])))
  let captured ← IO.mkRef ""
  let got ←
    waitFor 3000 do
        let (found, bytes) ← Linger.App.Api.capture env "api"
        captured.set (reprStr found)
        return shows bytes "got hello"
  tell report "capture" (← captured.get)
  tell report "got" (toString got)
  let listed ← Linger.App.Api.list env (.named true ["api"])
  match listed.shown with
  | .rows _ rows =>
    tell report "list" (reprStr listed.found)
    tell report "listed" (toString (rows.any (·.lookup "name" == some "api")))
  | _ =>
    tell report "list" "no rows"
  tell report "wait" (reprStr (← Linger.App.Api.wait env ["api"]))
  tell report "start2" (reprStr (← Linger.App.Api.start env "api2" "/bin/sleep" ["30"]))
  let due := (← monotonicMs) + 300
  tell report "late" (reprStr (← Linger.App.Api.wait env ["api2"] (some due)))
  tell report "kill" (reprStr (← Linger.App.Api.kill env "api2"))
  tell report "killed" (reprStr (← Linger.App.Api.wait env ["api2"]))
  tell report "ghost" (reprStr (← Linger.App.Api.detach env "ghost"))
  tell report "remote" (reprStr (← Linger.App.Api.detach env "x@far"))
  tell report "said" (String.intercalate " | " (← said.get).toList)
  return 0

/-- The API's calls, in a child whose standard streams are pipes and whose environment names
another namespace, and what they found. -/
private def apiChecks (e : Env) : IO Unit := do
  let report := s!"{e.dir}/api.report"
  let wrong := s!"{e.dir}/wrong"
  IO.FS.createDirAll wrong
  -- an `ssh` on the PATH records that it ran, as a transport would
  let bins := s!"{e.dir}/bins"
  IO.FS.createDirAll bins
  let ran := s!"{e.dir}/ssh.ran"
  IO.FS.writeFile s!"{bins}/ssh" s!"#!/bin/sh\n: > '{ran}'\nexit 0\n"
  chmod s!"{bins}/ssh" 0o755
  let path := ((← IO.getEnv "PATH").getD "/usr/bin:/bin")
  let child ←
    IO.Process.spawn
        { cmd := (← IO.appPath).toString, args := #["--api-probe", e.dir, e.bin, report],
          stdin := .null, stdout := .piped, stderr := .piped,
          env :=
            #[("LINGER_DIR", some wrong), ("XDG_RUNTIME_DIR", some wrong),
                ("XDG_STATE_HOME", some wrong), ("HOME", some wrong), ("SHELL", some "/bin/sh"),
                ("PATH", some s!"{bins}:{path}")] ++
              e.sourceEnv.map fun (k, v) => (k, some v) }
  let out ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let err ← child.stderr.readToEnd
  let rc ← child.wait
  let out ← IO.ofExcept out.get
  let found := records (← IO.FS.readFile report)
  let said (key : String) := (found.find? (·.1 == key)).map (·.2)
  expect (rc == 0 && out.isEmpty && err.isEmpty)
      s!"the API writes nothing to standard output or standard error (rc={rc}, {out.length} and \
        {err.length} bytes)"
  let (lsRc, ls, _) ← e.cli #["ls", "api", "--porcelain"]
  expect
      (said "start" == some "Linger.App.Api.Found.done" && said "ready" == some "true" &&
        lsRc == 0 &&
        has ls "name\tapi" &&
        (← System.FilePath.readDir wrong).isEmpty)
      s!"start finds done, in the namespace the caller names and not LINGER_DIR's ({said "start"})"
  expect
      (said "send" == some "Linger.App.Api.Found.done" && said "got" == some "true" &&
        said "capture" == some "Linger.App.Api.Found.done")
      s!"send delivers the input, and capture's bytes show the program read it ({said "send"})"
  expect (said "list" == some "Linger.App.Api.Found.done" && said "listed" == some "true")
      s!"ls gives the session's record ({said "list"})"
  expect
      (said "wait" ==
        some
          "Linger.App.Api.Found.ended (Linger.Session.Ending.program (Linger.Session.Outcome.exited 3))")
      s!"wait finds how the program ended ({said "wait"})"
  expect
      (said "start2" == some "Linger.App.Api.Found.done" &&
        said "late" == some "Linger.App.Api.Found.late")
      s!"a wait the Lean caller gives a deadline finds late, the session running ({said "late"})"
  expect
      (said "kill" == some "Linger.App.Api.Found.done" &&
        said "killed" ==
          some
            "Linger.App.Api.Found.ended (Linger.Session.Ending.program (Linger.Session.Outcome.signaled 1))")
      s!"kill finds done once the session has ended ({said "kill"}, {said "killed"})"
  expect
      (said "ghost" == some "Linger.App.Api.Found.missing" &&
        (said "said").any (has · "no session 'ghost'"))
      s!"what the API says goes to its caller ({said "ghost"}, {said "said"})"
  expect
      (said "remote" == some "Linger.App.Api.Found.refused" && !(← System.FilePath.pathExists ran))
      s!"a remote target with no transport passed is refused, and no transport runs \
        ({said "remote"})"

/-- The suite. -/
def run :
    IO UInt32 := Env.suite "api" fun e => do
    try
      apiChecks e
    finally
      e.endSessions

end Linger.App.Suites.Api
