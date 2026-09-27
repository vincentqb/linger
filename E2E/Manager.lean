module

public import E2E.Harness
public import Manager.Picker

public section

/-! # E2E.Manager — public entry point and shared picker executor

The helper mode of this same test binary records exact argument vectors and
observes the terminal before the manager, in each listing/attach child, and
after the manager returns. `stty -g` is a test observer, resolved before giving
the manager a restricted PATH. Comparing that portable representation avoids
inspecting the opaque termios blob's padding.

Synthetic failure, argv and terminal cases call `Manager.Picker.run` through
the test probe with a fixture-owned absolute recorder path. These test the
shared executor; public CLI checks and source gates cover entry-point wiring.
Help, argument validation, terminal dispatch and live attach/detach drive the
actual `linger` binary with no `linger` on the fixture PATH.
`E2ETest.main` dispatches `--manager-probe <args>` to `probe` below.
-/

namespace E2E.Manager

open E2E.Harness
open Linger.Posix
open Linger.Core.Render (modeSet csiNum screenText)
open Linger.Core.Vt (Vt)

private def call (args : List String) : String :=
  "CALL\x00linger\x00" ++ String.intercalate "\x00" args ++ "\x00\n"

private def quote (text : String) : String := "'" ++ text.replace "'" "'\\''" ++ "'"

private def readText (path : System.FilePath) : IO String := do
  if ← path.pathExists then
    IO.FS.readFile path
  else
    pure ""

private def appendText (path : System.FilePath) (text : String) : IO Unit := do
  let file ← IO.FS.Handle.mk path .append
  file.putStr text
  file.flush

private def numberFile (path : System.FilePath) (fallback : Nat := 0) : IO Nat := do
  return (← readText path).trimAscii.toString.toNat? |>.getD fallback

private def snapshot : IO String := do
  let some stty ←
    IO.getEnv "MANAGER_TEST_STTY" | throw (IO.userError "manager probe has no stty observer")
  let result ←
    IO.Process.output { cmd := "/bin/sh", args := #["-c", s!"exec {quote stty} -g </dev/tty"] }
  if result.exitCode != 0 || result.stdout.trimAscii.isEmpty then
    throw (IO.userError s!"manager terminal observation failed: {result.stderr}")
  return result.stdout.trimAscii.toString

private def waitChild {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (ms : Nat := 15000) : IO UInt32 := do
  if let some rc← waitProcess child ms then
    return rc
  child.kill
  if let some rc← waitProcess child 1000 then
    return rc
  kill child.pid 9
  let _ ← waitProcess child 1000
  return 99

private def recordCommand (root : System.FilePath) (args : List String) : IO UInt32 := do
  let count ← numberFile (root / "command-count")
  if count ≥ 16 then
    throw (IO.userError "manager probe command budget exceeded")
  IO.FS.writeFile (root / "command-count") (toString (count + 1))
  appendText (root / "calls") (call args)
  IO.FS.writeFile (root / s!"termios-{count + 1}") (← snapshot)
  let ttyIn ← (← IO.getStdin).isTty
  let ttyOut ← (← IO.getStdout).isTty
  IO.FS.writeFile (root / s!"ttys-{count + 1}") s!"{ttyIn},{ttyOut}"
  match args with
  | ["ls", "-r", "--porcelain"] =>
    let output ← IO.getStdout
    output.putStr (← readText (root / "listing"))
    output.flush
    return UInt32.ofNat (← numberFile (root / "listing-rc"))
  | ["attach", _] =>
    let count ← numberFile (root / "attach-count")
    IO.FS.writeFile (root / "attach-count") (toString (count + 1))
    writeAll stdoutFd s!"\r\nMANAGER-ATTACH-{count + 1}\r\n".toUTF8
    return UInt32.ofNat (← numberFile (root / "attach-rc") 7)
  | _ =>
    return 98

private def launch (root : System.FilePath) (manager mode : String) (args : List String) :
    IO UInt32 := do
  IO.FS.writeFile (root / "before") (← snapshot)
  let (cmd, args) :=
    if mode == "readonly-output" then
      ("/bin/sh", #["-c", "exec \"$@\" 1</dev/tty", "--", manager] ++ args.toArray)
    else
      if mode == "stdin-only" then
        ("/bin/sh",
          #["-c", s!"exec \"$@\" >{quote (root / "stdout").toString}", "--", manager] ++
            args.toArray)
      else (manager, args.toArray)
  -- spawnPty accepts K=V entries; remove presence-sensitive flags at this boundary.
  let child ←
    IO.Process.spawn
        { cmd, args, env := #[("LINGER_SESSION", none), ("LINGER_NO_DETACH_KEY", none)],
          stdin := if mode == "stdout-only" then .null else .inherit }
  IO.FS.writeFile (root / "manager-pid") (toString child.pid)
  let rc ← waitChild child
  IO.FS.writeFile (root / "after") (← snapshot)
  IO.FS.writeFile (root / "result") (toString rc)
  writeAll stdoutFd s!"\r\nMANAGER-EXIT:{rc}\r\n".toUTF8
  return rc

/-- Test-only child dispatch for the terminal wrapper, shared picker and recorder. -/
def probe (args : List String) : IO UInt32 := do
  let some dir ← IO.getEnv "MANAGER_TEST_CASE" |
    IO.eprintln "manager probe has no private case directory";
    return 98
  let root := System.FilePath.mk dir
  try
    match args with
    | "command" :: rest =>
      recordCommand root rest
    | "launch" :: manager :: mode :: rest =>
      launch root manager mode rest
    | ["picker", executable] =>
      Manager.Picker.run executable
    | _ =>
      pure 98
  catch err =>
    appendText (root / "probe-errors") s!"{err}\n"
    if args.head? == some "picker" then
      IO.eprintln s!"picker probe: {err}"
      return 1
    if args.head? == some "launch" then
      IO.FS.writeFile (root / "result") "98"
      writeAll stdoutFd "\r\nMANAGER-EXIT:98\r\n".toUTF8
    else
      IO.eprintln s!"manager probe: {err}"
    return 98

private structure Fixture where
  root : System.FilePath
  manager : String
  self : String
  executable : String
  managerArgs : Array String := #[]
  env : Array (String × Option String)

private def Fixture.make (e : Env) (slug : String) : IO Fixture := do
  let root := System.FilePath.mk e.dir / slug
  let bin := root / "bin"
  IO.FS.createDirAll bin
  let self := (← IO.appPath).toString
  let executable := ((← IO.FS.realPath root) / "record command").toString
  let observer ← IO.Process.output { cmd := "/bin/sh", args := #["-c", "command -v stty"] }
  if observer.exitCode != 0 || observer.stdout.trimAscii.isEmpty then
    throw (IO.userError "stty is required to observe manager terminal restoration")
  IO.FS.writeFile executable s!"#!/bin/sh\nexec {quote self} --manager-probe command \"$@\"\n"
  let chmod ← IO.Process.output { cmd := "chmod", args := #["+x", executable] }
  if chmod.exitCode != 0 then
    throw (IO.userError s!"manager recorder chmod failed: {chmod.stderr}")
  IO.FS.writeFile (root / "listing") "name\tAlpha\nname\tBeta\nname\tGamma\n"
  IO.FS.writeFile (root / "listing-rc") "0"
  IO.FS.writeFile (root / "attach-rc") "7"
  let env :=
    e.procEnv ++
      #[("PATH", some bin.toString), ("HOME", some root.toString), ("TERM", some "xterm-256color"),
        ("LINGER_SESSION", none), ("LINGER_NO_DETACH_KEY", none),
        ("MANAGER_TEST_CASE", some root.toString),
        ("MANAGER_TEST_STTY", some observer.stdout.trimAscii.toString)]
  return { root, manager := e.bin, self, executable, env }

private def Fixture.picker (f : Fixture) : Fixture :=
  { f with
    manager := f.self, managerArgs := #["--manager-probe", "picker", f.executable] }

private def Fixture.calls (f : Fixture) : IO String := readText (f.root / "calls")

private def Fixture.listing (f : Fixture) (text : String) (rc : Nat := 0) : IO Unit := do
  IO.FS.writeFile (f.root / "listing") text
  IO.FS.writeFile (f.root / "listing-rc") (toString rc)

private def Fixture.piped (f : Fixture) (args : Array String) : IO (UInt32 × String × String) := do
  let child ←
    IO.Process.spawn
        { cmd := f.manager, args := f.managerArgs ++ args, env := f.env, stdin := .null,
          stdout := .piped, stderr := .piped }
  let rc ← waitChild child 4000
  return (rc, ← child.stdout.readToEnd, ← child.stderr.readToEnd)

private structure Session where
  fixture : Fixture
  client : Client
  output : IO.Ref ByteArray

private def Fixture.start (f : Fixture) (args : Array String := #[]) (mode : String := "both")
    (cols : UInt32 := 80) (rows : UInt32 := 12) : IO Session := do
  let env := f.env.map fun (key, value) => s!"{key}={value.getD ""}"
  let (pid, fd) ←
    spawnPty cols rows "" f.self
        (#["--manager-probe", "launch", f.manager, mode] ++ f.managerArgs ++ args) env
  return { fixture := f, client := { pid, fd }, output := ← IO.mkRef ByteArray.empty }

private def Session.mark (s : Session) : IO Nat := return (← s.output.get).size

/-- Read under a deadline, retaining all bytes for order and cleanup assertions.
EOF and the wrapper's completion marker end a failed positive wait promptly. -/
private def Session.until (s : Session) (needle : String) (start : Nat := 0) (ms : Nat := 4000) :
    IO Bool := do
  let deadline := (← monotonicMs) + ms
  let mut done := false
  while !done && (← monotonicMs) < deadline do
    let current ← s.output.get
    let tail := current.extract start current.size
    if hasText tail needle then
      return true
    if hasText tail "MANAGER-EXIT:" then
      return false
    let fds := #[s.client.fd]
    let events ← poll fds #[POLLIN] 50
    if events[0]! &&& (POLLIN ||| POLLERR ||| POLLHUP) != 0 then
      match ← read s.client.fd 65536 with
      | none =>
        done := true
      | some bs =>
        if !bs.isEmpty then
          s.output.modify (· ++ bs)
  return hasText ((← s.output.get).extract start (← s.output.get).size) needle

/-- Negative assertions must observe an interval, not accept the first quiet poll. -/
private def Session.observe (s : Session) (ms : Nat) : IO Unit := do
  let deadline := (← monotonicMs) + ms
  let fds := #[s.client.fd]
  while (← monotonicMs) < deadline do
    let events ← poll fds #[POLLIN] 10
    if events[0]! &&& (POLLIN ||| POLLERR ||| POLLHUP) != 0 then
      match ← read s.client.fd 65536 with
      | none =>
        return
      | some bytes =>
        s.output.modify (· ++ bytes)

private def Session.send (s : Session) (bytes : ByteArray) : IO Unit := writeAll s.client.fd bytes

private def Session.text (s : Session) (text : String) : IO Unit := s.send text.toUTF8

private def Session.prompt (s : Session) (query : String := "") (start : Nat := 0) :
    IO Bool := s.until ("linger> " ++ query) start

private def Session.typeQuery (s : Session) (text query : String) : IO Bool := do
  let start ← s.mark
  s.text text
  s.prompt query start

private def Session.result (s : Session) : IO (Option Nat) := do
  let _ ← s.until "MANAGER-EXIT:"
  let _ ← s.client.reap 1000
  return (← readText (s.fixture.root / "result")).toNat?

private def Session.retire (s : Session) : IO Unit := do
  unless ← (s.fixture.root / "result").pathExists do
    try
      s.text "\x03"
    catch _ =>
      pure ()
    let _ ← s.until "MANAGER-EXIT:" 0 1000
    unless ← (s.fixture.root / "result").pathExists do
      let pid ← numberFile (s.fixture.root / "manager-pid")
      if pid > 0 then
        try
          kill (UInt32.ofNat pid) 15
        catch _ =>
          pure ()
      let _ ← s.until "MANAGER-EXIT:" 0 1000
  IO.FS.writeBinFile (s.fixture.root / "terminal.bin") (← s.output.get)
  s.client.bye (sendDetach := false)

private def withSession (f : Fixture) (args : Array String) (body : Session → IO Bool)
    (mode : String := "both") (cols : UInt32 := 80) (rows : UInt32 := 12) : IO Bool := do
  let s ← f.start args mode cols rows
  try
    body s
  finally
    s.retire

private def check (e : Env) (slug label : String) (body : Fixture → IO Bool) : IO Nat := do
  let ok ←
    try
      body (← Fixture.make e slug)
    catch err =>
      IO.eprintln s!"note: manager {slug}: {err}"
      pure false
  expect ok label

private def sequenceCount (out : ByteArray) (seq : List UInt8) : Nat :=
  let text := String.fromUTF8? out |>.getD ""
  let needle := String.fromUTF8? (ByteArray.mk seq.toArray) |>.getD ""
  (text.splitOn needle).length - 1

private def ordered (out : ByteArray) (first second : List UInt8) : Bool :=
  match findBytes out first, findBytes out second with
  | some a, some b => a < b
  | _, _ => false

private def modesRestored (out : ByteArray) (entries : Nat) : Bool :=
  [(modeSet 1049 true, modeSet 1049 false), (modeSet 25 false, modeSet 25 true),
          (modeSet 2004 true, modeSet 2004 false)].all
      (fun (enter, leave) =>
        sequenceCount out enter == entries && sequenceCount out leave == entries &&
          ordered out enter leave) &&
    !hasBytes out (csiNum 3 0x4A)

private def termiosRestored (s : Session) (rc : Nat) : IO Bool := do
  let result ← s.result
  let before ← readText (s.fixture.root / "before")
  let after ← readText (s.fixture.root / "after")
  return result == some rc && !before.isEmpty && before == after

private def restored (s : Session) (rc : Nat) (entries : Nat := 1) : IO Bool := do
  return (← termiosRestored s rc) && modesRestored (← s.output.get) entries

/-- Compare only the command's output, before the launcher's completion marker.
The pty expands each newline; redirected stdout retains the original bytes. -/
private def Session.printed (s : Session) (expected : String) (mode : String := "both") : IO Bool :=
  do
  let output ← s.output.get
  let some stop := findText output "\r\r\nMANAGER-EXIT:" | return false
  let commandOutput := output.extract 0 stop
  if mode == "stdin-only" then
    return commandOutput.isEmpty && (← readText (s.fixture.root / "stdout")) == expected
  return commandOutput == (expected.replace "\n" "\r\n").toUTF8

private def childNormal (f : Fixture) (index : Nat) (attach : Bool := false) : IO Bool := do
  let before ← readText (f.root / "before")
  return !before.isEmpty && (← readText (f.root / s!"termios-{index}")) == before &&
      (!attach || (← readText (f.root / s!"ttys-{index}")) == "true,true")

private def beforeAttach (s : Session) (count : Nat := 1) (entries : Nat := 1) : IO Bool := do
  let out ← s.output.get
  let some position := findText out s!"MANAGER-ATTACH-{count}" | return false
  return modesRestored (out.extract 0 position) entries

/-- The next prompt must follow this attach, with an empty query and the new
snapshot's first row selected. An earlier prompt cannot satisfy the wait. -/
private def returned (s : Session) (target : String) (count : Nat := 1) : IO Bool := do
  let marker := s!"MANAGER-ATTACH-{count}"
  unless ← s.until marker do
    return false
  let some position := findText (← s.output.get) marker | return false
  let start := position + marker.utf8ByteSize
  unless ← s.until "linger> \r\n" start do
    return false
  return ← s.until ("> " ++ target) start

/-- Accept from the current snapshot, observe a different listing after attach,
then cancel explicitly. Count every visit, including any preceding refresh. -/
private def acceptThenCancel (s : Session) (keys : String := "\r") (visits : Nat := 2) : IO Bool :=
  do
  s.fixture.listing "name\tFresh\nname\tOther\n"
  s.text keys
  unless ← returned s "Fresh" do
    return false
  s.text "\x03"
  let clean ← restored s 130 visits
  return clean && (← beforeAttach s 1 (visits - 1)) && (← childNormal s.fixture 1) &&
      (← childNormal s.fixture visits true) &&
      (← childNormal s.fixture (visits + 1))

private def usageChecks (e : Env) : IO Nat := do
  let mut failures := 0
  failures :=
    failures +
      (←
        check e "help" "linger help aliases agree without a terminal or linger on PATH" fun f => do
            let (rc, out, err) ← f.piped #["--help"]
            let (shortRc, shortOut, shortErr) ← f.piped #["-h"]
            let (helpRc, helpOut, helpErr) ← f.piped #["help"]
            let (hRc, hOut, hErr) ← f.piped #["h"]
            IO.FS.writeFile (f.root / "help.txt") out
            return rc == 0 && shortRc == 0 && helpRc == 0 && hRc == 0 && shortOut == out &&
                helpOut == out &&
                hOut == out &&
                [err, shortErr, helpErr, hErr].all String.isEmpty &&
                has out "Usage: linger" &&
                (out.splitOn "\n").any (fun line => line.trimAscii.toString.startsWith "select ") &&
                has out "linger import [SAVE]" &&
                !has out "--loop" &&
                !has out "--restore-processes" &&
                !has out "lz")
  failures :=
    failures +
      (←
        check e "usage" "linger rejects malformed arguments and select/import operands" fun f => do
            let mut ok := true
            for args in
              [#["work"], #["--unknown"], #["--help", "extra"], #["-h", "extra"],
                #["help", "extra"], #["ls", "--unknown"], #["select", ""], #["select", "work"],
                #["select", "--help"], #["select", "-h"], #["select", "one", "two"],
                #["--loop", ""], #["--loop", "one", "two"], #["import-resurrect"], #["import", ""],
                #["import", "--unknown"], #["import", "--help"], #["import", "-h"],
                #["import", "-save"], #["import", "one", "two"]] do
              let (rc, _, _) ← f.piped args
              appendText (f.root / "usage-results") s!"{repr args}: {rc}\n"
              ok := ok && rc == 2
            return ok)
  for (slug, args) in [("loop", #["--loop"]), ("loop-target", #["--loop", "-work@me@dev-a"])] do
    failures :=
      failures +
        (←
          check e s!"removed-{slug}"
              s!"linger rejects removed loop arguments in a terminal ({slug})" fun f =>
              withSession f args fun s => do
                return (← termiosRestored s 2) && !hasBytes (← s.output.get) (modeSet 1049 true))
  failures :=
    failures +
      (←
        check e "select-extra" "linger select rejects extra operands before terminal entry" fun f =>
            withSession f #["select", "extra"] fun s => do
              return (← termiosRestored s 2) && !hasBytes (← s.output.get) (modeSet 1049 true) &&
                  !hasText (← s.output.get) "linger>")
  failures :=
    failures +
      (←
        check e "restore-option" "linger rejects process replay options without creating sessions"
            fun f => do
            let saves := f.root / ".tmux" / "resurrect"
            IO.FS.createDirAll saves
            let save := saves / "last"
            IO.FS.writeFile save
                (String.intercalate "\t"
                    ["pane", "work", "1", "0", ":", "0", "title", ":" ++ f.root.toString, "1", "sh",
                      ":vim"] ++
                  "\n")
            let before ← e.out #["ls", "--porcelain"]
            let mut ok := true
            for args in
              [#["import", "--restore-processes"],
                #["import", "--restore-processes", save.toString],
                #["import", save.toString, "--restore-processes"]] do
              let (rc, _, _) ← f.piped args
              appendText (f.root / "usage-results") s!"{repr args}: {rc}\n"
              ok := ok && rc == 2
            return ok && (← e.out #["ls", "--porcelain"]) == before)
  failures :=
    failures +
      (←
        check e "help-neither"
            "bare linger prints exactly help without creating state (neither tty)" fun f => do
            let state := f.root / "absent"
            let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
            let (helpRc, expected, helpErr) ← f.piped #["help"]
            let (rc, out, err) ← f.piped #[]
            IO.FS.writeFile (f.root / "stdout") out
            return helpRc == 0 && !expected.isEmpty && helpErr.isEmpty && rc == 0 &&
                out == expected &&
                err.isEmpty &&
                !(← state.pathExists))
  for mode in ["stdin-only", "stdout-only", "both"] do
    failures :=
      failures +
        (←
          check e s!"help-{mode}"
              s!"bare linger prints exactly help without creating state or changing terminal modes ({mode})"
              fun f => do
              let state := f.root / "absent"
              let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
              let (helpRc, expected, helpErr) ← f.piped #["help"]
              withSession f #[]
                  (fun s => do
                    let clean ← termiosRestored s 0
                    return helpRc == 0 && !expected.isEmpty && helpErr.isEmpty && clean &&
                        (← s.printed expected mode) &&
                        !(← state.pathExists))
                  mode)
  failures :=
    failures +
      (←
        check e "help-sockets"
            "bare linger help neither probes live sockets nor cleans stale sockets" fun f => do
            let f := { f with env := f.env.push ("LINGER_DIR", some f.root.toString) }
            let (helpRc, expected, helpErr) ← f.piped #["help"]
            let stale := f.root / "stale.sock"
            close (← unixListen stale.toString)
            let listener ← unixListen (f.root / "unread.sock").toString
            try
              let (rc, out, err) ← f.piped #[]
              let events ← poll #[listener] #[POLLIN] 0
              let untouched ← stale.pathExists
              IO.FS.writeFile (f.root / "stdout") out
              IO.FS.writeFile (f.root / "socket-observation")
                  s!"exit={rc}\nlistener-events={events[0]!}\nstale-preserved={untouched}\n"
              return helpRc == 0 && !expected.isEmpty && helpErr.isEmpty && rc == 0 &&
                  out == expected &&
                  err.isEmpty &&
                  events[0]! == 0 &&
                  untouched
            finally
              close listener)
  failures :=
    failures +
      (←
        check e "listing-both" "linger ls prints exactly one listing and exits in a terminal"
            fun f => do
            let (listRc, expected, listErr) ← f.piped #["ls"]
            withSession f #["ls"] fun s => do
                return listRc == 0 && !expected.isEmpty && listErr.isEmpty &&
                    (← termiosRestored s 0) &&
                    (← s.printed expected))
  failures :=
    failures +
      (←
        check e "select-neither" "linger select requires both terminal streams (neither tty)"
            fun f => do
            let state := f.root / "absent"
            let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
            let (rc, out, err) ← f.piped #["select"]
            IO.FS.writeFile (f.root / "stderr") err
            return rc == 1 && out.isEmpty && has err "terminal input and output" &&
                !has err "\x1b" &&
                !(← state.pathExists))
  for mode in ["stdin-only", "stdout-only"] do
    failures :=
      failures +
        (←
          check e s!"select-{mode}"
              s!"linger select rejects redirection before listing or terminal entry ({mode})"
              fun f => do
              let state := f.root / "absent"
              let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
              withSession f #["select"]
                  (fun s => do
                    let clean ← termiosRestored s 1
                    let output ← s.output.get
                    return clean && hasText output "terminal input and output" &&
                        !hasText output "linger>" &&
                        !hasText output "\x1b" &&
                        (← readText (f.root / "stdout")).isEmpty &&
                        !(← state.pathExists))
                  mode)
  failures :=
    failures +
      (←
        check e "tty-select"
            "linger select waits in a terminal and unmatched Enter creates nothing with no linger on PATH"
            fun f => do
            let state := f.root / "state"
            let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
            withSession f #["select"] fun s => do
                unless ← s.prompt do
                  return false
                unless ← s.typeQuery "new-session" "new-session" do
                  return false
                s.text "\r"
                s.observe 350
                let waiting := !(← (f.root / "result").pathExists)
                let noSession := (← state.readDir).isEmpty
                s.text "\x03"
                return waiting && noSession && (← restored s 130))
  return failures

private def failureChecks (e : Env) : IO Nat := do
  let mut failures := 0
  for (slug, listing) in [("empty", ""), ("partial", "name\tAlpha\n")] do
    failures :=
      failures +
        (←
          check e s!"listing-{slug}"
              s!"picker probe preserves failed listing status before UI ({slug})" fun f => do
              f.listing listing 7
              withSession f.picker #[] fun s => do
                  let rc ← s.result
                  return rc == some 7 && (← f.calls) == call ["ls", "-r", "--porcelain"] &&
                      hasText (← s.output.get) "linger: could not list sessions (exit 7)" &&
                      !hasBytes (← s.output.get) (modeSet 1049 true) &&
                      (← childNormal f 1))
  let invalid :=
    [("empty-name", "name\t\n"), ("missing-field", "name\n"), ("extra-field", "name\tbad\textra\n"),
      ("duplicate", "name\tAlpha\n"), ("cr", "name\tbad\r\n"), ("escape", "name\tbad\x1b[2J\n"),
      ("nul", "name\tbad\x00name\n")]
  for (slug, bad) in invalid do
    failures :=
      failures +
        (←
          check e s!"bad-{slug}" s!"picker probe rejects the whole malformed listing ({slug})"
              fun f => do
              f.listing ("name\tAlpha\n" ++ bad)
              withSession f.picker #[] fun s => do
                  let rc ← s.result
                  return rc == some 1 && (← f.calls) == call ["ls", "-r", "--porcelain"] &&
                      !hasBytes (← s.output.get) (modeSet 1049 true))
  failures :=
    failures +
      (←
        check e "missing-command"
            "picker probe reports a missing listing executable without entering the UI" fun f => do
            IO.FS.removeFile f.executable
            withSession f.picker #[] fun s => do
                let rc ← s.result
                return rc.isSome && rc != some 0 && (← f.calls).isEmpty &&
                    !hasBytes (← s.output.get) (modeSet 1049 true))
  failures :=
    failures +
      (←
        check e "missing-attach"
            "picker probe restores the terminal when the attach executable disappears" fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              IO.FS.removeFile f.executable
              s.text "\r"
              let rc ← s.result
              let before ← readText (f.root / "before")
              return rc.isSome && rc != some 0 && !before.isEmpty &&
                  before == (← readText (f.root / "after")) &&
                  modesRestored (← s.output.get) 1 &&
                  (← f.calls) == call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "readonly-output"
            "picker probe restores termios when opening and closing screen writes both fail"
            fun f =>
            withSession f.picker #[]
              (fun s => do
                let clean ← termiosRestored s 1
                return clean && (← childNormal f 1) &&
                    (← f.calls) == call ["ls", "-r", "--porcelain"] &&
                    !hasBytes (← s.output.get) (modeSet 1049 true))
              "readonly-output")
  return failures

private def selectionChecks (e : Env) : IO Nat := do
  let mut failures := 0
  for (slug, target) in
    [("remote", "work@me@dev-a"), ("leading", "-leading+name"),
      ("shell-text", "work@host with 'spaces' $TERM")] do
    failures :=
      failures +
        (←
          check e s!"exact-{slug}"
              s!"picker probe attaches the original target as one argument ({target})" fun f => do
              f.listing s!"name\t{target}\n"
              withSession f.picker #[] fun s => do
                  unless ← s.prompt do
                    return false
                  let shown ← s.until target
                  let clean ← acceptThenCancel s
                  return shown && clean &&
                      (← f.calls) ==
                        call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                          call ["ls", "-r", "--porcelain"])
  let moves :=
    [("down", "\x1b[B", "Beta"), ("up", "\x1b[B\x1b[B\x1b[A", "Beta"), ("ctrl-n", "\x0e", "Beta"),
      ("ctrl-p", "\x0e\x0e\x10", "Beta"), ("end", "\x1b[F", "Gamma"),
      ("home", "\x1b[F\x1b[H", "Alpha")]
  for (slug, keys, target) in moves do
    failures :=
      failures +
        (←
          check e slug s!"picker probe navigation selects the expected row ({slug})" fun f =>
              withSession f.picker #[] fun s => do
                unless ← s.prompt do
                  return false
                return (← acceptThenCancel s (keys ++ "\r")) &&
                    (← f.calls) ==
                      call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                        call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "subsequence"
            "picker probe filtering is case-insensitive, subsequence-based and stable" fun f => do
            f.listing "name\tPrefix\nname\tWork\nname\tweak\n"
            withSession f.picker #[] fun s => do
                unless ← s.prompt do
                  return false
                unless ← s.typeQuery "WK" "WK" do
                  return false
                return (← acceptThenCancel s "\x0e\r") &&
                    (← f.calls) ==
                      call ["ls", "-r", "--porcelain"] ++ call ["attach", "weak"] ++
                        call ["ls", "-r", "--porcelain"])
  for (slug, erase) in [("del", "\x7f"), ("backspace", "\x08")] do
    failures :=
      failures +
        (←
          check e slug s!"picker probe query deletion works ({slug})" fun f =>
              withSession f.picker #[] fun s => do
                unless ← s.prompt do
                  return false
                unless ← s.typeQuery "Bx" "Bx" do
                  return false
                unless ← s.typeQuery erase "B" do
                  return false
                return (← acceptThenCancel s) &&
                    (← f.calls) ==
                      call ["ls", "-r", "--porcelain"] ++ call ["attach", "Beta"] ++
                        call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "clear" "picker probe Ctrl-U clears the whole query" fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              unless ← s.typeQuery "unmatched" "unmatched" do
                return false
              unless ← s.typeQuery "\x15Gamma" "Gamma" do
                return false
              return (← acceptThenCancel s) &&
                  (← f.calls) ==
                    call ["ls", "-r", "--porcelain"] ++ call ["attach", "Gamma"] ++
                      call ["ls", "-r", "--porcelain"])
  for (slug, listing, query) in
    [("no-match", "name\tAlpha\n", "new-session"), ("empty-list", "", "")] do
    failures :=
      failures +
        (←
          check e slug
              s!"picker probe Enter with no match stays editable and creates nothing ({slug})"
              fun f => do
              f.listing listing
              withSession f.picker #[] fun s => do
                  unless ← s.prompt do
                    return false
                  if !query.isEmpty then
                    unless ← s.typeQuery query query do
                      return false
                  s.text "\r"
                  s.observe 350
                  let waiting := !(← (f.root / "result").pathExists)
                  let noCommand := (← f.calls) == call ["ls", "-r", "--porcelain"]
                  s.text "\x03"
                  return waiting && noCommand && (← restored s 130))
  return failures

private def inputChecks (e : Env) : IO Nat := do
  let mut failures := 0
  for (slug, key) in [("ctrl-c", "\x03"), ("ctrl-d", "\x04"), ("escape", "\x1b")] do
    failures :=
      failures +
        (←
          check e slug s!"picker probe cancellation restores termios and display modes ({slug})"
              fun f =>
              withSession f.picker #[] fun s => do
                unless ← s.prompt do
                  return false
                s.text key
                return (← restored s 130) && (← f.calls) == call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "split-arrow" "picker probe decodes an arrow split between reads" fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              s.text "\x1b["
              s.observe 50
              return (← acceptThenCancel s "B\r") &&
                  (← f.calls) ==
                    call ["ls", "-r", "--porcelain"] ++ call ["attach", "Beta"] ++
                      call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "split-utf8" "picker probe retains split UTF-8 query characters" fun f => do
            let target := "work@界é"
            f.listing s!"name\tother\nname\t{target}\n"
            withSession f.picker #[] fun s => do
                unless ← s.prompt do
                  return false
                s.send (ByteArray.mk #[0xE7])
                s.observe 50
                let start ← s.mark
                s.send (ByteArray.mk #[0x95, 0x8C, 0xC3])
                unless ← s.prompt "界" start do
                  return false
                let next ← s.mark
                s.send (ByteArray.mk #[0xA9])
                unless ← s.prompt "界é" next do
                  return false
                return (← acceptThenCancel s) &&
                    (← f.calls) ==
                      call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                        call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "paste"
            "picker probe paste survives idle, suppresses newlines and handles a split end marker"
            fun f => do
            f.listing "name\talphabeta\nname\tother\n"
            withSession f.picker #[] fun s => do
                unless ← s.prompt do
                  return false
                unless ← s.typeQuery "\x1b[200~alpha" "alpha" do
                  return false
                s.observe 350
                unless ← s.typeQuery "\r\nbeta" "alphabeta" do
                  return false
                s.observe 200
                let waiting := !(← (f.root / "result").pathExists)
                let noAttach := (← f.calls) == call ["ls", "-r", "--porcelain"]
                s.text "\x1b[20"
                s.observe 50
                s.text "1~"
                unless ← s.typeQuery "\x15BETA" "BETA" do
                  return false
                return waiting && noAttach && (← acceptThenCancel s) &&
                    (← f.calls) ==
                      call ["ls", "-r", "--porcelain"] ++ call ["attach", "alphabeta"] ++
                        call ["ls", "-r", "--porcelain"])
  return failures

private def refreshChecks (e : Env) : IO Nat := do
  let mut failures := 0
  failures :=
    failures +
      (←
        check e "snapshot" "picker probe keeps its listing snapshot while idle and resizing"
            fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              f.listing "name\tReplacement\n"
              let start ← s.mark
              s.client.resize 40 6
              unless ← s.prompt "" start do
                return false
              -- Observe past five seconds so a periodic refresh would change the call record.
              s.observe 5500
              let once := (← f.calls) == call ["ls", "-r", "--porcelain"]
              return once && (← acceptThenCancel s) &&
                  (← f.calls) ==
                    call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                      call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "refresh" "picker probe Ctrl-R lists in normal mode and resets query and selection"
            fun f => do
            f.listing "name\tBeta\nname\tBravo\n"
            withSession f.picker #[] fun s => do
                unless ← s.prompt do
                  return false
                unless ← s.typeQuery "B" "B" do
                  return false
                s.text "\x1b[F"
                f.listing "name\tReplacement\nname\tBeta\n"
                let start ← s.mark
                s.text "\x12"
                unless ← s.until "Replacement" start do
                  return false
                return (← acceptThenCancel s "\r" 3) && (← childNormal f 2) &&
                    (← f.calls) ==
                      call ["ls", "-r", "--porcelain"] ++ call ["ls", "-r", "--porcelain"] ++
                        call ["attach", "Replacement"] ++
                        call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "refresh-failure"
            "picker probe failed refresh restores the terminal and preserves listing status"
            fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              f.listing "name\tPartial\n" 9
              s.text "\x12"
              return (← restored s 9) && (← childNormal f 2) &&
                  (← f.calls) ==
                    call ["ls", "-r", "--porcelain"] ++ call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "resize"
            "picker probe redraw fits a resized terminal and clips wide text without changing its target"
            fun f => do
            let target := "wide@界界界界Z"
            f.listing s!"name\t{target}\nname\tsecond\nname\tthird\nname\tfourth\n"
            withSession f.picker #[]
                (fun s => do
                  unless ← s.prompt do
                    return false
                  unless ← s.until target do
                    return false
                  let start ← s.mark
                  s.client.resize 12 4
                  unless ← s.prompt "" start do
                    return false
                  unless ← s.until "wide@" start do
                    return false
                  s.observe 150
                  let out ← s.output.get
                  let frame := out.extract start out.size
                  let vt := (Vt.init 12 4).feedBytes frame
                  let screen := ByteArray.mk (screenText vt).toArray
                  IO.FS.writeBinFile (f.root / "resized-frame.bin") frame
                  IO.FS.writeBinFile (f.root / "screen.txt") screen
                  let fits :=
                    hasText screen "linger>" && hasText screen "wide@" && !hasText screen "Z"
                  return fits && (← acceptThenCancel s) &&
                      (← f.calls) ==
                        call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                          call ["ls", "-r", "--porcelain"])
                "both" 80 12)
  for (slug, description, rows) in [("one-row", "one-row", 1), ("two-rows", "two-row", 2)] do
    failures :=
      failures +
        (←
          check e slug
              s!"picker probe keeps its current candidate visible in a {description} terminal"
              fun f =>
              withSession f.picker #[]
                (fun s => do
                  let shown ← s.until "Alpha"
                  s.observe 150
                  let vt := (Vt.init 40 rows).feedBytes (← s.output.get)
                  let screen := ByteArray.mk (screenText vt).toArray
                  IO.FS.writeBinFile (f.root / "screen.txt") screen
                  let visible :=
                    shown && hasText screen "Alpha" &&
                      hasText screen "linger>" == decide (rows > 1) &&
                      !hasText screen "sessions"
                  s.text "\x03"
                  return visible && (← restored s 130) &&
                      (← f.calls) == call ["ls", "-r", "--porcelain"])
                "both" 40 (UInt32.ofNat rows))
  return failures

private def defaultChecks (e : Env) : IO Nat := do
  let mut failures := 0
  for empty in [true, false] do
    let slug := if empty then "empty-path" else "impostor-path"
    failures :=
      failures +
        (←
          check e slug s!"picker probe uses its absolute executable for ls and attach ({slug})"
              fun f => do
              let impostor := f.root / "bin" / "linger"
              IO.FS.writeFile impostor
                  s!"#!/bin/sh\nprintf hit >{quote (f.root / "impostor-hit").toString}\nexit 97\n"
              let chmod ← IO.Process.output { cmd := "chmod", args := #["+x", impostor.toString] }
              if chmod.exitCode != 0 then
                throw (IO.userError s!"manager impostor chmod failed: {chmod.stderr}")
              let path := if empty then "" else (f.root / "bin").toString
              let f := { f with env := f.env.push ("PATH", some path) }
              withSession f.picker #[] fun s => do
                  unless ← s.prompt do
                    return false
                  return (← acceptThenCancel s) && !(← (f.root / "impostor-hit").pathExists) &&
                      (← f.calls) ==
                        call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                          call ["ls", "-r", "--porcelain"])
  for rc in [0, 7, 255] do
    failures :=
      failures +
        (←
          check e s!"default-{rc}"
              s!"picker probe returns to a fresh picker after attach status {rc}" fun f => do
              IO.FS.writeFile (f.root / "attach-rc") (toString rc)
              withSession f.picker #[] fun s => do
                  unless ← s.prompt do
                    return false
                  return (← acceptThenCancel s) &&
                      (← f.calls) ==
                        call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                          call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "successive"
            "picker probe repeatedly attaches from fresh snapshots after statuses 0, 7 and 255"
            fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              let remote := "-work@me@dev-a"
              let shellText := "work@host with 'spaces' $TERM"
              let mut expected := call ["ls", "-r", "--porcelain"]
              let mut count := 0
              let mut normal ← childNormal f 1
              for (target, query, rc, next) in
                [("Beta", "B", 0, remote), (remote, "wrk", 7, shellText),
                  (shellText, "host", 255, "Fresh")] do
                unless ← s.typeQuery query query do
                  return false
                f.listing s!"name\t{next}\nname\tOther\n"
                IO.FS.writeFile (f.root / "attach-rc") (toString rc)
                s.text "\r"
                count := count + 1
                unless ← returned s next count do
                  return false
                expected := expected ++ call ["attach", target] ++ call ["ls", "-r", "--porcelain"]
                normal :=
                  normal && (← beforeAttach s count count) && (← childNormal f (2 * count) true) &&
                    (← childNormal f (2 * count + 1)) &&
                    (← f.calls) == expected
              s.text "\x03"
              return normal && (← restored s 130 4) && (← f.calls) == expected)
  failures :=
    failures +
      (←
        check e "return-listing-failure"
            "picker probe preserves a failed listing status after attach and restores the terminal"
            fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              f.listing "name\tPartial\n" 9
              s.text "\r"
              let clean ← restored s 9
              return clean && (← beforeAttach s) && (← childNormal f 1) &&
                  (← childNormal f 2 true) &&
                  (← childNormal f 3) &&
                  (← f.calls) ==
                    call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                      call ["ls", "-r", "--porcelain"])
  failures :=
    failures +
      (←
        check e "return-malformed"
            "picker probe rejects a malformed listing after attach before another picker visit"
            fun f =>
            withSession f.picker #[] fun s => do
              unless ← s.prompt do
                return false
              f.listing "name\tNext\nname\tNext\n"
              s.text "\r"
              let clean ← restored s 1
              return clean && (← beforeAttach s) && (← childNormal f 1) &&
                  (← childNormal f 2 true) &&
                  (← childNormal f 3) &&
                  (← f.calls) ==
                    call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                      call ["ls", "-r", "--porcelain"])
  return failures

private def realCheck (e : Env) : IO Nat :=
  check e "real" "linger select attaches, detaches and returns to selection with no linger on PATH"
    fun f => do
    let name := "manager-live"
    let create ← IO.Process.output { cmd := e.bin, args := #["run", name, "true"], env := f.env }
    if create.exitCode != 0 then
      throw (IO.userError s!"manager live fixture failed: {create.stderr}")
    try
      withSession f #["select"] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.until name do
            return false
          s.text "\r"
          let attached ←
            waitFor 5000 do
                return (← e.info name "clients") == some "1"
          if !attached then
            return false
          let start ← s.mark
          s.text "printf 'manager-live-%s\\n' \"$((20+22))\"\r"
          unless ← s.until "manager-live-42" start do
            return false
          let beforeDetach ← s.mark
          s.client.detach
          unless ← s.prompt "" beforeDetach do
            return false
          let detached ←
            waitFor 5000 do
                return (← e.info name "clients") == some "0"
          s.text "\x03"
          return detached && (← termiosRestored s 130) &&
              sequenceCount (← s.output.get) (modeSet 1049 true) ≥ 2
    finally
      e.killAll #[name]

def run : IO UInt32 := do
  let e ← Env.make "manager"
  let mut failures ← usageChecks e
  failures := failures + (← failureChecks e)
  failures := failures + (← selectionChecks e)
  failures := failures + (← inputChecks e)
  failures := failures + (← refreshChecks e)
  failures := failures + (← defaultChecks e)
  failures := failures + (← realCheck e)
  verdict e failures

end E2E.Manager
