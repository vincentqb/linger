module

import Linger.Manager.Picker
import Linger.Manager.Resurrect
import Linger.Core.Name
import Linger.Core.Remote
import Linger.Core.Terminal
import Linger.Runtime.Paths
import Linger.Tools.Resurrect
import E2E.Recipes
import Std.Sync.Mutex

public section

/-! # E2E.Manager — public entry point and shared picker executor

The helper mode of this same test binary records exact argument vectors and
observes the terminal before the manager, in each listing/attach child, and
after the manager returns. `stty -g` is a test observer, resolved before giving
the manager a restricted PATH. Comparing that portable representation avoids
inspecting the opaque termios blob's padding.

Synthetic failure, argv and terminal cases call `Linger.Manager.Picker.run` through
the test probe with a fixture-owned absolute recorder path. The frozen-save
case uses that recorder with `Linger.Manager.Resurrect.run`. These test the shared
executors; public CLI checks and source gates cover entry-point wiring.
Help, argument validation, terminal dispatch and live attach/detach drive the
actual `linger` binary with no `linger` on the fixture PATH.
File handshakes hold a listing child open without sleeping in the test driver.
The optional `MANAGER_TEST_LINGER` and `MANAGER_TEST_PICKER` overrides let the
same checks and recorder drive preserved predecessor executables.
`E2ETest.main` dispatches `--manager-probe <args>` to `probe` below.
-/

namespace E2E.Manager

open E2E.Harness
open Linger.Posix
open Linger.Core.Render (modeSet csiNum screenText)
open Linger.Core.Vt (Vt)
open Linger.Core.Remote renaming shellQuote → quote

/-- PTY acquisition uses libc's shared `ptsname` buffer and briefly holds
descriptors without close-on-exec. Keep every parent launch out of that region,
including ordinary process launches and the harness's one-shot CLI calls.
Session observations and waits for explicitly spawned children stay outside. -/
private initialize launchMutex : Std.Mutex Unit ←
  Std.Mutex.new ()

private def withLaunchLock {α : Type} (action : IO α) : IO α :=
  launchMutex.atomically fun _ => action

private def rowText (vt : Vt) (row : Nat) : String :=
  String.fromUTF8! (ByteArray.mk (Linger.Core.Render.rowText (vt.getRow row)).toArray)

private def call (args : List String) : String :=
  "CALL\x00linger\x00" ++ String.intercalate "\x00" args ++ "\x00\n"

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

private def writeListing (root : System.FilePath) (text : String) (rc : Nat) : IO Unit := do
  IO.FS.writeFile (root / "listing-rc-next") (toString rc)
  IO.FS.rename (root / "listing-rc-next") (root / "listing-rc")
  IO.FS.writeFile (root / "listing-next") text
  IO.FS.rename (root / "listing-next") (root / "listing")

private def snapshot (root : System.FilePath) : IO String := do
  let some stty ←
    IO.getEnv "MANAGER_TEST_STTY" | throw (IO.userError "manager probe has no stty observer")
  let terminal ← readText (root / "terminal-path")
  if terminal.isEmpty then
    throw (IO.userError "manager probe has no observed terminal path")
  let result ←
    withLaunchLock <|
        IO.Process.output
          { cmd := "/bin/sh", args := #["-c", s!"exec {quote stty} -g <{quote terminal}"] }
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
  IO.FS.writeFile (root / s!"termios-{count + 1}") (← snapshot root)
  let ttyIn ← (← IO.getStdin).isTty
  let ttyOut ← (← IO.getStdout).isTty
  IO.FS.writeFile (root / s!"ttys-{count + 1}") s!"{ttyIn},{ttyOut}"
  match args with
  | ["ls", "-r", "--porcelain"] | ["tmux", "ls", "--porcelain", _] =>
    let serial := (← numberFile (root / "list-count")) + 1
    let pid ← getpid
    let started ← monotonicMs
    let text ← readText (root / "listing")
    let rc ← numberFile (root / "listing-rc")
    IO.FS.writeFile (root / "list-count") (toString serial)
    appendText (root / "list-starts") s!"{serial}\t{pid}\t{started}\n"
    let overlap ←
      try
        IO.FS.createDir (root / "listing-active")
        pure false
      catch _ =>
        appendText (root / "listing-overlap") s!"{serial}\t{pid}\n"
        pure true
    try
      let output ← IO.getStdout
      let holdFrom ← numberFile (root / "hold-listing-from")
      if holdFrom > 0 && serial ≥ holdFrom then
        output.putStr (← readText (root / "listing-prefix"))
        output.flush
        IO.FS.writeFile (root / s!"list-started-{serial}") (toString pid)
        let released ←
          waitFor 10000 do
              return (← (root / s!"release-listing-{serial}").pathExists) ||
                  (← (root / "release-all-listings").pathExists)
        unless released do
          return 96
      else
        IO.FS.writeFile (root / s!"list-started-{serial}") (toString pid)
      -- Keep publishing the captured catalog while the actual save changes.
      -- Even a refresh cannot turn this into a timing-dependent acceptance test.
      if args.head? == some "tmux" then
        let save ← readText (root / "rewrite-save")
        if !save.isEmpty then
          IO.FS.writeFile save (← readText (root / "replacement-save"))
      output.putStr text
      output.flush
      IO.FS.writeFile (root / s!"list-completed-{serial}") (toString (← monotonicMs))
      return UInt32.ofNat rc
    finally
      IO.FS.writeFile (root / s!"list-ended-{pid}") (toString (← monotonicMs))
      unless overlap do
        IO.FS.removeDir (root / "listing-active")
  | ["attach", target] | ["attach", "--", target] =>
    let count ← numberFile (root / "attach-count")
    IO.FS.writeFile (root / "attach-count") (toString (count + 1))
    IO.FS.writeFile (root / s!"attach-termios-{count + 1}") (← snapshot root)
    IO.FS.writeFile (root / s!"attach-ttys-{count + 1}") s!"{ttyIn},{ttyOut}"
    if ← (root / "after-attach-listing").pathExists then
      writeListing root (← readText (root / "after-attach-listing"))
          (← numberFile (root / "after-attach-listing-rc"))
    writeAll stdoutFd s!"\r\nMANAGER-ATTACH-{count + 1}\r\n".toUTF8
    let previousPid ← numberFile (root / "vanish-before-attach")
    if previousPid > 0 then
      -- Planning has already listed the existing session. Remove it here,
      -- then delegate native upsert with the exact cwd the manager supplied.
      IO.FS.writeFile (root / "attach-cwd") (← IO.currentDir).toString
      let executable ← readText (root / "real-executable")
      let child ←
        withLaunchLock <| IO.Process.spawn { cmd := executable, args := #["kill", target] }
      let rc ← waitChild child 5000
      unless rc == 0 do
        return rc
      let socket ← Linger.Runtime.Paths.socketPath target
      let checkpoint ← Linger.Runtime.Paths.ckptPath target
      let vanished ←
        waitFor 3000 do
            return !(← alive (UInt32.ofNat previousPid)) &&
                !(← (System.FilePath.mk socket).pathExists) &&
                !(← (System.FilePath.mk checkpoint).pathExists)
      IO.FS.writeFile (root / "vanished-before-native-attach") (toString vanished)
      unless vanished do
        return 97
      let child ← withLaunchLock <| IO.Process.spawn { cmd := executable, args := args.toArray }
      return ← waitChild child 10000
    return UInt32.ofNat (← numberFile (root / "attach-rc") 7)
  | _ =>
    let executable ← readText (root / "real-executable")
    if !executable.isEmpty && (args == ["ls", "--porcelain"] || args.head? == some "run") then
      if args.head? == some "run" then
        IO.FS.writeFile (root / "run-cwd") (← IO.currentDir).toString
      let child ← withLaunchLock <| IO.Process.spawn { cmd := executable, args := args.toArray }
      return ← waitChild child 5000
    return 98

private def launch (root : System.FilePath) (manager mode : String) (args : List String) :
    IO UInt32 := do
  let some tty ←
    IO.getEnv "MANAGER_TEST_TTY" | throw (IO.userError "manager probe has no tty observer")
  let observer ←
    withLaunchLock <|
        IO.Process.spawn { cmd := tty, stdin := .inherit, stdout := .piped, stderr := .piped }
  let rc ← waitChild observer 4000
  let terminal := (← observer.stdout.readToEnd).trimAscii.toString
  let error ← observer.stderr.readToEnd
  if rc != 0 || !terminal.startsWith "/dev/" || terminal == "/dev/tty" then
    throw (IO.userError s!"manager terminal path observation failed: {terminal} {error}")
  -- An isolated listing child has no controlling /dev/tty. Observe the launcher's
  -- actual slave path in every process, including before attach and after exit.
  IO.FS.writeFile (root / "terminal-path") terminal
  IO.FS.writeFile (root / "before") (← snapshot root)
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
  let noColor ←
    if ← (root / "no-color").pathExists then
      some <$> IO.FS.readFile (root / "no-color")
    else
      pure none
  let child ←
    withLaunchLock <|
        IO.Process.spawn
          { cmd, args,
            env :=
              #[("LINGER_SESSION", none), ("LINGER_NO_DETACH_KEY", none), ("NO_COLOR", noColor)],
            stdin := if mode == "stdout-only" then .null else .inherit }
  IO.FS.writeFile (root / "manager-pid") (toString child.pid)
  let rc ← waitChild child
  IO.FS.writeFile (root / "after") (← snapshot root)
  IO.FS.writeFile (root / "result") (toString rc)
  writeAll stdoutFd s!"\r\nMANAGER-EXIT:{rc}\r\n".toUTF8
  return rc

/-- A real session foreground program. Challenge replies prove it still runs
after selector cancellation; while attached its default SIGINT disposition
lets the terminal interrupt it and return control to the session shell. -/
private def sessionProgram (root : System.FilePath) : IO UInt32 := do
  IO.FS.writeFile (root / "session-program-pid") (toString (← getpid))
  writeAll stdoutFd "MANAGER-PROGRAM-READY\n".toUTF8
  let input ← IO.getStdin
  while true do
    let line ← input.getLine
    if line.isEmpty || line.trimAscii.toString == "stop-program" then
      return 0
    IO.FS.writeFile (root / "session-program-response") line.trimAscii.toString
  return 0

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
      Linger.Manager.Picker.run executable
    | ["tmux-picker", executable, save] =>
      Linger.Manager.Resurrect.run executable ["select", save]
    | ["session-program"] =>
      sessionProgram root
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
  pickerExecutable : String
  executable : String
  managerArgs : Array String := #[]
  cwd : Option System.FilePath := none
  env : Array (String × Option String)

private def Fixture.make (e : Env) (slug : String) : IO Fixture := do
  let root := System.FilePath.mk e.dir / slug
  let bin := root / "bin"
  IO.FS.createDirAll bin
  let self := (← IO.appPath).toString
  let pickerExecutable := (← IO.getEnv "MANAGER_TEST_PICKER").getD self
  let executable := ((← IO.FS.realPath root) / "record command").toString
  let observer ←
    withLaunchLock <| IO.Process.output { cmd := "/bin/sh", args := #["-c", "command -v stty"] }
  if observer.exitCode != 0 || observer.stdout.trimAscii.isEmpty then
    throw (IO.userError "stty is required to observe manager terminal restoration")
  let tty ←
    withLaunchLock <| IO.Process.output { cmd := "/bin/sh", args := #["-c", "command -v tty"] }
  if tty.exitCode != 0 || tty.stdout.trimAscii.isEmpty then
    throw (IO.userError "tty is required to observe the manager terminal path")
  IO.FS.writeFile executable s!"#!/bin/sh\nexec {quote self} --manager-probe command \"$@\"\n"
  chmod executable 0o755
  IO.FS.writeFile (root / "listing") "name\tAlpha\nname\tBeta\nname\tGamma\n"
  IO.FS.writeFile (root / "listing-rc") "0"
  IO.FS.writeFile (root / "attach-rc") "7"
  let env :=
    e.procEnv ++
      #[("PATH", some bin.toString), ("HOME", some root.toString), ("TERM", some "xterm-256color"),
        ("LINGER_SESSION", none), ("LINGER_NO_DETACH_KEY", none),
        ("MANAGER_TEST_CASE", some root.toString),
        ("MANAGER_TEST_STTY", some observer.stdout.trimAscii.toString),
        ("MANAGER_TEST_TTY", some tty.stdout.trimAscii.toString)]
  return { root, manager := e.bin, self, pickerExecutable, executable, env }

private def Fixture.picker (f : Fixture) : Fixture :=
  { f with
    manager := f.pickerExecutable, managerArgs := #["--manager-probe", "picker", f.executable] }

private def Fixture.calls (f : Fixture) : IO String := readText (f.root / "calls")

/-- Adjacent complete-listing attempts belong to one selection visit. Keep
unexpected argv and every attach in order, without assuming how many periodic
attempts fit between unrelated keyboard actions. The raw trace stays on disk. -/
private def Fixture.visits (f : Fixture) : IO String := do
  let listing := (call ["ls", "-r", "--porcelain"]).dropEnd 1 |>.toString
  let mut records : List String := []
  for record in lines (← f.calls) do
    unless record == listing && records.getLast? == some record do
      records := records ++ [record]
  return String.intercalate "\n" records ++ if records.isEmpty then "" else "\n"

private def Fixture.listing (f : Fixture) (text : String) (rc : Nat := 0) : IO Unit := do
  writeListing f.root text rc

/-- Publish the return snapshot only when attach starts, so a periodic refresh
cannot legitimately display the next visit's fixture before Enter is sent. -/
private def Fixture.afterAttach (f : Fixture) (text : String) (rc : Nat := 0) : IO Unit := do
  IO.FS.writeFile (f.root / "after-attach-listing") text
  IO.FS.writeFile (f.root / "after-attach-listing-rc") (toString rc)

private def Fixture.piped (f : Fixture) (args : Array String) : IO (UInt32 × String × String) := do
  let child ←
    withLaunchLock <|
        IO.Process.spawn
          { cmd := f.manager, args := f.managerArgs ++ args, cwd := f.cwd, env := f.env,
            stdin := .null, stdout := .piped, stderr := .piped }
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
    withLaunchLock <|
        spawnPty cols rows (f.cwd.map (·.toString) |>.getD "") f.self
          (#["--manager-probe", "launch", f.manager, mode] ++ f.managerArgs ++ args) env
  return { fixture := f, client := { pid, fd }, output := ← IO.mkRef ByteArray.empty }

private def Session.mark (s : Session) : IO Nat := return (← s.output.get).size

/-- Read under a deadline, retaining all bytes for order and cleanup assertions.
EOF and the wrapper's completion marker end a failed positive wait promptly. -/
private def Session.untilOutput (s : Session) (ready : ByteArray → Bool) (start : Nat := 0)
    (ms : Nat := 4000) : IO Bool := do
  let deadline := (← monotonicMs) + ms
  let mut done := false
  while !done && (← monotonicMs) < deadline do
    let current ← s.output.get
    let tail := current.extract start current.size
    if ready tail then
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
  let output ← s.output.get
  return ready (output.extract start output.size)

private def Session.untilAny (s : Session) (needles : List String) (start : Nat := 0)
    (ms : Nat := 4000) : IO Bool :=
  s.untilOutput (fun output => needles.any (hasText output)) start ms

private def Session.until (s : Session) (needle : String) (start : Nat := 0) (ms : Nat := 4000) :
    IO Bool := s.untilAny [needle] start ms

/-- Match rendered cells from this action's output: inline emphasis may split
a target's bytes, and an earlier selected row must not satisfy a new wait. -/
private def Session.untilScreen (s : Session) (ready : Vt → Bool) (start : Nat := 0)
    (ms : Nat := 4000) : IO Bool := do
  let (cols, rows) ← winsizeGet s.client.fd
  s.untilOutput (fun output => ready ((Vt.init cols.toNat rows.toNat).feedBytes output)) start ms

private def Session.untilRow (s : Session) (text : String) (start : Nat := 0) : IO Bool :=
  s.untilScreen (fun vt => (List.range vt.rowCount).any fun row => has (rowText vt row) text) start

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

private def Session.prompt (s : Session) (query : String := "") (start : Nat := 0) : IO Bool := do
  unless ← s.untilAny ["  › " ++ query, "linger> " ++ query] start do
    return false
  -- Normal actions need a loaded snapshot. The initial loading frame also has
  -- an editable prompt; the held-initial-list checks exercise that separately.
  s.untilAny
      ["  ↵ attach", "  ↵ create", "  Type a valid name",
        " | enter choose | esc quit | ctrl-r refresh"]
      start

/-- Require the selected marker, exact target prefix and reverse video.
Do not depend on where the renderer starts or resets inline styles. -/
private def Session.selected (s : Session) (label : String) (start : Nat := 0) : IO Bool :=
  s.untilScreen
    (fun vt =>
      (List.range vt.rowCount).any fun row =>
        let text := rowText vt row
        let col := if label.startsWith "+ Create " then 4 else 6
        let rest := String.ofList (text.toList.drop col)
        text.startsWith "  ▸ " && (rest == label || rest.startsWith (label ++ " ")) &&
          (vt.getCell 2 row).pen.reverse &&
          (vt.getCell col row).pen.reverse)
    start

private def Session.typeQuery (s : Session) (text query : String) : IO Bool := do
  let start ← s.mark
  s.text text
  s.prompt query start

private def Session.result (s : Session) : IO (Option Nat) := do
  let _ ← s.until "MANAGER-EXIT:"
  let _ ← s.client.reap 1000
  return (← readText (s.fixture.root / "result")).toNat?

private def Session.retire (s : Session) : IO Unit := do
  IO.FS.writeFile (s.fixture.root / "release-all-listings") ""
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
  for record in lines (← readText (s.fixture.root / "list-starts")) do
    if let [_, pid, _] := record.splitOn "\t" then
      if let some pid := pid.toNat? then
        if pid > 0 && !(← (s.fixture.root / s!"list-ended-{pid}").pathExists) then
          try
            if ← alive (UInt32.ofNat pid) then
              kill (UInt32.ofNat pid) 9
          catch _ =>
            pure ()

private def withSession (f : Fixture) (args : Array String) (body : Session → IO Bool)
    (mode : String := "both") (cols : UInt32 := 80) (rows : UInt32 := 12) : IO Bool := do
  let s ← f.start args mode cols rows
  try
    body s
  finally
    s.retire

private def check (e : Env) (slug label : String) (body : Fixture → IO Bool) : IO Unit := do
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

/-- A first snapshot can fail before UI entry or after a cancellable loading
frame. Every entered visit must leave before the error, and actual termios must
match the launcher. A prior completed attachment accounts for its own visit. -/
private def failureRestored (s : Session) (rc : Nat) (error : String) (completedVisits : Nat := 0) :
    IO Bool := do
  unless ← termiosRestored s rc do
    return false
  let out ← s.output.get
  let some position := findText out error | return false
  let entries := sequenceCount out (modeSet 1049 true)
  if entries < completedVisits || entries > completedVisits + 1 then
    return false
  if entries == 0 then
    return !hasText out "\x1b"
  return modesRestored out entries && modesRestored (out.extract 0 position) entries

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

private def attachNormal (f : Fixture) (index : Nat := 1) : IO Bool := do
  let before ← readText (f.root / "before")
  return !before.isEmpty && (← readText (f.root / s!"attach-termios-{index}")) == before &&
      (← readText (f.root / s!"attach-ttys-{index}")) == "true,true"

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
  unless ← s.untilAny ["Find or create a session", "linger> \r\n"] start do
    return false
  return ← s.selected target start

/-- Accept from the current snapshot, observe a different listing after attach,
then cancel explicitly. Count every visit, including any preceding refresh. -/
private def acceptThenCancel (s : Session) (keys : String := "\r") (visits : Nat := 2) : IO Bool :=
  do
  s.fixture.afterAttach "name\tFresh\nname\tOther\n"
  s.text keys
  unless ← returned s "Fresh" do
    return false
  s.text "\x03"
  let clean ← restored s 130 visits
  return clean && (← beforeAttach s 1 (visits - 1)) && (← attachNormal s.fixture)

private def usageChecks (e : Env) : IO Unit := do
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
          (out.splitOn "\n").any (fun line => line.trimAscii.toString.startsWith "attach ") &&
          !(out.splitOn "\n").any
              (fun line =>
                line.trimAscii.toString.startsWith "select " ||
                  line.trimAscii.toString.startsWith "status " ||
                  line.trimAscii.toString.startsWith "watch " ||
                  line.trimAscii.toString.startsWith "history ") &&
          has out "ls --summary" &&
          has out "attach --read-only" &&
          has out "capture --history" &&
          has out "tmux" &&
          !has out "linger import [SAVE]" &&
          !has out "--loop" &&
          !has out "--restore-processes" &&
          !has out "lz"
  check e "usage" "linger rejects retired commands and conflicting listing options" fun f => do
      let mut ok := true
      for args in
        [#["work"], #["--unknown"], #["--help", "extra"], #["-h", "extra"], #["help", "extra"],
          #["ls", "--unknown"], #["select"], #["status"], #["--summary"], #["watch", "work"],
          #["history", "work"], #["hi", "work"], #["attach", "--unknown"], #["attach", "--"],
          #["attach", "--read-only", "work", "/bin/sh"], #["capture", "--unknown"],
          #["capture", "--"], #["capture", "--history"], #["capture", "--history", "work", "extra"],
          #["capture", "work", "--history"], #["ls", "--summary", "--porcelain"],
          #["ls", "--porcelain", "--summary"], #["ls", "--summary", "-r"],
          #["ls", "-r", "--summary"], #["ls", "--summary", "extra"], #["select", ""],
          #["select", "work"], #["select", "--help"], #["select", "-h"], #["select", "one", "two"],
          #["--loop", ""], #["--loop", "one", "two"], #["import-resurrect"], #["import", ""],
          #["import", "--unknown"], #["import", "--help"], #["import", "-h"], #["import", "-save"],
          #["import", "one", "two"], #["import"], #["export", "save"], #["tmux", "select", ""],
          #["tmux", "select", "-save"], #["tmux", "select", "one", "two"],
          #["tmux", "select", "--unknown"]] do
        let (rc, _, _) ← f.piped args
        appendText (f.root / "usage-results") s!"{repr args}: {rc}\n"
        ok := ok && rc == 2
      return ok
  for (slug, args) in [("loop", #["--loop"]), ("loop-target", #["--loop", "-work@me@dev-a"])] do
    check e s!"removed-{slug}" s!"linger rejects removed loop arguments in a terminal ({slug})"
        fun f =>
        withSession f args fun s => do
          return (← termiosRestored s 2) && !hasBytes (← s.output.get) (modeSet 1049 true)
  check e "select-extra" "linger select rejects extra operands before terminal entry" fun f =>
      withSession f #["select", "extra"] fun s => do
        return (← termiosRestored s 2) && !hasBytes (← s.output.get) (modeSet 1049 true) &&
            !hasText (← s.output.get) "linger>"
  check e "restore-option" "linger rejects process replay options without creating sessions"
      fun f => do
      let saves := f.root / ".tmux" / "resurrect"
      IO.FS.createDirAll saves
      let save := saves / "last"
      IO.FS.writeFile save (Recipes.paneLine "work" "1" "0" f.root.toString "vim")
      let before ← withLaunchLock (e.out #["ls", "--porcelain"])
      let mut ok := true
      for args in
        [#["tmux", "import", "--restore-processes"],
          #["tmux", "import", "--restore-processes", save.toString],
          #["tmux", "import", save.toString, "--restore-processes"]] do
        let (rc, _, _) ← f.piped args
        appendText (f.root / "usage-results") s!"{repr args}: {rc}\n"
        ok := ok && rc == 2
      return ok && (← withLaunchLock (e.out #["ls", "--porcelain"])) == before
  check e "help-neither" "bare linger prints exactly help without creating state (neither tty)"
      fun f => do
      let state := f.root / "absent"
      let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
      let (helpRc, expected, helpErr) ← f.piped #["help"]
      let (rc, out, err) ← f.piped #[]
      IO.FS.writeFile (f.root / "stdout") out
      return helpRc == 0 && !expected.isEmpty && helpErr.isEmpty && rc == 0 && out == expected &&
          err.isEmpty &&
          !(← state.pathExists)
  for mode in ["stdin-only", "stdout-only", "both"] do
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
            mode
  check e "help-sockets" "bare linger help neither probes live sockets nor cleans stale sockets"
      fun f => do
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
        return helpRc == 0 && !expected.isEmpty && helpErr.isEmpty && rc == 0 && out == expected &&
            err.isEmpty &&
            events[0]! == 0 &&
            untouched
      finally
        close listener
  check e "listing-both" "linger ls prints exactly one listing and exits in a terminal" fun f => do
      let (listRc, expected, listErr) ← f.piped #["ls"]
      withSession f #["ls"] fun s => do
          return listRc == 0 && !expected.isEmpty && listErr.isEmpty && (← termiosRestored s 0) &&
              (← s.printed expected)
  check e "select-neither" "linger attach requires both terminal streams (neither tty)" fun f => do
      let state := f.root / "absent"
      let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
      let (rc, out, err) ← f.piped #["attach"]
      IO.FS.writeFile (f.root / "stderr") err
      return rc == 1 && out.isEmpty && has err "terminal input and output" && !has err "\x1b" &&
          !(← state.pathExists)
  for mode in ["stdin-only", "stdout-only"] do
    check e s!"select-{mode}"
        s!"linger attach rejects redirection before listing or terminal entry ({mode})" fun f => do
        let state := f.root / "absent"
        let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
        withSession f #["attach"]
            (fun s => do
              let clean ← termiosRestored s 1
              let output ← s.output.get
              return clean && hasText output "terminal input and output" &&
                  !hasText output "linger>" &&
                  !hasText output "\x1b" &&
                  (← readText (f.root / "stdout")).isEmpty &&
                  !(← state.pathExists))
            mode
  check e "tty-select"
      "linger attach keeps invalid input editable without creating state with no linger on PATH"
      fun f => do
      let state := f.root / "state"
      let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
      withSession f #["attach"] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "invalid/name" "invalid/name" do
            return false
          s.text "\r"
          s.observe 350
          let waiting := !(← (f.root / "result").pathExists)
          let noSession := (← state.readDir).isEmpty
          s.text "\x03"
          return waiting && noSession && (← restored s 130)

private def failureChecks (e : Env) : IO Unit := do
  for (slug, listing) in [("empty", ""), ("partial", "name\tAlpha\n")] do
    check e s!"listing-{slug}"
        s!"picker probe preserves initial listing failure status and reports it after restoration ({slug})"
        fun f => do
        f.listing listing 7
        withSession f.picker #[] fun s => do
            let clean ← failureRestored s 7 "linger: could not list sessions (exit 7)"
            return clean && (← f.visits) == call ["ls", "-r", "--porcelain"] &&
                !hasText (← s.output.get) "Alpha"
  let invalid :=
    [("empty-name", "name\t\n"), ("missing-field", "name\n"), ("extra-field", "name\tbad\textra\n"),
      ("duplicate", "name\tAlpha\n"), ("cr", "name\tbad\r\n"), ("escape", "name\tbad\x1b[2J\n"),
      ("nul", "name\tbad\x00name\n")]
  for (slug, bad) in invalid do
    check e s!"bad-{slug}" s!"picker probe rejects the whole malformed listing ({slug})" fun f => do
        f.listing ("name\tAlpha\n" ++ bad)
        withSession f.picker #[] fun s => do
            let clean ← failureRestored s 1 "picker probe:"
            return clean && (← f.visits) == call ["ls", "-r", "--porcelain"] &&
                !hasText (← s.output.get) "Alpha"
  check e "missing-command"
      "picker probe reports a missing listing executable after terminal restoration" fun f => do
      IO.FS.removeFile f.executable
      withSession f.picker #[] fun s => do
          -- A direct spawn reports its exception; an isolated child can
          -- instead report exec failure through its exit status/stderr.
          let clean ←
            match ← s.result with
            | some 1 =>
              failureRestored s 1 "picker probe:"
            | some 255 =>
              failureRestored s 255 "could not execute external process"
            | _ =>
              pure false
          return clean && (← f.visits).isEmpty
  check e "missing-attach"
      "picker probe restores the terminal when the attach executable disappears" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        IO.FS.removeFile f.executable
        s.text "\r"
        let rc ← s.result
        let clean ←
          match rc with
          | some 1 =>
            failureRestored s 1 "picker probe:" 1
          | some 255 =>
            failureRestored s 255 "linger: could not list sessions (exit 255)" 1
          | _ =>
            pure false
        -- Exec failure can return from attach and start a new loading
        -- visit. The first visit must already be restored before the
        -- attach error, and every visit must leave before the final error.
        let out ← s.output.get
        let firstError :=
          if rc == some 1 then "picker probe:" else "could not execute external process"
        let some position := findText out firstError | return false
        return clean && modesRestored (out.extract 0 position) 1 &&
            (← f.visits) == call ["ls", "-r", "--porcelain"]
  check e "readonly-output"
      "picker probe restores termios when opening and closing screen writes both fail" fun f =>
      withSession f.picker #[]
        (fun s => do
          let clean ← failureRestored s 1 "picker probe:"
          let visits ← f.visits
          return clean && (visits.isEmpty || visits == call ["ls", "-r", "--porcelain"]) &&
              !hasBytes (← s.output.get) (modeSet 1049 true))
        "readonly-output"

private def selectionChecks (e : Env) : IO Unit := do
  for (slug, target, separator) in
    [("remote", "work@me@dev-a", []), ("leading", "-leading+name", ["--"]),
      ("shell-text", "work@host with 'spaces' $TERM", [])] do
    check e s!"exact-{slug}"
        s!"picker probe attaches the original target as one argument ({target})" fun f => do
        f.listing s!"name\t{target}\n"
        withSession f.picker #[] fun s => do
            unless ← s.prompt do
              return false
            let shown ← s.until target
            let clean ← acceptThenCancel s
            return shown && clean &&
                (← f.visits) ==
                  call ["ls", "-r", "--porcelain"] ++ call ("attach" :: separator ++ [target]) ++
                    call ["ls", "-r", "--porcelain"]
  let moves :=
    [("down", "\x1b[B", "Beta"), ("up", "\x1b[B\x1b[B\x1b[A", "Beta"), ("ctrl-n", "\x0e", "Beta"),
      ("ctrl-p", "\x0e\x0e\x10", "Beta"), ("end", "\x1b[F", "main"),
      ("home", "\x1b[F\x1b[H", "Alpha")]
  for (slug, keys, target) in moves do
    check e slug s!"picker probe navigation selects the expected row ({slug})" fun f =>
        withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          return (← acceptThenCancel s (keys ++ "\r")) &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                  call ["ls", "-r", "--porcelain"]
  check e "subsequence" "picker probe filtering is case-insensitive, subsequence-based and stable"
      fun f => do
      f.listing "name\tPrefix\nname\tWork\nname\tweak\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "WK" "WK" do
            return false
          return (← acceptThenCancel s "\x0e\r") &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "weak"] ++
                  call ["ls", "-r", "--porcelain"]
  for (slug, erase) in [("del", "\x7f"), ("backspace", "\x08")] do
    check e slug s!"picker probe query deletion works ({slug})" fun f =>
        withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "Bx" "Bx" do
            return false
          unless ← s.typeQuery erase "B" do
            return false
          return (← acceptThenCancel s) &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "Beta"] ++
                  call ["ls", "-r", "--porcelain"]
  check e "clear" "picker probe Ctrl-U clears the whole query" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        unless ← s.typeQuery "unmatched" "unmatched" do
          return false
        unless ← s.typeQuery "\x15Gamma" "Gamma" do
          return false
        return (← acceptThenCancel s) &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "Gamma"] ++
                call ["ls", "-r", "--porcelain"]
  for (slug, listing, query, target, separator) in
    [("no-match", "name\tAlpha\n", "new-session", "new-session", []),
      ("empty-list", "", "", "main", []),
      ("create-leading", "", "-leading+name", "-leading+name", ["--"]),
      ("create-remote", "", "work@me@dev-a", "work@me@dev-a", []),
      ("create-shell-text", "", "work@host with 'spaces' $TERM", "work@host with 'spaces' $TERM",
        []),
      ("create-unicode-host", "", "work@界é", "work@界é", []),
      ("create-max-name", "", String.ofList (List.replicate Linger.Core.Name.maxLen 'n'),
        String.ofList (List.replicate Linger.Core.Name.maxLen 'n'), [])] do
    check e slug
        s!"picker probe visibly creates the exact target through a restored attach child ({slug})"
        fun f => do
        f.listing listing
        withSession f.picker #[]
            (fun s => do
              unless ← s.prompt do
                return false
              let start ← s.mark
              if !query.isEmpty then
                unless ← s.typeQuery query query do
                  return false
              let shown ← s.selected s!"+ Create {target}" (if query.isEmpty then 0 else start)
              let clean ← acceptThenCancel s
              return shown && clean &&
                  (← f.visits) ==
                    call ["ls", "-r", "--porcelain"] ++ call ("attach" :: separator ++ [target]) ++
                      call ["ls", "-r", "--porcelain"])
            "both" (UInt32.ofNat (Linger.Core.Name.maxLen + 40)) 12
  for create in [false, true] do
    let slug := if create then "prefix-create" else "prefix-existing"
    check e slug
        s!"picker probe lists existing prefix matches first and attaches only the highlighted row ({slug})"
        fun f => do
        f.listing "name\tworkshop\nname\tworkbench\nname\tOther\n"
        withSession f.picker #[] fun s => do
            unless ← s.prompt do
              return false
            unless ← s.typeQuery "work" "work" do
              return false
            s.observe 100
            let vt := (Vt.init 80 12).feedBytes (← s.output.get)
            let orderedRows :=
              rowText vt 4 == "  ▸ ? workshop  (busy)" &&
                rowText vt 5 == "    ? workbench (busy)" &&
                rowText vt 6 == "    + Create work"
            if create then
              let next ← s.mark
              s.text "\x1b[F"
              unless ← s.selected "+ Create work" next do
                return false
            s.observe 200
            let noAttach := (← f.visits) == call ["ls", "-r", "--porcelain"]
            let target := if create then "work" else "workshop"
            let clean ← acceptThenCancel s
            return orderedRows && noAttach && clean &&
                (← f.visits) ==
                  call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                    call ["ls", "-r", "--porcelain"]
  for (slug, listing, query, absent, target) in
    [("exact-suppression", "name\tAlpha\nname\tAlphabet\n", "Alpha", "Alpha", "Alphabet"),
      ("default-suppression", "name\tmain\nname\tOther\n", "", "main", "Other")] do
    check e slug s!"picker probe suppresses creation for exact snapshot members ({slug})" fun f =>
        do
        f.listing listing
        withSession f.picker #[] fun s => do
            unless ← s.prompt do
              return false
            let start ← s.mark
            if !query.isEmpty then
              unless ← s.typeQuery query query do
                return false
            s.observe 150
            let output ← s.output.get
            let frame := output.extract (if query.isEmpty then 0 else start) output.size
            let screen := ByteArray.mk (screenText ((Vt.init 80 12).feedBytes frame)).toArray
            let suppressed := !hasText screen s!"Create {absent}"
            let clean ← acceptThenCancel s "\x1b[F\r"
            return suppressed && clean &&
                (← f.visits) ==
                  call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                    call ["ls", "-r", "--porcelain"]
  check e "case-distinct"
      "picker probe permits explicit case-distinct creation beside a folded existing match" fun f =>
      do
      f.listing "name\tAlpha\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "alpha" "alpha" do
            return false
          s.observe 100
          let vt := (Vt.init 80 12).feedBytes (← s.output.get)
          let shown := rowText vt 4 == "  ▸ ? Alpha (busy)" && rowText vt 5 == "    + Create alpha"
          let clean ← acceptThenCancel s "\x1b[F\r"
          return shown && clean &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "alpha"] ++
                  call ["ls", "-r", "--porcelain"]
  check e "edit-create"
      "picker probe editing a highlighted creation row resets to the first existing match" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        unless ← s.typeQuery "Al" "Al" do
          return false
        let start ← s.mark
        s.text "\x1b[F"
        unless ← s.selected "+ Create Al" start do
          return false
        let next ← s.mark
        unless ← s.typeQuery "\x7f" "A" do
          return false
        let reset ← s.selected "Alpha" next
        let noAttach := (← f.visits) == call ["ls", "-r", "--porcelain"]
        let clean ← acceptThenCancel s
        return reset && noAttach && clean &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                call ["ls", "-r", "--porcelain"]
  let overlong := String.ofList (List.replicate (Linger.Core.Name.maxLen + 1) 'n')
  for (slug, query) in
    [("slash", "bad/name"), ("leading-dot", ".hidden"), ("space", "two words"), ("unicode", "界"),
      ("empty-host", "work@"), ("empty-local", "@host"), ("overlong", overlong),
      ("overlong-remote", overlong ++ "@host")] do
    check e s!"invalid-create-{slug}"
        s!"picker probe invalid creation has no row, ignores Enter and remains editable ({slug})"
        fun f =>
        withSession f.picker #[]
          (fun s => do
            unless ← s.prompt do
              return false
            let start ← s.mark
            unless ← s.typeQuery query query do
              return false
            s.text "\r"
            s.observe 350
            let output ← s.output.get
            let vt :=
              (Vt.init (Linger.Core.Name.maxLen + 40) 12).feedBytes
                (output.extract start output.size)
            let noChoice := !hasText (ByteArray.mk (screenText vt).toArray) "Create "
            let waiting := !(← (f.root / "result").pathExists)
            let noAttach := (← f.visits) == call ["ls", "-r", "--porcelain"]
            unless ← s.typeQuery "\x15Beta" "Beta" do
              return false
            let clean ← acceptThenCancel s
            return noChoice && waiting && noAttach && clean &&
                (← f.visits) ==
                  call ["ls", "-r", "--porcelain"] ++ call ["attach", "Beta"] ++
                    call ["ls", "-r", "--porcelain"])
          "both" (UInt32.ofNat (Linger.Core.Name.maxLen + 40)) 12

private def inputChecks (e : Env) : IO Unit := do
  for (slug, key) in [("ctrl-c", "\x03"), ("ctrl-d", "\x04"), ("escape", "\x1b")] do
    check e slug s!"picker probe cancellation restores termios and display modes ({slug})" fun f =>
        withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "new-session" "new-session" do
            return false
          s.text key
          return (← restored s 130) && (← f.visits) == call ["ls", "-r", "--porcelain"]
  check e "split-arrow" "picker probe decodes an arrow split between reads" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        s.text "\x1b["
        s.observe 50
        return (← acceptThenCancel s "B\r") &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "Beta"] ++
                call ["ls", "-r", "--porcelain"]
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
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                  call ["ls", "-r", "--porcelain"]
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
          let noAttach := (← f.visits) == call ["ls", "-r", "--porcelain"]
          s.text "\x1b[20"
          s.observe 50
          s.text "1~"
          unless ← s.typeQuery "\x15BETA" "BETA" do
            return false
          return waiting && noAttach && (← acceptThenCancel s) &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "alphabeta"] ++
                  call ["ls", "-r", "--porcelain"]
  check e "invalid-control-paste"
      "picker probe pasted controls cannot create, refresh or cancel an invalid query" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        let start ← s.mark
        unless ← s.typeQuery "bad/" "bad/" do
          return false
        s.text "\x1b[200~\x00\x07\x7f\u0085\r\n\x03\x04\x12\x1b[201~"
        s.observe 350
        s.text "\r"
        s.observe 350
        let output ← s.output.get
        let frame := output.extract start output.size
        let screen := ByteArray.mk (screenText ((Vt.init 80 12).feedBytes frame)).toArray
        let ignored := !hasText screen "Create " && !hasText frame "\u0085"
        let waiting := !(← (f.root / "result").pathExists)
        let noCommand := (← f.visits) == call ["ls", "-r", "--porcelain"]
        unless ← s.typeQuery "\x15Beta" "Beta" do
          return false
        let clean ← acceptThenCancel s
        return ignored && waiting && noCommand && clean &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "Beta"] ++
                call ["ls", "-r", "--porcelain"]

private def lastColumnBlank (vt : Vt) : Bool :=
  (List.range vt.rowCount).all fun row =>
    let cell := vt.getCell (vt.colCount - 1) row
    cell.base == ' ' && cell.width == 1 && cell.marks.isEmpty

private def underlined (vt : Vt) (row : Nat) : List Nat :=
  (List.range vt.colCount).filter fun col => (vt.getCell col row).pen.underline

private def Session.capture (s : Session) (name : String) (cols : Nat := 80) (rows : Nat := 12) :
    IO Vt := do
  s.observe 100
  let output ← s.output.get
  let vt := (Vt.init cols rows).feedBytes output
  IO.FS.writeBinFile (s.fixture.root / s!"{name}.bin") output
  IO.FS.writeBinFile (s.fixture.root / s!"{name}.txt") (ByteArray.mk (screenText vt).toArray)
  return vt

private def statusChecks (e : Env) : IO Unit := do
  for (slug, noColor) in
    [("status-colors", none), ("status-no-color-empty", some ""),
      ("status-no-color-set", some "1")] do
    check e slug
        s!"picker shares listing rows and keeps match underline independent of selection and status ({slug})"
        fun f => do
        let statuses : List Linger.Core.Status.Status :=
          [.working, .wantsYou, .exitedOk, .exitedBad, .idle, .resumable, .unknown]
        let fields :=
          statuses.zipIdx |>.map fun (status, index) =>
            [("name", s!"case{index}"), ("status", Linger.Core.Status.name status),
              ("cmd", "editor"), ("pid", "123"), ("label.project", "demo"), ("clients", "2")]
        f.listing
            (String.intercalate "\n"
              (fields.map fun row =>
                String.join (row.map fun (key, value) => s!"{key}\t{value}\n")))
        if let some value := noColor then
          IO.FS.writeFile (f.root / "no-color") value
        withSession f.picker #[]
            (fun s => do
              unless ← s.prompt do
                return false
              let vt ← s.capture slug 100 20
              let expectedColors : List Linger.Core.Vt.Color :=
                [.idx 6, .idx 3, .idx 2, .idx 1, .default, .default, .idx 3]
              let rowsMatch := fun (frame : Vt) =>
                fields.zipIdx |>.all fun (info, index) =>
                  let badge := frame.getCell 4 (4 + index)
                  let name := frame.getCell 6 (4 + index)
                  let expected :=
                    String.fromUTF8! (ByteArray.mk (Linger.Core.Listing.humanRow 5 info).toArray)
                  rowText frame (4 + index) ==
                      (if index == 0 then "  ▸ " else "    ") ++ expected &&
                    badge.pen.fg == (if noColor.isSome then .default else expectedColors[index]!) &&
                    badge.pen.dim == (!noColor.isSome && (index == 4 || index == 5)) &&
                    (List.range (4 + expected.length)).all
                      (fun col => (frame.getCell col (4 + index)).pen.reverse == (index == 0)) &&
                    name.pen.fg == .default &&
                    !name.pen.dim
              let plain := (List.range vt.rowCount).all fun row => (underlined vt row).isEmpty
              unless ← s.typeQuery "CA" "CA" do
                return false
              let matched ← s.capture "status-matched" 100 20
              let emphasis :=
                (List.range matched.rowCount).all fun row =>
                  underlined matched row ==
                    if 4 ≤ row && row < 4 + fields.length then [6, 7] else []
              IO.FS.writeFile (f.root / "match-observation")
                  s!"plain-rows={rowsMatch vt}\nempty-query-unmarked={plain}\nmatched-rows={rowsMatch matched}\nunderlined-columns={repr ((List.range matched.rowCount).map (underlined matched))}\nexpected-session-columns=[6, 7]\n"
              let output ← s.output.get
              let onlyAnsi := !hasText output "[38;" && !hasText output "[48;"
              s.text "\x03"
              let clean ← restored s 130
              return rowsMatch vt && plain && rowsMatch matched && emphasis && onlyAnsi && clean &&
                  hasBytes output (Linger.Core.Terminal.Title.ansi "linger") &&
                  hasBytes (← s.output.get) (Linger.Core.Terminal.Title.ansi ""))
            "both" 100 20
  check e "status-metadata-refresh"
      "picker redraws changed metadata with unchanged names and preserves query, target and all details"
      fun f => do
      f.listing
          "name\talpha\nstatus\tidle\ncmd\told\npid\t1\nlabel.project\tbefore\nclients\t1\nname\tbeta\nstatus\tworking\ncmd\tother\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "a" "a" do
            return false
          let before ← s.capture "metadata-before"
          let start ← s.mark
          f.listing
              "name\talpha\nstatus\texited-bad\ncmd\tnew\npid\t2\nlabel.project\tafter\nclients\t3\nname\tbeta\nstatus\tworking\ncmd\tother\n"
          unless ← s.until "pid 2  new" start do
            return false
          let after ← s.capture "metadata-after"
          let changed :=
            has (rowText before 4) "old  [project=before]  +1" &&
              rowText after 4 == "  ▸ ! alpha pid 2  new  [project=after]  +3" &&
              rowText after 2 == "  › a" &&
              (after.getCell 4 4).pen.fg == .idx 1 &&
              (after.getCell 6 4).pen.reverse
          return changed && (← acceptThenCancel s) &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "alpha"] ++
                  call ["ls", "-r", "--porcelain"]
  check e "status-control-text"
      "picker keeps hostile metadata out of terminal controls while retaining ordinary details"
      fun f => do
      f.listing
          "name\talpha\nstatus\tworking\ncmd\tvi\x1b[31m\u009b31m\nlabel.project\tok\x07\nclients\t2\nname\tbeta\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          let vt ← s.capture "metadata-controls"
          let row := rowText vt 4
          let output ← s.output.get
          let safe :=
            has row "vi�[31m�31m" && has row "[project=ok�]" && !hasText output "\u009b" &&
              !hasText output "vi\x1b" &&
              (vt.getCell 6 4).pen.fg == .default &&
              rowText vt 5 == "    ? beta  (busy)"
          s.text "\x03"
          return safe && (← restored s 130)

private def fuzzyChecks (e : Env) : IO Unit := do
  check e "fuzzy-optimal"
      "picker highlights the best competing alignment only in the exact target and clears it with the query"
      fun f => do
      let fields :=
        [("name", "axab"), ("status", Linger.Core.Status.name .wantsYou), ("cmd", "ab"),
          ("pid", "123"), ("label.project", "ab"), ("clients", "2")]
      f.listing (String.join (fields.map fun (key, value) => s!"{key}\t{value}\n"))
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "AB" "AB" do
            return false
          let matched ← s.capture "competing-match"
          let expected :=
            "  ▸ " ++
              String.fromUTF8! (ByteArray.mk (Linger.Core.Listing.humanRow 4 fields).toArray)
          -- The later adjacent pair beats the earliest subsequence.
          -- Matching metadata and the explicit create label stay plain.
          let positions :=
            (List.range matched.rowCount).all fun row =>
              underlined matched row == if row == 4 then [8, 9] else []
          let spelling := rowText matched 4 == expected && rowText matched 5 == "    + Create AB"
          unless ← s.typeQuery "\x15" "" do
            return false
          let cleared ← s.capture "cleared-match"
          let empty :=
            rowText cleared 4 == expected &&
              (List.range cleared.rowCount).all fun row => (underlined cleared row).isEmpty
          IO.FS.writeFile (f.root / "match-observation")
              s!"exact-row-and-create-label={spelling}\nunderlined-columns={repr (underlined matched 4)}\nexpected-columns=[8, 9]\nonly-target-matches-underlined={positions}\nempty-query-cleared={empty}\n"
          s.text "\x03"
          return spelling && positions && empty && (← restored s 130)
  check e "fuzzy-order"
      "picker keeps listing order across different alignment scores and attaches the selected original target"
      fun f => do
      let targets := ["a---b", "axab", "ab-z"]
      let fields := targets.map fun target => [("name", target)]
      f.listing (String.join (targets.map fun target => s!"name\t{target}\n"))
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "ab" "ab" do
            return false
          let vt ← s.capture "original-order"
          -- Scores rise through these rows, but input order is authoritative.
          let ordered :=
            fields.zipIdx |>.all fun (info, index) =>
              rowText vt (4 + index) ==
                (if index == 0 then "  ▸ " else "    ") ++
                  String.fromUTF8!
                    (ByteArray.mk
                      (Linger.Core.Listing.humanRow (Linger.Core.Listing.nameWidth fields)
                          info).toArray)
          let start ← s.mark
          s.text "\x0e"
          unless ← s.selected "axab" start do
            return false
          let clean ← acceptThenCancel s
          return ordered && clean &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "axab"] ++
                  call ["ls", "-r", "--porcelain"]
  check e "fuzzy-unicode"
      "picker highlights accent-only and wide matches, clips whole cells, and attaches the untruncated target"
      fun f => do
      let target := "work@e\u0301界éZ"
      f.listing s!"name\t{target}\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "界é" "界é" do
            return false
          let wide ← s.capture "wide-match"
          let scalarPositions :=
            underlined wide 4 == [12, 13, 14] && (wide.getCell 11 4).base == 'e' &&
              (wide.getCell 11 4).marks == ['\u0301'] &&
              (wide.getCell 12 4).base == '界' &&
              (wide.getCell 12 4).width == 2 &&
              (wide.getCell 13 4).width == 0 &&
              (wide.getCell 14 4).base == 'é' &&
              (wide.getCell 15 4).base == 'Z'
          unless ← s.typeQuery "\x15\u0301" "\u0301" do
            return false
          let accent ← s.capture "accent-only-match"
          -- A matched mark must emphasize its containing cell even when
          -- the base scalar itself does not match the query.
          let accentVisible :=
            rowText accent 4 == rowText wide 4 && (accent.getCell 11 4).base == 'e' &&
              (accent.getCell 11 4).marks == ['\u0301'] &&
              (List.range accent.rowCount).all fun row =>
                underlined accent row == if row == 4 then [11] else []
          let accentStyles :=
            (List.range accent.colCount).all fun col =>
              { (accent.getCell col 4).pen with underline := false } ==
                { (wide.getCell col 4).pen with underline := false }
          unless ← s.typeQuery "\x15" "" do
            return false
          let cleared ← s.capture "accent-cleared"
          let clears :=
            rowText cleared 4 == rowText wide 4 &&
              (List.range cleared.rowCount).all fun row => (underlined cleared row).isEmpty
          unless ← s.typeQuery "\x15e\u0301界" "e\u0301界" do
            return false
          let combining ← s.capture "combining-match"
          let cluster :=
            underlined combining 4 == [11, 12, 13] && (combining.getCell 11 4).marks == ['\u0301']
          let start ← s.mark
          s.client.resize 14 4
          unless ← s.untilRow "  ▸ ? work@e\u0301" start do
            return false
          let clipped ← s.capture "clipped-wide-match" 14 4
          let narrow :=
            rowText clipped 1 == "  ▸ ? work@e\u0301" && underlined clipped 1 == [11] &&
              (clipped.getCell 11 1).marks == ['\u0301'] &&
              (clipped.getCell 12 1).base == ' ' &&
              (clipped.getCell 12 1).width == 1 &&
              lastColumnBlank clipped
          unless ← s.typeQuery "\x15\u0301" "\u0301" do
            return false
          let accentClipped ← s.capture "accent-only-clipped" 14 4
          let accentNarrow :=
            rowText accentClipped 1 == rowText clipped 1 &&
              accentClipped.getCell 11 1 == clipped.getCell 11 1 &&
              (List.range accentClipped.rowCount).all
                (fun row => underlined accentClipped row == if row == 1 then [11] else []) &&
              lastColumnBlank accentClipped
          unless ← s.typeQuery "\x15e\u0301界" "e\u0301界" do
            return false
          let start ← s.mark
          s.client.resize 16 4
          unless ← s.untilRow "  ▸ ? work@e\u0301界é" start do
            return false
          let fitted ← s.capture "fitted-wide-match" 16 4
          let fits :=
            rowText fitted 1 == "  ▸ ? work@e\u0301界é" && underlined fitted 1 == [11, 12, 13] &&
              (fitted.getCell 12 1).width == 2 &&
              (fitted.getCell 13 1).width == 0 &&
              lastColumnBlank fitted
          IO.FS.writeFile (f.root / "match-observation")
              s!"wide-columns={repr (underlined wide 4)} expected=[12, 13, 14]\nscalar-positions={scalarPositions}\naccent-only-columns={repr (underlined accent 4)} expected=[11]\naccent-only-visible={accentVisible}\naccent-selection-status-styles={accentStyles}\naccent-cleared={clears}\ncombining-columns={repr (underlined combining 4)} expected=[11, 12, 13]\ncluster={cluster}\nclipped-columns={repr (underlined clipped 1)} expected=[11]\nwhole-cell-clipping={narrow}\naccent-clipped-columns={repr (underlined accentClipped 1)} expected=[11]\naccent-clipped-visible={accentNarrow}\nfitted-columns={repr (underlined fitted 1)} expected=[11, 12, 13]\nwhole-wide-cell={fits}\n"
          let start ← s.mark
          s.client.resize 80 12
          unless ← s.prompt "e\u0301界" start do
            return false
          let clean ← acceptThenCancel s
          return scalarPositions && accentVisible && accentStyles && clears && cluster && narrow &&
              accentNarrow &&
              fits &&
              clean &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                  call ["ls", "-r", "--porcelain"]

private def displayChecks (e : Env) : IO Unit := do
  check e "normal-frame"
      "picker normal frame has the spaced title, dim placeholder, exact rows and attach help"
      fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        let vt ← s.capture "normal-frame"
        let footer := (List.range vt.rowCount).find? fun row => has (rowText vt row) "↵ attach"
        let layout :=
          (rowText vt 0).trimAscii.toString == "linger" && rowText vt 1 == "" &&
            rowText vt 2 == "  › Find or create a session" &&
            rowText vt 3 == "" &&
            rowText vt 4 == "  ▸ ? Alpha (busy)" &&
            rowText vt 5 == "    ? Beta  (busy)" &&
            rowText vt 6 == "    ? Gamma (busy)" &&
            rowText vt 7 == "    + Create main" &&
            (vt.getCell 4 2).pen.dim &&
            (vt.getCell 2 4).pen.reverse &&
            (vt.getCell 4 4).pen.reverse &&
            !(vt.getCell 4 5).pen.reverse &&
            !(vt.getCell 2 0).pen.bold &&
            lastColumnBlank vt
        let help :=
          match footer with
          | none => false
          | some row =>
            row ≥ 9 && rowText vt (row - 1) == "" && (rowText vt row).startsWith "  ↵ attach" &&
              has (rowText vt row) "↑↓ move" &&
              has (rowText vt row) "esc / ^C quit" &&
              !has (rowText vt row) "refresh" &&
              (vt.getCell 2 row).pen.dim
        s.text "\x03"
        return layout && help && (← restored s 130)
  check e "create-frame"
      "picker query text stays undimmed and the explicit creation row changes Enter help" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        unless ← s.typeQuery "new-session" "new-session" do
          return false
        let vt ← s.capture "create-frame"
        let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
        let shown :=
          rowText vt 2 == "  › new-session" && !(vt.getCell 4 2).pen.dim &&
            rowText vt 4 == "  ▸ + Create new-session" &&
            (vt.getCell 4 4).pen.reverse &&
            has screen "  ↵ create" &&
            has screen "↑↓ move" &&
            has screen "esc / ^C quit" &&
            !has screen "↵ attach" &&
            !has screen "Find or create a session" &&
            (List.range vt.rowCount).all (fun row => (underlined vt row).isEmpty) &&
            lastColumnBlank vt
        return shown && (← acceptThenCancel s) &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "new-session"] ++
                call ["ls", "-r", "--porcelain"]
  check e "unchanged-keys"
      "picker clamped movement, empty editing and ignored controls cause no repaint" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        s.observe 100
        let start ← s.mark
        s.text "\x1b[A\x10\x1b[H\x7f\x08\x15\x00\x07"
        s.observe 350
        let quiet := (← s.mark) == start
        s.text "\x03"
        return quiet && (← restored s 130)

private def Fixture.waitListing (f : Fixture) (serial : Nat) (completed : Bool := false) :
    IO Bool :=
  waitFor 4500
    ((f.root / s!"list-{if completed then "completed" else "started"}-{serial}").pathExists)

private def Fixture.releaseListing (f : Fixture) (serial : Nat) : IO Unit :=
  IO.FS.writeFile (f.root / s!"release-listing-{serial}") ""

private def refreshChecks (e : Env) : IO Unit := do
  check e "refresh-reordered"
      "automatic refresh retains query and exact highlighted target across changed ordering"
      fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        unless ← s.typeQuery "a" "a" do
          return false
        let selection ← s.mark
        s.text "\x0e"
        unless ← s.selected "Beta" selection do
          return false
        let start ← s.mark
        f.listing "name\tGamma\nname\tDelta\nname\tAlpha\nname\tBeta\n"
        unless ← s.untilRow "Delta" start do
          return false
        unless ← s.selected "Beta" start do
          return false
        let vt ← s.capture "reordered-frame"
        let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
        let retained := has screen "  › a" && has screen "  ▸ ? Beta  (busy)"
        return retained && (← acceptThenCancel s) &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "Beta"] ++
                call ["ls", "-r", "--porcelain"]
  check e "refresh-removed"
      "automatic refresh clamps a removed selection while preserving an invalid creation query"
      fun f => do
      f.listing "name\tone@host\nname\ttwo@host\nname\tthree@host\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "@" "@" do
            return false
          let selection ← s.mark
          s.text "\x1b[F"
          unless ← s.selected "three@host" selection do
            return false
          let start ← s.mark
          f.listing "name\tfirst@host\nname\tlast@host\n"
          unless ← s.selected "last@host" start do
            return false
          let vt ← s.capture "removed-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          return has screen "  › @" && !has screen "Create " && (← acceptThenCancel s) &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "last@host"] ++
                  call ["ls", "-r", "--porcelain"]
  check e "refresh-created"
      "automatic refresh turns a highlighted creation into the same existing target and attach help"
      fun f => do
      f.listing "name\tworkshop\nname\tworkbench\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "work" "work" do
            return false
          let selection ← s.mark
          s.text "\x1b[F"
          unless ← s.selected "+ Create work" selection do
            return false
          let start ← s.mark
          f.listing "name\twork\nname\tworkshop\nname\tworkbench\n"
          unless ← s.selected "work" start do
            return false
          let vt ← s.capture "created-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          return has screen "  › work" && has screen "  ▸ ? work      (busy)\n" &&
              !has screen "Create work" &&
              has screen "↵ attach" &&
              (← acceptThenCancel s) &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "work"] ++
                  call ["ls", "-r", "--porcelain"]
  check e "ctrl-r-ignored"
      "picker Ctrl-R preserves query and highlight without repaint or a new terminal visit" fun f =>
      do
      f.listing "name\tBeta\nname\tBravo\n"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "B" "B" do
            return false
          let selection ← s.mark
          s.text "\x1b[F"
          unless ← s.selected "+ Create B" selection do
            return false
          s.observe 100
          let start ← s.mark
          s.text "\x12"
          s.observe 400
          let quiet := (← s.mark) == start
          let vt ← s.capture "ctrl-r-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          s.text "\x03"
          return quiet && has screen "  › B" && has screen "  ▸ + Create B" && (← restored s 130) &&
              (← f.visits) == call ["ls", "-r", "--porcelain"]
  check e "idle-refresh"
      "picker repeats complete listings about one second apart without repainting unchanged snapshots"
      fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        s.observe 100
        let start ← s.mark
        let repeated ← f.waitListing 3 true
        s.observe 100
        let quiet := (← s.mark) == start
        let starts :=
          (lines (← readText (f.root / "list-starts"))).filterMap fun line =>
            ((line.splitOn "\t")[2]?).bind String.toNat?
        let gaps := (starts.zip starts.tail).map fun (a, b) => b - a
        IO.FS.writeFile (f.root / "attempt-gaps-ms") (reprStr gaps)
        -- Observer timestamps are taken in the child after exec and stty. Allow
        -- scheduling variance there; a tight loop or a five-second timer fails.
        let spaced := starts.length ≥ 3 && gaps.all (· ≥ 850)
        s.text "\x03"
        return repeated && quiet && spaced && (← restored s 130) &&
            (← f.visits) == call ["ls", "-r", "--porcelain"] &&
            !(← (f.root / "listing-overlap").pathExists)
  for (slug, text, rc, error) in
    [("failure", "name\tPartial\n", 9, "could not list sessions (exit 9)"),
      ("duplicate", "name\tFresh\nname\tFresh\n", 1, "duplicate session target"),
      ("malformed", "name\tFresh\nname\tbad\textra\n", 1, "malformed name record")] do
    check e s!"refresh-{slug}"
        s!"automatic refresh rejects the entire bad snapshot and prints an error after restoration ({slug})"
        fun f =>
        withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          f.listing text (if slug == "failure" then rc else 0)
          let visible ← s.until error
          let clean ← restored s rc
          let out ← s.output.get
          return visible && clean && !hasText out "Partial" && !hasText out "Fresh" &&
              ordered out (modeSet 1049 false) error.toUTF8.toList &&
              (← numberFile (f.root / "list-count")) ≥ 2 &&
              (← f.visits) == call ["ls", "-r", "--porcelain"]
  check e "refresh-partial"
      "incomplete listing output cannot replace displayed rows and keyboard editing stays responsive"
      fun f => do
      f.listing "name\talpha@host\nname\tbeta@host\nname\tgamma@host\n"
      IO.FS.writeFile (f.root / "hold-listing-from") "2"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          IO.FS.writeFile (f.root / "listing-prefix") "name\tready@host\n"
          f.listing "name\tbeta@host\nname\tnew@host\n"
          unless ← f.waitListing 2 do
            return false
          unless ← s.typeQuery "@" "@" do
            return false
          let selection ← s.mark
          s.text "\x0e"
          unless ← s.selected "beta@host" selection do
            return false
          let before ← s.capture "partial-frame"
          let beforeText := String.fromUTF8! (ByteArray.mk (screenText before).toArray)
          let incomplete :=
            has beforeText "beta@host" && !has beforeText "ready@host" && !has beforeText "new@host"
          let start ← s.mark
          f.releaseListing 2
          unless ← s.untilRow "new@host" start do
            return false
          unless ← s.selected "beta@host" start do
            return false
          let vt ← s.capture "complete-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          s.text "\x03"
          return incomplete && has screen "ready@host" && has screen "new@host" &&
              has screen "  › @" &&
              !has screen "alpha@host" &&
              (← restored s 130)
  check e "refresh-input-order"
      "completed refresh follows displayed navigation and paints before the next accepted key"
      fun f => do
      f.listing "name\talpha@host\nname\tbeta@host\nname\tgamma@host\n"
      IO.FS.writeFile (f.root / "hold-listing-from") "2"
      withSession f.picker #[] fun s => do
          unless ← s.prompt do
            return false
          unless ← s.typeQuery "@" "@" do
            return false
          f.listing "name\tbeta@host\nname\tdelta@host\nname\tgamma@host\nname\talpha@host\n"
          unless ← f.waitListing 2 do
            return false
          let start ← s.mark
          s.text "\x0e"
          f.releaseListing 2
          unless ← s.untilRow "delta@host" start do
            return false
          let vt ← s.capture "ready-frame"
          let displayed := rowText vt 4 == "  ▸ ? beta@host  (busy)"
          IO.FS.removeFile (f.root / "hold-listing-from")
          let start ← s.mark
          s.text "\x0e"
          unless ← s.selected "delta@host" start do
            return false
          return displayed && (← acceptThenCancel s) &&
              (← f.visits) ==
                call ["ls", "-r", "--porcelain"] ++ call ["attach", "delta@host"] ++
                  call ["ls", "-r", "--porcelain"]
  for (phase, serial) in [("initial", 1), ("refresh", 2)] do
    for (slug, key) in [("ctrl-c", "\x03"), ("escape", "\x1b")] do
      let caseName := if serial == 1 then s!"initial-cancel-{slug}" else s!"slow-cancel-{slug}"
      check e caseName
          s!"slow {phase} listing owns one child, accepts keyboard input, cancels promptly and reaps that child ({slug})"
          fun f => do
          IO.FS.writeFile (f.root / "hold-listing-from") (toString serial)
          withSession f.picker #[] fun s => do
              if serial == 2 then
                unless ← s.prompt do
                  return false
              unless ← f.waitListing serial do
                return false
              let pid ← numberFile (f.root / s!"list-started-{serial}")
              let live := pid > 0 && (← alive (UInt32.ofNat pid))
              let start ← s.mark
              -- Enter cannot accept an item before the first complete snapshot.
              s.text (if serial == 1 then "\rB" else "B")
              let responsive ← s.untilAny ["  › B", "linger> B"] start 1500
              -- This interval crosses another refresh deadline while stdout is held.
              s.observe 1200
              let one :=
                (← numberFile (f.root / "list-count")) == serial &&
                  !(← (f.root / "listing-overlap").pathExists)
              let start ← s.mark
              let began ← monotonicMs
              s.text key
              let promptExit ← s.until "MANAGER-EXIT:130" start 2000
              let elapsed := (← monotonicMs) - began
              let reaped ←
                waitFor 500 do
                    return pid > 0 && !(← alive (UInt32.ofNat pid))
              IO.FS.writeFile (f.root / "cancel-observation")
                  s!"pid={pid}\nalive-before={live}\nkeyboard-responsive={responsive}\none-in-flight={one}\nexit-within-deadline={promptExit}\nelapsed-ms={elapsed}\nchild-gone={reaped}\n"
              return live && responsive && one && promptExit && reaped && (← restored s 130) &&
                  (← f.visits) == call ["ls", "-r", "--porcelain"]
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
            s.client.resize 14 4
            unless ← s.until "wide@" start do
              return false
            s.observe 150
            let out ← s.output.get
            let frame := out.extract start out.size
            let vt := (Vt.init 14 4).feedBytes frame
            let screen := ByteArray.mk (screenText vt).toArray
            IO.FS.writeBinFile (f.root / "resized-frame.bin") frame
            IO.FS.writeBinFile (f.root / "screen.txt") screen
            let fits := hasText screen "  ▸ ? wide@界" && !hasText screen "Z" && lastColumnBlank vt
            s.client.resize 80 12
            unless ← s.prompt "" (← s.mark) do
              return false
            return fits && (← acceptThenCancel s) &&
                (← f.visits) ==
                  call ["ls", "-r", "--porcelain"] ++ call ["attach", target] ++
                    call ["ls", "-r", "--porcelain"])
          "both" 80 12
  for (slug, description, rows) in [("one-row", "one-row", 1), ("two-rows", "two-row", 2)] do
    check e slug s!"picker probe keeps its current candidate visible in a {description} terminal"
        fun f =>
        withSession f.picker #[]
          (fun s => do
            let shown ← s.until "Alpha"
            s.observe 150
            let vt := (Vt.init 40 rows).feedBytes (← s.output.get)
            let screen := ByteArray.mk (screenText vt).toArray
            IO.FS.writeBinFile (f.root / "screen.txt") screen
            let visible :=
              shown && rowText vt (rows - 1) == "  ▸ ? Alpha (busy)" && !hasText screen "linger" &&
                !hasText screen "↵" &&
                lastColumnBlank vt
            s.text "\x03"
            return visible && (← restored s 130) &&
                (← f.visits) == call ["ls", "-r", "--porcelain"])
          "both" 40 (UInt32.ofNat rows)

private def defaultChecks (e : Env) : IO Unit := do
  for empty in [true, false] do
    let slug := if empty then "empty-path" else "impostor-path"
    check e slug s!"picker probe uses its absolute executable for ls and attach ({slug})" fun f =>
        do
        let impostor := f.root / "bin" / "linger"
        IO.FS.writeFile impostor
            s!"#!/bin/sh\nprintf hit >{quote (f.root / "impostor-hit").toString}\nexit 97\n"
        chmod impostor.toString 0o755
        let path := if empty then "" else (f.root / "bin").toString
        let f := { f with env := f.env.push ("PATH", some path) }
        withSession f.picker #[] fun s => do
            unless ← s.prompt do
              return false
            return (← acceptThenCancel s) && !(← (f.root / "impostor-hit").pathExists) &&
                (← f.visits) ==
                  call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                    call ["ls", "-r", "--porcelain"]
  for rc in [0, 7, 255] do
    check e s!"default-{rc}" s!"picker probe returns to a fresh picker after attach status {rc}"
        fun f => do
        IO.FS.writeFile (f.root / "attach-rc") (toString rc)
        withSession f.picker #[] fun s => do
            unless ← s.prompt do
              return false
            return (← acceptThenCancel s) &&
                (← f.visits) ==
                  call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                    call ["ls", "-r", "--porcelain"]
  check e "successive"
      "picker probe repeatedly attaches from fresh snapshots after statuses 0, 7 and 255" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        let remote := "-work@me@dev-a"
        let shellText := "work@host with 'spaces' $TERM"
        let mut expected := call ["ls", "-r", "--porcelain"]
        let mut count := 0
        let mut normal := true
        for (target, query, rc, next, separator) in
          [("Beta", "B", 0, remote, []), (remote, "wrk", 7, shellText, ["--"]),
            (shellText, "host", 255, "Fresh", [])] do
          unless ← s.typeQuery query query do
            return false
          f.afterAttach s!"name\t{next}\nname\tOther\n"
          IO.FS.writeFile (f.root / "attach-rc") (toString rc)
          s.text "\r"
          count := count + 1
          unless ← returned s next count do
            return false
          expected :=
            expected ++ call ("attach" :: separator ++ [target]) ++ call ["ls", "-r", "--porcelain"]
          normal :=
            normal && (← beforeAttach s count count) && (← attachNormal f count) &&
              (← f.visits) == expected
        s.text "\x03"
        return normal && (← restored s 130 4) && (← f.visits) == expected
  check e "return-listing-failure"
      "picker probe preserves a failed listing status after attach and restores the terminal"
      fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        f.afterAttach "name\tPartial\n" 9
        s.text "\r"
        let clean ← failureRestored s 9 "linger: could not list sessions (exit 9)" 1
        return clean && (← beforeAttach s) && (← attachNormal f) &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                call ["ls", "-r", "--porcelain"]
  check e "return-malformed"
      "picker probe rejects a malformed listing after attach before another picker visit" fun f =>
      withSession f.picker #[] fun s => do
        unless ← s.prompt do
          return false
        f.afterAttach "name\tNext\nname\tNext\n"
        s.text "\r"
        let clean ← failureRestored s 1 "picker probe:" 1
        return clean && (← beforeAttach s) && (← attachNormal f) &&
            (← f.visits) ==
              call ["ls", "-r", "--porcelain"] ++ call ["attach", "Alpha"] ++
                call ["ls", "-r", "--porcelain"]

private def realCheck (e : Env) : IO Unit := do
  for (slug, query, name, existing) in
    [("real", "", "manager-live", true), ("real-create", "new-session", "new-session", false),
      ("real-default", "", "main", false)] do
    check e slug
        s!"linger attach {if existing then "attaches" else "creates"}, detaches and returns to selection with no linger on PATH ({slug})"
        fun f => do
        let owned : Env := { e with dir := (f.root / "state").toString }
        let f := { f with env := f.env.push ("LINGER_DIR", some owned.dir) }
        let state := System.FilePath.mk owned.dir
        if existing then
          let create ←
            withLaunchLock <|
                IO.Process.spawn
                  { cmd := e.bin, args := #["run", name, "true"], env := f.env, stdin := .null,
                    stdout := .piped, stderr := .piped }
          let rc ← waitChild create 5000
          if rc != 0 then
            throw (IO.userError s!"manager live fixture failed: {← create.stderr.readToEnd}")
        try
          withSession f #["attach"] fun s => do
              unless ← s.prompt do
                return false
              let start ← s.mark
              if !query.isEmpty then
                unless ← s.typeQuery query query do
                  return false
              let row := if existing then name else s!"+ Create {name}"
              let shown ← s.selected row (if query.isEmpty then 0 else start)
              s.observe 200
              let untouched := existing || (← state.readDir).isEmpty
              IO.FS.writeFile (f.root / "before-accept")
                  s!"row-visible={shown}\nno-early-creation={untouched}\n"
              s.text "\r"
              let attached ←
                waitFor 5000 do
                    return (← withLaunchLock (owned.info name "clients")) == some "1"
              let listing ← withLaunchLock (owned.out #["ls", "--porcelain"])
              IO.FS.writeFile (f.root / "after-accept") listing
              let names :=
                (records listing).filterMap fun (k, v) => if k == "name" then some v else none
              if !attached then
                return false
              let shellStart ← s.mark
              s.text "printf 'manager-live-%s\\n' \"$((20+22))\"\r"
              unless ← s.until "manager-live-42" shellStart do
                return false
              let beforeDetach ← s.mark
              s.client.detach
              unless ← s.prompt "" beforeDetach do
                return false
              unless ← s.selected name beforeDetach do
                return false
              let detached ←
                waitFor 5000 do
                    return (← withLaunchLock (owned.info name "clients")) == some "0"
              IO.FS.writeFile (f.root / "after-detach")
                  (← withLaunchLock (owned.out #["info", name]))
              s.text "\x03"
              return shown && untouched && names == [name] && detached &&
                  (← termiosRestored s 130) &&
                  sequenceCount (← s.output.get) (modeSet 1049 true) ≥ 2
        finally
          withLaunchLock (owned.killAll #[name])

/-- Foreign fixtures use explicit files and private homes/state. The native
encoding keeps expected identities tied to the save parser's own policy. -/
private def savedPane (name dir command : String := "") : String :=
  s!"pane\t{Linger.Tools.Resurrect.encodeName name}\t0\t1\t:*\t0\ttitle\t:{dir}\t1\tsh\t:{command}\n"

private def Fixture.nativeNames (f : Fixture) : IO (List String) := do
  let (rc, out, err) ← f.piped #["ls", "--porcelain"]
  unless rc == 0 do
    throw (IO.userError s!"native fixture listing failed: {err}")
  return (records out).filterMap fun (key, value) => if key == "name" then some value else none

private def checkSaved (e : Env) (slug label : String) (body : Fixture → Env → IO Bool) : IO Unit :=
  check e s!"tmux-{slug}" label fun f => do
    let owned : Env := { e with dir := (f.root / "state").toString }
    let f := { f with env := f.env.push ("LINGER_DIR", some owned.dir) }
    try
      body f owned
    finally
      withLaunchLock
          (owned.killAll #["saved-first", "saved-chosen", "-saved-chosen", "never-create"])

private def savedChecks (e : Env) : IO Unit := do
  for (slug, key) in [("ctrl-c", "\x03"), ("ctrl-d", "\x04"), ("escape", "\x1b")] do
    checkSaved e slug
        s!"tmux select cancellation leaves all saved panes unimported and restores the terminal ({slug})"
        fun f _ => do
        let save := f.root / "saved file"
        IO.FS.writeFile save
            (savedPane "saved-first" f.root.toString ++ savedPane "saved-chosen" f.root.toString)
        withSession f #["tmux", "select", save.toString] fun s => do
            unless ← s.selected "saved-first" do
              return false
            let header ← s.untilRow "linger · tmux save"
            s.observe 150
            let before ← f.nativeNames
            s.text key
            let clean ← restored s 130
            return header && before.isEmpty && clean && (← f.nativeNames).isEmpty
  checkSaved e "unmatched"
      "tmux select has no Create row for empty or unmatched queries and Enter starts no session"
      fun f _ => do
      let save := f.root / "saved file"
      IO.FS.writeFile save (savedPane "saved-first" f.root.toString)
      withSession f #["tmux", "select", save.toString] fun s => do
          unless ← s.selected "saved-first" do
            return false
          let initial ← s.capture "empty-query"
          let initialNoCreate := !hasText (ByteArray.mk (screenText initial).toArray) "Create "
          let start ← s.mark
          s.text "never-create"
          unless ← s.untilRow "  › never-create" start do
            return false
          s.text "\r"
          s.observe 350
          let unmatched ← s.capture "unmatched-query"
          let noCreate := !hasText (ByteArray.mk (screenText unmatched).toArray) "Create "
          let waiting := !(← (f.root / "result").pathExists)
          let names ← f.nativeNames
          let start ← s.mark
          s.text "\x15"
          let editable ← s.selected "saved-first" start
          s.text "\x03"
          return initialNoCreate && noCreate && waiting && names.isEmpty && editable &&
              (← restored s 130) &&
              (← f.nativeNames).isEmpty
  checkSaved e "chosen"
      "tmux select creates only the chosen fresh shell in its exact cwd, ignores saved commands and returns after detach"
      fun f owned => do
      let dir := f.root / "cwd 'literal' $HOME \"quoted\" 界"
      IO.FS.createDirAll dir
      let dir ← IO.FS.realPath dir
      let save := f.root / "saved file"
      let replayed := f.root / "saved-command-ran"
      let command := s!"printf replay >{quote replayed.toString}"
      -- A nonexistent unchosen directory must not block the valid selection.
      IO.FS.writeFile save
          (savedPane "saved-first" (f.root / "absent").toString command ++
            savedPane "saved-chosen" dir.toString command)
      withSession f #["tmux", "select", save.toString] fun s => do
          unless ← s.selected "saved-first" do
            return false
          let start ← s.mark
          s.text "chosen"
          unless ← s.selected "saved-chosen" start do
            return false
          let untouched := (← f.nativeNames).isEmpty
          s.text "\r"
          let attached ←
            waitFor 5000 do
                return (← withLaunchLock (owned.info "saved-chosen" "clients")) == some "1"
          unless attached do
            return false
          let cwdFile := f.root / "shell-cwd"
          let start ← s.mark
          s.text s!"pwd -P >{quote cwdFile.toString}; printf 'saved-shell-%s\\n' \"$((20+22))\"\r"
          let shell ← s.until "saved-shell-42" start
          let cwd ← readText cwdFile
          let names ← f.nativeNames
          let start ← s.mark
          s.client.detach
          let returned ← s.selected "saved-first" start
          let header ← s.untilRow "linger · tmux save" start
          let detached ←
            waitFor 3000 do
                return (← withLaunchLock (owned.info "saved-chosen" "clients")) == some "0"
          s.text "\x03"
          let clean ← termiosRestored s 130
          IO.FS.writeFile (f.root / "selection-observation")
              s!"no-early-import={untouched}\nshell={shell}\ncwd={repr cwd}\nnames={repr names}\nreturned={returned}\ndetached={detached}\n"
          return untouched && shell && cwd == dir.toString ++ "\n" && names == ["saved-chosen"] &&
              returned &&
              header &&
              detached &&
              clean &&
              !(← replayed.pathExists)
  checkSaved e "chosen-leading"
      "tmux select attaches a chosen saved pane whose name starts with - and returns after detach"
      fun f owned => do
      let save := f.root / "saved file"
      IO.FS.writeFile save (savedPane "-saved-chosen" f.root.toString)
      withSession f #["tmux", "select", save.toString] fun s => do
          unless ← s.selected "-saved-chosen" do
            return false
          s.text "\r"
          let attached ←
            waitFor 5000 do
                return (← withLaunchLock (owned.info "-saved-chosen" "clients")) == some "1"
          unless attached do
            return false
          let start ← s.mark
          s.client.detach
          let returned ← s.selected "-saved-chosen" start
          s.text "\x03"
          return returned && (← termiosRestored s 130)
  for (slug, content, error) in
    [("missing", none, "save not found"),
      ("malformed", some "pane\tbroken\n", "malformed pane record")] do
    checkSaved e slug
        s!"tmux select save failure restores terminal state and starts no sessions ({slug})"
        fun f _ => do
        let save := f.root / "saved file"
        if let some text := content then
          IO.FS.writeFile save text
        withSession f #["tmux", "select", save.toString] fun s => do
            let clean ← failureRestored s 1 error
            return clean && (← f.nativeNames).isEmpty
  checkSaved e "missing-cwd"
      "tmux select preflight rejects the chosen missing cwd after restoring the terminal" fun f _ =>
      do
      let save := f.root / "saved file"
      IO.FS.writeFile save (savedPane "saved-first" (f.root / "absent").toString)
      withSession f #["tmux", "select", save.toString] fun s => do
          unless ← s.selected "saved-first" do
            return false
          s.text "\r"
          let clean ← failureRestored s 1 "working directory not found at line 1" 1
          return clean && (← f.nativeNames).isEmpty
  checkSaved e "frozen-cwd" "tmux select accepts the displayed cwd after its save has been replaced"
      fun f owned => do
      let original := f.root / "original 'cwd' $HOME"
      let replacement := f.root / "replacement"
      IO.FS.createDirAll original
      IO.FS.createDirAll replacement
      let original ← IO.FS.realPath original
      let save := f.root / "saved file"
      IO.FS.writeFile save ("\n" ++ savedPane "saved-chosen" original.toString)
      let (rc, catalog, _) ← f.piped #["tmux", "ls", "--porcelain", save.toString]
      unless rc == 0 do
        return false
      f.listing catalog
      let changed := savedPane "saved-chosen" replacement.toString
      IO.FS.writeFile (f.root / "replacement-save") changed
      IO.FS.writeFile (f.root / "rewrite-save") save.toString
      IO.FS.writeFile (f.root / "real-executable") f.manager
      let probe :=
        { f with
          manager := f.self,
          managerArgs := #["--manager-probe", "tmux-picker", f.executable, save.toString] }
      withSession probe #[] fun s => do
          unless ← s.selected "saved-chosen" do
            return false
          let replaced := (← readText save) == changed
          s.text "\r"
          unless ← s.until "MANAGER-ATTACH-1" do
            return false
          let some position := findText (← s.output.get) "MANAGER-ATTACH-1" | return false
          let returned ← s.selected "saved-chosen" (position + "MANAGER-ATTACH-1".utf8ByteSize)
          s.text "\x03"
          let clean ← restored s 130 2
          let calls ← f.calls
          let exact :=
            has calls (call ["tmux", "ls", "--porcelain", save.toString]) &&
              has calls (call ["run", "saved-chosen", "true"]) &&
              has calls (call ["attach", "saved-chosen"])
          let pid := (← withLaunchLock (owned.info "saved-chosen" "pid")).bind String.toNat?
          let cwd ←
            match pid with
            | some pid =>
              getcwdOf (UInt32.ofNat pid)
            | none =>
              pure ""
          return replaced && returned && clean && exact && (← attachNormal f) &&
              (← beforeAttach s) &&
              (← readText (f.root / "run-cwd")) == original.toString &&
              cwd == original.toString &&
              (← f.nativeNames) == ["saved-chosen"]
  checkSaved e "recreated-cwd"
      "tmux select final attach recreates a vanished session in the displayed cwd" fun f owned => do
      let dir := f.root / "displayed 'cwd' $HOME"
      IO.FS.createDirAll dir
      let dir ← IO.FS.realPath dir
      let save := f.root / "saved file"
      IO.FS.writeFile save (savedPane "saved-chosen" dir.toString)
      let (rc, catalog, _) ← f.piped #["tmux", "ls", "--porcelain", save.toString]
      unless rc == 0 do
        return false
      f.listing catalog
      let seeded := { f with cwd := some dir }
      let (created, _, _) ← seeded.piped #["run", "saved-chosen", "true"]
      unless created == 0 do
        return false
      let some oldPid := (← withLaunchLock (owned.info "saved-chosen" "pid")).bind String.toNat?
        | return false
      IO.FS.writeFile (f.root / "vanish-before-attach") (toString oldPid)
      IO.FS.writeFile (f.root / "real-executable") f.manager
      let probe :=
        { f with
          manager := f.self,
          managerArgs := #["--manager-probe", "tmux-picker", f.executable, save.toString] }
      withSession probe #[] fun s => do
          unless ← s.selected "saved-chosen" do
            return false
          s.text "\r"
          let attached ←
            waitFor 5000 do
                return (← withLaunchLock (owned.info "saved-chosen" "clients")) == some "1"
          unless attached do
            return false
          let newPid := (← withLaunchLock (owned.info "saved-chosen" "pid")).bind String.toNat?
          let cwdFile := f.root / "recreated-shell-cwd"
          let start ← s.mark
          s.text s!"pwd -P >{quote cwdFile.toString}; printf 'recreated-%s\\n' shell-ok\r"
          let answered ← s.until "recreated-shell-ok" start
          let actual ← readText cwdFile
          let attachCwd ← readText (f.root / "attach-cwd")
          let vanished ← readText (f.root / "vanished-before-native-attach")
          let start ← s.mark
          s.client.detach
          let returned ← s.selected "saved-chosen" start
          s.text "\x03"
          let clean ← termiosRestored s 130
          let calls ← f.calls
          let skippedCreation :=
            has calls (call ["ls", "--porcelain"]) &&
              !has calls (call ["run", "saved-chosen", "true"])
          IO.FS.writeFile (f.root / "recreation-observation")
              s!"old-pid={oldPid}\nnew-pid={repr newPid}\nvanished={vanished}\nskipped-creation={skippedCreation}\nexpected-cwd={repr dir.toString}\nattach-cwd={repr attachCwd}\nshell-cwd={repr actual}\nanswered={answered}\nreturned={returned}\nterminal-restored={clean}\n"
          return vanished == "true" && skippedCreation && newPid.isSome && newPid != some oldPid &&
              answered &&
              attachCwd == dir.toString &&
              actual == dir.toString ++ "\n" &&
              returned &&
              clean &&
              (← attachNormal f) &&
              (← beforeAttach s) &&
              (← f.nativeNames) == ["saved-chosen"]
  checkSaved e "relative-last" "tmux select refresh follows a repointed relative last symlink"
      fun f _ => do
      let f := { f with cwd := some f.root }
      IO.FS.writeFile (f.root / "first-save") (savedPane "saved-first" f.root.toString)
      IO.FS.writeFile (f.root / "second-save") (savedPane "saved-chosen" f.root.toString)
      for (target, name) in [("first-save", "last"), ("second-save", "next-last")] do
        let link ←
          withLaunchLock <|
              IO.Process.output { cmd := "ln", args := #["-s", target, (f.root / name).toString] }
        unless link.exitCode == 0 do
          throw (IO.userError s!"could not create private save symlink: {link.stderr}")
      withSession f #["tmux", "select", "last"] fun s => do
          unless ← s.selected "saved-first" do
            return false
          let start ← s.mark
          IO.FS.rename (f.root / "next-last") (f.root / "last")
          let (rc, catalog, _) ← f.piped #["tmux", "ls", "--porcelain", "last"]
          IO.FS.writeFile (f.root / "repointed-catalog") catalog
          let changed := rc == 0 && has catalog "name\tsaved-chosen\n"
          let refreshed ← s.selected "saved-chosen" start
          let _ ← s.capture "after-repoint"
          s.text "\x03"
          let clean ← restored s 130
          let names ← f.nativeNames
          IO.FS.writeFile (f.root / "refresh-observation")
              s!"repointed-catalog={changed}\nrefreshed={refreshed}\nterminal-restored={clean}\nnames={repr names}\n"
          return changed && refreshed && clean && names.isEmpty

private def startProgram (f : Fixture) (owned : Env) (name : String) : IO Bool := do
  let child ←
    withLaunchLock <|
        IO.Process.spawn
          { cmd := owned.bin,
            args := #["run", name, s!"{quote f.self} --manager-probe session-program"],
            env := f.env, stdin := .null, stdout := .piped, stderr := .piped }
  let rc ← waitChild child 5000
  if rc != 0 then
    throw (IO.userError s!"session program launch failed: {← child.stderr.readToEnd}")
  return ←
      waitFor 5000 do
          return (← numberFile (f.root / "session-program-pid")) > 0 &&
              has (← withLaunchLock (owned.out #["capture", name])) "MANAGER-PROGRAM-READY"

private def programChecks (e : Env) : IO Unit := do
  for (slug, key) in [("ctrl-c", "\x03"), ("escape", "\x1b")] do
    check e s!"program-survives-{slug}"
        s!"linger attach cancellation leaves the actual session program alive and responsive ({slug})"
        fun f => do
        let owned : Env := { e with dir := (f.root / "state").toString }
        let f := { f with env := f.env.push ("LINGER_DIR", some owned.dir) }
        let name := "program-survivor"
        try
          unless ← startProgram f owned name do
            return false
          let pid ← numberFile (f.root / "session-program-pid")
          let before ← withLaunchLock (owned.out #["info", name])
          withSession f #["attach"] fun s => do
              unless ← s.prompt do
                return false
              unless ← s.selected name do
                return false
              let live := pid > 0 && (← alive (UInt32.ofNat pid))
              s.text key
              let clean ← restored s 130
              let survived := pid > 0 && (← alive (UInt32.ofNat pid))
              let challenge := s!"challenge-after-{slug}"
              let (sent, _, _) ← withLaunchLock (owned.cli #["send", name, challenge ++ "\n"])
              let answered ←
                waitFor 2000 do
                    return (← readText (f.root / "session-program-response")) == challenge
              let detached := (← withLaunchLock (owned.info name "clients")) == some "0"
              IO.FS.writeFile (f.root / "program-survival")
                  s!"pid={pid}\nalive-before={live}\nalive-after={survived}\nsend-exit={sent}\nanswered-after-cancel={answered}\nno-client={detached}\n"
              IO.FS.writeFile (f.root / "before-info") before
              IO.FS.writeFile (f.root / "after-info") (← withLaunchLock (owned.out #["info", name]))
              return clean && live && survived && sent == 0 && answered && detached
        finally
          let _ ← withLaunchLock (owned.cli #["send", name, "stop-program\n"])
          withLaunchLock (owned.killAll #[name])
  check e "attached-ctrl-c"
      "Ctrl-C still interrupts the attached foreground program and leaves its session shell usable"
      fun f => do
      let owned : Env := { e with dir := (f.root / "state").toString }
      let f := { f with env := f.env.push ("LINGER_DIR", some owned.dir) }
      let name := "attached-interrupt"
      try
        unless ← startProgram f owned name do
          return false
        let pid ← numberFile (f.root / "session-program-pid")
        withSession f #["attach"] fun s => do
            unless ← s.prompt do
              return false
            unless ← s.selected name do
              return false
            s.text "\r"
            let attached ←
              waitFor 5000 do
                  return (← withLaunchLock (owned.info name "clients")) == some "1"
            let live := pid > 0 && (← alive (UInt32.ofNat pid))
            unless attached && live do
              return false
            s.text "\x03"
            let interrupted ←
              waitFor 2000 do
                  return !(← alive (UInt32.ofNat pid))
            let start ← s.mark
            s.text "printf 'attached-%s\\n' interrupt-ok\r"
            let shell ← s.until "attached-interrupt-ok" start
            let start ← s.mark
            s.client.detach
            let returned ← s.prompt "" start
            s.text "\x03"
            let clean ← termiosRestored s 130
            IO.FS.writeFile (f.root / "interrupt-observation")
                s!"pid={pid}\nattached={attached}\nalive-before={live}\nprogram-gone={interrupted}\nshell-responded={shell}\nselector-returned={returned}\nterminal-restored={clean}\n"
            return interrupted && shell && returned && clean &&
                (← withLaunchLock (owned.info name "clients")) == some "0"
      finally
        let _ ← withLaunchLock (owned.cli #["send", name, "stop-program\n"])
        withLaunchLock (owned.killAll #[name])

def run : IO UInt32 :=
  Env.suite "manager" fun e => do
    let e := { e with bin := (← IO.getEnv "MANAGER_TEST_LINGER").getD e.bin }
    -- Each check owns a distinct fixture directory, pty and child process tree;
    -- withLaunchLock serializes the process-wide acquisition state.
    -- Overlap two independent groups, keeping each group's observation windows
    -- and deadlines unchanged. Start the long refresh and selection groups first;
    -- wait for every started group before verdict removes their shared parent.
    let groups : List (String × (Env → IO Unit)) :=
      [("refresh", refreshChecks), ("selection", selectionChecks), ("usage", usageChecks),
        ("failure", failureChecks), ("input", inputChecks), ("display", displayChecks),
        ("status", statusChecks), ("fuzzy", fuzzyChecks), ("default", defaultChecks),
        ("real", realCheck), ("program", programChecks), ("saved", savedChecks)]
    let notes ← IO.mkRef (#[] : Array String)
    let timed (name : String) (checks : Env → IO Unit) : IO (String × Nat) := do
      let start ← monotonicMs
      checks e
      return (name, (← monotonicMs) - start)
    parallel 2 (groups.map fun (name, checks) => timed name checks) fun
        | .error err => do
          recordFailure
          notes.modify (·.push s!"note: manager check group: {err}")
        | .ok (name, elapsed) => notes.modify (·.push s!"manager {name}: {elapsed} ms")
    -- Runner merges stderr into stdout. Join every writer and flush buffered
    -- assertions before diagnostics, or a timing can split a PASS line.
    (← IO.getStdout).flush
    for note in ← notes.get do
      IO.eprintln note

end E2E.Manager
