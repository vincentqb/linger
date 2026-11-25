module

import Linger.Os.CoreCode.Answer
import Linger.App.CoreCode.Commands
import Linger.Selector.WorldCode
import Linger.Selector.CoreCode.Picker
import Linger.Import.WorldCode
import Linger.Display.CoreCode.Listing
import ExactJSON.Codec
import Linger.Display.CoreCode.View
import Linger.Target.CoreCode.Name
import Linger.Target.CoreCode.Remote
import Linger.Target.CoreSpec
import Terminal.CoreCode.Title
import Terminal.CoreCode.Mediation
import Linger.Session.WorldCode.Paths
import Linger.Session.WorldCode.Names
import Linger.Import.CoreCode.Resurrect
import Linger.Session.CoreCode.Checkpoint
import Linger.Import.Suites.Recipes
import Std.Sync.Mutex

public section

/-! # Linger.App.Suites.Manager — public entry point and shared picker executor

The helper mode of this same test binary records exact argument vectors and
observes the terminal before the manager, in each listing/attach child, and
after the manager returns. `stty -g` is a test observer, resolved before giving
the manager a restricted PATH. Comparing that portable representation avoids
inspecting the opaque termios blob's padding.

Synthetic failure, argv and terminal cases call `Linger.Selector.Shell.run` through
the test probe with a fixture-owned absolute recorder path. These test the shared
executors; public CLI checks and source gates cover entry-point wiring.
Help, argument validation, terminal dispatch and live attach/detach drive the
actual `linger` binary with no `linger` on the fixture PATH.
File handshakes hold a listing child open without sleeping in the test driver.
The optional `MANAGER_TEST_LINGER` and `MANAGER_TEST_PICKER` overrides let the
same checks and recorder drive preserved predecessor executables.
`Verify.Main.main` dispatches `--manager-probe <args>` to `probe` below.
-/

namespace Linger.App.Suites.Manager

open Terminal
open Verify.Harness
open Os.Shell
open Terminal.Render (modeSet csiNum screenText)
open Terminal.Vt (Vt)
open Verify.Harness renaming shellQuote → quote

/-- PTY acquisition uses libc's shared `ptsname` buffer and briefly holds
descriptors without close-on-exec. Keep every parent launch out of that region,
including ordinary process launches and the harness's one-shot CLI calls.
Session observations and waits for explicitly spawned children stay outside. -/
private initialize launchMutex : Std.Mutex Unit ←
  Std.Mutex.new ()

private def withLaunchLock {α : Type} (action : IO α) : IO α :=
  launchMutex.atomically fun _ => action

private def rowText (vt : Vt) (row : Nat) : String :=
  String.fromUTF8! (ByteArray.mk (Terminal.Render.rowText (vt.getRow row)).toArray)

private def call (args : List String) : String :=
  "CALL\x00linger\x00" ++ String.intercalate "\x00" args ++ "\x00\n"

/-- A listing of these rows' records, their JSON Lines, as `ls --porcelain` prints them. -/
private def jsonListing (records : List (List (String × String))) : String :=
  ExactJSON.encodeLines (records.map Linger.Display.Listing.Record.ofRow).toArray

/-- A listing of sessions with these names and no other field. -/
private def namesListing (names : List String) : String :=
  jsonListing (names.map fun name => [("name", name)])

/-- The full listing a selection visit starts with, and repeats on return. -/
private def listed : String := call ["ls", "-r", "--porcelain"]

/-- One accepted visit: the listing, the attach of `target`, and the listing on return. -/
private def attachVisit (target : List String) : String :=
  listed ++ call ("attach" :: "--" :: target) ++ listed

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
  return withoutPendin result.stdout.trimAscii.toString

private def waitChild {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg)
    (ms : Nat := 15000) : IO UInt32 := return (← waitOrKill child ms).getD 99

/-- The listing argv this recorder answers from the fixture. A native picker lists
local rows alone between remote queries; both native listings print the fixture's
rows, and the picker keeps only a local listing's local rows. -/
private def listingArgs (args : List String) : Bool :=
  match args with
  | ["ls", "-r", "--porcelain"] | ["ls", "--porcelain"] => true
  | _ => false

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
  if listingArgs args then
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
        -- held past `hangMs`, so a picker that waited for this listing, rather than cancelling
        -- or replacing it, would outlast its check's ceiling
        let released ←
          waitFor hangMs do
              return (← (root / s!"release-listing-{serial}").pathExists) ||
                  (← (root / "release-all-listings").pathExists)
        unless released do
          return 96
      else
        IO.FS.writeFile (root / s!"list-started-{serial}") (toString pid)
      output.putStr text
      output.flush
      IO.FS.writeFile (root / s!"list-completed-{serial}") (toString (← monotonicMs))
      return UInt32.ofNat rc
    finally
      IO.FS.writeFile (root / s!"list-ended-{pid}") (toString (← monotonicMs))
      unless overlap do
        IO.FS.removeDir (root / "listing-active")
  match args with
  | ["attach", _] | ["attach", "--", _] =>
    let count ← numberFile (root / "attach-count")
    IO.FS.writeFile (root / "attach-count") (toString (count + 1))
    IO.FS.writeFile (root / s!"attach-termios-{count + 1}") (← snapshot root)
    IO.FS.writeFile (root / s!"attach-ttys-{count + 1}") s!"{ttyIn},{ttyOut}"
    if ← (root / "after-attach-listing").pathExists then
      writeListing root (← readText (root / "after-attach-listing"))
          (← numberFile (root / "after-attach-listing-rc"))
    writeAll stdoutFd s!"\r\nMANAGER-ATTACH-{count + 1}\r\n".toUTF8
    IO.FS.writeFile (root / "attach-cwd") (← IO.currentDir).toString
    return UInt32.ofNat (← numberFile (root / "attach-rc") 7)
  | _ =>
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
  -- spawnPty accepts K=V entries; remove presence-sensitive flags at this boundary. The files
  -- `no-color`, `term` and `linger-session` hold NO_COLOR, TERM and LINGER_SESSION, and a
  -- variable without its file is unset.
  let valueOf (file : String) : IO (Option String) := do
    if ← (root / file).pathExists then
      return some (← IO.FS.readFile (root / file))
    return none
  let noColor ← valueOf "no-color"
  let term ← valueOf "term"
  let session ← valueOf "linger-session"
  let child ←
    withLaunchLock <|
        IO.Process.spawn
          { cmd, args,
            env :=
              #[("LINGER_SESSION", session), ("LINGER_NO_DETACH_KEY", none), ("NO_COLOR", noColor),
                ("TERM", term)],
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
      return (← Linger.Selector.Shell.run executable Linger.Session.Shell.Names.nameOf).code
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
  IO.FS.writeFile (root / "listing") (namesListing ["Alpha", "Beta", "Gamma"])
  IO.FS.writeFile (root / "listing-rc") "0"
  IO.FS.writeFile (root / "attach-rc") "7"
  IO.FS.writeFile (root / "term") "xterm-256color"
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

/-- Adjacent native listing attempts belong to one selection visit: keep the first,
which must query remote hosts, and drop the periodic local or remote ones after it.
Keep unexpected argv and every attach in order, without assuming how many periodic
attempts fit between unrelated keyboard actions. The raw trace stays on disk. -/
private def Fixture.visits (f : Fixture) : IO String := do
  let listing (record : String) :=
    [["ls", "-r", "--porcelain"], ["ls", "--porcelain"]].any fun args =>
      record == ((call args).dropEnd 1).toString
  let mut records : List String := []
  for record in lines (← f.calls) do
    unless listing record && records.getLast?.any listing do
      records := records ++ [record]
  return String.intercalate "\n" records ++ if records.isEmpty then "" else "\n"

private def Fixture.listing (f : Fixture) (text : String) (rc : Nat := 0) : IO Unit := do
  writeListing f.root text rc

/-- Give the launched command NO_COLOR and TERM as these say, each a value or unset. -/
private def Fixture.colorEnv (f : Fixture) (noColor term : Option String) : IO Unit := do
  for (file, value) in [("no-color", noColor), ("term", term)] do
    match value with
    | some value =>
      IO.FS.writeFile (f.root / file) value
    | none =>
      if ← (f.root / file).pathExists then
        IO.FS.removeFile (f.root / file)

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
  let rc ← waitChild child patienceMs
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
    (ms : Nat := patienceMs) : IO Bool := do
  let _ ←
    s.client.awaitText s.output (fun tail => ready tail || hasText tail "MANAGER-EXIT:") start ms
  let output ← s.output.get
  return ready (output.extract start output.size)

private def Session.untilAny (s : Session) (needles : List String) (start : Nat := 0)
    (ms : Nat := patienceMs) : IO Bool :=
  s.untilOutput (fun output => needles.any (hasText output)) start ms

private def Session.until (s : Session) (needle : String) (start : Nat := 0)
    (ms : Nat := patienceMs) : IO Bool := s.untilAny [needle] start ms

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

/-- Match rendered cells once this action has written something: inline emphasis may split a
target's bytes, and an earlier selected row must not satisfy a new wait. The cells are the
whole stream's, since a frame repaints only the rows that changed. -/
private def Session.untilScreen (s : Session) (ready : Vt → Bool) (start : Nat := 0)
    (ms : Nat := patienceMs) : IO Bool := do
  let (cols, rows) ← winsizeGet s.client.fd
  let shows := fun (output : ByteArray) =>
    output.size > start && ready ((Vt.init cols.toNat rows.toNat).feedBytes output)
  let _ ←
    Verify.Harness.waitFor ms do
        s.observe 20
        let output ← s.output.get
        return shows output || hasText (output.extract start output.size) "MANAGER-EXIT:"
  return shows (← s.output.get)

private def Session.untilRow (s : Session) (text : String) (start : Nat := 0) : IO Bool :=
  s.untilScreen (fun vt => (List.range vt.rowCount).any fun row => has (rowText vt row) text) start

/-- `waitFor` that keeps reading this terminal. A client blocked writing to it does
not read the keys a check waits on, as when an attach's replay exceeds the pty's
output buffer: about 1 KB on macOS, tens of KB on Linux. -/
private def Session.waitFor (s : Session) (ms : Nat) (p : IO Bool) : IO Bool :=
  Verify.Harness.waitFor ms do
    s.observe 20
    p

private def Session.send (s : Session) (bytes : ByteArray) : IO Unit := writeAll s.client.fd bytes

private def Session.text (s : Session) (text : String) : IO Unit := s.send text.toUTF8

private def Session.prompt (s : Session) (query : String := "") (start : Nat := 0) : IO Bool :=
  -- Normal actions need a loaded snapshot. The initial loading frame also has
  -- an editable prompt; the held-initial-list checks exercise that separately.
  s.untilScreen
    (fun vt =>
      let rows := (List.range vt.rowCount).map (rowText vt)
      rows.any
          (fun row =>
            if query.isEmpty then row.startsWith "  › Find" else row.startsWith s!"  › {query} ") &&
        rows.any fun row =>
          ["  ↵ attach", "  ↵ create", "  Type a valid name"].any fun help => row.startsWith help)
    start

/-- Require the selected marker, exact target prefix and reverse video.
Do not depend on where the renderer starts or resets inline styles. -/
private def Session.selected (s : Session) (label : String) (start : Nat := 0) : IO Bool :=
  s.untilScreen
    (fun vt =>
      (List.range vt.rowCount).any fun row =>
        let text := rowText vt row
        let col := if label.startsWith "+ Create " then 4 else 8
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

/-- Wait until session `name` in `owned` reports `count` attached clients. -/
private def clientsReach (owned : Env) (name count : String) (ms : Nat := patienceMs) : IO Bool :=
  waitFor ms do
    return (← withLaunchLock (owned.info name "clients")) == some count

private def withSession (f : Fixture) (args : Array String) (body : Session → IO Bool)
    (mode : String := "both") (cols : UInt32 := 80) (rows : UInt32 := 12) : IO Bool := do
  let s ← f.start args mode cols rows
  try
    body s
  finally
    s.retire

/-- `withSession` from the first loaded prompt; a session that never shows one fails. -/
private def withPrompt (f : Fixture) (args : Array String) (body : Session → IO Bool)
    (mode : String := "both") (cols : UInt32 := 80) (rows : UInt32 := 12) : IO Bool :=
  withSession f args
    (fun s => do
      unless ← s.prompt do
        return false
      body s)
    mode cols rows

/-- The last `n` bytes on one line: printable ASCII as is, every other byte as `\xNN`. -/
private def escapedTail (bytes : ByteArray) (n : Nat) : String :=
  (bytes.extract (bytes.size - n) bytes.size).foldl
    (fun text byte =>
      if 0x20 ≤ byte && byte < 0x7F then text.push (Char.ofNat byte.toNat)
      else
        let hex := Nat.toDigits 16 byte.toNat
        text ++ "\\x" ++ String.ofList (if hex.length < 2 then '0' :: hex else hex))
    ""

/-- A failed check's evidence, for logs read where the suite cannot be rerun:
every `*-observation` file in its fixture, then the end of its terminal output. -/
private def explain (root : System.FilePath) (slug : String) : IO Unit := do
  if !(← root.isDir) then
    return
  let observations := (← root.readDir).filter (·.fileName.endsWith "-observation")
  for entry in observations.qsort (·.fileName < ·.fileName) do
    for line in lines (← readText entry.path) do
      IO.println s!"note: manager {slug}: {entry.fileName}: {line}"
  if ← (root / "terminal.bin").pathExists then
    let tail := escapedTail (← IO.FS.readBinFile (root / "terminal.bin")) 1200
    IO.println s!"note: manager {slug}: terminal tail: {tail}"

private def check (e : Env) (slug label : String) (body : Fixture → IO Bool) : IO Unit := do
  let ok ←
    try
      body (← Fixture.make e slug)
    catch err =>
      IO.println s!"note: manager {slug}: {err}"
      pure false
  unless ok do
    explain (System.FilePath.mk e.dir / slug) slug
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
  let ok := result == some rc && !before.isEmpty && before == after
  unless ok do
    IO.eprintln s!"manager: exit {result} (want {rc}); termios before '{before}', after '{after}'"
  return ok

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

/-- The next prompt must follow this attach, with an empty query and `target` selected: the row
attached to when the new snapshot lists it, else its first row. An earlier prompt cannot satisfy
the wait. -/
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
  -- rows no visit lists before an attach, so the return enters with them alone, the first
  -- selected
  s.fixture.afterAttach (namesListing ["Fresh", "Later"])
  s.text keys
  unless ← returned s "Fresh" do
    return false
  s.text "\x03"
  let clean ← restored s 130 visits
  return clean && (← beforeAttach s 1 (visits - 1)) && (← attachNormal s.fixture)

private def usageChecks (e : Env) : IO Unit := do
  check e "help"
      "linger --help lists each operation's one command on one line, in table order, then its options, every status and exit code"
      fun f => do
      let (rc, out, err) ← f.piped #[Linger.App.Commands.helpOption]
      IO.FS.writeFile (f.root / "help.txt") out
      let lines := (out.dropEnd 1).toString.splitOn "\n"
      let rows := lines.takeWhile (· != "")
      let footer := lines.dropWhile (· != "")
      return rc == 0 && err.isEmpty && out.endsWith "\n" && rows == Linger.App.Commands.helpLines &&
          rows.map (fun line => (line.splitOn " ").headD "") ==
            Linger.App.Commands.table.map (·.word) &&
          Linger.App.Commands.table.map (·.op) == Linger.App.Commands.Op.all &&
          rows.all
            (fun line =>
              line == line.trimAscii.toString &&
                ((line.splitOn "  ").filter (!·.isEmpty)).length ≥ 2) &&
          footer.any
            (fun line =>
              has line Linger.App.Commands.helpOption &&
                has line Linger.App.Commands.versionOption) &&
          Linger.Display.Status.legend.all
            (fun line =>
              footer.contains
                (if line == "Attention" || line == "State" then line else "  " ++ line)) &&
          footer.any
            (fun line =>
              has line
                ("count " ++
                  String.intercalate " "
                    (Linger.Display.Status.counted.map
                      (String.singleton ∘ Linger.Display.Status.mark)))) &&
          Linger.Os.Answer.legend.all (fun line => footer.contains ("  " ++ line)) &&
          has out "--summary" &&
          has out "--read-only" &&
          has out "--history" &&
          !has out "--remote" &&
          !has out "linger import [SAVE]" &&
          !has out "--loop" &&
          !has out "--restore-processes" &&
          !has out "lz"
  check e "version" "linger --version prints the version and the state paths, and nothing else does"
      fun f => do
      let (rc, out, err) ← f.piped #[Linger.App.Commands.versionOption]
      let (extraRc, _, _) ← f.piped #[Linger.App.Commands.versionOption, "extra"]
      return rc == 0 && err.isEmpty && has out s!"linger {Terminal.Mediation.versionNumber}" &&
          has out "sockets: " &&
          has out "state: " &&
          extraRc == 2
  check e "removed"
      "a word no command has, a removed one's included, gets the ordinary usage error and says nothing of what it was"
      fun f => do
      let (_, _, unknown) ← f.piped #["no-such-word"]
      let mut ok := !unknown.isEmpty
      for word in
        ["run", "r", "a", "list", "l", "s", "d", "k", "c", "w", "info", "i", "get", "g", "set",
          "unset", "un", "clear", "cl", "help", "h", "-h", "version", "v", "tmux"] do
        for args in [#[word], #[word, "work"]] do
          let (rc, out, err) ← f.piped args
          appendText (f.root / "removed-observation") s!"{repr args}: {rc} {repr err}\n"
          ok :=
            ok && rc == 2 && out.isEmpty && err == unknown && !has err "removed" &&
              (Linger.App.Commands.lookup word).isNone
      return ok
  check e "ls-named"
      "ls with names lists only those sessions, in the order named, as their porcelain records, a name with only an end record as its ending, and answers notFound for a name no session took"
      fun f => do
      let (oneRc, _, _) ←
        f.piped
            #["start", "named-one", "/bin/sh", "-c",
              "printf '\\033]2;first one\\007'; exec /bin/cat"]
      let (twoRc, _, _) ← f.piped #["start", "named-two", "/bin/cat"]
      let titled ←
        waitFor patienceMs do
            return has (← f.piped #["ls", "named-one", "--porcelain"]).2.1 "\"title\":\"first one\""
      let (rc, out, err) ← f.piped #["ls", "named-two", "named-one", "--porcelain"]
      let (allRc, all, _) ← f.piped #["ls", "--porcelain"]
      let (humanRc, human, _) ← f.piped #["ls", "named-one"]
      let (missingRc, missingOut, missingErr) ← f.piped #["ls", "--porcelain", "named-missing"]
      IO.FS.writeFile (f.root / "named-observation") s!"{rc} {repr out} {repr err}\n{repr human}\n"
      let blocks := listingRecords
      let named := blocks out
      let field := fun (row : List (String × String)) (key : String) => row.lookup key
      let listed := blocks all
      let rowOf := fun (name : String) => listed.find? (field · "name" == some name)
      -- each named record holds its row of the full listing's identity and liveness
      let same := fun (row : List (String × String)) =>
        match field row "name" >>= rowOf with
        | some full =>
          ["name", "pid", "cmd", "state", "start_dir"].all
            (fun key => field row key == field full key)
        | none => false
      let (killRc, _, _) ← f.piped #["kill", "named-one"]
      let (endedRc, ended, _) ← f.piped #["ls", "named-one", "--porcelain"]
      let (twoKilled, _, _) ← f.piped #["kill", "named-two"]
      let endedRow := records ended
      return oneRc == 0 && twoRc == 0 && titled && rc == 0 && allRc == 0 && err.isEmpty &&
          named.map (field · "name") == [some "named-two", some "named-one"] &&
          named.all same &&
          named.all (field · "state" == some "live") &&
          field (named.getD 0 []) "cmd" == some "/bin/cat" &&
          (field (named.getD 1 []) "cmd").any (·.startsWith "/bin/sh") &&
          field (named.getD 1 []) "title" == some "first one" &&
          (field (named.getD 0 []) "title").isNone &&
          humanRc == 0 &&
          has human "named-one" &&
          has human "first one" &&
          !has human "named-two" &&
          missingRc == 127 &&
          missingOut.isEmpty &&
          has missingErr "no session 'named-missing'" &&
          killRc == 0 &&
          twoKilled == 0 &&
          endedRc == 0 &&
          (listingRecords ended).length == 1 &&
          endedRow.lookup "name" == some "named-one" &&
          (endedRow.lookup "exit").isSome
  check e "usage" "linger rejects unknown commands and conflicting listing options" fun f => do
      let mut ok := true
      for args in
        [#["work"], #["--unknown"], #["--help", "extra"], #["-h", "extra"], #["help", "extra"],
          #["--porcelain"], #["-r"], #["--summary", "work"], #["ls", "--remote"],
          #["ls", "--remote", "host"], #["ls", "work", "-r"], #["ls", "-r", "host", "work"],
          #["ls", "--summary", "work"], #["ls", "work", "--summary"], #["ls", "--unknown"],
          #["select"], #["status"], #["--summary"], #["watch", "work"], #["history", "work"],
          #["hi", "work"], #["run", "work", "true"], #["r", "work"], #["attach", "--unknown"],
          #["attach", "--"], #["attach", "--read-only", "work", "/bin/sh"],
          #["capture", "--unknown"], #["capture", "--"], #["capture", "--history"],
          #["capture", "--history", "work", "extra"], #["capture", "work", "--history"],
          #["ls", "--summary", "--porcelain"], #["ls", "--porcelain", "--summary"],
          #["ls", "--summary", "-r"], #["ls", "-r", "--summary"], #["ls", "--summary", "extra"],
          #["select", ""], #["select", "work"], #["select", "--help"], #["select", "-h"],
          #["select", "one", "two"], #["--loop", ""], #["--loop", "one", "two"],
          #["import-resurrect"], #["import", ""], #["import", "--unknown"], #["import", "--help"],
          #["import", "-h"], #["import", "-save"], #["import", "one", "two"], #["import"],
          #["export", "save"], #["tmux", "select", ""], #["tmux", "select", "-save"],
          #["tmux", "select", "one", "two"], #["tmux", "select", "--unknown"], #["tmux"],
          #["tmux", "ls"], #["tmux", "export", "save"], #["ls", "--resurrect", "extra"],
          #["ls", "--resurrect", "--porcelain"], #["ls", "--porcelain", "--resurrect"],
          #["ls", "work", "--resurrect"]] do
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
      IO.FS.writeFile save
          (Linger.Import.Suites.Recipes.paneLine "work" "1" "0" f.root.toString "vim")
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
      let (helpRc, expected, helpErr) ← f.piped #[Linger.App.Commands.helpOption]
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
        let (helpRc, expected, helpErr) ← f.piped #[Linger.App.Commands.helpOption]
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
      let (helpRc, expected, helpErr) ← f.piped #[Linger.App.Commands.helpOption]
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
      withPrompt f #["attach"] fun s => do
          unless ← s.typeQuery "-invalid name" "-invalid name" do
            return false
          s.text "\r"
          s.observe 350
          let waiting := !(← (f.root / "result").pathExists)
          let noSession := (← state.readDir).isEmpty
          s.text "\x03"
          return waiting && noSession && (← restored s 130)

private def failureChecks (e : Env) : IO Unit := do
  for (slug, listing) in [("empty", ""), ("partial", (namesListing ["Alpha"]))] do
    check e s!"listing-{slug}"
        s!"picker probe preserves initial listing failure status and reports it after restoration ({slug})"
        fun f => do
        f.listing listing 7
        withSession f.picker #[] fun s => do
            let clean ← failureRestored s 7 "linger: could not list sessions (exit 7)"
            return clean && (← f.visits) == listed && !hasText (← s.output.get) "Alpha"
  let invalid :=
    [("empty-name", namesListing [""]), ("null-field", "{\"name\":null}\n"),
      ("extra-field", "{\"extra\":[],\"name\":\"bad\"}\n"), ("duplicate", namesListing ["Alpha"]),
      ("cr", namesListing ["bad\r"]), ("escape", namesListing ["bad\x1b[2J"]),
      ("nul", namesListing ["bad\x00name"]), ("spaced", "{\"name\": \"bad\"}\n"),
      ("unsorted", "{\"pid\":\"1\",\"name\":\"bad\"}\n"), ("crlf", "{\"name\":\"bad\"}\r\n")]
  for (slug, bad) in invalid do
    check e s!"bad-{slug}" s!"picker probe rejects the whole malformed listing ({slug})" fun f => do
        f.listing (namesListing ["Alpha"] ++ bad)
        withSession f.picker #[] fun s => do
            let clean ← failureRestored s 1 "picker probe:"
            return clean && (← f.visits) == listed && !hasText (← s.output.get) "Alpha"
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
      withPrompt f.picker #[] fun s => do
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
        return clean && modesRestored (out.extract 0 position) 1 && (← f.visits) == listed
  check e "readonly-output"
      "picker probe restores termios when opening and closing screen writes both fail" fun f =>
      withSession f.picker #[]
        (fun s => do
          let clean ← failureRestored s 1 "picker probe:"
          let visits ← f.visits
          return clean && (visits.isEmpty || visits == listed) &&
              !hasBytes (← s.output.get) (modeSet 1049 true))
        "readonly-output"

private def selectionChecks (e : Env) : IO Unit := do
  for (slug, target) in
    [("remote", "work@me@dev-a"), ("leading", "-leading+name"),
      ("shell-text", "work@host with 'spaces' $TERM")] do
    check e s!"exact-{slug}"
        s!"picker probe attaches the original target as one argument ({target})" fun f => do
        f.listing (namesListing [target])
        withPrompt f.picker #[] fun s => do
            let shown ← s.until target
            let clean ← acceptThenCancel s
            return shown && clean && (← f.visits) == attachVisit [target]
  let moves :=
    [("down", "\x1b[B", "Beta"), ("up", "\x1b[B\x1b[B\x1b[A", "Beta"), ("ctrl-n", "\x0e", "Beta"),
      ("ctrl-p", "\x0e\x0e\x10", "Beta"), ("end", "\x1b[F", "main"),
      ("home", "\x1b[F\x1b[H", "Alpha")]
  for (slug, keys, target) in moves do
    check e slug s!"picker probe navigation selects the expected row ({slug})" fun f =>
        withPrompt f.picker #[] fun s => do
          return (← acceptThenCancel s (keys ++ "\r")) && (← f.visits) == attachVisit [target]
  -- the moves cycle, as fzf's do with `--cycle`, by every key bound to a move of one row: up from
  -- the first row selects the last, here the creation row, and down from it the first
  for (slug, up, down) in
    [("cycle-arrows", "\x1b[A", "\x1b[B"), ("cycle-ctrl", "\x10", "\x0e"),
      ("cycle-tab", "\x10", "\t")] do
    check e slug
        s!"picker probe up from the first row selects the last, and down from the last the first ({slug})"
        fun f =>
        withPrompt f.picker #[] fun s => do
          let start ← s.mark
          s.text up
          unless ← s.selected "+ Create main" start do
            return false
          let next ← s.mark
          s.text down
          unless ← s.selected "Alpha" next do
            return false
          return (← acceptThenCancel s) && (← f.visits) == attachVisit ["Alpha"]
  check e "keystroke-rows"
      "picker probe repaints only the rows a move changes, in place, and clears nothing" fun f =>
      withPrompt f.picker #[] fun s => do
        s.observe 150
        let (cols, _) ← winsizeGet s.client.fd
        let mut sizes : List Nat := []
        let mut cleared := false
        for keys in ["\x1b[B", "\x1b[B", "\x1b[A"] do
          let start ← s.mark
          s.text keys
          let _ ← s.untilOutput (fun written => !written.isEmpty) start
          s.observe 150
          let out ← s.output.get
          let written := out.extract start out.size
          sizes := sizes ++ [written.size]
          cleared := cleared || hasBytes written (csiNum 2 0x4A)
        appendText (f.root / "keystroke-observation")
            s!"bytes per keystroke {sizes}, cleared {cleared}, columns {cols}\n"
        -- two rows change: the one the highlight leaves and the one it reaches
        let near := sizes.all fun n => 0 < n && n ≤ 2 * (cols.toNat + 48)
        let moved ← s.selected "Beta"
        return !cleared && near && moved && (← acceptThenCancel s) &&
            (← f.visits) == attachVisit ["Beta"]
  check e "subsequence" "picker probe filtering is case-insensitive, subsequence-based and stable"
      fun f => do
      f.listing (namesListing ["Prefix", "Work", "weak"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "WK" "WK" do
            return false
          return (← acceptThenCancel s "\x0e\r") && (← f.visits) == attachVisit ["weak"]
  for (slug, erase) in [("del", "\x7f"), ("backspace", "\x08")] do
    check e slug s!"picker probe query deletion works ({slug})" fun f =>
        withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "Bx" "Bx" do
            return false
          unless ← s.typeQuery erase "B" do
            return false
          return (← acceptThenCancel s) && (← f.visits) == attachVisit ["Beta"]
  check e "clear" "picker probe Ctrl-U clears the whole query" fun f =>
      withPrompt f.picker #[] fun s => do
        unless ← s.typeQuery "unmatched" "unmatched" do
          return false
        unless ← s.typeQuery "\x15Gamma" "Gamma" do
          return false
        return (← acceptThenCancel s) && (← f.visits) == attachVisit ["Gamma"]
  for (slug, listing, query, target) in
    [("no-match", (namesListing ["Alpha"]), "new-session", "new-session"),
      ("empty-list", "", "", "main"), ("create-leading", "", "-leading+name", "-leading+name"),
      ("create-remote", "", "work@me@dev-a", "work@me@dev-a"),
      ("create-shell-text", "", "work@host with 'spaces' $TERM", "work@host with 'spaces' $TERM"),
      ("create-unicode-host", "", "work@界é", "work@界é"),
      ("create-max-name", "", String.ofList (List.replicate Linger.Target.Name.maxLen 'n'),
        String.ofList (List.replicate Linger.Target.Name.maxLen 'n'))] do
    check e slug
        s!"picker probe visibly creates the exact target through a restored attach child ({slug})"
        fun f => do
        f.listing listing
        withPrompt f.picker #[]
            (fun s => do
              let start ← s.mark
              if !query.isEmpty then
                unless ← s.typeQuery query query do
                  return false
              let shown ← s.selected s!"+ Create {target}" (if query.isEmpty then 0 else start)
              let clean ← acceptThenCancel s
              return shown && clean && (← f.visits) == attachVisit [target])
            "both" (UInt32.ofNat (Linger.Target.Name.maxLen + 40)) 12
  for create in [false, true] do
    let slug := if create then "prefix-create" else "prefix-existing"
    check e slug
        s!"picker probe lists existing prefix matches first and attaches only the highlighted row ({slug})"
        fun f => do
        f.listing (namesListing ["workshop", "workbench", "Other"])
        withPrompt f.picker #[] fun s => do
            unless ← s.typeQuery "work" "work" do
              return false
            s.observe 100
            let vt := (Vt.init 80 12).feedBytes (← s.output.get)
            let orderedRows :=
              rowText vt 4 == "  ▸   ? workshop  (busy)" &&
                rowText vt 5 == "      ? workbench (busy)" &&
                rowText vt 6 == "    + Create work"
            if create then
              let next ← s.mark
              s.text "\x1b[F"
              unless ← s.selected "+ Create work" next do
                return false
            s.observe 200
            let noAttach := (← f.visits) == listed
            let target := if create then "work" else "workshop"
            let clean ← acceptThenCancel s
            return orderedRows && noAttach && clean && (← f.visits) == attachVisit [target]
  for (slug, listing, query, absent, target) in
    [("exact-suppression", (namesListing ["Alpha", "Alphabet"]), "Alpha", "Alpha", "Alphabet"),
      ("default-suppression", (namesListing ["main", "Other"]), "", "main", "Other")] do
    check e slug s!"picker probe suppresses creation for exact snapshot members ({slug})" fun f =>
        do
        f.listing listing
        withPrompt f.picker #[] fun s => do
            if !query.isEmpty then
              unless ← s.typeQuery query query do
                return false
            s.observe 150
            let output ← s.output.get
            let screen := ByteArray.mk (screenText ((Vt.init 80 12).feedBytes output)).toArray
            let suppressed := !hasText screen s!"Create {absent}"
            let clean ← acceptThenCancel s "\x1b[F\r"
            return suppressed && clean && (← f.visits) == attachVisit [target]
  check e "case-distinct"
      "picker probe permits explicit case-distinct creation beside a folded existing match" fun f =>
      do
      f.listing (namesListing ["Alpha"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "alpha" "alpha" do
            return false
          s.observe 100
          let vt := (Vt.init 80 12).feedBytes (← s.output.get)
          let shown :=
            rowText vt 4 == "  ▸   ? Alpha (busy)" && rowText vt 5 == "    + Create alpha"
          let clean ← acceptThenCancel s "\x1b[F\r"
          return shown && clean && (← f.visits) == attachVisit ["alpha"]
  check e "edit-create"
      "picker probe editing a highlighted creation row resets to the first existing match" fun f =>
      withPrompt f.picker #[] fun s => do
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
        let noAttach := (← f.visits) == listed
        let clean ← acceptThenCancel s
        return reset && noAttach && clean && (← f.visits) == attachVisit ["Alpha"]
  -- more bytes than a name may take, in fewer columns than a terminal's width
  let overlong := String.ofList (List.replicate (Linger.Target.Name.maxBytes / 3 + 1) '€')
  -- every clean text is a name, and a key an older linger kept; these are neither
  for (slug, query) in
    [("leading-option", "-a b"), ("blank", "   "), ("option-unicode", "-界 x"),
      ("blank-remote", "   @host"), ("empty-host", "work@"), ("empty-local", "@host"),
      ("overlong", overlong), ("overlong-remote", overlong ++ "@host")] do
    check e s!"invalid-create-{slug}"
        s!"picker probe invalid creation has no row, ignores Enter and remains editable ({slug})"
        fun f =>
        withPrompt f.picker #[]
          (fun s => do
            unless ← s.typeQuery query query do
              return false
            s.text "\r"
            s.observe 350
            let output ← s.output.get
            let vt := (Vt.init 80 12).feedBytes output
            let noChoice := !hasText (ByteArray.mk (screenText vt).toArray) "Create "
            let waiting := !(← (f.root / "result").pathExists)
            let noAttach := (← f.visits) == listed
            unless ← s.typeQuery "\x15Beta" "Beta" do
              return false
            let clean ← acceptThenCancel s
            return noChoice && waiting && noAttach && clean && (← f.visits) == attachVisit ["Beta"])
          "both" (UInt32.ofNat (Linger.Target.Name.maxLen + 40)) 12

private def inputChecks (e : Env) : IO Unit := do
  -- Ctrl-D ends the input only once the query is empty, as on a line editor's empty line
  for (slug, key) in [("ctrl-c", "\x03"), ("ctrl-d", "\x15\x04"), ("escape", "\x1b")] do
    check e slug s!"picker probe cancellation restores termios and display modes ({slug})" fun f =>
        withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "new-session" "new-session" do
            return false
          s.text key
          return (← restored s 130) && (← f.visits) == listed
  check e "ctrl-d-query"
      "picker Ctrl-D after a query deletes nothing and keeps the chooser open with its query and highlight, unrepainted"
      fun f => do
      f.listing (namesListing ["Beta", "Bravo"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "B" "B" do
            return false
          let selection ← s.mark
          s.text "\x0e"
          unless ← s.selected "Bravo" selection do
            return false
          s.observe 100
          let start ← s.mark
          s.text "\x04"
          s.observe 400
          let quiet := (← s.mark) == start
          let waiting := !(← (f.root / "result").pathExists)
          let vt := (Vt.init 80 12).feedBytes (← s.output.get)
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          IO.FS.writeFile (f.root / "ctrl-d-observation") s!"quiet={quiet}\nwaiting={waiting}\n"
          s.text "\x03"
          return quiet && waiting && has screen "  › B 2" && has screen "  ▸   ? Bravo" &&
              (← restored s 130) &&
              (← f.visits) == listed
  -- a signal that ends the picker leaves it as a cancellation does, and its answer says which
  -- signal: 128 plus its number, the status a shell reports for a program that signal ended
  for (slug, sig) in [("sigterm", (15 : UInt32)), ("sighup", 1), ("sigint", 2)] do
    check e slug
        s!"a signal to the picker restores termios and display modes and answers {128 + sig} \
          ({slug})"
        fun f =>
        withPrompt f.picker #[] fun s => do
          let pid ← numberFile (f.root / "manager-pid")
          if pid == 0 then
            return false
          kill (UInt32.ofNat pid) sig
          return ← restored s (128 + sig.toNat)
  check e "split-arrow" "picker probe decodes an arrow split between reads" fun f =>
      withPrompt f.picker #[] fun s => do
        s.text "\x1b["
        s.observe 50
        return (← acceptThenCancel s "B\r") && (← f.visits) == attachVisit ["Beta"]
  check e "split-utf8" "picker probe retains split UTF-8 query characters" fun f => do
      let target := "work@界é"
      f.listing (namesListing ["other", target])
      withPrompt f.picker #[] fun s => do
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
          return (← acceptThenCancel s) && (← f.visits) == attachVisit [target]
  check e "paste"
      "picker probe paste survives idle, suppresses newlines and handles a split end marker"
      fun f => do
      f.listing (namesListing ["alphabeta", "other"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "\x1b[200~alpha" "alpha" do
            return false
          s.observe 350
          unless ← s.typeQuery "\r\nbeta" "alphabeta" do
            return false
          s.observe 200
          let waiting := !(← (f.root / "result").pathExists)
          let noAttach := (← f.visits) == listed
          s.text "\x1b[20"
          s.observe 50
          s.text "1~"
          unless ← s.typeQuery "\x15BETA" "BETA" do
            return false
          return waiting && noAttach && (← acceptThenCancel s) &&
              (← f.visits) == attachVisit ["alphabeta"]
  check e "invalid-control-paste"
      "picker probe pasted controls cannot create, refresh or cancel an invalid query" fun f =>
      withPrompt f.picker #[] fun s => do
        let start ← s.mark
        unless ← s.typeQuery "-bad " "-bad " do
          return false
        s.text "\x1b[200~\x00\x07\x7f\u0085\r\n\x03\x04\x0c\x12\x1b[201~"
        s.observe 350
        s.text "\r"
        s.observe 350
        let output ← s.output.get
        let frame := output.extract start output.size
        let screen := ByteArray.mk (screenText ((Vt.init 80 12).feedBytes output)).toArray
        let ignored := !hasText screen "Create " && !hasText frame "\u0085"
        let waiting := !(← (f.root / "result").pathExists)
        let noCommand := (← f.visits) == listed
        unless ← s.typeQuery "\x15Beta" "Beta" do
          return false
        let clean ← acceptThenCancel s
        return ignored && waiting && noCommand && clean && (← f.visits) == attachVisit ["Beta"]

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
  -- NO_COLOR and TERM as the picker reads them, and whether its badges have color: an empty
  -- NO_COLOR asks for nothing, and an unset, empty or `dumb` TERM names no terminal that takes it
  let xterm := some "xterm-256color"
  for (slug, noColor, term, colored) in
    [("status-colors", none, xterm, true), ("status-no-color-empty", some "", xterm, true),
      ("status-no-color-set", some "1", xterm, false),
      ("status-term-dumb", none, some "dumb", false), ("status-term-unset", none, none, false),
      ("status-term-empty", none, some "", false)] do
    check e slug
        s!"picker shares listing rows and keeps match underline independent of selection and status ({slug})"
        fun f => do
        let statuses : List Linger.Display.Status.Status :=
          [⟨.asked, .working⟩, ⟨.none, .working⟩, ⟨.unread, .idle⟩, ⟨.unread, .exitedOk⟩,
            ⟨.unread, .exitedBad⟩, ⟨.none, .idle⟩, ⟨.none, .resumable⟩, ⟨.none, .unknown⟩,
            ⟨.none, .errored⟩, ⟨.none, .paused⟩]
        let fields :=
          statuses.zipIdx |>.map fun (status, index) =>
            [("name", s!"case{index}")] ++ Linger.Display.Listing.statusFields status ++
              [("cmd", "editor"), ("pid", "123"), ("label.project", "demo"), ("clients", "2")]
        f.listing (jsonListing fields)
        f.colorEnv noColor term
        -- the picker lists them as `ls` does, what has something for you first (`View.sort`),
        -- each with its state badge's color and dimness, and its mark's
        let expectedColors : List Terminal.Vt.Color :=
          [.idx 6, .idx 6, .default, .idx 2, .idx 1, .default, .default, .idx 3, .idx 1, .default]
        let shown :=
          Linger.Display.View.sort (fun (_, status, _) => status)
            ((fields.zip statuses).zip expectedColors |>.map fun ((info, status), color) =>
              (info, status, color))
        withPrompt f.picker #[]
            (fun s => do
              let vt ← s.capture slug 100 20
              let rowsMatch := fun (frame : Vt) =>
                shown.zipIdx |>.all fun ((info, status, color), index) =>
                  let marked := frame.getCell 4 (4 + index)
                  let badge := frame.getCell 6 (4 + index)
                  let name := frame.getCell 8 (4 + index)
                  let expected :=
                    String.fromUTF8!
                      (ByteArray.mk
                        (Linger.Display.Listing.humanRow (Linger.Display.Listing.layoutOf fields)
                            info).toArray)
                  rowText frame (4 + index) ==
                      (if index == 0 then "  ▸ " else "    ") ++ expected &&
                    badge.pen.fg == (if colored then color else .default) &&
                    badge.pen.dim ==
                      (colored &&
                        (status.state == .idle || status.state == .paused ||
                          status.state == .resumable)) &&
                    marked.pen.fg ==
                      (if colored && status.attention != .none then .idx 3 else .default) &&
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
                    if 4 ≤ row && row < 4 + fields.length then [8, 9] else []
              IO.FS.writeFile (f.root / "match-observation")
                  s!"plain-rows={rowsMatch vt}\nempty-query-unmarked={plain}\nmatched-rows={rowsMatch matched}\nunderlined-columns={repr ((List.range matched.rowCount).map (underlined matched))}\nexpected-session-columns=[8, 9]\n"
              let output ← s.output.get
              let onlyAnsi := !hasText output "[38;" && !hasText output "[48;"
              s.text "\x03"
              let clean ← restored s 130
              return rowsMatch vt && plain && rowsMatch matched && emphasis && onlyAnsi && clean &&
                  hasBytes output (Terminal.Title.ansi "linger") &&
                  hasBytes (← s.output.get) (Terminal.Title.ansi ""))
            "both" 100 20
  check e "status-metadata-refresh"
      "picker redraws changed metadata with unchanged names and preserves query, target and all details"
      fun f => do
      f.listing
          (jsonListing
            [[("name", "beta"), ("status", "working"), ("cmd", "other")],
              [("name", "alpha"), ("status", "idle"), ("cmd", "sh"), ("pid", "1"), ("fg", "old"),
                ("fgpid", "7"), ("description", "before"), ("clients", "1")]])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "a" "a" do
            return false
          let before ← s.capture "metadata-before"
          let start ← s.mark
          f.listing
              (jsonListing
                [[("name", "beta"), ("status", "working"), ("cmd", "other")],
                  [("name", "alpha"), ("status", "exited-bad"), ("cmd", "sh"), ("pid", "2"),
                    ("fg", "new"), ("fgpid", "8"), ("description", "after"), ("clients", "3")]])
          unless ← s.until "after   new" start do
            return false
          let after ← s.capture "metadata-after"
          -- beta, listed first, shares its place with the quiet alpha; alpha now asks for
          -- someone but keeps its row while the chooser is open, and the cursor stays on beta;
          -- each field keeps its column, beta's empty caption included
          let changed :=
            rowText before 4 == "  ▸   ⣷ beta          other" &&
              rowText before 5 == "      ⣀ alpha before  old    +1" &&
              rowText after 4 == "  ▸   ⣷ beta          other" &&
              rowText after 5 == "      ✗ alpha after   new    +3" &&
              rowText after 2 == "  › a 2" &&
              (after.getCell 6 5).pen.fg == .idx 1 &&
              (after.getCell 8 4).pen.reverse
          return changed && (← acceptThenCancel s) && (← f.visits) == attachVisit ["beta"]
  check e "status-control-text"
      "picker keeps hostile metadata out of terminal controls while retaining ordinary details"
      fun f => do
      f.listing
          (jsonListing
            [[("name", "alpha"), ("status", "working"), ("cmd", "vi\x1b[31m\u009b31m"),
                ("description", "ok\x07"), ("clients", "2")],
              [("name", "beta")]])
      withPrompt f.picker #[] fun s => do
          let vt ← s.capture "metadata-controls"
          -- beta reports no status, so linger could not read it, and it comes after the running alpha
          let row := rowText vt 4
          let output ← s.output.get
          let safe :=
            has row "vi�[31m�31m" && has row "ok�" && !hasText output "\u009b" &&
              !hasText output "vi\x1b" &&
              (vt.getCell 8 4).pen.fg == .default &&
              rowText vt 5 == "      ? beta  (busy)"
          s.text "\x03"
          return safe && (← restored s 130)

private def fuzzyChecks (e : Env) : IO Unit := do
  check e "fuzzy-optimal"
      "picker highlights the best competing alignment only in the exact target and clears it with the query"
      fun f => do
      let fields :=
        [("name", "axab"), ("status", "idle"), ("attention", "unread"), ("cmd", "ab"),
          ("pid", "123"), ("label.project", "ab"), ("clients", "2")]
      f.listing (jsonListing [fields])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "AB" "AB" do
            return false
          let matched ← s.capture "competing-match"
          let expected :=
            "  ▸ " ++
              String.fromUTF8!
                (ByteArray.mk
                  (Linger.Display.Listing.humanRow (Linger.Display.Listing.layoutOf [fields])
                      fields).toArray)
          -- The later adjacent pair beats the earliest subsequence.
          -- Matching metadata and the explicit create label stay plain.
          let positions :=
            (List.range matched.rowCount).all fun row =>
              underlined matched row == if row == 4 then [10, 11] else []
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
      f.listing (namesListing targets)
      withPrompt f.picker #[] fun s => do
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
                      (Linger.Display.Listing.humanRow (Linger.Display.Listing.layoutOf fields)
                          info).toArray)
          let start ← s.mark
          s.text "\x0e"
          unless ← s.selected "axab" start do
            return false
          let clean ← acceptThenCancel s
          return ordered && clean && (← f.visits) == attachVisit ["axab"]
  check e "fuzzy-unicode"
      "picker highlights accent-only and wide matches, clips whole cells, and attaches the untruncated target"
      fun f => do
      let target := "work@e\u0301界éZ"
      f.listing (namesListing [target])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "界é" "界é" do
            return false
          let wide ← s.capture "wide-match"
          let scalarPositions :=
            underlined wide 4 == [14, 15, 16] && (wide.getCell 13 4).base == 'e' &&
              (wide.getCell 13 4).marks == ['\u0301'] &&
              (wide.getCell 14 4).base == '界' &&
              (wide.getCell 14 4).width == 2 &&
              (wide.getCell 15 4).width == 0 &&
              (wide.getCell 16 4).base == 'é' &&
              (wide.getCell 17 4).base == 'Z'
          unless ← s.typeQuery "\x15\u0301" "\u0301" do
            return false
          let accent ← s.capture "accent-only-match"
          -- A matched mark must emphasize its containing cell even when
          -- the base scalar itself does not match the query.
          let accentVisible :=
            rowText accent 4 == rowText wide 4 && (accent.getCell 13 4).base == 'e' &&
              (accent.getCell 13 4).marks == ['\u0301'] &&
              (List.range accent.rowCount).all fun row =>
                underlined accent row == if row == 4 then [13] else []
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
            underlined combining 4 == [13, 14, 15] && (combining.getCell 13 4).marks == ['\u0301']
          let start ← s.mark
          s.client.resize 16 4
          unless ← s.untilRow "  ▸   ? work@e\u0301" start do
            return false
          let clipped ← s.capture "clipped-wide-match" 16 4
          let narrow :=
            rowText clipped 1 == "  ▸   ? work@e\u0301" && underlined clipped 1 == [13] &&
              (clipped.getCell 13 1).marks == ['\u0301'] &&
              (clipped.getCell 14 1).base == ' ' &&
              (clipped.getCell 14 1).width == 1 &&
              lastColumnBlank clipped
          unless ← s.typeQuery "\x15\u0301" "\u0301" do
            return false
          let accentClipped ← s.capture "accent-only-clipped" 16 4
          let accentNarrow :=
            rowText accentClipped 1 == rowText clipped 1 &&
              accentClipped.getCell 13 1 == clipped.getCell 13 1 &&
              (List.range accentClipped.rowCount).all
                (fun row => underlined accentClipped row == if row == 1 then [13] else []) &&
              lastColumnBlank accentClipped
          unless ← s.typeQuery "\x15e\u0301界" "e\u0301界" do
            return false
          let start ← s.mark
          s.client.resize 18 4
          unless ← s.untilRow "  ▸   ? work@e\u0301界é" start do
            return false
          let fitted ← s.capture "fitted-wide-match" 18 4
          let fits :=
            rowText fitted 1 == "  ▸   ? work@e\u0301界é" && underlined fitted 1 == [13, 14, 15] &&
              (fitted.getCell 14 1).width == 2 &&
              (fitted.getCell 15 1).width == 0 &&
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
              (← f.visits) == attachVisit [target]

private def displayChecks (e : Env) : IO Unit := do
  check e "normal-frame"
      "picker normal frame has the spaced title, dim placeholder, exact rows and the keys' help, Ctrl-L's included"
      fun f =>
      withPrompt f.picker #[] fun s => do
        let vt ← s.capture "normal-frame"
        let footer := (List.range vt.rowCount).find? fun row => has (rowText vt row) "↵ attach"
        let layout :=
          (rowText vt 0).trimAscii.toString ==
              String.intercalate " · "
                (Linger.Display.View.headerParts [] [default, default, default]) &&
            rowText vt 1 == "" &&
            rowText vt 2 == "  › Find or create a session" &&
            rowText vt 3 == "" &&
            rowText vt 4 == "  ▸   ? Alpha (busy)" &&
            rowText vt 5 == "      ? Beta  (busy)" &&
            rowText vt 6 == "      ? Gamma (busy)" &&
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
              has (rowText vt row) "^L refresh" &&
              has (rowText vt row) "esc / ^C quit" &&
              (vt.getCell 2 row).pen.dim
        s.text "\x03"
        return layout && help && (← restored s 130)
  check e "create-frame"
      "picker query text stays undimmed and the explicit creation row changes Enter help" fun f =>
      withPrompt f.picker #[] fun s => do
        unless ← s.typeQuery "new-session" "new-session" do
          return false
        let vt ← s.capture "create-frame"
        let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
        let shown :=
          rowText vt 2 == "  › new-session 0" && !(vt.getCell 4 2).pen.dim &&
            (vt.getCell 16 2).pen.dim &&
            rowText vt 4 == "  ▸ + Create new-session" &&
            (vt.getCell 4 4).pen.reverse &&
            has screen "  ↵ create" &&
            has screen "↑↓ move" &&
            has screen "esc / ^C quit" &&
            !has screen "↵ attach" &&
            !has screen "Find or create a session" &&
            (List.range vt.rowCount).all (fun row => (underlined vt row).isEmpty) &&
            lastColumnBlank vt
        return shown && (← acceptThenCancel s) && (← f.visits) == attachVisit ["new-session"]
  check e "hidden-groups"
      "picker sums up the rows its window leaves out by typeable groups whose counts add up"
      fun f => do
      let names := (List.range 4).map (s!"ag-build-{·}") ++ (List.range 6).map (s!"ag-test-{·}")
      f.listing (namesListing names)
      withPrompt f.picker #[] fun s => do
          let vt ← s.capture "hidden-groups"
          -- five rows fit with the summary below them; the five left out share one group
          let header :=
            (rowText vt 0).trimAscii.toString ==
              String.intercalate " · "
                (Linger.Display.View.headerParts [] (names.map fun _ => default))
          let window :=
            rowText vt 4 == "  ▸   ? ag-build-0 (busy)" &&
              rowText vt 8 == "      ? ag-test-0  (busy)" &&
              rowText vt 9 == "    … 5 more: ag-test 5" &&
              (vt.getCell 4 9).pen.dim
          unless ← s.typeQuery "ag-test" "ag-test" do
            return false
          let narrowed ← s.capture "hidden-groups-typed"
          let typed := rowText narrowed 2 == "  › ag-test 6" && rowText narrowed 9 == "    … 1 more"
          s.text "\x03"
          return header && window && typed && (← restored s 130)
  check e "unchanged-keys"
      "picker clamped movement, empty editing and ignored controls cause no repaint" fun f =>
      withPrompt f.picker #[] fun s => do
        s.observe 100
        let start ← s.mark
        s.text "\x1b[A\x10\x1b[H\x7f\x08\x15\x00\x07"
        s.observe 350
        let quiet := (← s.mark) == start
        s.text "\x03"
        return quiet && (← restored s 130)

private def Fixture.waitListing (f : Fixture) (serial : Nat) (completed : Bool := false) :
    IO Bool :=
  waitFor patienceMs
    ((f.root / s!"list-{if completed then "completed" else "started"}-{serial}").pathExists)

private def Fixture.releaseListing (f : Fixture) (serial : Nat) : IO Unit :=
  IO.FS.writeFile (f.root / s!"release-listing-{serial}") ""

/-- Each listing the visit has started, in order: whether it queried remote hosts, and when it
started in the recording child, on the monotonic clock this process reads too. -/
private def Fixture.listings (f : Fixture) : IO (List (Bool × Nat)) := do
  let kinds :=
    (lines (← f.calls)).filterMap fun record =>
      if record == (listed.dropEnd 1).toString then some true
      else if record == ((call ["ls", "--porcelain"]).dropEnd 1).toString then some false else none
  let starts :=
    (lines (← readText (f.root / "list-starts"))).filterMap fun line =>
      ((line.splitOn "\t")[2]?).bind String.toNat?
  return kinds.zip starts

/-- Whether the first listing that started at `since` or later queried remote hosts, once it has
completed; `none` when none completes in time. -/
private def Fixture.firstListingFrom (f : Fixture) (since : Nat) : IO (Option Bool) := do
  let found ← IO.mkRef (none : Option Bool)
  let _ ←
    waitFor patienceMs do
        match (← f.listings).zipIdx.find? (fun ((_, start), _) => start ≥ since) with
        | some ((remote, _), index) =>
          if ← (f.root / s!"list-completed-{index + 1}").pathExists then
            found.set (some remote)
            return true
          return false
        | none =>
          return false
  found.get

private def refreshChecks (e : Env) : IO Unit := do
  check e "refresh-reordered"
      "automatic refresh retains query and exact highlighted target across changed ordering"
      fun f =>
      withPrompt f.picker #[] fun s => do
        unless ← s.typeQuery "a" "a" do
          return false
        let selection ← s.mark
        s.text "\x0e"
        unless ← s.selected "Beta" selection do
          return false
        let start ← s.mark
        f.listing (namesListing ["Gamma", "Delta", "Alpha", "Beta"])
        unless ← s.untilRow "Delta" start do
          return false
        unless ← s.selected "Beta" start do
          return false
        let vt ← s.capture "reordered-frame"
        let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
        let retained := has screen "  › a" && has screen "  ▸   ? Beta  (busy)"
        return retained && (← acceptThenCancel s) && (← f.visits) == attachVisit ["Beta"]
  check e "refresh-activity"
      "automatic refresh keeps each running session's row where it was when it starts or stops saying it works"
      fun f => do
      f.listing
          (jsonListing
            [[("name", "alpha"), ("status", "working")], [("name", "beta"), ("status", "idle")]])
      withPrompt f.picker #[] fun s => do
          unless ← s.untilRow "⣷ alpha" do
            return false
          unless ← s.untilRow "⣀ beta" do
            return false
          let before ← s.capture "activity-before"
          let start ← s.mark
          f.listing
              (jsonListing
                [[("name", "alpha"), ("status", "idle")],
                  [("name", "beta"), ("status", "working")]])
          unless ← s.untilRow "⣀ alpha" start do
            return false
          unless ← s.untilRow "⣷ beta" start do
            return false
          let after ← s.capture "activity-after"
          let rowOf := fun (vt : Vt) (name : String) =>
            (List.range vt.rowCount).find? fun row => has (rowText vt row) name
          let kept :=
            match rowOf before "alpha", rowOf before "beta" with
            | some alpha, some beta =>
              alpha < beta && rowOf after "alpha" == some alpha && rowOf after "beta" == some beta
            | _, _ => false
          return kept && (← s.selected "alpha" start) && (← acceptThenCancel s) &&
              (← f.visits) == attachVisit ["alpha"]
  check e "refresh-keeps-order"
      "automatic refresh keeps the rows a visit shows where they are, a vanished row closing up and a new one last, until Ctrl-L sorts them again"
      fun f => do
      f.listing
          (jsonListing
            [[("name", "alpha"), ("status", "idle")], [("name", "beta"), ("status", "idle")],
              [("name", "gamma"), ("status", "idle")]])
      withPrompt f.picker #[] fun s => do
          unless ← s.untilRow "⣀ gamma" do
            return false
          let rowOf := fun (vt : Vt) (name : String) =>
            (List.range vt.rowCount).find? fun row => has (rowText vt row) name
          let start ← s.mark
          -- gamma starts asking, beta ends and delta, which asks, is new: a fresh view would
          -- list gamma and delta first
          f.listing
              (jsonListing
                [[("name", "alpha"), ("status", "idle")],
                  [("name", "gamma"), ("status", "idle"), ("attention", "asked")],
                  [("name", "delta"), ("status", "idle"), ("attention", "asked")]])
          unless ← s.untilRow "⚑ ⣀ delta" start do
            return false
          let kept ← s.capture "kept-order"
          let pressed ← s.mark
          s.text "\x0c"
          let _ ←
            s.untilScreen
                (fun vt =>
                  rowOf vt "gamma" == some 4 && rowOf vt "delta" == some 5 &&
                    rowOf vt "alpha" == some 6)
                pressed
          let sorted ← s.capture "sorted-order"
          IO.FS.writeFile (f.root / "order-observation")
              s!"kept={[rowOf kept "alpha", rowOf kept "beta", rowOf kept "gamma", rowOf kept "delta"]}\nsorted={[rowOf sorted "alpha", rowOf sorted "gamma", rowOf sorted "delta"]}\n"
          let keptOrder :=
            rowOf kept "alpha" == some 4 && rowOf kept "gamma" == some 5 &&
              rowOf kept "delta" == some 6 &&
              rowOf kept "beta" == none
          let sortedOrder :=
            rowOf sorted "gamma" == some 4 && rowOf sorted "delta" == some 5 &&
              rowOf sorted "alpha" == some 6
          let highlight ← s.selected "alpha" pressed
          s.text "\x03"
          return keptOrder && sortedOrder && highlight && (← restored s 130) &&
              (← f.visits) == listed
  check e "refresh-columns"
      "automatic refresh keeps each column's width, cutting a longer value, until Ctrl-L lays the rows out again"
      fun f => do
      f.listing
          (jsonListing
            [[("name", "alpha"), ("pid", "1"), ("cmd", "sh"), ("description", "ab")],
              [("name", "beta"), ("pid", "1"), ("cmd", "sh"), ("description", "cd")]])
      withPrompt f.picker #[] fun s => do
          unless ← s.untilRow "? alpha ab" do
            return false
          let start ← s.mark
          f.listing
              (jsonListing
                [[("name", "alpha"), ("pid", "1"), ("cmd", "sh"), ("description", "abcdefgh")],
                  [("name", "beta"), ("pid", "1"), ("cmd", "sh"), ("description", "cd")]])
          let kept ← s.untilRow "? alpha a…" start
          let pressed ← s.mark
          s.text "\x0c"
          let laidOut ← s.untilRow "? alpha abcdefgh" pressed
          let beta ← s.untilRow "? beta  cd" pressed
          s.text "\x03"
          return kept && laidOut && beta && (← restored s 130) && (← f.visits) == listed
  check e "refresh-removed"
      "automatic refresh clamps a removed selection while preserving an invalid creation query"
      fun f => do
      f.listing (namesListing ["one -. x", "two -. x", "three -. x"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "-. " "-. " do
            return false
          let selection ← s.mark
          s.text "\x1b[F"
          unless ← s.selected "three -. x" selection do
            return false
          let start ← s.mark
          f.listing (namesListing ["first -. x", "last -. x"])
          unless ← s.selected "last -. x" start do
            return false
          let vt ← s.capture "removed-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          return has screen "  › -." && !has screen "Create " && (← acceptThenCancel s) &&
              (← f.visits) == attachVisit ["last -. x"]
  check e "refresh-created"
      "automatic refresh turns a highlighted creation into the same existing target and attach help"
      fun f => do
      f.listing (namesListing ["workshop", "workbench"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "work" "work" do
            return false
          let selection ← s.mark
          s.text "\x1b[F"
          unless ← s.selected "+ Create work" selection do
            return false
          let start ← s.mark
          f.listing (namesListing ["work", "workshop", "workbench"])
          unless ← s.selected "work" start do
            return false
          let vt ← s.capture "created-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          return has screen "  › work" && has screen "  ▸   ? work      (busy)\n" &&
              !has screen "Create work" &&
              has screen "↵ attach" &&
              (← acceptThenCancel s) &&
              (← f.visits) == attachVisit ["work"]
  check e "ctrl-l-refresh"
      "picker Ctrl-L clears and redraws the whole screen, keeps query and highlight and lists remote hosts again at once"
      fun f => do
      f.listing (namesListing ["Beta", "Bravo"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "B" "B" do
            return false
          let selection ← s.mark
          s.text "\x1b[F"
          unless ← s.selected "+ Create B" selection do
            return false
          -- the opening's listing queried remote hosts, the one after it only local sessions
          unless ← f.waitListing 2 true do
            return false
          s.observe 100
          let start ← s.mark
          let pressed ← monotonicMs
          s.text "\x0c"
          -- the first listing to start after the key queries remote hosts
          let fetched ← f.firstListingFrom pressed
          s.observe 400
          let vt ← s.capture "ctrl-l-frame"
          let output ← s.output.get
          -- over a screen something else covered with `X`, what the picker wrote after the key
          -- shows exactly what the picker shows: it painted every row again
          let covered :=
            (Vt.init 80 12).feedBytes (ByteArray.mk (List.replicate (80 * 12) 0x58).toArray)
          let redrawn :=
            screenText (covered.feedBytes (output.extract start output.size)) == screenText vt
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          IO.FS.writeFile (f.root / "ctrl-l-observation")
              s!"pressed={pressed}\nlistings={← f.listings}\nfetched={fetched}\nredrawn={redrawn}\n"
          s.text "\x03"
          return fetched == some true && redrawn && has screen "  › B" &&
              has screen "  ▸ + Create B" &&
              (← restored s 130) &&
              (← f.visits) == listed
  check e "ctrl-r-ignored"
      "picker Ctrl-R preserves query and highlight without repaint or a listing of its own" fun f =>
      do
      f.listing (namesListing ["Beta", "Bravo"])
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "B" "B" do
            return false
          let selection ← s.mark
          s.text "\x1b[F"
          unless ← s.selected "+ Create B" selection do
            return false
          unless ← f.waitListing 2 true do
            return false
          s.observe 100
          let start ← s.mark
          let pressed ← monotonicMs
          s.text "\x12"
          -- the first listing to start after the key is the next second's, of local rows alone
          let fetched ← f.firstListingFrom pressed
          s.observe 400
          let quiet := (← s.mark) == start
          let vt ← s.capture "ctrl-r-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          let listings ← f.listings
          let gaps := (listings.zip listings.tail).map fun ((_, a), (_, b)) => b - a
          IO.FS.writeFile (f.root / "ctrl-r-observation")
              s!"pressed={pressed}\nlistings={listings}\nfetched={fetched}\ngaps={gaps}\n"
          s.text "\x03"
          return fetched == some false && quiet && gaps.all (· ≥ 850) && has screen "  › B" &&
              has screen "  ▸ + Create B" &&
              (← restored s 130) &&
              (← f.visits) == listed
  check e "idle-refresh"
      "picker repeats complete listings about one second apart without repainting unchanged snapshots"
      fun f =>
      withPrompt f.picker #[] fun s => do
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
        return repeated && quiet && spaced && (← restored s 130) && (← f.visits) == listed &&
            !(← (f.root / "listing-overlap").pathExists)
  check e "remote-on-events"
      "picker lists local rows every second and queries remote hosts only when it opens and on Ctrl-L"
      fun f => do
      f.listing
          (jsonListing
            [[("name", "Alpha"), ("status", "idle")], [("name", "work@host"), ("status", "idle")]])
      withPrompt f.picker #[] fun s => do
          unless ← f.waitListing 1 true do
            return false
          let start ← s.mark
          f.listing
              (jsonListing
                [[("name", "Beta"), ("status", "idle")],
                  [("name", "next@host"), ("status", "idle")]])
          unless ← s.untilRow "Beta" start do
            return false
          -- six seconds of listings, longer than the cadence the chooser once queried hosts at:
          -- no event asked for remote rows, so none of them queries a remote host
          unless ← f.waitListing 7 true do
            return false
          let localFrame ← s.capture "local-refresh-frame"
          let localScreen := String.fromUTF8! (ByteArray.mk (screenText localFrame).toArray)
          let held := has localScreen "work@host" && !has localScreen "next@host"
          let before ← f.listings
          let start ← s.mark
          let pressed ← monotonicMs
          s.text "\x0c"
          let shown ←
            s.untilScreen
                (fun vt => (List.range vt.rowCount).any fun row => has (rowText vt row) "next@host")
                start
          let remoteFrame ← s.capture "remote-refresh-frame"
          let remoteScreen := String.fromUTF8! (ByteArray.mk (screenText remoteFrame).toArray)
          let fetched ← f.firstListingFrom pressed
          s.text "\x03"
          let clean ← restored s 130
          let gaps := (before.zip before.tail).map fun ((_, a), (_, b)) => b - a
          IO.FS.writeFile (f.root / "cadence-observation")
              s!"before={before}\npressed={pressed}\nfetched={fetched}\ngaps={gaps}\n"
          let opened := before.map (·.1) == true :: List.replicate (before.length - 1) false
          return held && before.length ≥ 7 && opened && gaps.all (· ≥ 850) && shown &&
              has remoteScreen "Beta" &&
              !has remoteScreen "work@host" &&
              fetched == some true &&
              clean &&
              (← f.visits) == listed &&
              !(← (f.root / "listing-overlap").pathExists)
  check e "remote-age"
      "picker header says how long ago it listed the remote rows, as a row says its last output's age, updates it with each listing by repainting that row alone, and gives no age once no remote row is left"
      fun f => do
      f.listing
          (jsonListing
            [[("name", "Alpha"), ("status", "idle")],
              [("name", "work@host"), ("status", "working")]])
      withPrompt f.picker #[] fun s => do
          let parts := Linger.Display.View.headerParts [] [⟨.none, .idle⟩, ⟨.none, .working⟩]
          -- the header's age, in the format a row gives the time since its session last printed
          let ageOf := fun (vt : Vt) =>
            (List.range 60).find? fun n =>
              (rowText vt 0).trimAscii.toString ==
                String.intercalate " · " (parts ++ [s!"remote {Linger.Display.Listing.ago n}"])
          unless ← s.untilScreen (fun vt => (ageOf vt).any (· ≥ 1)) do
            return false
          let older ← s.capture "remote-age-first"
          let start ← s.mark
          let later := fun (vt : Vt) => (ageOf vt).any fun n => (ageOf older).any (· < n)
          unless ← s.untilScreen later start do
            return false
          let newer ← s.capture "remote-age-next"
          let output ← s.output.get
          let written := output.extract start output.size
          -- the listings in between changed the age alone: they rewrote the header's row and no
          -- other, and painted no whole frame
          let headerOnly :=
            hasText written "\x1b[1;1H" && !hasText written "\x1b[H" &&
              (List.range (newer.rowCount - 1)).all fun k => !hasText written s!"\x1b[{k + 2};1H"
          -- once a listing of remote hosts finds no remote row, the header gives no age
          f.listing (jsonListing [[("name", "Alpha"), ("status", "idle")]])
          let cleared ← s.mark
          s.text "\x0c"
          let plain :=
            String.intercalate " · " (Linger.Display.View.headerParts [] [⟨.none, .idle⟩])
          let gone ← s.untilScreen (fun vt => (rowText vt 0).trimAscii.toString == plain) cleared
          s.observe 1200
          let after ← s.capture "remote-age-gone"
          let screen := String.fromUTF8! (ByteArray.mk (screenText after).toArray)
          IO.FS.writeFile (f.root / "age-observation")
              s!"first={ageOf older}\nnext={ageOf newer}\nheader-only={headerOnly}\ngone={gone}\nheader-after={rowText after 0}\nlistings={← f.listings}\n"
          s.text "\x03"
          return headerOnly && gone && (rowText after 0).trimAscii.toString == plain &&
              !has screen "work@host" &&
              (← restored s 130) &&
              (← f.visits) == listed
  for (slug, text, rc, error) in
    [("failure", (namesListing ["Partial"]), 9, "could not list sessions (exit 9)"),
      ("duplicate", (namesListing ["Fresh", "Fresh"]), 1, "duplicate session target"),
      ("malformed", namesListing ["Fresh"] ++ "{\"extra\":[],\"name\":\"bad\"}\n", 1,
        "a listing that is not the JSON Lines of session records")] do
    check e s!"refresh-{slug}"
        s!"automatic refresh rejects the entire bad snapshot and prints an error after restoration ({slug})"
        fun f =>
        withPrompt f.picker #[] fun s => do
          f.listing text (if slug == "failure" then rc else 0)
          let visible ← s.until error
          let clean ← restored s rc
          let out ← s.output.get
          return visible && clean && !hasText out "Partial" && !hasText out "Fresh" &&
              ordered out (modeSet 1049 false) error.toUTF8.toList &&
              (← numberFile (f.root / "list-count")) ≥ 2 &&
              (← f.visits) == listed
  check e "refresh-partial"
      "incomplete listing output cannot replace displayed rows and keyboard editing stays responsive"
      fun f => do
      f.listing (namesListing ["alpha.x", "beta.x", "gamma.x"])
      IO.FS.writeFile (f.root / "hold-listing-from") "2"
      withPrompt f.picker #[] fun s => do
          IO.FS.writeFile (f.root / "listing-prefix") (namesListing ["ready.x"])
          f.listing (namesListing ["beta.x", "new.x"])
          unless ← f.waitListing 2 do
            return false
          unless ← s.typeQuery "." "." do
            return false
          let selection ← s.mark
          s.text "\x0e"
          unless ← s.selected "beta.x" selection do
            return false
          let before ← s.capture "partial-frame"
          let beforeText := String.fromUTF8! (ByteArray.mk (screenText before).toArray)
          let incomplete :=
            has beforeText "beta.x" && !has beforeText "ready.x" && !has beforeText "new.x"
          let start ← s.mark
          f.releaseListing 2
          unless ← s.untilRow "new.x" start do
            return false
          unless ← s.selected "beta.x" start do
            return false
          let vt ← s.capture "complete-frame"
          let screen := String.fromUTF8! (ByteArray.mk (screenText vt).toArray)
          s.text "\x03"
          return incomplete && has screen "ready.x" && has screen "new.x" && has screen "  › ." &&
              !has screen "alpha.x" &&
              (← restored s 130)
  check e "refresh-input-order"
      "completed refresh follows displayed navigation and paints before the next accepted key"
      fun f => do
      f.listing (namesListing ["alpha.x", "beta.x", "gamma.x"])
      IO.FS.writeFile (f.root / "hold-listing-from") "2"
      withPrompt f.picker #[] fun s => do
          unless ← s.typeQuery "." "." do
            return false
          f.listing (namesListing ["beta.x", "delta.x", "gamma.x", "alpha.x"])
          unless ← f.waitListing 2 do
            return false
          let start ← s.mark
          s.text "\x0e"
          f.releaseListing 2
          unless ← s.untilRow "delta.x" start do
            return false
          let vt ← s.capture "ready-frame"
          -- the rows shown keep their places and the new delta.x comes last
          let displayed := rowText vt 5 == "  ▸   ? beta.x  (busy)" && has (rowText vt 7) "delta.x"
          IO.FS.removeFile (f.root / "hold-listing-from")
          let start ← s.mark
          s.text "\x0e"
          unless ← s.selected "gamma.x" start do
            return false
          return displayed && (← acceptThenCancel s) && (← f.visits) == attachVisit ["gamma.x"]
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
              let responsive ← s.untilAny ["  › B", "linger> B"] start
              -- This interval crosses another refresh deadline while stdout is held.
              s.observe 1200
              let one :=
                (← numberFile (f.root / "list-count")) == serial &&
                  !(← (f.root / "listing-overlap").pathExists)
              let start ← s.mark
              let began ← monotonicMs
              s.text key
              -- The listing is held past `hangMs`: a cancel that waited for it, or left its
              -- child running, could pass neither wait.
              let promptExit ← s.until "MANAGER-EXIT:130" start
              let elapsed := (← monotonicMs) - began
              let reaped ←
                waitFor patienceMs do
                    return pid > 0 && !(← alive (UInt32.ofNat pid))
              IO.FS.writeFile (f.root / "cancel-observation")
                  s!"pid={pid}\nalive-before={live}\nkeyboard-responsive={responsive}\none-in-flight={one}\nexit-within-deadline={promptExit}\nelapsed-ms={elapsed}\nchild-gone={reaped}\n"
              return live && responsive && one && promptExit && reaped && (← restored s 130) &&
                  (← f.visits) == listed
  check e "resize"
      "picker probe redraw fits a resized terminal and clips wide text without changing its target"
      fun f => do
      let target := "wide@界界界界Z"
      f.listing (namesListing [target, "second", "third", "fourth"])
      withPrompt f.picker #[]
          (fun s => do
            unless ← s.until target do
              return false
            let start ← s.mark
            s.client.resize 16 4
            unless ← s.until "wide@" start do
              return false
            s.observe 150
            let out ← s.output.get
            let frame := out.extract start out.size
            let vt := (Vt.init 16 4).feedBytes frame
            let screen := ByteArray.mk (screenText vt).toArray
            IO.FS.writeBinFile (f.root / "resized-frame.bin") frame
            IO.FS.writeBinFile (f.root / "screen.txt") screen
            let fits := hasText screen "  ▸   ? wide@界" && !hasText screen "Z" && lastColumnBlank vt
            s.client.resize 80 12
            unless ← s.prompt "" (← s.mark) do
              return false
            return fits && (← acceptThenCancel s) && (← f.visits) == attachVisit [target])
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
              shown && rowText vt (rows - 1) == "  ▸   ? Alpha (busy)" &&
                !hasText screen "linger" &&
                !hasText screen "↵" &&
                lastColumnBlank vt
            s.text "\x03"
            return visible && (← restored s 130) && (← f.visits) == listed)
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
        withPrompt f.picker #[] fun s => do
            return (← acceptThenCancel s) && !(← (f.root / "impostor-hit").pathExists) &&
                (← f.visits) == attachVisit ["Alpha"]
  for rc in [0, 7, 255] do
    check e s!"default-{rc}" s!"picker probe returns to a fresh picker after attach status {rc}"
        fun f => do
        IO.FS.writeFile (f.root / "attach-rc") (toString rc)
        withPrompt f.picker #[] fun s => do
            return (← acceptThenCancel s) && (← f.visits) == attachVisit ["Alpha"]
  check e "successive"
      "picker probe repeatedly attaches from fresh snapshots after statuses 0, 7 and 255" fun f =>
      withPrompt f.picker #[] fun s => do
        let remote := "-work@me@dev-a"
        let shellText := "work@host with 'spaces' $TERM"
        let mut expected := listed
        let mut count := 0
        let mut normal := true
        for (target, query, rc, next) in
          [("Beta", "B", 0, remote), (remote, "wrk", 7, shellText),
            (shellText, "host", 255, "Fresh")] do
          unless ← s.typeQuery query query do
            return false
          f.afterAttach (namesListing [next, s!"Other{count}"])
          IO.FS.writeFile (f.root / "attach-rc") (toString rc)
          s.text "\r"
          count := count + 1
          unless ← returned s next count do
            return false
          expected := expected ++ call ["attach", "--", target] ++ listed
          normal :=
            normal && (← beforeAttach s count count) && (← attachNormal f count) &&
              (← f.visits) == expected
        s.text "\x03"
        return normal && (← restored s 130 4) && (← f.visits) == expected
  check e "return-selects"
      "picker returns from an attach to the view it left, the attached row highlighted" fun f =>
      withPrompt f.picker #[] fun s => do
        let selection ← s.mark
        s.text "\x1b[B"
        unless ← s.selected "Beta" selection do
          return false
        f.afterAttach (namesListing ["Gamma", "Beta", "Alpha", "Delta"])
        s.text "\r"
        unless ← returned s "Beta" do
          return false
        let vt ← s.capture "return-frame"
        -- the rows the visit left, in its order, and the new Delta last
        let rows :=
          ["Alpha", "Beta", "Gamma", "Delta"].zipIdx.all fun (name, index) =>
            has (rowText vt (4 + index)) name
        s.text "\x03"
        return rows && (← restored s 130 2) && (← beforeAttach s) && (← attachNormal f) &&
            (← f.visits) == attachVisit ["Beta"]
  -- `LINGER_SESSION` holds the session's ID: a renamed session's ID, which the names directory
  -- leads its new name to, selects the row of that name
  for (slug, session, chosen) in
    [("inside-session", "Gamma", "Gamma"), ("inside-session-empty", "", "Alpha"),
      ("inside-session-gone", "Gone", "Alpha"), ("inside-session-renamed", "Delta", "Gamma")] do
    check e slug
        s!"picker opened inside a session starts on that session, or the top row without one ({slug})"
        fun f => do
        IO.FS.writeFile (f.root / "linger-session") session
        if slug == "inside-session-renamed" then
          IO.FS.createDirAll (f.root / "state" / "names")
          IO.FS.writeFile (f.root / "state" / "names" / "Gamma") "Delta"
        let f := { f with env := f.env.push ("LINGER_DIR", some (f.root / "state").toString) }
        withPrompt f.picker #[] fun s => do
            let highlight ← s.selected chosen
            s.text "\x03"
            return highlight && (← restored s 130) && (← f.visits) == listed
  check e "return-listing-failure"
      "picker probe preserves a failed listing status after attach and restores the terminal"
      fun f =>
      withPrompt f.picker #[] fun s => do
        f.afterAttach (namesListing ["Partial"]) 9
        s.text "\r"
        let clean ← failureRestored s 9 "linger: could not list sessions (exit 9)" 1
        return clean && (← beforeAttach s) && (← attachNormal f) &&
            (← f.visits) == attachVisit ["Alpha"]
  check e "return-malformed"
      "picker probe rejects a malformed listing after attach before another picker visit" fun f =>
      withPrompt f.picker #[] fun s => do
        f.afterAttach (namesListing ["Next", "Next"])
        s.text "\r"
        let clean ← failureRestored s 1 "picker probe:" 1
        return clean && (← beforeAttach s) && (← attachNormal f) &&
            (← f.visits) == attachVisit ["Alpha"]

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
                  { cmd := e.bin, args := #["start", name, "/bin/sh"], env := f.env, stdin := .null,
                    stdout := .piped, stderr := .piped }
          let rc ← waitChild create 5000
          if rc != 0 then
            throw (IO.userError s!"manager live fixture failed: {← create.stderr.readToEnd}")
        try
          withPrompt f #["attach"] fun s => do
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
              let attached ← clientsReach owned name "1"
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
              let detached ← clientsReach owned name "0"
              IO.FS.writeFile (f.root / "after-detach")
                  (← withLaunchLock (owned.out #["ls", "--porcelain", "--", name]))
              s.text "\x03"
              return shown && untouched && names == [name] && detached &&
                  (← termiosRestored s 130) &&
                  sequenceCount (← s.output.get) (modeSet 1049 true) ≥ 2
        finally
          withLaunchLock (owned.killAll #[name])

/-- Foreign fixtures use explicit files and private homes/state. The native
encoding keeps expected identities tied to the save parser's own policy. -/
private def savedPane (name dir command : String := "") : String :=
  s!"pane\t{Linger.Import.Resurrect.encodeName name}\t0\t1\t:*\t0\ttitle\t:{dir}\t1\tsh\t:{command}\n"

/-- Install the real archive reader and gzip on the restricted fixture PATH. -/
private def Fixture.archive (f : Fixture) (captures : List (String × String)) :
    IO System.FilePath := do
  for tool in ["tar", "gzip"] do
    let observer ←
      withLaunchLock <|
          IO.Process.output { cmd := "/bin/sh", args := #["-c", s!"command -v {tool}"] }
    unless observer.exitCode == 0 && !observer.stdout.trimAscii.isEmpty do
      throw (IO.userError s!"{tool} is required for saved pane capture checks")
    let reader := f.root / "bin" / tool
    unless ← reader.pathExists do
      let linked ←
        withLaunchLock <|
            IO.Process.output
              { cmd := "ln", args := #["-s", observer.stdout.trimAscii.toString, reader.toString] }
      unless linked.exitCode == 0 do
        throw (IO.userError s!"could not install fixture archive reader: {linked.stderr}")
  let staging := f.root / "archive-source"
  IO.FS.createDirAll (staging / "pane_contents")
  for (name, content) in captures do
    let session := Linger.Import.Resurrect.encodeName name
    IO.FS.writeFile (staging / "pane_contents" / s!"pane-{session}:0.0") content
  let path := f.root / "pane_contents.tar.gz"
  let result ←
    withLaunchLock <|
        IO.Process.output
          { cmd := (f.root / "bin" / "tar").toString,
            args := #["-czf", path.toString, "-C", staging.toString, "./pane_contents"] }
  unless result.exitCode == 0 do
    throw (IO.userError s!"could not create fixture archive: {result.stderr}")
  return path

/-- The names of the sessions `ls --porcelain` lists, without the saved tmux panes it lists after
them, which its `source` field marks. -/
private def Fixture.nativeNames (f : Fixture) : IO (List String) := do
  let (rc, out, err) ← f.piped #["ls", "--porcelain"]
  unless rc == 0 do
    throw (IO.userError s!"native fixture listing failed: {err}")
  return (listingRecords out).filterMap fun fields =>
      if (fields.lookup "source").isSome then none else fields.lookup "name"

private def checkSaved (e : Env) (slug label : String) (body : Fixture → Env → IO Bool) : IO Unit :=
  check e s!"tmux-{slug}" label fun f => do
    let owned : Env := { e with dir := (f.root / "state").toString }
    let f := { f with env := f.env.push ("LINGER_DIR", some owned.dir) }
    try
      body f owned
    finally
      withLaunchLock
          (owned.killAll #["saved-first", "saved-chosen", "-saved-chosen", "never-create"])

/-- The latest save, where tmux-resurrect keeps it for a fixture whose home is its root and whose
PATH has no tmux: `~/.tmux/resurrect/last`. -/
private def Fixture.save (f : Fixture) : System.FilePath := f.root / ".tmux" / "resurrect" / "last"

/-- Write `text` as the fixture's latest save. -/
private def Fixture.writeSave (f : Fixture) (text : String) : IO Unit := do
  IO.FS.createDirAll (f.root / ".tmux" / "resurrect")
  IO.FS.writeFile f.save text

private def savedChecks (e : Env) : IO Unit := do
  checkSaved e "cancel"
      "the chooser lists the latest save's panes as saved, and cancelling imports none" fun f _ =>
      do
      f.writeSave
          (savedPane "saved-first" f.root.toString ++ savedPane "saved-chosen" f.root.toString)
      withSession f #["attach"] fun s => do
          unless ← s.selected "saved-chosen" do
            return false
          let marked ← s.untilRow "(saved by tmux)"
          s.observe 150
          let before ← f.nativeNames
          s.text "\x03"
          let clean ← restored s 130
          return marked && before.isEmpty && clean && (← f.nativeNames).isEmpty
  checkSaved e "chosen"
      "the chooser attaches a chosen saved pane as a fresh shell in its exact cwd, ignores saved commands and returns after detach"
      fun f owned => do
      let dir := f.root / "cwd 'literal' $HOME \"quoted\" 界"
      IO.FS.createDirAll dir
      let dir ← IO.FS.realPath dir
      let replayed := f.root / "saved-command-ran"
      let command := s!"printf replay >{quote replayed.toString}"
      -- A nonexistent unchosen directory must not block the valid selection.
      f.writeSave
          (savedPane "saved-first" (f.root / "absent").toString command ++
            savedPane "saved-chosen" dir.toString command)
      withSession f #["attach"] fun s => do
          unless ← s.selected "saved-chosen" do
            return false
          let untouched := (← f.nativeNames).isEmpty
          s.text "\r"
          let attached ← clientsReach owned "saved-chosen" "1"
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
          let returned ← s.selected "saved-chosen" start
          let detached ← clientsReach owned "saved-chosen" "0" (ms := 3000)
          s.text "\x03"
          let clean ← termiosRestored s 130
          IO.FS.writeFile (f.root / "selection-observation")
              s!"no-early-import={untouched}\nshell={shell}\ncwd={repr cwd}\nnames={repr names}\nreturned={returned}\ndetached={detached}\n"
          return untouched && shell && cwd == dir.toString ++ "\n" && names == ["saved-chosen"] &&
              returned &&
              detached &&
              clean &&
              !(← replayed.pathExists)
  checkSaved e "chosen-leading"
      "the chooser attaches a chosen saved pane whose name starts with - and returns after detach"
      fun f owned => do
      f.writeSave (savedPane "-saved-chosen" f.root.toString)
      withSession f #["attach"] fun s => do
          unless ← s.selected "-saved-chosen" do
            return false
          s.text "\r"
          let attached ← clientsReach owned "-saved-chosen" "1"
          unless attached do
            return false
          let start ← s.mark
          s.client.detach
          let returned ← s.selected "-saved-chosen" start
          s.text "\x03"
          return returned && (← termiosRestored s 130)
  checkSaved e "chosen-capture"
      "the chooser restores only the chosen pane's contents and metadata into a fresh shell"
      fun f owned => do
      let marker := f.root / "saved-command-ran"
      let command := s!"printf bad >{quote marker.toString}"
      f.writeSave
          (savedPane "saved-first" (f.root / "absent").toString command ++
            savedPane "saved-chosen" f.root.toString command ++
            "window\tlinger=saved-chosen\t0\t:Saved window\t1\t:*\t1234,80x12,0,0,1\toff\n")
      let archive ←
        f.archive
            [("saved-first", "unchosen old\nunchosen screen\n"),
              ("saved-chosen", "chosen old λ\nchosen saved screen\n")]
      IO.FS.rename archive (f.root / ".tmux" / "resurrect" / "pane_contents.tar.gz")
      withSession f #["attach"] fun s => do
          unless ← s.selected "saved-chosen" do
            return false
          s.text "\r"
          unless ← clientsReach owned "saved-chosen" "1" do
            return false
          let restoredScreen ← s.until "chosen saved screen"
          let history ← withLaunchLock (owned.out #["capture", "--history", "saved-chosen"])
          let savedCommand ← withLaunchLock (owned.info "saved-chosen" "tmux.saved-command")
          let capture ← withLaunchLock (owned.info "saved-chosen" "tmux.capture")
          let description ← withLaunchLock (owned.info "saved-chosen" "description")
          let start ← s.mark
          s.text "printf 'capture-shell-%s\\n' ready\r"
          let shell ← s.until "capture-shell-ready" start
          let start ← s.mark
          s.client.detach
          let returned ← s.selected "saved-chosen" start
          s.text "\x03"
          return restoredScreen && has history "chosen old λ" && !has history "unchosen old" &&
              savedCommand == some command &&
              capture == some "saved" &&
              description == some "Saved window" &&
              shell &&
              returned &&
              (← termiosRestored s 130) &&
              (← f.nativeNames) == ["saved-chosen"] &&
              !(← marker.pathExists)

private def stoppedBy (f : Fixture) (args : Array String) (ready : String) (sig : UInt32) :
    IO (Bool × Bool × Option Reaped) := do
  let env := f.env.map fun (key, value) => s!"{key}={value.getD ""}"
  let (pid, fd) ← withLaunchLock <| spawnPty 80 12 "" f.manager args env
  let c : Client := { pid, fd }
  try
    let shown ← IO.mkRef ByteArray.empty
    let up ← c.awaitText shown (hasText · ready)
    let mark := (← shown.get).size
    kill pid sig
    let handed ← c.awaitText shown (hasBytes · Linger.Selector.Picker.exitAnsi) (start := mark)
    let ended ← c.ending patienceMs
    IO.FS.writeFile (f.root / "signal-observation")
        s!"ready={up}\nhanded-back={handed}\nended={repr ended}\n"
    return (up, handed, ended)
  finally
    c.bye (sendDetach := false)

/-- A signal that stops the chooser, `linger attach` alone, ends it as a cancellation does,
handing its terminal back, and then the signal ends the process, as it ends a program that does
not catch it, so its caller sees the signal itself, which a shell reports as 128 plus its number:
SIGTERM, as a logout sends, SIGHUP, as a closed window sends, and SIGINT. -/
private def signalChecks (e : Env) : IO Unit := do
  for (slug, sig) in [("sigterm", (15 : UInt32)), ("sighup", 1), ("sigint", 2)] do
    check e s!"chooser-{slug}"
        s!"a signal to linger's chooser hands its terminal back and then ends it ({slug})" fun f =>
        do
        let owned : Env := { e with dir := (f.root / "state").toString }
        let f := { f with env := f.env.push ("LINGER_DIR", some owned.dir) }
        let (up, handed, ended) ← stoppedBy f #["attach"] "Find or create a session" sig
        return up && handed && ended == some (.signaled sig.toUInt8)

/-- Start session `name` running a shell, and the session program probe in it, so Ctrl-C ends the
probe and returns to the shell. -/
private def startProgram (f : Fixture) (owned : Env) (name : String) : IO Bool := do
  let probe := s!"{quote f.self} --manager-probe session-program\n"
  for args in [#["start", name, "/bin/sh"], #["send", name, probe]] do
    let child ←
      withLaunchLock <|
          IO.Process.spawn
            { cmd := owned.bin, args, env := f.env, stdin := .null, stdout := .piped,
              stderr := .piped }
    let rc ← waitChild child 5000
    if rc != 0 then
      throw (IO.userError s!"session program launch failed: {← child.stderr.readToEnd}")
  return ←
      waitFor 5000 do
          return (← numberFile (f.root / "session-program-pid")) > 0 &&
              has (← withLaunchLock (owned.out #["capture", name])) "MANAGER-PROGRAM-READY"

/-- Why a foreground program outlived Ctrl-C, as lines for a remote log: the
process state of it, its shell and the daemon, its threads' top frames where
macOS `sample` exists, and whether a SIGINT sent to the program itself ends it.
The last separates a signal the terminal never delivered from one the program
does not act on. -/
private def interruptEvidence (root : System.FilePath) (pid : Nat) : IO (List String) := do
  let table ←
    IO.Process.output
        { cmd := "/bin/sh",
          args :=
            #["-c",
              "s=$(ps -o ppid= -p \"$1\" | tr -d ' '); d=$(ps -o ppid= -p \"$s\" | tr -d ' '); " ++
                "ps -o pid,ppid,pgid,tpgid,stat,pending,blocked,ignored,caught,wchan,command -p \"$1,$s,$d\"",
              "sh", toString pid] }
  let report := root / "sample.txt"
  let stacks ←
    if !(← System.FilePath.pathExists "/usr/bin/sample") then
      pure ["no /usr/bin/sample on this host"]
    else
      let out ←
        IO.Process.output
            { cmd := "/usr/bin/sample", args := #[toString pid, "1", "-file", report.toString] }
      if out.exitCode != 0 then
        pure [s!"sample exited {out.exitCode}: {out.stderr.trimAscii.toString}"]
      else
        let rows := (lines (← readText report)).map (·.trimAscii.toString)
        let top := (rows.dropWhile (!·.startsWith "Sort by top of stack")).takeWhile (!·.isEmpty)
        pure (rows.filter (has · "Thread_") ++ top)
  kill (UInt32.ofNat pid) 2
  let direct ←
    waitFor 1000 do
        return !(← alive (UInt32.ofNat pid))
  return (lines table.stdout).map ("ps " ++ ·) ++ stacks.map ("stack " ++ ·) ++
      [s!"direct-sigint-ends-program={direct}"]

/-- What the command printed on standard output once it exited: the terminal's bytes before the
launcher's completion marker, or the file a redirected standard output went to. -/
private def Session.stdout (s : Session) (mode : String) : IO ByteArray := do
  let _ ← s.until "MANAGER-EXIT:"
  if mode == "stdin-only" then
    return ← IO.FS.readBinFile (s.fixture.root / "stdout")
  let output ← s.output.get
  let some stop := findText output "\r\r\nMANAGER-EXIT:" | return output
  return output.extract 0 stop

/-- `ls` colors its listing exactly when it goes to a terminal, NO_COLOR is unset or empty and
TERM names a terminal other than `dumb`, whether it lists a saved session or a saved tmux pane,
whose badge has its status's style when the listing colors, and no byte of a plain listing is an
escape. -/
private def colorChecks (e : Env) : IO Unit := do
  let xterm := some "xterm-256color"
  let cases : List (String × Option String × Option String × String × Bool) :=
    [("colors", none, xterm, "both", true), ("no-color-empty", some "", xterm, "both", true),
      ("no-color-set", some "1", xterm, "both", false),
      ("term-dumb", none, some "dumb", "both", false), ("term-unset", none, none, "both", false),
      ("term-empty", none, some "", "both", false),
      ("redirected", none, xterm, "stdin-only", false)]
  for verb in ["ls", "ls-pane"] do
    for (slug, noColor, term, mode, colored) in cases do
      check e s!"color-{verb}-{slug}"
          s!"linger {verb} {if colored then "colors" else "does not color"} its listing ({slug})"
          fun f => do
          let state := f.root / "state"
          IO.FS.createDirAll state
          if verb == "ls" then
            IO.FS.writeBinFile (state / "saved.ckpt")
                (Linger.Session.Checkpoint.saveBytes ⟨Vt.init 20 2, f.root.toString, []⟩)
          else
            f.writeSave (savedPane "saved" f.root.toString)
          let f := { f with env := f.env.push ("LINGER_DIR", some state.toString) }
          f.colorEnv noColor term
          let args := #["ls"]
          withSession f args
              (fun s => do
                let out ← s.stdout mode
                let clean ← termiosRestored s 0
                let badge := Linger.Display.Listing.sgr (Linger.Display.Status.style .resumable)
                IO.FS.writeBinFile (f.root / "listing.out") out
                IO.FS.writeFile (f.root / "color-observation")
                    s!"exit-clean={clean}\nbadge-styled={hasBytes out badge}\nescapes={hasBytes out [0x1B]}\n"
                return clean && hasText out "saved" &&
                    (if colored then hasBytes out badge else !hasBytes out [0x1B]))
              mode

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
          let before ← withLaunchLock (owned.out #["ls", "--porcelain", "--", name])
          withPrompt f #["attach"] fun s => do
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
              IO.FS.writeFile (f.root / "survival-observation")
                  s!"pid={pid}\nalive-before={live}\nalive-after={survived}\nsend-exit={sent}\nanswered-after-cancel={answered}\nno-client={detached}\n"
              IO.FS.writeFile (f.root / "before-info") before
              IO.FS.writeFile (f.root / "after-info")
                  (← withLaunchLock (owned.out #["ls", "--porcelain", "--", name]))
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
      -- Each stage is appended as it completes, so a stalled or failed run keeps its timeline.
      let begin ← monotonicMs
      let observe (text : String) : IO Unit := do
        appendText (f.root / "interrupt-observation") s!"{(← monotonicMs) - begin} ms {text}\n"
      try
        unless ← startProgram f owned name do
          return false
        let pid ← numberFile (f.root / "session-program-pid")
        -- The attach replay of a 400x200 screen, about 80 KB, overflows the pty's output
        -- buffer on Linux as an 80x12 one does on macOS, so the client blocks on output.
        withPrompt f #["attach"] (cols := 400) (rows := 200) fun s => do
            unless ← s.selected name do
              return false
            s.text "\r"
            let attached ← clientsReach owned name "1"
            let live := pid > 0 && (← alive (UInt32.ofNat pid))
            observe
                s!"pid={pid} attached={attached} alive-before={live} info={repr (← withLaunchLock (owned.out #["ls", "--porcelain", "--", name]))}"
            unless attached && live do
              return false
            s.text "\x03"
            let interrupted ←
              s.waitFor 2000 do
                  return !(← alive (UInt32.ofNat pid))
            observe s!"program-gone={interrupted}"
            unless interrupted do
              -- Fail now: the shell cannot answer while the program holds the terminal.
              for line in ← interruptEvidence f.root pid do
                observe line
              return false
            let start ← s.mark
            s.text "printf 'attached-%s\\n' interrupt-ok\r"
            let shell ← s.until "attached-interrupt-ok" start
            observe s!"shell-responded={shell}"
            let start ← s.mark
            s.client.detach
            let returned ← s.prompt "" start
            observe s!"selector-returned={returned}"
            s.text "\x03"
            let clean ← termiosRestored s 130
            observe s!"terminal-restored={clean}"
            return interrupted && shell && returned && clean &&
                (← withLaunchLock (owned.info name "clients")) == some "0"
      finally
        observe
            s!"screen={repr (← withLaunchLock (owned.out #["capture", name]))} info={repr (← withLaunchLock (owned.out #["ls", "--porcelain", "--", name]))}"
        let _ ← withLaunchLock (owned.cli #["send", name, "stop-program\n"])
        withLaunchLock (owned.killAll #[name])

/-- The manager suite: the public entry point and the shared picker executor, against
`MANAGER_TEST_LINGER` when it is set and the built `linger` otherwise. -/
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
        ("real", realCheck), ("program", programChecks), ("saved", savedChecks),
        ("color", colorChecks), ("signal", signalChecks)]
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

end Linger.App.Suites.Manager
