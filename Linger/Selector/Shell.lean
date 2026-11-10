module

public import Linger.Selector.Picker
import Linger.Os.Shell
import Linger.Target.Remote
import Linger.Terminal.Title
import Linger.Os.Shell.Command
import Linger.Display.View
import Std.Data.HashMap.Basic
import Linger.Display.Status
import Linger.Selector.Key

public section

/-! Terminal executor for the session selector. Selection and decoding
are pure tool modules; this module owns terminal lifetime and subprocesses. -/

namespace Linger.Selector.Shell

open Linger.Os.Shell

/-- How one selection visit ended. -/
inductive Choice where
  /-- An accepted row's exact target, existing or new, with the snapshot displayed
  when it was accepted. -/
  | attach (target : String) (snapshot : Linger.Selector.Picker.Snapshot)
  /-- Cancellation by key, or the end of terminal input. -/
  | cancel
  /-- A listing exited nonzero, with its exit status and standard error. -/
  | failed (status : UInt32) (stderr : String)

/-- Each listed target's status, read once per listing in one pass over its records: a name
record starts a row, a blank record ends it, and its `status` record says its status, as
`Picker.Snapshot.row` reads it. A target without one is unknown. -/
private def statusesOf (snapshot : Linger.Selector.Picker.Snapshot) :
    Std.HashMap String Linger.Display.Status.Status :=
  Id.run do
    let mut current : Option String := none
    let mut statuses := {}
    for fields in snapshot.records do
      match fields with
      | ["name", target] =>
        current := some target
      | [""] =>
        current := none
      | ["status", name] =>
        if let some target := current then
          statuses := statuses.insert target (Linger.Display.Status.ofName name)
      | _ =>
        pure ()
    return statuses

/-- The terminal bytes of a picker frame (`Picker.frameLines`). Keep the final column unused
so neither a full-width name nor a resize induces an automatic line wrap. -/
private def draw (state : Linger.Selector.Picker.State) (snapshot : Linger.Selector.Picker.Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (cols rows : UInt32) : String :=
  Id.run do
    let width := cols.toNat - 1
    let lines :=
      Linger.Selector.Picker.frameLines state snapshot statusOf loaded withColor savedTmux
        rows.toNat
    let mut frame := "\x1b[0m\x1b[H\x1b[2J"
    let mut first := true
    for line in lines do
      if !first then
        frame := frame ++ "\r\n"
      first := false
      let mut used := 0
      let mut clipped := false
      let mut activeStyle := ""
      for (text, style) in line do
        if clipped then
          break
        if style != activeStyle then
          frame := frame ++ "\x1b[0m" ++ style
          activeStyle := style
        for raw in text.toList do
          let c := if Linger.Selector.Input.printable raw then raw else '?'
          let cells := Linger.Terminal.Vt.charWidth c
          if used + cells > width then
            clipped := true
            break
          frame := frame.push c
          used := used + cells
      if !activeStyle.isEmpty then
        frame := frame ++ "\x1b[0m"
    return frame

/-- A native visit lists local rows every second but queries remote hosts again only
this long after its previous remote query completed: each host costs an SSH
connection. Meanwhile remote rows stay as that query reported them. -/
def remoteRefreshMs : Nat := 5000

/-- Own raw mode and at most one listing for one selection visit. Keys always
act on the displayed snapshot, which is returned on acceptance; a completed
replacement is applied afterward and rendered before polling again.
Saved-tmux and read-only visits have no creation choice. The first listing is cancellable too.
A native visit starts with a full listing, then lists local rows alone between
remote queries. Native listings get a cooperative stop so they can retire isolated SSH groups. -/
def choose (executable : String) (save : Option String := none) (readOnly : Bool := false) :
    IO Choice := do
  let savedTmux := save.isSome
  unless (← stdinIsTty) && (← (← IO.getStdout).isTty) do
    throw (IO.userError "the picker needs terminal input and output")
  let fullArgs :=
    if savedTmux then #["tmux", "ls", "--porcelain"] ++ save.toArray
    else #["ls", "-r", "--porcelain"]
  let pending ← IO.mkRef (none : Option Linger.Os.Shell.Command.Job)
  let withColor := (← IO.getEnv "NO_COLOR").isNone
  let saved ← termRaw stdinFd
  try
    writeAll stdoutFd "\x1b[?1049h\x1b[?25l\x1b[?2004h".toUTF8
    writeAll stdoutFd (ByteArray.mk (Linger.Terminal.Title.ansi "linger").toArray)
    let fds := #[stdinFd]
    let events := #[POLLIN]
    let mut state := Linger.Selector.Picker.init [] (!savedTmux && !readOnly)
    let mut snapshot : Linger.Selector.Picker.Snapshot := {}
    let mut statuses : Std.HashMap String Linger.Display.Status.Status := {}
    let mut loaded := false
    let mut decoder := Linger.Selector.Input.init
    let mut lastInput ← monotonicMs
    let mut nextListing := 0
    let mut full := true
    let mut lastFull : Linger.Selector.Picker.Snapshot := {}
    let mut nextRemote := 0
    let mut size := (0, 0)
    let mut lastFrame := ""
    let mut dirty := true
    while true do
      let current ← winsizeGet stdoutFd
      if dirty || current != size then
        let frame :=
          draw state snapshot (statuses.getD · .unknown) loaded withColor savedTmux current.1
            current.2
        if frame != lastFrame || current != size then
          writeAll stdoutFd frame.toUTF8
          lastFrame := frame
        size := current
        dirty := false
      let ready ← poll fds events 50
      let bits := ready[0]!
      if bits &&& POLLNVAL != 0 then
        throw (IO.userError "picker input descriptor became invalid")
      let mut keys : Array Linger.Selector.Key := #[]
      if bits &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        match ← read stdinFd 4096 with
        | none =>
          return .cancel
        | some bytes =>
          if !bytes.isEmpty then
            lastInput ← monotonicMs
          for byte in bytes do
            let (next, emitted) := Linger.Selector.Input.feed decoder byte
            decoder := next
            keys := keys ++ (emitted.filterMap Linger.Selector.Key.ofInput).toArray
      else if Linger.Selector.Input.pending decoder && (← monotonicMs) - lastInput ≥ 150 then
        let (next, emitted) := Linger.Selector.Input.flush decoder
        decoder := next
        keys := (emitted.filterMap Linger.Selector.Key.ofInput).toArray
      for key in keys do
        if !loaded && key == .accept then
          continue
        match Linger.Selector.Picker.step state key with
        | .stay next =>
          dirty := dirty || next != state
          state := next
        | .attach target | .create target =>
          return .attach target snapshot
        | .cancel =>
          return .cancel
      if let some result← Linger.Os.Shell.Command.poll pending then
        if result.exitCode != 0 then
          return .failed result.exitCode result.stderr
        let listed ← IO.ofExcept (Linger.Selector.Picker.parseSnapshot result.stdout)
        if full then
          lastFull := listed
          nextRemote := (← monotonicMs) + remoteRefreshMs
        let incoming := if full then listed else listed.withRemote lastFull
        -- what asks for someone first, as `ls` lists it (`View.sort`)
        let incomingStatuses := statusesOf incoming
        let ordered :=
          Linger.Display.View.sort (incomingStatuses.getD · .unknown) incoming.candidates
        let next :=
          if loaded then Linger.Selector.Picker.refresh state ordered
          else { (Linger.Selector.Picker.init ordered state.allowCreate) with query := state.query }
        dirty := dirty || !loaded || next != state || incoming != snapshot
        state := next
        snapshot := incoming
        statuses := incomingStatuses
        loaded := true
        nextListing := (← monotonicMs) + 1000
      if (← pending.get).isNone && (← monotonicMs) ≥ nextListing then
        full := savedTmux || (← monotonicMs) ≥ nextRemote
        let args := if full then fullArgs else #["ls", "--porcelain"]
        pending.set (some (← Linger.Os.Shell.Command.start executable args))
    return .cancel
  finally
    try
      try
        writeAll stdoutFd "\x1b[0m\x1b[?2004l\x1b[?25h\x1b[?1049l".toUTF8
        writeAll stdoutFd (ByteArray.mk (Linger.Terminal.Title.ansi "").toArray)
      finally
        termRestore stdinFd saved
    finally
      Linger.Os.Shell.Command.stop pending (if savedTmux then 0 else 1000)

/-- The exact attach argv for a chosen target. Its operands are the ones the attach
parser reads back as `target` (`targetArgs_targetOperands`). -/
def attachArgs (target : String) (readOnly : Bool := false) : Array String :=
  ("attach" :: (if readOnly then ["--read-only"] else []) ++
      Linger.Target.Remote.targetOperands target).toArray

/-- Execute either selected row through attach, after terminal restoration. Every attach
exit returns to a fresh listing; cancellation ends the manager. The caller
supplies one frozen absolute executable for all listing and attach children. -/
def run (executable : String) (readOnly : Bool := false) : IO UInt32 := do
  while true do
    match ← choose executable (readOnly := readOnly) with
    | .cancel =>
      return 130
    | .failed status stderr =>
      IO.eprintln s!"linger: could not list sessions (exit {status})"
      if !stderr.isEmpty then
        IO.eprint stderr
      return status
    | .attach target _ =>
      let child ← IO.Process.spawn { cmd := executable, args := attachArgs target readOnly }
      discard child.wait
  return 0

end Linger.Selector.Shell
