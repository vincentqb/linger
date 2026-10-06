module

public import Linger.Tools.Picker
import Linger.Posix
import Linger.Core.Terminal
import Linger.Runtime.Command

public section

/-! Terminal executor for the session selector. Selection and decoding
are pure tool modules; this module owns terminal lifetime and subprocesses. -/

namespace Linger.Manager.Picker

open Linger.Posix

inductive Choice where
  | attach (target : String) (snapshot : Linger.Tools.Picker.Snapshot)
  | cancel
  | failed (status : UInt32) (stderr : String)

/-- The viewport follows the bounded selection. Keep the final column unused
so neither a full-width name nor a resize induces an automatic line wrap.
In short terminals the selected row takes priority over decoration and help.
Before the first snapshot the query is editable, but there is no selectable row. -/
private def draw (state : Linger.Tools.Picker.State) (snapshot : Linger.Tools.Picker.Snapshot)
    (loaded withColor : Bool) (cols rows : UInt32) : String :=
  Id.run do
    let width := cols.toNat - 1
    let height := max 1 rows.toNat
    let items := Linger.Tools.Picker.items state.candidates state.query state.allowCreate
    let nameCol :=
      Linger.Core.Listing.nameWidth (snapshot.candidates.map fun target => [("name", target)])
    let mut lines : Array (Array (String × String)) := #[]
    if height ≥ 7 then
      let title := if state.allowCreate then "  linger" else "  linger · tmux save"
      lines := lines.push #[(title, "")]
      if !state.allowCreate then
        let globals := snapshot.records.takeWhile (fun fields => fields.head? != some "name")
        let metadata :=
          globals.filterMap fun fields =>
            match fields with
            | ["source", value] => some s!"  source  {value}"
            | ["saved", value] => some s!"  saved   {value}"
            | _ => none
        for text in metadata.take (height - 7) do
          lines := lines.push #[(text, "\x1b[2m")]
      lines := lines.push #[]
    if height > 1 then
      let placeholder :=
        if state.allowCreate then "Find or create a session" else "Find a saved pane"
      let text := if state.query.isEmpty then placeholder else state.query
      let style := if state.query.isEmpty then "\x1b[2m" else ""
      lines := lines.push #[("  › ", ""), (text, style)]
      if height ≥ 6 then
        lines := lines.push #[]
    let footerRows := if height ≥ 6 then 2 else if height > 2 then 1 else 0
    let slots := max 1 (height - lines.size - footerRows)
    let start := state.cursor + 1 - slots
    if !loaded then
      let text := if state.allowCreate then "  Loading sessions…" else "  Loading saved panes…"
      lines := lines.push #[(text, "\x1b[2m")]
    else if items.isEmpty then
      let text := if state.allowCreate then "  No valid target" else "  No matching saved panes"
      lines := lines.push #[(text, "\x1b[2m")]
    else
      let mut index := start
      for item in (items.drop start).take slots do
        let chosen := index == state.cursor
        let selection := if chosen then "\x1b[7m" else ""
        let mut pieces := #[(if chosen then "  ▸ " else "    ", selection)]
        let chars := Linger.Tools.Picker.highlightedPresentation snapshot nameCol state.query item
        for char in Linger.Tools.Picker.emphasizeCells chars do
          let statusStyle :=
            if withColor then (char.status.map Linger.Core.Status.style).getD "" else ""
          let emphasis := if char.matched then "\x1b[4m" else ""
          pieces := pieces.push (String.singleton char.char, selection ++ statusStyle ++ emphasis)
        lines := lines.push pieces
        index := index + 1
    if height > 2 then
      if height ≥ 6 then
        lines := lines.push #[]
      let action :=
        if !loaded then "  Type to search"
        else
          match Linger.Tools.Picker.selected state with
          | some (.existing _) => if state.allowCreate then "  ↵ attach" else "  ↵ import / attach"
          | some (.create _) => "  ↵ create"
          | none => if state.allowCreate then "  Type a valid name" else "  Type to search"
      lines := lines.push #[(s!"{action}  ·  ↑↓ move  ·  esc / ^C quit", "\x1b[2m")]
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
          let c := if raw.toNat < 0x20 || (raw.toNat ≥ 0x7F && raw.toNat < 0xA0) then '?' else raw
          let cells := Linger.Core.Vt.charWidth c
          if used + cells > width then
            clipped := true
            break
          frame := frame.push c
          used := used + cells
      if !activeStyle.isEmpty then
        frame := frame ++ "\x1b[0m"
    return frame

/-- Own raw mode and at most one listing for one selection visit. Keys always
act on the displayed snapshot, which is returned on acceptance; a completed
replacement is applied afterward and rendered before polling again.
Saved-tmux visits have no creation choice. The first listing is cancellable too.
Native listings get a cooperative stop so they can retire isolated SSH groups. -/
def choose (executable : String) (savedTmux : Bool := false) (save : Option String := none) :
    IO Choice := do
  unless (← stdinIsTty) && (← (← IO.getStdout).isTty) do
    throw (IO.userError "the picker needs terminal input and output")
  let args :=
    if savedTmux then #["tmux", "ls", "--porcelain"] ++ save.toArray
    else #["ls", "-r", "--porcelain"]
  let pending ← IO.mkRef (none : Option Linger.Runtime.Command.Job)
  let withColor := (← IO.getEnv "NO_COLOR").isNone
  let saved ← termRaw stdinFd
  try
    writeAll stdoutFd "\x1b[?1049h\x1b[?25l\x1b[?2004h".toUTF8
    writeAll stdoutFd (ByteArray.mk (Linger.Core.Terminal.Title.ansi "linger").toArray)
    let fds := #[stdinFd]
    let events := #[POLLIN]
    let mut state := Linger.Tools.Picker.init [] (!savedTmux)
    let mut snapshot : Linger.Tools.Picker.Snapshot := {}
    let mut loaded := false
    let mut decoder := Linger.Tools.Input.init
    let mut lastInput ← monotonicMs
    let mut nextListing := 0
    let mut size := (0, 0)
    let mut lastFrame := ""
    let mut dirty := true
    while true do
      let current ← winsizeGet stdoutFd
      if dirty || current != size then
        let frame := draw state snapshot loaded withColor current.1 current.2
        if frame != lastFrame || current != size then
          writeAll stdoutFd frame.toUTF8
          lastFrame := frame
        size := current
        dirty := false
      let ready ← poll fds events 50
      let bits := ready[0]!
      if bits &&& POLLNVAL != 0 then
        throw (IO.userError "picker input descriptor became invalid")
      let mut keys : Array Linger.Tools.Key := #[]
      if bits &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        match ← read stdinFd 4096 with
        | none =>
          return .cancel
        | some bytes =>
          if !bytes.isEmpty then
            lastInput ← monotonicMs
          for byte in bytes.toList do
            let (next, emitted) := Linger.Tools.Input.feed decoder byte
            decoder := next
            keys := keys ++ (emitted.filterMap Linger.Tools.Key.ofInput).toArray
      else if Linger.Tools.Input.pending decoder && (← monotonicMs) - lastInput ≥ 150 then
        let (next, emitted) := Linger.Tools.Input.flush decoder
        decoder := next
        keys := (emitted.filterMap Linger.Tools.Key.ofInput).toArray
      for key in keys do
        if !loaded && key == .accept then
          continue
        match Linger.Tools.Picker.step state key with
        | .stay next =>
          dirty := dirty || next != state
          state := next
        | .attach target | .create target =>
          return .attach target snapshot
        | .cancel =>
          return .cancel
      if let some result← Linger.Runtime.Command.poll pending then
        if result.exitCode != 0 then
          return .failed result.exitCode result.stderr
        let incoming ← IO.ofExcept (Linger.Tools.Picker.parseSnapshot result.stdout)
        let next :=
          if loaded then Linger.Tools.Picker.refresh state incoming.candidates
          else
            { (Linger.Tools.Picker.init incoming.candidates state.allowCreate) with
              query := state.query }
        dirty := dirty || !loaded || next != state || incoming != snapshot
        state := next
        snapshot := incoming
        loaded := true
        nextListing := (← monotonicMs) + 1000
      if (← pending.get).isNone && (← monotonicMs) ≥ nextListing then
        pending.set (some (← Linger.Runtime.Command.start executable args))
    return .cancel
  finally
    try
      try
        writeAll stdoutFd "\x1b[0m\x1b[?2004l\x1b[?25h\x1b[?1049l".toUTF8
        writeAll stdoutFd (ByteArray.mk (Linger.Core.Terminal.Title.ansi "").toArray)
      finally
        termRestore stdinFd saved
    finally
      Linger.Runtime.Command.stop pending (if savedTmux then 0 else 1000)

/-- Execute either selected row through attach, after terminal restoration. Every attach
exit returns to a fresh listing; cancellation ends the manager. The caller
supplies one frozen absolute executable for all listing and attach children. -/
def run (executable : String) : IO UInt32 := do
  while true do
    match ← choose executable with
    | .cancel =>
      return 130
    | .failed status stderr =>
      IO.eprintln s!"linger: could not list sessions (exit {status})"
      if !stderr.isEmpty then
        IO.eprint stderr
      return status
    | .attach target _ =>
      let child ← IO.Process.spawn { cmd := executable, args := #["attach", target] }
      discard child.wait
  return 0

end Linger.Manager.Picker
