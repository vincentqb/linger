module

public import Tools.Picker
public import Tools.Input
public import Linger.Posix
public import Linger.Core.Vt

public section

/-! Terminal executor for the session selector. Selection and decoding
are pure tool modules; this module owns terminal lifetime and subprocesses. -/

namespace Manager.Picker

open Linger.Posix

private inductive Choice where
  | attach (target : String)
  | cancel
  | failed (status : UInt32) (stderr : String)

/-- The selector owns the listing group and both pipe readers until completion or
retirement. Only the input loop reaps its leader, keeping its PID reserved until
the group is retired. -/
private structure Listing where
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }
  stdout : Task (Except IO.Error String)
  stderr : Task (Except IO.Error String)

private def listing (executable : String) : IO Listing := do
  let child ←
    IO.Process.spawn
        { cmd := executable, args := #["ls", "-r", "--porcelain"], stdin := .null, stdout := .piped,
          stderr := .piped, setsid := true }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  return { child, stdout, stderr }

/-- Retire the isolated listing group before reaping its leader: a remote-listing
helper may still hold the pipes after the leader exits. Join both readers so no
task or reaper escapes selection. -/
private def Listing.stop (job : Listing) : IO Unit := do
  try
    try
      job.child.kill
    finally
      discard job.child.wait
  finally
    discard <| IO.wait job.stdout
    discard <| IO.wait job.stderr

/-- The viewport follows the bounded selection. Keep the final column unused
so neither a full-width name nor a resize induces an automatic line wrap.
In short terminals the selected row takes priority over decoration and help.
Before the first snapshot the query is editable, but there is no selectable row. -/
private def draw (state : Tools.Picker.State) (loaded : Bool) (cols rows : UInt32) : String :=
  Id.run do
    let width := cols.toNat - 1
    let height := max 1 rows.toNat
    let items := Tools.Picker.items state.candidates state.query
    let mut lines : Array (Array (String × String)) := #[]
    if height ≥ 7 then
      lines := lines.push #[("  linger", "")] |>.push #[]
    if height > 1 then
      let text := if state.query.isEmpty then "Find or create a session" else state.query
      let style := if state.query.isEmpty then "\x1b[2m" else ""
      lines := lines.push #[("  › ", ""), (text, style)]
      if height ≥ 6 then
        lines := lines.push #[]
    let footerRows := if height ≥ 6 then 2 else if height > 2 then 1 else 0
    let slots := max 1 (height - lines.size - footerRows)
    let start := state.cursor + 1 - slots
    if !loaded then
      lines := lines.push #[("  Loading sessions…", "\x1b[2m")]
    else if items.isEmpty then
      lines := lines.push #[("  No valid target", "\x1b[2m")]
    else
      let mut index := start
      for item in (items.drop start).take slots do
        let label :=
          match item with
          | .existing target => target
          | .create target => s!"+ Create {target}"
        let chosen := index == state.cursor
        let text := (if chosen then "  ▸ " else "    ") ++ label
        lines := lines.push #[(text, if chosen then "\x1b[7m" else "")]
        index := index + 1
    if height > 2 then
      if height ≥ 6 then
        lines := lines.push #[]
      let action :=
        if !loaded then "  Type to search"
        else
          match Tools.Picker.selected state with
          | some (.existing _) => "  ↵ attach"
          | some (.create _) => "  ↵ create"
          | none => "  Type a valid name"
      lines := lines.push #[(s!"{action}  ·  ↑↓ move  ·  esc / ^C quit", "\x1b[2m")]
    let mut frame := "\x1b[0m\x1b[H\x1b[2J"
    let mut first := true
    for line in lines do
      if !first then
        frame := frame ++ "\r\n"
      first := false
      let mut used := 0
      let mut clipped := false
      for (text, style) in line do
        if clipped then
          break
        frame := frame ++ style
        for raw in text.toList do
          let c := if raw.toNat < 0x20 || (raw.toNat ≥ 0x7F && raw.toNat < 0xA0) then '?' else raw
          let cells := Linger.Core.Vt.charWidth c
          if used + cells > width then
            clipped := true
            break
          frame := frame.push c
          used := used + cells
        if !style.isEmpty then
          frame := frame ++ "\x1b[0m"
    return frame

/-- Own raw mode and at most one listing for one selection visit. Keys always
act on the displayed snapshot; a completed replacement is applied afterward
and rendered before polling again. The first listing is cancellable too. -/
private def choose (executable : String) : IO Choice := do
  let pending ← IO.mkRef (none : Option Listing)
  let saved ← termRaw stdinFd
  try
    writeAll stdoutFd "\x1b[?1049h\x1b[?25l\x1b[?2004h".toUTF8
    let fds := #[stdinFd]
    let events := #[POLLIN]
    let mut state := Tools.Picker.init []
    let mut loaded := false
    let mut decoder := Tools.Input.init
    let mut lastInput ← monotonicMs
    let mut nextListing := 0
    let mut size := (0, 0)
    let mut lastFrame := ""
    let mut dirty := true
    while true do
      let current ← winsizeGet stdoutFd
      if dirty || current != size then
        let frame := draw state loaded current.1 current.2
        if frame != lastFrame || current != size then
          writeAll stdoutFd frame.toUTF8
          lastFrame := frame
        size := current
        dirty := false
      let ready ← poll fds events 50
      let bits := ready[0]!
      if bits &&& POLLNVAL != 0 then
        throw (IO.userError "picker input descriptor became invalid")
      let mut keys : Array Tools.Key := #[]
      if bits &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        match ← read stdinFd 4096 with
        | none =>
          return .cancel
        | some bytes =>
          if !bytes.isEmpty then
            lastInput ← monotonicMs
          for byte in bytes.toList do
            let (next, emitted) := Tools.Input.feed decoder byte
            decoder := next
            keys := keys ++ emitted.toArray
      else if Tools.Input.pending decoder && (← monotonicMs) - lastInput ≥ 150 then
        let (next, emitted) := Tools.Input.flush decoder
        decoder := next
        keys := emitted.toArray
      for key in keys do
        if !loaded && key == .accept then
          continue
        match Tools.Picker.step state key with
        | .stay next =>
          dirty := dirty || next != state
          state := next
        | .attach target | .create target =>
          return .attach target
        | .cancel =>
          return .cancel
      if let some job← pending.get then
        if (← IO.hasFinished job.stdout) && (← IO.hasFinished job.stderr) then
          if let some status← job.child.tryWait then
            pending.set none
            let stdout ← IO.ofExcept (← IO.wait job.stdout)
            let stderr ← IO.ofExcept (← IO.wait job.stderr)
            if status != 0 then
              return .failed status stderr
            let candidates ← IO.ofExcept (Tools.Picker.parseListing stdout)
            let next :=
              if loaded then Tools.Picker.refresh state candidates
              else { (Tools.Picker.init candidates) with query := state.query }
            dirty := dirty || !loaded || next != state
            state := next
            loaded := true
            nextListing := (← monotonicMs) + 1000
      if (← pending.get).isNone && (← monotonicMs) ≥ nextListing then
        pending.set (some (← listing executable))
    return .cancel
  finally
    try
      try
        writeAll stdoutFd "\x1b[0m\x1b[?2004l\x1b[?25h\x1b[?1049l".toUTF8
      finally
        termRestore stdinFd saved
    finally
      if let some job← pending.get then
        job.stop

/-- Execute either selected row through attach, after terminal restoration. Every attach
exit returns to a fresh listing; cancellation ends the manager. The caller
supplies one frozen absolute executable for all listing and attach children. -/
def run (executable : String) : IO UInt32 := do
  unless (← stdinIsTty) && (← (← IO.getStdout).isTty) do
    throw (IO.userError "the picker needs terminal input and output")
  while true do
    match ← choose executable with
    | .cancel =>
      return 130
    | .failed status stderr =>
      IO.eprintln s!"linger: could not list sessions (exit {status})"
      if !stderr.isEmpty then
        IO.eprint stderr
      return status
    | .attach target =>
      let child ← IO.Process.spawn { cmd := executable, args := #["attach", target] }
      discard child.wait
  return 0

end Manager.Picker
