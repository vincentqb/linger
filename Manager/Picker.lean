module

public import Tools.Picker
public import Tools.Input
public import Linger.Posix
public import Linger.Core.Vt

public section

/-! Terminal executor for the optional session selector. Selection and decoding
are pure tool modules; this module owns terminal lifetime and subprocesses. -/

namespace Manager.Picker

open Linger.Posix

private inductive Choice where
  | attach (target : String)
  | cancel
  | refresh

/-- Read one complete snapshot. A failed subprocess cannot supply candidates. -/
private def listing : IO (Except UInt32 (List String)) := do
  let out ← IO.Process.output { cmd := "linger", args := #["ls", "-r", "--porcelain"] }
  if out.exitCode != 0 then
    IO.eprintln s!"lz: could not list sessions (exit {out.exitCode})"
    if !out.stderr.isEmpty then
      IO.eprint out.stderr
    return .error out.exitCode
  return .ok (← IO.ofExcept (Tools.Picker.parseListing out.stdout))

/-- The viewport follows the bounded selection. Keep the final column unused
so neither a full-width name nor a resize induces an automatic line wrap.
In short terminals the selected row takes priority over the prompt and help. -/
private def draw (state : Tools.Picker.State) (cols rows : UInt32) : IO Unit := do
  let width := cols.toNat - 1
  let height := max 1 rows.toNat
  let names := Tools.Picker.visible state.candidates state.query
  let slots := max 1 (height - 2)
  let start := state.cursor + 1 - slots
  let mut lines := if height > 1 then #[(s!"lz> {state.query}", false)] else #[]
  let mut index := start
  for target in (names.drop start).take slots do
    let chosen := index == state.cursor
    lines := lines.push ((if chosen then "> " else "  ") ++ target, chosen)
    index := index + 1
  if height > 2 then
    let count := if names.isEmpty then "No matches" else s!"{names.length} sessions"
    lines := lines.push (s!"{count} | enter attach | esc quit | ctrl-r refresh", false)
  let mut frame := "\x1b[H\x1b[2J"
  let mut first := true
  for (text, chosen) in lines do
    if !first then
      frame := frame ++ "\r\n"
    first := false
    if chosen then
      frame := frame ++ "\x1b[7m"
    let mut used := 0
    for raw in text.toList do
      let c := if raw.toNat < 0x20 || (raw.toNat ≥ 0x7F && raw.toNat < 0xA0) then '?' else raw
      let cells := Linger.Core.Vt.charWidth c
      if used + cells > width then
        break
      frame := frame.push c
      used := used + cells
    if chosen then
      frame := frame ++ "\x1b[0m"
  writeAll stdoutFd frame.toUTF8

/-- Own raw mode for exactly one selection visit. Refresh leaves this scope as
well, so listing subprocesses run with the caller's normal terminal modes. -/
private def choose (candidates : List String) : IO Choice := do
  let saved ← termRaw stdinFd
  try
    writeAll stdoutFd "\x1b[?1049h\x1b[?25l\x1b[?2004h".toUTF8
    let fds := #[stdinFd]
    let events := #[POLLIN]
    let mut state := Tools.Picker.init candidates
    let mut decoder := Tools.Input.init
    let mut lastInput ← monotonicMs
    let mut size := (0, 0)
    let mut dirty := true
    while true do
      let current ← winsizeGet stdoutFd
      if dirty || current != size then
        draw state current.1 current.2
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
        match Tools.Picker.step state key with
        | .stay next =>
          state := next
          dirty := true
        | .attach target =>
          return .attach target
        | .cancel =>
          return .cancel
        | .refresh =>
          return .refresh
    return .cancel
  finally
    try
      writeAll stdoutFd "\x1b[0m\x1b[?2004l\x1b[?25h\x1b[?1049l".toUTF8
    finally
      termRestore stdinFd saved

private def attach (target : String) : IO UInt32 := do
  let child ← IO.Process.spawn { cmd := "linger", args := #["attach", target] }
  child.wait

/-- The manager delegates to ordinary linger argv after terminal restoration.
Only an explicit initial target or a proved selection can reach attach. -/
def run (loop : Bool) (initial : Option String) : IO UInt32 := do
  unless (← stdinIsTty) && (← (← IO.getStdout).isTty) do
    throw (IO.userError "the picker needs terminal input and output")
  if let some target := initial then
    let _ ← attach target
  while true do
    let snapshot ← listing
    match snapshot with
    | .error status =>
      return status
    | .ok candidates =>
      match ← choose candidates with
      | .cancel =>
        return 130
      | .refresh =>
        continue
      | .attach target =>
        let status ← attach target
        if !loop then
          return status
  return 0

end Manager.Picker
