import Zmx.Posix
import Zmx.Core.Tui
import Zmx.Core.Remote
import Zmx.Core.Checkpoint
import Zmx.Core.Render
import Zmx.Runtime.Paths
import Zmx.Runtime.Client
import Zmx.Runtime.Cli
/-! # Zmx.Runtime.Tui — terminal shell around `Core.Tui.step`

Owns: raw mode + alt screen, key decoding, gathering rows (live via
socket info, resumable via checkpoints), preview fetching (history for
live sessions, checkpoint render for resumable ones), and executing
effects. Attach *exec*s the plain client — the TUI leaves the byte
path entirely (zmx philosophy).

Remote hosts (`~/.config/lzmx/remotes`, one host per line) are wired
in Step 9 via `Zmx.Core.Remote`.
-/

namespace Zmx.Runtime.Tui

open Zmx.Posix
open Zmx.Core.Tui
open Zmx.Runtime

/-- Decode one input chunk into keys (tiny scanner; unrecognized ESC
sequences are swallowed). -/
def decodeKeys (bs : List UInt8) : List Key :=
  let rec go : List UInt8 → List Key
    | [] => []
    | 0x1B :: 0x5B :: b :: rest =>
      (match b with
       | 0x41 => [Key.up]
       | 0x42 => [Key.down]
       | _ => []) ++ go rest
    | [0x1B] => [.esc]
    | 0x1B :: rest => .esc :: go rest
    | 0x0D :: rest => .enter :: go rest
    | 0x7F :: rest | 0x08 :: rest => .backspace :: go rest
    | 0x03 :: rest => .ctrlC :: go rest
    | 0x0E :: rest => .ctrlN :: go rest
    | 0x10 :: rest => .ctrlP :: go rest
    | 0x0A :: rest => .ctrlJ :: go rest
    | 0x0B :: rest => .ctrlK :: go rest
    | 0x18 :: rest => .ctrlX :: go rest
    | 0x12 :: rest => .ctrlR :: go rest
    | 0x11 :: rest => .ctrlQ :: go rest
    | b :: rest =>
      (if 0x20 ≤ b && b < 0x7F then [Key.char (Char.ofNat b.toNat)] else [])
        ++ go rest
  go bs

def previewLines : Nat := 40

/-- Resolve the remote-host list, once, at startup. `override` is the
`--remote` (`-r`) flag; when present it *replaces* the file (same
override-not-union rule as `LZMX_DIR`), otherwise the persistent set
comes from `~/.config/lzmx/remotes` (one host per line, `#` comments).
Duplicates are a hard error (`Remote.checkHosts`) — raised here, before
the alt-screen, so the message is actually visible. -/
def resolveRemotes (override : Option (List String)) : IO (List String) := do
  let raw ← match override with
    | some hs => pure hs
    | none => do
      let home := (← IO.getEnv "HOME").getD "/tmp"
      let path := s!"{home}/.config/lzmx/remotes"
      if ← System.FilePath.pathExists path then
        pure ((← IO.FS.readFile path).splitOn "\n")
      else pure []
  let hosts := (raw.map (·.trimAscii.toString)).filter
    (fun h => !h.isEmpty && !h.startsWith "#")
  match Zmx.Core.Remote.checkHosts hosts with
  | .ok l => return l
  | .error e => throw (IO.userError e)

/-- Ask one host for its sessions. Failures (host down, no lzmx there,
timeout) yield `[]` — a dead remote must never block the local picker.
`BatchMode=yes` keeps ssh from prompting inside the TUI. -/
def fetchRemote (host : String) : IO (List Row) := do
  let out ← try
      IO.Process.output {
        cmd := "ssh",
        args := #["-o", "BatchMode=yes", "-o", "ConnectTimeout=3", "--",
                  host, "lzmx", "list", "--porcelain"] }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  if out.exitCode != 0 then return []
  return (Zmx.Core.Remote.parse out.stdout).map (fun r => {
    name := r.name, host := .remote host,
    state := if r.live then .live else .resumable,
    cmd := r.cmd, labels := r.labels })

/-- Rows: live daemons (info query each) + resumable checkpoints +
the already-resolved remote hosts. -/
def gatherRows (remotes : List String) : IO (List Row) := do
  let live ← Paths.listSocketNames
  let ckpts ← Paths.listCkptNames
  let mut rows : List Row := []
  for name in live do
    match ← Zmx.Runtime.Cli.queryInfo name with
    | some info =>
      -- the row is named from the socket, not from the reply (§Row): a
      -- daemon too busy to answer still lists correctly
      rows := rows ++ [rowOfInfo name info]
    | none =>
      -- connect() itself failed: nothing is listening, the file is stale
      try IO.FS.removeFile (← Paths.socketPath name) catch _ => pure ()
  for name in ckpts do
    if !live.contains name then
      rows := rows ++ [{ name, state := .resumable }]
  -- remote hosts last: a slow ssh must not reorder local rows
  for host in remotes do
    rows := rows ++ (← fetchRemote host)
  return rows

/-- Live preview: ask the daemon for history, keep the tail. -/
partial def fetchLivePreview (name : String) : IO (List String) := do
  match ← Client.connect name with
  | none => return ["(gone)"]
  | some fd =>
    Client.sendMsg fd .history
    let mut dec : Zmx.Core.Wire.Decoder := {}
    let mut acc : ByteArray := .empty
    let mut go := true
    let deadline := (← monotonicMs) + 1500
    while go && (← monotonicMs) < deadline do
      let revs ← poll #[fd] #[POLLIN] 300
      if revs[0]! == 0 then continue
      match ← read fd 65536 with
      | none => go := false
      | some bs =>
        if bs.isEmpty then continue
        let (dec', msgs) := dec.feed bs.toList
        dec := dec'
        for m in msgs do
          match m with
          | .output payload => acc := acc ++ ByteArray.mk payload.toArray
          | .done => go := false
          | .err _ => go := false
          | _ => pure ()
    close fd
    let txt := (String.fromUTF8? acc).getD ""
    let lines := txt.splitOn "\n"
    return lines.drop (lines.length - previewLines)

/-- Resumable preview: render the checkpoint's screen tail. -/
def fetchCkptPreview (name : String) : IO (List String) := do
  let path ← Paths.ckptPath name
  let bytes ← try IO.FS.readBinFile path catch _ => return ["(unreadable)"]
  match Zmx.Core.Checkpoint.load bytes.toList with
  | some ck => return Zmx.Core.Render.previewLines ck.vt previewLines
  | none => return ["(corrupt checkpoint)"]

/-- Remote preview: `ssh host lzmx history <name>`, tail kept. Failure
is a message, never an exception. -/
def fetchRemotePreview (host name : String) : IO (List String) := do
  let out ← try
      IO.Process.output {
        cmd := "ssh",
        args := #["-o", "BatchMode=yes", "-o", "ConnectTimeout=3", "--",
                  host, "lzmx", "history", name] }
    catch _ => pure { exitCode := 1, stdout := "", stderr := "" }
  if out.exitCode != 0 then return [s!"({host}: unavailable)"]
  let lines := out.stdout.splitOn "\n"
  return lines.drop (lines.length - previewLines)

structure Term where
  saved : ByteArray

def enterTerm : IO Term := do
  let saved ← termRaw stdinFd
  writeAll stdoutFd "\x1b[?1049h\x1b[?25l".toUTF8  -- alt screen, hide cursor
  return { saved }

def leaveTerm (t : Term) : IO Unit := do
  writeAll stdoutFd "\x1b[?25h\x1b[?1049l\x1b[0m".toUTF8
  termRestore stdinFd t.saved

/-- Leave the TUI and become `lzmx attach <name>` (or ssh for remote —
step 9). Only returns on exec failure. -/
def execAttach (t : Term) (name : String) (host : Host) : IO Unit := do
  leaveTerm t
  let self ← IO.appPath
  match host with
  | .local => exec self.toString #["attach", name]
  | .remote h => exec "ssh" #["-t", h, "lzmx", "attach", name]

partial def runEffects (t : Term) (remotes : List String) (st : State) (effs : List Effect) :
    IO (State × Bool) := do
  let mut st := st
  let mut quit := false
  for eff in effs do
    match eff with
    | .quit => quit := true
    | .attach name host => execAttach t name host  -- no return on success
    | .create name => execAttach t name .local
    | .kill name host =>
      match host with
      | .local =>
        let _ ← Client.sendOnly name .kill
        -- a resumable session's "kill" is dropping its checkpoint
        try IO.FS.removeFile (← Paths.ckptPath name) catch _ => pure ()
      | .remote h =>
        let _ ← IO.Process.output { cmd := "ssh", args := #[h, "lzmx", "kill", name] }
    | .refresh =>
      let rows ← gatherRows remotes
      let (st', effs') := step st (.rowsUpdated rows)
      st := st'
      let (st'', more) ← runEffects t remotes st effs'
      st := st''
      quit := quit || more
    | .fetchPreview name host =>
      let rowState := (st.rows.find? (fun r => r.name == name)).map (·.state)
      let lines ← match host, rowState with
        | .local, some RowState.live => fetchLivePreview name
        | .local, _ => fetchCkptPreview name
        | .remote h, _ => fetchRemotePreview h name
      let (st', effs') := step st (.previewUpdated name host lines)
      st := st'
      let (st'', more) ← runEffects t remotes st effs'
      st := st''
      quit := quit || more
  return (st, quit)

partial def loop (t : Term) (remotes : List String) (st : State) : IO Unit := do
  writeAll stdoutFd (render st).toUTF8
  let revs ← poll #[stdinFd] #[POLLIN] 2000
  -- resize check (same poll-diff trick as the attach client)
  let (c, r) ← winsizeGet stdinFd
  let mut st := st
  let mut quit := false
  if c.toNat != st.cols || r.toNat != st.rows_ then
    let (st', effs) := step st (.resized c.toNat r.toNat)
    let (st'', q) ← runEffects t remotes st' effs
    st := st''
    quit := quit || q
  if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
    match ← read stdinFd 4096 with
    | none => quit := true
    | some bs =>
      for k in decodeKeys bs.toList do
        let (st', effs) := step st (.key k)
        let (st'', q) ← runEffects t remotes st' effs
        st := st''
        quit := quit || q
  else
    -- idle round: refresh rows (cheap; sessions come and go)
    let (st', q) ← runEffects t remotes st [.refresh]
    st := st'
    quit := quit || q
  if quit then
    leaveTerm t
  else
    loop t remotes st

/-- `remoteOverride` is the `--remote` (`-r`) flag (replaces the file
when present). Remotes are resolved + dup-checked here, *before* the alt
screen, so a bad list errors visibly instead of into a cleared screen. -/
def main (remoteOverride : Option (List String)) : IO UInt32 := do
  -- resolve + dup-check the host list first: an argv/config error should
  -- report itself even when piped, before the environment (tty) check
  let remotes ← resolveRemotes remoteOverride
  if !(← isatty stdinFd) then
    throw (IO.userError "the session manager needs a terminal")
  let rows ← gatherRows remotes
  let (c, r) ← winsizeGet stdinFd
  let st0 : State := { cols := c.toNat, rows_ := r.toNat }
  let (st1, effs) := step st0 (.rowsUpdated rows)
  let t ← enterTerm
  try
    let (st2, quit) ← runEffects t remotes st1 effs
    if !quit then loop t remotes st2 else leaveTerm t
  catch e =>
    leaveTerm t
    throw e
  return 0

end Zmx.Runtime.Tui
