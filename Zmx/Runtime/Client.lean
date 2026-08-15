import Zmx.Posix
import Zmx.Core.Wire
import Zmx.Core.Render
import Zmx.Runtime.Paths
/-! # Zmx.Runtime.Client — attach and one-shot conversations

The attach client is deliberately dumb: raw mode, forward stdin bytes
as `input` frames (watching for the detach key), write `output` frames
to stdout, resize on terminal size change (checked each poll round —
no signal handling needed), leave on `exited`/EOF. The daemon's
restore blob arrives as ordinary output.

Detach key: `ctrl-\` (0x1C), disabled by `LINGER_NO_DETACH_KEY`.
-/

namespace Zmx.Runtime.Client

open Zmx.Posix
open Zmx.Core.Wire (Msg Decoder encode)

def encodeBA (m : Msg) : ByteArray := ByteArray.mk (Zmx.Core.Wire.encode m).toArray

/-- Blocking connect to a session socket. `none` = no live daemon. -/
def connect (name : String) : IO (Option UInt32) := do
  let path ← Paths.socketPath name
  let r ← unixConnect path
  if r ≥ 0 then return some r.toUInt64.toUInt32
  return none

def sendMsg (fd : UInt32) (m : Msg) : IO Unit :=
  writeAll fd (encodeBA m)

/-- Read frames until the daemon closes or a terminator arrives.
Output payloads stream to stdout as they come. Returns the exit status
if the session reported one. -/
partial def drainReplies (fd : UInt32) (untilDone : Bool) : IO (Option UInt32) := do
  let mut dec : Decoder := {}
  let mut result : Option UInt32 := none
  let mut go := true
  while go do
    let revs ← poll #[fd] #[POLLIN] (-1)
    if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
      continue
    match ← read fd 65536 with
    | none => go := false
    | some bs =>
      if bs.isEmpty then continue
      let (dec', msgs) := dec.feed bs.toList
      dec := dec'
      if dec.errored then
        go := false
      for m in msgs do
        match m with
        | .output payload => writeAll stdoutFd (ByteArray.mk payload.toArray)
        | .infoReply payload => writeAll stdoutFd (ByteArray.mk payload.toArray)
        | .exited status =>
          result := some status
          go := false
        | .done =>
          if untilDone then go := false
        | .err msg =>
          let msgTxt := String.fromUTF8? (ByteArray.mk msg.toArray) |>.getD "error"
          IO.eprintln s!"linger: {msgTxt}"
          go := false
        | _ => pure ()
  return result

/-- Fire-and-forget: deliver one message, no reply expected. -/
def sendOnly (name : String) (m : Msg) : IO Bool := do
  match ← connect name with
  | none => return false
  | some fd =>
    sendMsg fd m
    close fd
    return true

/-- One-shot request/reply against a session. Returns false if there is
no live daemon. -/
def oneShot (name : String) (m : Msg) : IO Bool := do
  match ← connect name with
  | none => return false
  | some fd =>
    sendMsg fd m
    let _ ← drainReplies fd true
    close fd
    return true

/-- Split stdin bytes at the detach key. Returns (bytes-to-send,
detach?). Bytes after the key are dropped — we're leaving. -/
def splitDetach (bs : ByteArray) (enabled : Bool) : ByteArray × Bool :=
  if !enabled then (bs, false)
  else
    match bs.toList.findIdx? (· == 0x1C) with
    | none => (bs, false)
    | some i => (ByteArray.mk (bs.toList.take i).toArray, true)

/-- Interactive attach. `readOnly` attaches as a 0×0 observer: output
mirrors, keyboard is not forwarded (abduco's `-r`), detach key still
works. Returns the child's exit status when the session ended, none
when we detached. -/
partial def attach (fd : UInt32) (readOnly : Bool := false) : IO (Option UInt32) := do
  let detachEnabled := (← IO.getEnv "LINGER_NO_DETACH_KEY").isNone
  let (cols, rows) ← winsizeGet stdinFd
  if readOnly then
    sendMsg fd (.attach 0 0)
  else
    sendMsg fd (.attach cols rows)
  let saved ← termRaw stdinFd
  let mut lastSize := (cols, rows)
  let mut dec : Decoder := {}
  let mut result : Option UInt32 := none
  let mut leaving := false
  try
    while !leaving do
      let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] 200
      -- terminal resized? (polled: no signal machinery)
      let size ← winsizeGet stdinFd
      if size != lastSize && !readOnly then
        lastSize := size
        sendMsg fd (.resize size.1 size.2)
      -- stdin → daemon (read-only: only the detach key is honored)
      if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        match ← read stdinFd 65536 with
        | none => leaving := true
        | some bs =>
          if !bs.isEmpty then
            let (out, detach) := splitDetach bs detachEnabled
            if !out.isEmpty && !readOnly then
              sendMsg fd (.input out.toList)
            if detach then leaving := true
      -- daemon → stdout
      if revs[1]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        match ← read fd 65536 with
        | none =>
          leaving := true
          IO.eprintln "\r\nlinger: session closed"
        | some bs =>
          if !bs.isEmpty then
            let (dec', msgs) := dec.feed bs.toList
            dec := dec'
            if dec.errored then leaving := true
            for m in msgs do
              match m with
              | .output payload => writeAll stdoutFd (ByteArray.mk payload.toArray)
              | .exited status =>
                result := some status
                leaving := true
              | _ => pure ()
  finally
    -- hand the terminal back before the line discipline: the session's last
    -- program may have left the alt screen, mouse reporting, a scroll region or
    -- a line-drawing charset on, and termios restores none of that
    -- (`Render.leaveAnsi`). In `finally`, so every way out of the loop — detach
    -- key, session exit, EOF, a decoder error, an exception — goes through it.
    writeAll stdoutFd (ByteArray.mk Zmx.Core.Render.leaveAnsi.toArray)
    termRestore stdinFd saved
  close fd
  return result

end Zmx.Runtime.Client
