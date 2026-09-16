module

public import Linger.Posix
public import Linger.Core.Wire
public import Linger.Core.Render
public import Linger.Core.Remote
public import Linger.Runtime.Paths

public section

/-! # Linger.Runtime.Client — attach and one-shot conversations

The attach client is deliberately dumb: raw mode, forward stdin bytes
as `input` frames (watching for the detach key), write `output` frames
to stdout, resize on terminal size change (checked each poll round), and
report detach, child exit, daemon refusal, or transport loss distinctly.

Detach key: `ctrl-\` (0x1C), disabled by `LINGER_NO_DETACH_KEY`.
-/

namespace Linger.Runtime.Client

open Linger.Posix
open Linger.Core.Wire (Msg Decoder encode)

def encodeBA (m : Msg) : ByteArray := ByteArray.mk (Linger.Core.Wire.encode m).toArray

/-- Blocking connect to a session socket. `none` = no live daemon. -/
def connect (name : String) : IO (Option UInt32) := do
  let path ← Paths.socketPath name
  let r ← unixConnect path
  if r ≥ 0 then
    return some r.toUInt64.toUInt32
  return none

def sendMsg (fd : UInt32) (m : Msg) : IO Unit := writeAll fd (encodeBA m)

/-- How a request/reply conversation ended. Messages stay data until the CLI
chooses an exit status and diagnostic; a refusal or transport loss cannot collapse
into ordinary completion. -/
inductive Drained where
  | done
  | exited (status : UInt32)
  | refused (why : String)
  | lost (why : String)
  | silent

/-- Untrusted daemon text made safe for stderr. -/
def replyText (fallback : String) (bytes : List UInt8) : String :=
  Linger.Core.Remote.scrub (String.fromUTF8? (ByteArray.mk bytes.toArray) |>.getD fallback)

/-- Read frames until the daemon closes or the requested terminator arrives. -/
def drainReplies (fd : UInt32) (untilDone : Bool) : IO Drained := do
  let mut dec : Decoder := {}
  let mut result : Drained := .lost "connection lost"
  let mut go := true
  while go do
    let revs ← poll #[fd] #[POLLIN] (-1)
    if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
      continue
    match ← read fd 65536 with
    | none =>
      go := false
    | some bs =>
      if bs.isEmpty then
        continue
      let (dec', msgs) := dec.feed bs.toList
      dec := dec'
      if dec.errored then
        result := .lost "invalid response from daemon"
        go := false
      else
        for m in msgs do
          if !go then
            continue
          match m with
          | .output payload | .infoReply payload =>
            writeAll stdoutFd (ByteArray.mk payload.toArray)
          | .exited status =>
            result := .exited status
            go := false
          | .done =>
            if untilDone then
              result := .done
              go := false
          | .err msg =>
            result := .refused (replyText "request refused" msg)
            go := false
          | _ =>
            pure ()
  return result

/-- Fire-and-forget: deliver one message, no reply expected. -/
def sendOnly (name : String) (m : Msg) : IO Bool := do
  match ← connect name with
  | none =>
    return false
  | some fd =>
    try
      sendMsg fd m
      return true
    finally
      close fd

/-- One-shot request/reply. `none` means no live daemon; every connected
conversation preserves its actual outcome. -/
def oneShot (name : String) (m : Msg) : IO (Option Drained) := do
  match ← connect name with
  | none =>
    return none
  | some fd =>
    try
      sendMsg fd m
      return some (← drainReplies fd true)
    finally
      close fd

/-- Like `drainReplies untilDone := true`, but gives up after `silenceMs` of
*silence*. For the one-shot verbs a pre-upgrade daemon does not know: an
unknown tag is dropped without a trace (Wire §Frame), so a daemon from before
the verb existed replies nothing at all, and the untimed drain would hang the
client forever — the deadline has to be owned here. Output payloads stream to
stdout as they come (`capture` is such a stream); the timeout is per poll
round, so a long reply that keeps arriving never trips it. -/
def drainBounded (fd : UInt32) (silenceMs : Int32 := 2000) : IO Drained := do
  let mut dec : Decoder := {}
  let mut result : Drained := .silent
  let mut go := true
  while go do
    let revs ← poll #[fd] #[POLLIN] silenceMs
    if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
      go := false
    else
      match ← read fd 65536 with
      | none =>
        result := .lost "connection lost"
        go := false
      | some bs =>
        if bs.isEmpty then
          continue
        let (dec', msgs) := dec.feed bs.toList
        dec := dec'
        if dec.errored then
          result := .lost "invalid response from daemon"
          go := false
        else
          for m in msgs do
            if !go then
              continue
            match m with
            | .output payload | .infoReply payload =>
              writeAll stdoutFd (ByteArray.mk payload.toArray)
            | .done =>
              result := .done
              go := false
            | .exited status =>
              result := .exited status
              go := false
            | .err msg =>
              result := .refused (replyText "request refused" msg)
              go := false
            | _ =>
              pure ()
  return result

/-- Split stdin bytes at the detach key. Returns (bytes-to-send,
detach?). Bytes after the key are dropped — we're leaving. -/
def splitDetach (bs : ByteArray) (enabled : Bool) : ByteArray × Bool :=
  if !enabled then (bs, false)
  else
    match bs.toList.findIdx? (· == 0x1C) with
    | none => (bs, false)
    | some i => (ByteArray.mk (bs.toList.take i).toArray, true)

/-- How an interactive attach ended. Each constructor carries exactly the facts
its case has, so a refusal or lost daemon cannot be reported as a detach. -/
inductive Outcome where
  /-- The session's child exited with this status. -/
  | ended (status : UInt32)
  /-- We left; the session lives on. -/
  | detached
  /-- The daemon refused the attach and said why. -/
  | refused (msg : String)
  /-- The socket closed or its framing became invalid before an outcome. -/
  | lost (why : String)
  deriving Repr, Inhabited

/-- Interactive attach. `readOnly` attaches as a 0×0 observer: output
mirrors, keyboard is not forwarded, detach key still works. -/
def attach (fd : UInt32) (readOnly : Bool := false) : IO Outcome := do
  try
    let detachEnabled := (← IO.getEnv "LINGER_NO_DETACH_KEY").isNone
    let (cols, rows) ← winsizeGet stdinFd
    if readOnly then
      sendMsg fd (.attach 0 0)
    else
      sendMsg fd (.attach cols rows)
    let saved ← termRaw stdinFd
    let mut lastSize := (cols, rows)
    let mut dec : Decoder := {}
    let mut result : Outcome := .detached
    let mut leaving := false
    try
      while !leaving do
        let revs ← poll #[stdinFd, fd] #[POLLIN, POLLIN] 200
        let size ← winsizeGet stdinFd
        if size != lastSize && !readOnly then
          lastSize := size
          sendMsg fd (.resize size.1 size.2)
        if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
          match ← read stdinFd 65536 with
          | none =>
            leaving := true
          | some bs =>
            if !bs.isEmpty then
              let (out, detach) := splitDetach bs detachEnabled
              if !out.isEmpty && !readOnly then
                sendMsg fd (.input out.toList)
              if detach then
                leaving := true
        if revs[1]! &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
          match ← read fd 65536 with
          | none =>
            result := .lost "connection lost"
            leaving := true
          | some bs =>
            if !bs.isEmpty then
              let (dec', msgs) := dec.feed bs.toList
              dec := dec'
              if dec.errored then
                result := .lost "invalid response from daemon"
                leaving := true
              else
                for m in msgs do
                  if leaving then
                    continue
                  match m with
                  | .output payload =>
                    writeAll stdoutFd (ByteArray.mk payload.toArray)
                  | .exited status =>
                    result := .ended status
                    leaving := true
                  | .err msg =>
                    result := .refused (replyText "attach refused" msg)
                    leaving := true
                  | _ =>
                    pure ()
    finally
      -- These cleanups are nested, not sequential: a broken stdout must not
      -- prevent termios restoration, and neither failure may leak the socket.
      try
        writeAll stdoutFd (ByteArray.mk Linger.Core.Render.leaveAnsi.toArray)
      finally
        termRestore stdinFd saved
    return result
  finally
    close fd

end Linger.Runtime.Client
