module

import Linger.Posix
public import Linger.Core.Wire
import Linger.Core.Terminal
import Linger.Core.Remote
import Linger.Core.Title
import Linger.Core.Status
import Linger.Runtime.Paths
import Linger.Runtime.Command

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

/-- Connect to a session socket. A nonblocking attempt can fail while a live
listener is busy, so callers must not treat that failure as proof of absence. -/
def connect (name : String) (nonblocking : Bool := false) : IO (Option UInt32) := do
  let path ← Paths.socketPath name
  let r ← unixConnect path nonblocking
  if r ≥ 0 then
    let fd := r.toUInt64.toUInt32
    try
      Paths.checkSpelling path
      return some fd
    catch err =>
      close fd
      throw err
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
  repeat
    let revs ← poll #[fd] #[POLLIN] (-1)
    if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
      continue
    match ← read fd 65536 with
    | none =>
      return .lost "connection lost"
    | some bs =>
      if bs.isEmpty then
        continue
      let (dec', msgs) := dec.feed bs.toList
      dec := dec'
      if dec.errored then
        return .lost "invalid response from daemon"
      for m in msgs do
        match m with
        | .output payload | .infoReply payload =>
          writeAll stdoutFd (ByteArray.mk payload.toArray)
        | .exited status =>
          return .exited status
        | .done =>
          if untilDone then
            return .done
        | .err msg =>
          return .refused (replyText "request refused" msg)
        | _ =>
          pure ()

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
  repeat
    let revs ← poll #[fd] #[POLLIN] silenceMs
    if revs[0]! &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
      return .silent
    match ← read fd 65536 with
    | none =>
      return .lost "connection lost"
    | some bs =>
      if bs.isEmpty then
        continue
      let (dec', msgs) := dec.feed bs.toList
      dec := dec'
      if dec.errored then
        return .lost "invalid response from daemon"
      for m in msgs do
        match m with
        | .output payload | .infoReply payload =>
          writeAll stdoutFd (ByteArray.mk payload.toArray)
        | .done =>
          return .done
        | .exited status =>
          return .exited status
        | .err msg =>
          return .refused (replyText "request refused" msg)
        | _ =>
          pure ()

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
def attach (name : String) (fd : UInt32) (readOnly : Bool := false) : IO Outcome := do
  try
    let detachEnabled := (← IO.getEnv "LINGER_NO_DETACH_KEY").isNone
    let self ← IO.appPath
    let pending ← IO.mkRef (none : Option Command.Job)
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
    let mut nextSummary : Nat := 0
    let mut summary := ""
    let mut observer := Linger.Core.Vt.Vt.init 1 1
    let mut receivedOutput := false
    let mut titleDirty := false
    try
      while !leaving do
        try
          if let some output← Command.poll pending then
            let fresh :=
              if output.exitCode == 0 then output.stdout.trimAscii.toString
              else String.singleton (Linger.Core.Status.icon .unknown)
            titleDirty := titleDirty || fresh != summary
            summary := fresh
            nextSummary := (← monotonicMs) + 1000
          if (← pending.get).isNone && (← monotonicMs) ≥ nextSummary then
            pending.set (some (← Command.start self.toString #["status"]))
        catch _ =>
          summary := String.singleton (Linger.Core.Status.icon .unknown)
          titleDirty := true
          nextSummary := (← monotonicMs) + 1000
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
                    observer := observer.observe payload
                    receivedOutput := true
                    -- Reassert even if the application repeats the same OSC title.
                    titleDirty := true
                  | .exited status =>
                    result := .ended status
                    leaving := true
                  | .err msg =>
                    result := .refused (replyText "attach refused" msg)
                    leaving := true
                  | _ =>
                    pure ()
        if receivedOutput && titleDirty && !leaving then
          let title :=
            Linger.Core.Title.compose name observer.windowTitle summary
              Linger.Core.Terminal.Title.maxChars
          let bytes := Linger.Core.Terminal.Title.update observer title
          if !bytes.isEmpty then
            writeAll stdoutFd (ByteArray.mk bytes.toArray)
            titleDirty := false
    finally
      -- These cleanups are nested, not sequential: a broken stdout must not
      -- prevent termios restoration, and neither failure may leak the socket.
      try
        try
          writeAll stdoutFd (ByteArray.mk Linger.Core.Render.leaveAnsi.toArray)
        finally
          termRestore stdinFd saved
      finally
        Command.stop pending
    return result
  finally
    close fd

end Linger.Runtime.Client
