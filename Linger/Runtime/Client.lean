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
to stdout, resize on terminal size change (checked each poll round —
no signal handling needed), leave on `exited`/EOF. The daemon's
restore blob arrives as ordinary output.

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
  if r ≥ 0 then return some r.toUInt64.toUInt32
  return none

def sendMsg (fd : UInt32) (m : Msg) : IO Unit :=
  writeAll fd (encodeBA m)

/-- Read frames until the daemon closes or a terminator arrives.
Output payloads stream to stdout as they come. Returns the exit status
if the session reported one. -/
def drainReplies (fd : UInt32) (untilDone : Bool) : IO (Option UInt32) := do
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

/-- How a bounded request/reply drain ended: `.done` arrived, the daemon
answered `.err` (message already printed), or it went silent/EOF'd without
either. -/
inductive Drained where
  | done
  | refused
  | silent
  deriving Repr, DecidableEq

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
      go := false  -- a full window of silence: no daemon is going to answer
    else
      match ← read fd 65536 with
      | none => go := false
      | some bs =>
        if bs.isEmpty then continue
        let (dec', msgs) := dec.feed bs.toList
        dec := dec'
        if dec.errored then go := false
        for m in msgs do
          match m with
          | .output payload => writeAll stdoutFd (ByteArray.mk payload.toArray)
          | .infoReply payload => writeAll stdoutFd (ByteArray.mk payload.toArray)
          | .done =>
            result := .done
            go := false
          | .err msg =>
            let msgTxt := String.fromUTF8? (ByteArray.mk msg.toArray) |>.getD "error"
            IO.eprintln s!"linger: {msgTxt}"
            result := .refused
            go := false
          | _ => pure ()
  return result

/-- Split stdin bytes at the detach key. Returns (bytes-to-send,
detach?). Bytes after the key are dropped — we're leaving. -/
def splitDetach (bs : ByteArray) (enabled : Bool) : ByteArray × Bool :=
  if !enabled then (bs, false)
  else
    match bs.toList.findIdx? (· == 0x1C) with
    | none => (bs, false)
    | some i => (ByteArray.mk (bs.toList.take i).toArray, true)

/-- How an interactive attach ended.

**A sum type rather than an `Option UInt32`**, for the reason
`Core.Listing.Row` gives: each constructor carries exactly the facts its case
has, so no caller can report one case as another. The `Option` could not say
"refused" — a daemon that answers `.err` (a `too many clients` roster refusal)
closed the connection immediately after, so the loop saw a clean EOF and
returned `none`, and `Cli` printed `detached from '<name>'` for an attach that
never happened. The refusal message was dropped on the floor: only
`drainReplies` (the one-shot path) ever printed `.err`. -/
inductive Outcome where
  /-- The session's child exited with this status. -/
  | ended (status : UInt32)
  /-- We left; the session lives on. -/
  | detached
  /-- The daemon refused the attach and said why. -/
  | refused (msg : String)
  deriving Repr, Inhabited

/-- Interactive attach. `readOnly` attaches as a 0×0 observer: output
mirrors, keyboard is not forwarded (abduco's `-r`), detach key still
works. -/
def attach (fd : UInt32) (readOnly : Bool := false) : IO Outcome := do
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
                result := .ended status
                leaving := true
              | .err msg =>
                -- a roster refusal ("too many clients") or other daemon error:
                -- carry the message out so `Cli` reports the refusal instead of
                -- a phantom detach. Scrubbed like any byte stream reaching a
                -- terminal — the message is our daemon's, but the socket is not
                -- a trusted channel. The daemon closes right after, so leaving.
                result := .refused (Linger.Core.Remote.scrub
                  (String.fromUTF8? (ByteArray.mk msg.toArray) |>.getD "refused"))
                leaving := true
              | _ => pure ()
  finally
    -- hand the terminal back before the line discipline: the session's last
    -- program may have left the alt screen, mouse reporting, a scroll region or
    -- a line-drawing charset on, and termios restores none of that
    -- (`Render.leaveAnsi`). In `finally`, so every way out of the loop — detach
    -- key, session exit, EOF, a decoder error, an exception — goes through it.
    writeAll stdoutFd (ByteArray.mk Linger.Core.Render.leaveAnsi.toArray)
    termRestore stdinFd saved
  close fd
  return result

end Linger.Runtime.Client
