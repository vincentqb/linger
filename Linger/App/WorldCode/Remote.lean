module

public import Linger.App.CoreSpec
public import Linger.Target.CoreSpec
import Linger.App.CoreCode.Serve
import Linger.App.CoreCode.Base64
import Linger.App.CoreCode.Codec
import Linger.Target.CoreCode.Remote
import Linger.Session.CoreCode.Wire
import Os.WorldCode
public import Os.WorldCode.Command
import Std.Sync.Mutex

public section

/-! # Linger.App.Remote — a host's `serve`, through its transport

Every command on a remote session runs `linger serve` on the host through the host's transport
(`Remote.argv`), and nothing else, and talks to it as any client of `serve` does: it writes the
handshake and its call, one JSON-RPC message a line, on the transport's standard input, and reads
what the host's `serve` writes, a line at a time, on its standard output (`ask`, `stream`). No word
of the request reaches a shell. The transport shares this process's terminal when the caller lets
it, as ssh asking for a password needs, and otherwise leads a process group of its own.

A remote attach is a bridge (`bridge`): once the host's `serve` has shaken hands, it hands the
attach client one end of a connected pair of sockets, on which the client converses as it does
with a daemon, relays the host's `session/attach` stream to it as the frames of the bytes it
carries (`Serve.Remote.relay`), and what the client sends as the attach's conversation, its keys,
its terminal's size and its leaving (`Serve.Remote.up`, `Serve.Remote.leave`). -/

namespace Linger.App.Remote

open Os.Shell
open Linger.App.Serve

/-- What a host's `serve` told a command: its answer (`Serve.Remote.heard`), and what the
transport wrote to its standard error, a line each. -/
structure Asked where
  /-- What the host's `serve` answered. -/
  heard : Serve.Remote.Heard
  /-- The lines the transport wrote to its standard error. -/
  errors : List String
  /-- Why the first line the host's `serve` wrote that is not canonical JSON is not, if one is not:
  a linger whose `serve` writes other JSON, which linger reads none of. -/
  unread : Option String := none

/-- The lines of what a transport wrote to its standard error, as clean text, empty ones left out. -/
private def errorLines (text : String) : List String :=
  ((text.splitOn "\n").map Linger.Target.Remote.scrub).filter fun line => !line.trimAscii.isEmpty

/-- Start the host's `serve` through `transport`, sharing this process's terminal when `terminal`
lets it. -/
private def start (transport : Linger.Target.Remote.Transport) (terminal : Bool) :
    IO (Option Command.Talk) := do
  match Linger.Target.Remote.argv transport with
  | cmd :: args =>
    return some (← Command.talk cmd args.toArray (isolated := !terminal))
  | [] =>
    return none

/-- A line a host's `serve` wrote, read as canonical JSON (`Value.parse`); a line that is not is no
message, and the first such line's reason, ExactJSON's, is kept in `unread`. -/
private def readLine (unread : IO.Ref (Option String)) (line : String) :
    IO (Option ExactJSON.Value) := do
  match ExactJSON.Value.parse line with
  | .ok message =>
    return some message
  | .error why =>
    if (← unread.get).isNone then
      unread.set (some why)
    return none

/-- The messages a host's `serve` writes until its output ends, each line read as canonical JSON
(`readLine`). -/
private def readAll (talk : Command.Talk) (unread : IO.Ref (Option String)) :
    IO (List ExactJSON.Value) := do
  let mut messages := #[]
  repeat
    match ← talk.line with
    | none =>
      break
    | some line =>
      if let some message← readLine unread line then
        messages := messages.push message
  return messages.toList

/-- The message a host's `serve` writes next that answers the request with the number `n`, the
messages before it skipped; none once its output ends first. -/
private def answerTo (talk : Command.Talk) (unread : IO.Ref (Option String)) (n : Int) :
    IO (Option ExactJSON.Value) := do
  repeat
    match ← talk.line with
    | none =>
      return none
    | some line =>
      if let some message← readLine unread line then
        if (member? "id" message).bind Id.of == some (.number n) then
          return some message
  return none

/-- End the conversation: end the host's input, read what it still writes, wait for its transport
to end, and read what it told linger, `before` the messages it wrote first. -/
private def finish (talk : Command.Talk) (unread : IO.Ref (Option String))
    (before : List ExactJSON.Value) : IO Asked := do
  talk.hangUp
  let rest ← readAll talk unread
  let status ← talk.finish
  return { heard := Serve.Remote.heard (before ++ rest) status,
           errors := errorLines (← talk.errors), unread := ← unread.get }

/-- **Ask a host's `serve`** of a call: write the handshake and the call (`Serve.Remote.lines`),
end its input, read what it writes until it ends, and read what it told linger
(`Serve.Remote.heard`). -/
def ask (transport : Linger.Target.Remote.Transport) (terminal : Bool) (method : String)
    (params : ExactJSON.Value) : IO Asked := do
  let some talk ← start transport terminal | return { heard := .silent, errors := [] }
  let unread ← IO.mkRef none
  try
    discard <| talk.say (Serve.Remote.lines method params)
    finish talk unread []
  catch err =>
    talk.stop
    throw err

/-- **Send standard input to a host's session as it comes**: after the handshake, each read of
`read` until it ends as one `session/send` of the session `name`, request 2, each answered before
the next is written, so that the session's program gets them in order; what the host answered the
last, or the first that was not `done`. -/
def stream (transport : Linger.Target.Remote.Transport) (terminal : Bool) (name : String)
    (read : IO (Option ByteArray)) : IO Asked := do
  let some talk ← start transport terminal | return { heard := .silent, errors := [] }
  let unread ← IO.mkRef none
  try
    discard <| talk.say Serve.Remote.handshake
    let some hello ← answerTo talk unread 1 | finish talk unread []
    unless Serve.Remote.shook [hello] do
      return ← finish talk unread [hello]
    let mut last : List ExactJSON.Value := [hello]
    let mut sent := false
    repeat
      let chunk ← read
      if chunk.isNone && sent then
        break
      -- an input that ends at once is sent as no bytes, which the host answers as `send -` would
      let bytes := chunk.getD ByteArray.empty
      if bytes.isEmpty && chunk.isSome then
        continue
      sent := true
      discard <|
          talk.say
            (Serve.Remote.request 2 "session/send"
              (ExactJSON.toValue ({ data := Base64.encode bytes.toList, name } : Sending)))
      let some answered ← answerTo talk unread 2 | return ← finish talk unread [hello]
      last := [hello, answered]
      unless Serve.Remote.heard last 0 matches .answered .done _ do
        break
      if chunk.isNone then
        break
    let asked ← finish talk unread []
    if asked.heard matches .refused then
      return asked
    return { asked with heard := Serve.Remote.heard last 0 }
  catch err =>
    talk.stop
    throw err

/-- A remote attach's bridge: the end of the connection the attach client converses on, and how
to wait for the bridge to end once the client has let it go, with what the host answered of the
attach: its request's answer, or how its stream closed. -/
structure Bridge where
  /-- The attach client's end of the connection. -/
  fd : UInt32
  /-- Wait for the bridge to end, once the client has closed its end. -/
  join : IO Asked

/-- How long a host's `serve` may take to end once its attach is let go before its transport is
stopped. -/
def endMs : Nat := 5000

/-- Write `messages` to the client's connection, `ours`, whole, one writer at a time (`lock`), so that
no two writes interleave their frames; a client that let its connection go takes nothing. -/
private def tell (lock : Std.Mutex Unit) (ours : UInt32) (messages : List Linger.Session.Wire.Msg) :
    IO Unit :=
  lock.atomically do
    try
      writeAll ours (ByteArray.mk (messages.flatMap Linger.Session.Wire.encode).toArray)
    catch _ =>
      pure ()

/-- Relay what the host's `serve` writes for the attach `id` to the client's connection, over
`ours`, as frames (`Serve.Remote.relay`), keeping in `final` the host's answer of the attach, its
request's and then its stream's `closed`, until the host's output ends; a stream that ends without
ending the attach tells the client its connection was lost. -/
private def relayDown (talk : Command.Talk) (unread : IO.Ref (Option String))
    (lock : Std.Mutex Unit) (ours : UInt32) (id : Id) (final : IO.Ref (Option ExactJSON.Value)) :
    IO Unit := do
  let mut ended := false
  repeat
    let some line ← talk.line | break
    let some message ← readLine unread line | continue
    if (member? "id" message).bind Id.of == some id then
      match member? "result" message, (member? "error" message).bind (member? "data") with
      | some result, _ =>
        final.set (some result)
      | none, some data =>
        final.set (some data)
      | none, none =>
        pure ()
    if member? "method" message == some (.string "session/output") then
      if let some closed := (member? "params" message).bind (member? "closed") then
        final.set (some closed)
    let frames := Serve.Remote.relay id message
    if !frames.isEmpty && !ended then
      tell lock ours frames
      if frames.any Linger.Session.Wire.Msg.ends then
        ended := true
  unless ended do
    tell lock ours [.err "connection to the host lost".toUTF8.toList]

/-- Relay what the attach client sends on `ours` to the host's `serve` as the attach `id`'s
conversation (`Serve.Remote.up`) until the client lets its connection go, then let the attach go
(`Serve.Remote.leave`) and end the host's input. An `info` request, which a client sends to be
woken, as `serve` wakes an attach it closed, is answered at once, with no fields. -/
private def relayUp (talk : Command.Talk) (lock : Std.Mutex Unit) (ours : UInt32) (id : Id)
    (name : String) (command : List String) : IO Unit := do
  let mut dec : Linger.Session.Wire.Decoder := {}
  let mut next := 3
  repeat
    let _ ← poll #[ours] #[POLLIN] (-1)
    let some bytes ←
      (try
          read ours 65536
        catch _ =>
          pure none) | break
    if bytes.isEmpty then
      continue
    let (decoder, messages) := dec.feed bytes.toList
    dec := decoder
    if dec.errored then
      break
    for message in messages do
      if message == .info then
        tell lock ours [.infoReply [], .done]
      for line in Serve.Remote.up id name command next message do
        discard <| talk.say line
        next := next + 1
  discard <| talk.say (Serve.Remote.leave id next)
  talk.hangUp

/-- **Bridge an attach client to a host's `session/attach`** of the session `name`, starting it with
`command` when none holds the name: once the host's `serve` has shaken hands, the client's end of a
connection on which the client converses as with a daemon, its first message the attach in its
mode and size, which the bridge calls `session/attach` with; or, when the host did not shake hands,
what it told linger. -/
def bridge (transport : Linger.Target.Remote.Transport) (terminal : Bool) (name : String)
    (command : List String) : IO (Except Asked Bridge) := do
  let some talk ← start transport terminal | return .error { heard := .silent, errors := [] }
  let unread ← IO.mkRef none
  try
    discard <| talk.say Serve.Remote.handshake
    let some hello ← answerTo talk unread 1 | return .error (← finish talk unread [])
    unless Serve.Remote.shook [hello] do
      return .error (← finish talk unread [hello])
    let (ours, theirs) ← socketPair
    let id : Id := .number 2
    let final ← IO.mkRef (none : Option ExactJSON.Value)
    let lock ← Std.Mutex.new ()
    let down ← IO.asTask (relayDown talk unread lock ours id final) .dedicated
    let up ← IO.asTask (relayUp talk lock ours id name command) .dedicated
    let join : IO Asked := do
      discard <| IO.wait up
      -- the attach is let go and the host's input ended: its `serve` ends, unless it hangs
      let deadline := (← monotonicMs) + endMs
      while !(← IO.hasFinished down) do
        unless ← nap deadline 20 do
          talk.stop
          break
      discard <| IO.wait down
      close ours
      let status ← talk.finish
      let answered :=
        match ← final.get with
        | some value => [hello, .table #[("id", id.json), ("result", value)]]
        | none => [hello]
      return { heard := Serve.Remote.heard answered status, errors := errorLines (← talk.errors),
               unread := ← unread.get }
    return .ok { fd := theirs, join }
  catch err =>
    talk.stop
    throw err

end Linger.App.Remote
