module

public import Linger.App.WorldCode.Api
import Linger.App.CoreCode.Serve
import Linger.App.CoreCode.Json
import Os.WorldCode
import Std.Sync.Mutex

public section

/-! # Linger.App.Serve.Shell — `linger serve`, the executor of a connection

`serve` reads standard input a line at a time (`Serve.Lines`), steps the connection's state with
each message (`Serve.step`), writes what the step writes and performs what it performs, each
request on a thread of its own, through `Api.perform` in the command line's namespace, the same
path a command line takes. A request's standard input is its `data` (`Api.Env.input`), never this
process's, and what it says goes into its result's `said`, never to a standard stream. Each
message is one write of one line, under one lock, so no two interleave. At most `maxInFlight`
requests are performed at once: past them `serve` reads no more input until one has answered. It
waits only for input and for its requests: once standard input ends, it waits for the requests it
read, writes their answers and ends, finding `done`. -/

namespace Linger.App.Serve.Shell

open Os.Shell

/-- At most this many requests are performed at once. -/
def maxInFlight : Nat := 64

/-- Write one message, a line of clean text (`Serve.line`). -/
private def emit (out : Outgoing) : IO Unit := writeAll stdoutFd (Serve.line out).toUTF8

/-- The members of a result that show what a request shows: a capture's bytes in base64,
`data`; a listing's records, `records`, each a session's fields as clean text; any other text, and
the sessions an upgrade carried over. -/
private def shownMembers : Api.Shown → List (String × Json)
  | .nothing => []
  | .bytes bytes => [("data", .str (Base64.encode bytes.toList))]
  | .rows _ rows => [("records", .arr ((Serve.records rows).map Record.json))]
  | .text text => [("text", .str (Serve.clean text))]
  | .upgraded names => [("upgraded", .arr (names.map fun name => .str (Serve.clean name)))]

/-- Perform a request as the command line does, with `bytes` for its standard input and what it
says kept for its result, and write its result: the answer it found, what it shows, how a session
it found ended, and what it said, `said`. -/
private def answer (env : Api.Env) (writer : Std.Mutex Unit) (id : Id) (request : Api.Request)
    (bytes : List UInt8) : IO Unit := do
  let said ← IO.mkRef (#[] : Array String)
  let env :=
    { env with
      say := fun s => said.modify (·.push s.text), input := some (ByteArray.mk bytes.toArray) }
  let reply ← Api.perform env request
  let told := (← said.get).toList.map fun text => Json.str (Serve.clean text)
  let members := shownMembers reply.shown ++ endingMembers reply.found ++ [("said", .arr told)]
  writer.atomically (emit (.result id (Serve.result reply.found members)))

/-- **Serve one connection** on standard input and output until standard input ends, performing
its requests in `env`'s namespace; `done` once the requests it read have answered. -/
def run (env : Api.Env) : IO Api.Found := do
  let writer ← Std.Mutex.new ()
  let mut state := State.init
  let mut lines : Lines := {}
  let mut running : Array (Task (Except IO.Error Unit)) := #[]
  let mut reading := true
  while reading do
    let _ ← poll #[stdinFd] #[POLLIN] (-1)
    match ← read stdinFd 65536 with
    | none =>
      reading := false
    | some chunk =>
      let (next, ended) := lines.feed chunk.toList
      lines := next
      for ended in ended do
        let message? :=
          match ended with
          | .text bytes =>
            ((String.fromUTF8? (ByteArray.mk bytes.toArray)).map decode).getD
              (some (.invalid none true))
          | .overlong => some (.invalid none false)
        let some message := message? | continue
        let (next, effects) := step state (.received message)
        state := next
        for effect in effects do
          match effect with
          | .send out =>
            writer.atomically (emit out)
          | .perform id _ request bytes =>
            running ← running.filterM fun task => return !(← IO.hasFinished task)
            if h : 0 < running.size then
              if maxInFlight ≤ running.size then
                discard <| IO.waitAny running.toList (by simpa using h)
            running := running.push (← IO.asTask (answer env writer id request bytes) .dedicated)
  for task in running do
    discard <| IO.wait task
  return .done

end Linger.App.Serve.Shell
