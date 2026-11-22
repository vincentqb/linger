module

public import Linger.App.WorldCode.Api
import Linger.App.CoreCode.Serve
import Linger.App.CoreCode.Json
import Os.WorldCode
import Std.Sync.Mutex

public section

/-! # Linger.App.Serve.Shell — `linger serve`, the executor of a connection

`serve` reads standard input a line at a time (`Serve.Lines`), steps the connection's state with
each message (`Serve.step`) and performs what the step performs, each request on a thread of its
own, through `Api.perform` in the command line's namespace, the same path a command line takes. A
request's standard input is its `data` (`Api.Env.input`), never this process's, and what it says
goes into its result's `said`, the last `saidCap` lines of it (`Log.push`), never to a standard
stream. One writer thread writes every message, one line each, in the order the state machine
and the requests queued them, and, each time nothing else waits, the update the subscriber has
due (`Serve.State.due`, `Event.writable`). While a subscription is open a sampler lists the
sessions `sampleMs` after its last listing ended and hands the step their records, which replace
the latest it holds (`Event.sampled`), so a subscriber that reads slowly holds back nothing but the
writer, and gets the latest records when it reads. At most `maxInFlight` requests are performed,
or messages wait, at once: past them `serve` reads no more input until one has answered or been
written. It waits only for input, its requests, its writer and, while a subscription is open, its
sampler's deadline: once standard input ends, it waits for the requests it read, writes what
waits and ends, finding `done`, or `refused` when its output was closed. -/

namespace Linger.App.Serve.Shell

open Os.Shell

/-- At most this many requests are performed, and messages wait to be written, at once. -/
def maxInFlight : Nat := 64

/-- How many lines of what a request says its result keeps, the last ones. -/
def saidCap : Nat := 32

/-- How long after a subscription's listing ends the next one starts: the chooser's cadence. -/
def sampleMs : Nat := 1000

/-- What a connection's threads share: its state, the messages waiting to be written, in order,
how many requests it is performing, whether a sampler runs, and whether input ended or writing
failed. -/
private structure Shared where
  /-- The connection's state. -/
  state : State := State.init
  /-- The messages waiting to be written, in order. -/
  outbox : List Outgoing := []
  /-- How many requests are being performed. -/
  inFlight : Nat := 0
  /-- Whether a sampler runs. -/
  sampling : Bool := false
  /-- Whether standard input ended. -/
  ended : Bool := false
  /-- Whether writing failed. -/
  broken : Bool := false

/-- Write one message, a line of clean text (`Serve.line`). -/
private def emit (out : Outgoing) : IO Unit := writeAll stdoutFd (Serve.line out).toUTF8

/-- Step the connection with `ev`, queue what the step writes, and give back what it performs. -/
private def stepShared (ev : Event) :
    Std.AtomicT Shared IO (List (Id × String × Api.Request × List UInt8)) := do
  let shared ← get
  let (state, effects) := step shared.state ev
  let sent : List Outgoing :=
    effects.filterMap fun (effect : Effect) =>
      match effect with
      | .send out => some out
      | .perform .. => none
  set
      { shared with
        state, outbox := shared.outbox ++ sent }
  return effects.filterMap fun (effect : Effect) =>
      match effect with
      | .perform id method request bytes => some (id, method, request, bytes)
      | .send _ => none

/-- The members of a result that show what a request shows: a capture's bytes in base64,
`data`; a listing's records, `records`, each a session's fields as clean text; any other text, and
the sessions an upgrade carried over. -/
private def shownMembers : Api.Shown → List (String × Json)
  | .nothing => []
  | .bytes bytes => [("data", .str (Base64.encode bytes.toList))]
  | .rows _ rows => [("records", .arr ((Serve.records rows).map Record.json))]
  | .text text => [("text", .str (Serve.clean text))]
  | .upgraded names => [("upgraded", .arr (names.map fun name => .str (Serve.clean name)))]

/-- The members of a result that show what the request said: its last lines, `said`, and how
many before them it dropped, `saidDropped`. -/
private def saidMembers (said : Log String) : List (String × Json) :=
  [("said", .arr (said.tail.map fun text => .str (Serve.clean text))),
    ("saidDropped", .number (toString said.dropped))]

/-- The writer: write what waits, in order, and the subscriber's update when it has one due and
nothing else waits, until input has ended and nothing waits, or writing fails. -/
private def writer (conn : Std.Mutex Shared) (wake : Std.Condvar) : IO Unit := do
  let mut writing := true
  while writing do
    let next ←
      conn.atomicallyOnce wake
          (do
            let s ← get
            return !s.outbox.isEmpty || s.state.due || s.ended || s.broken)
          (do
            let s ← get
            match s.outbox with
            | out :: rest =>
              set { s with outbox := rest }
              return some out
            | [] =>
              if s.ended || s.broken || !s.state.due then
                return none
              else
                let (state, effects) := step s.state .writable
                set { s with state }
                return effects.findSome? fun (effect : Effect) =>
                    match effect with
                    | .send out => some out
                    | .perform .. => none)
    match next with
    | none =>
      if ← conn.atomically (return (← get).ended || (← get).broken) then
        writing := false
    | some out =>
      try
        emit out
      catch _ =>
        conn.atomically (modify fun s => { s with broken := true })
        writing := false
      wake.notifyAll

/-- The sampler: while a subscription is open and input has not ended, list the sessions
`sampleMs` after the last listing ended, and hand the step their records. -/
private def sampler (env : Api.Env) (conn : Std.Mutex Shared) (wake : Std.Condvar) : IO Unit := do
  let env := { env with say := fun _ => pure () }
  let mut next := (← monotonicMs) + sampleMs
  let mut sampling := true
  while sampling do
    if ← nap next sampleMs then
      continue
    let open? ←
      conn.atomically do
          let s ← get
          if s.state.subscription.isNone || s.ended || s.broken then
            set { s with sampling := false }
            return false
          return true
    if !open? then
      sampling := false
      wake.notifyAll
    else
      let reply ← Api.perform env (.list (.every true none))
      if let .rows _ rows := reply.shown then
        discard <| conn.atomically (stepShared (.sampled (Serve.records rows)))
        wake.notifyAll
      next := (← monotonicMs) + sampleMs

/-- Perform a request as the command line does, with `bytes` for its standard input and what it
says kept for its result, and queue its result: the answer it found, what it shows, how a
session it found ended, and what it said. A `sessions/subscribe`'s listing is the table its
subscriber first holds, and starts the sampler when none runs. -/
private def answer (env : Api.Env) (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id)
    (method : String) (request : Api.Request) (bytes : List UInt8) : IO Unit := do
  let said ← IO.mkRef ({} : Log String)
  let env :=
    { env with
      say := fun s => said.modify (Log.push saidCap · s.text)
      input := some (ByteArray.mk bytes.toArray) }
  let reply ← Api.perform env request
  let members := shownMembers reply.shown ++ endingMembers reply.found ++ saidMembers (← said.get)
  let start ←
    conn.atomically do
        modify fun s =>
            { s with
              outbox := s.outbox ++ [.result id (Serve.result reply.found members)]
              inFlight := s.inFlight - 1 }
        if method = "sessions/subscribe" then
          if let .rows _ rows := reply.shown then
            discard <| stepShared (.opened id (Serve.records rows))
          let s ← get
          if !s.sampling && s.state.subscription == some id then
            set { s with sampling := true }
            return true
        return false
  wake.notifyAll
  if start then
    discard <| IO.asTask (sampler env conn wake) .dedicated

/-- **Serve one connection** on standard input and output until standard input ends, performing
its requests in `env`'s namespace; `done` once the requests it read have answered and what waits
is written, `refused` when its output was closed first. -/
def run (env : Api.Env) : IO Api.Found := do
  let conn ← Std.Mutex.new ({} : Shared)
  let wake ← Std.Condvar.new
  let writing ← IO.asTask (writer conn wake) .dedicated
  let mut lines : Lines := {}
  let mut reading := true
  while reading do
    let _ ← poll #[stdinFd] #[POLLIN] (-1)
    match ← read stdinFd 65536 with
    | none =>
      reading := false
    | some chunk =>
      let (next, ended) := lines.feed chunk.toList
      lines := next
      for line in ended do
        let some message := line.message | continue
        -- room for what the line asks: the requests performed and the messages waiting below
        -- their cap
        let performs ←
          conn.atomicallyOnce wake
              (do
                let s ← get
                return s.broken || s.inFlight + s.outbox.length < maxInFlight)
              (do
                if (← get).broken then
                  return []
                let performs ← stepShared (.received message)
                modify fun s => { s with inFlight := s.inFlight + performs.length }
                return performs)
        wake.notifyAll
        for (id, method, request, bytes) in performs do
          discard <| IO.asTask (answer env conn wake id method request bytes) .dedicated
      if ← conn.atomically (return (← get).broken) then
        reading := false
  conn.atomicallyOnce wake
      (do
        let s ← get
        return s.inFlight == 0 || s.broken)
      (modify fun s => { s with ended := true })
  wake.notifyAll
  discard <| IO.wait writing
  conn.atomicallyOnce wake (return !(← get).sampling) (pure ())
  return if (← conn.atomically get).broken then .refused else .done

end Linger.App.Serve.Shell
