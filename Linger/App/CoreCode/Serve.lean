module

public import Linger.App.CoreSpec
public import Linger.App.CoreCode.Json
import Linger.App.CoreCode.Api
import Linger.Os.CoreCode.Answer
import Linger.Session.CoreCode
import Linger.Display.CoreCode.Listing
import Terminal.CoreCode.Mediation
public import Terminal.CoreCode.Vt
import Terminal.CoreCode.Render

public section

/-! # Linger.App.Serve — linger's operations as JSON-RPC 2.0, one message a line

`linger serve` reads JSON-RPC 2.0 messages from standard input and writes its own to standard
output, one JSON value a line (`Lines`, `decode`, `line`). A connection is a state machine
(`step`): it answers `initialize` with the version it chooses of those it speaks, and with an
error any other request until the client says `initialized`; then each request of a method
`methods` lists is the request of its command line (`Serve.words`, `parse`), which the shell
performs as the command line does and answers with its result (`result`): the answer the command
line would exit with, its name and its code, then what the request shows. A method it does not
answer, params it does not take and a line that is no request get JSON-RPC's errors, with
linger's answer, `usage`, in their `data`. -/

namespace Linger.App.Serve

/-- A connection's state: where its handshake stands, the subscription open, by the id of the
request that opened it, the records its subscriber was last told and the latest a listing found,
and the watches of sessions' terminals it holds, each under the id of the request that asked for
it. -/
structure StateRec where
  /-- Where the handshake stands. -/
  stage : Phase := .fresh
  /-- The open subscription, by the id of the request that opened it. -/
  open? : Option Id := none
  /-- The records the subscriber was last told. -/
  toldRecords : Option (List Record) := none
  /-- The records the latest listing found. -/
  latestRecords : Option (List Record) := none
  /-- The watches, each under the id of the request that asked for it. -/
  watches : List (Id × Watch) := []

/-- A connection's state. -/
abbrev State : Type := StateRec

/-- A connection before any message. -/
def State.init : State := {}

/-- Where a connection stands in its handshake. -/
def State.phase (s : State) : Phase := s.stage

/-- The open subscription, by the id of the request that opened it. -/
def State.subscription (s : State) : Option Id := s.open?

/-- The records the subscriber was last told. -/
def State.told (s : State) : Option (List Record) := s.toldRecords

/-- The records the latest listing found. -/
def State.latest (s : State) : Option (List Record) := s.latestRecords

/-- What the connection holds for the watch with this id. -/
def State.watching (s : State) (id : Id) : Option Watch := s.watches.lookup id

/-- The most watches a connection holds at once: a watch past them is refused. -/
def maxWatches : Nat := 16

/-- The connection with the watch under `id` set to `w`. -/
def State.setWatch (s : State) (id : Id) (w : Watch) : State :=
  { s with watches := s.watches.map fun entry => if entry.1 = id then (id, w) else entry }

/-- The connection without the watch under `id`. -/
def State.dropWatch (s : State) (id : Id) : State :=
  { s with watches := s.watches.filter fun entry => entry.1 != id }

/-- Whether a watch has an update due: an open screen whose latest look differs from what its
subscriber was last told, or an open history with lines it has not sent or a count of drops. -/
def Watch.due : Watch → Bool
  | .screen told latest => told != latest
  | .history pending => !pending.tail.isEmpty || pending.dropped != 0
  | .asked _ => false

/-! ## Logs -/

/-- A log with `entry` appended: its last `cap` entries, and one more dropped when it held as many
already. -/
def Log.push {α : Type} (cap : Nat) (log : Log α) (entry : α) : Log α :=
  if (log.tail ++ [entry]).length ≤ cap then { log with tail := log.tail ++ [entry] }
  else { tail := (log.tail ++ [entry]).drop 1, dropped := log.dropped + 1 }

/-- A log with the entries of another after its own, as pushing each of them would leave it: the
other's entries pushed after its own, or, when the other dropped some, after a gap for each entry
it held and each the other dropped. -/
def Log.append {α : Type} (cap : Nat) (log more : Log α) : Log α :=
  more.tail.foldl (Log.push cap)
    (if more.dropped = 0 then log
    else { tail := [], dropped := log.dropped + log.tail.length + more.dropped })

/-! ## A session's terminal as rows -/

/-- The runs of equal pens in a list of pens, in order, each as long as its run. -/
def Span.runs (pens : List Terminal.Vt.Pen) : List Span :=
  pens.foldr
    (fun pen runs =>
      match runs with
      | run :: rest =>
        if run.pen = pen then { run with length := run.length + 1 } :: rest
        else ⟨1, pen⟩ :: run :: rest
      | [] => [⟨1, pen⟩])
    []

/-- **A row as a reader holds it**: its text as `capture` prints it (`Render.rowText`), and the
runs of its characters' pens (`Line.pens`). -/
def Line.of (row : Terminal.Vt.Row) : Line :=
  { text := Terminal.Render.rowText row, spans := Span.runs (Line.pens row) }

/-- **A terminal's screen as a reader holds it**: each row as `Line.of` renders it, top first, the
cursor where the terminal has it and whether it shows, and the window title as clean text. -/
def Screen.render (v : Terminal.Vt.Vt) : Screen :=
  { lines := (List.range v.rowCount).map fun y => Line.of (v.getRow y)
    cursor := { x := v.cursorPos.1, y := v.cursorPos.2, visible := v.getModes.cursorVisible }
    title := Linger.Display.Listing.clean v.windowTitle }

/-- **The update from `told` to `latest`**: each line `latest` holds that `told` holds otherwise or
not at all, under its number, the numbers of the lines `told` holds and `latest` does not, and the
cursor and the title when they changed. -/
def Screen.changes (told latest : Screen) : Screen.Update :=
  { lines :=
      (latest.lines.zipIdx.filter fun (line, y) => told.lines[y]? != some line).map fun (line, y) =>
        (y, line)
    removed := (List.range told.lines.length).filter fun y => latest.lines.length ≤ y
    cursor := if told.cursor = latest.cursor then none else some latest.cursor
    title := if told.title = latest.title then none else some latest.title }

/-- Feed output to a mirror of a terminal whose history is empty, and keep it empty: the mirror
after `bytes`, and `left` with the rows they pushed into its history, oldest first, each as
`Line.of` renders it, kept as a log of at most `historyCap` lines does (`Log.push`). A byte that
pushes no row leaves the history empty; one that pushes rows pushes at most as many as the screen
has, all of which an empty history keeps, and the mirror after it is the one `Vt.observe` gives,
its history emptied. -/
def feedLeaving (v : Terminal.Vt.Vt) (bytes : List UInt8) (left : Log Line) :
    Terminal.Vt.Vt × Log Line :=
  bytes.foldl
    (fun (acc : Terminal.Vt.Vt × Log Line) b =>
      let next := acc.1.step b
      match next.scrollback with
      | [] => (next, acc.2)
      | rows =>
        (acc.1.observe [b],
          rows.foldl (fun log row => Log.push historyCap log (Line.of row)) acc.2))
    (v, left)

/-- The first watch with an update due, by its id. -/
def State.watchDue (s : State) : Option Id :=
  match s.phase with
  | .ready _ => (s.watches.find? fun entry => entry.2.due).map (·.1)
  | _ => none

/-- Whether the subscriber has an update due: the latest records differ from those it was last
told, read without the clock (`changes`, `removed`). -/
def State.due (s : State) : Bool :=
  match s.phase, s.subscription, s.told, s.latest with
  | .ready _, some _, some told, some latest =>
    !(changes told latest).isEmpty || !(removed told latest).isEmpty
  | _, _, _, _ => false

/-- **A method's request is its command line's**: the request `Api.parse` reads from the words
`Serve.words` gives the method and its params, with the standard input `Serve.input` gives them;
none for a method `methods` does not list or params it does not take. -/
def parse (method : String) (params : Json) : Option (Api.Request × List UInt8) :=
  (words method params).bind fun argv =>
    (Api.parse argv).bind fun request => (input method params).map ((request, ·))

/-- An answer as JSON members: its name and its code. -/
def answerMembers (answer : Os.Answer) : List (String × Json) :=
  [("answer", .str (answerName answer)), ("code", .number (toString answer.code))]

/-- **The result of a performed request**: the answer the command line exits with for what it
found (`Api.answer`), its name and its code, then the members of what it shows. -/
def result (found : Api.Found) (members : List (String × Json)) : Json :=
  .obj (answerMembers (Api.answer found) ++ members)

/-- The `data` of an error: linger's answer, `usage`, as a command line it does not take gets,
and `extra`. -/
def refusal (extra : List (String × Json) := []) : Json := .obj (answerMembers .usage ++ extra)

/-- The version `initialize`'s params ask for, if `serve` speaks it. -/
def chosen (params : Json) : Option String :=
  match params.member? "protocolVersion" with
  | some (.str version) => if version ∈ versions then some version else none
  | _ => none

/-- The error that answers a request a connection takes no request but `initialize` before. -/
private def notInitialized (id : Id) : Outgoing :=
  .error (some id) (-32002) "not initialized" (refusal)

/-- `sessions/unsubscribe` of the subscription its params name: the sessions table's, a watch's,
or both when they share the id, each closed; a watch not answered yet is answered `done`, as a
detach ends an attach. -/
def unsubscribe (s : State) (id : Id) (params : Json) : State × List Effect :=
  match (params.member? "subscription").bind Id.of with
  | some key =>
    if s.subscription = some key ∨ (s.watching key).isSome then
      ((if s.subscription = some key then
              { s with
                open? := none, toldRecords := none, latestRecords := none }
            else s).dropWatch
          key,
        (match s.watching key with
          | some (.asked _) => [.send (.result key (result .done []))]
          | _ => []) ++
          [.send (.result id (result .done []))])
    else (s, [.send (.error (some id) (-32602) "no such subscription" (refusal))])
  | none => (s, [.send (.error (some id) (-32602) "no such subscription" (refusal))])

/-- What a connection does with a request it performs: a `sessions/subscribe` opens its
subscription, and a watch is asked for under its id, unless the connection holds `maxWatches` or a
subscription under the id already, when it is refused. -/
def performs (s : State) (id : Id) (method : String) (req : Api.Request) (bytes : List UInt8) :
    State × List Effect :=
  if method = "sessions/subscribe" then
    ({ s with
        open? := some id, toldRecords := none, latestRecords := none },
      [.perform id method req bytes])
  else
    if method = "session/screen" ∨ method = "session/history" then
      if s.watches.length < maxWatches ∧ s.subscription ≠ some id ∧ (s.watching id).isNone then
        ({ s with watches := s.watches ++ [(id, .asked (method = "session/history"))] },
          [.perform id method req bytes])
      else (s, [.send (.result id (result .refused []))])
    else (s, [.perform id method req bytes])

/-- What a connection does with a request: `initialize` once, before anything else, then the
methods `methods` lists, each performed as its command line's request (`parse`), a
`sessions/subscribe` opening its subscription, a watch asked for, and `sessions/unsubscribe` of an
open one. -/
private def request (s : State) (id : Id) (method : String) (params : Json) : State × List Effect :=
  if method = "initialize" then
    match s.phase with
    | .fresh =>
      match chosen params with
      | some version =>
        ({ s with stage := .negotiated version },
          [.send (.result id (welcome version Terminal.Mediation.versionNumber))])
      | none =>
        (s,
          [.send
              (.error (some id) (-32602) "unsupported protocol version"
                (refusal [("supported", .arr (versions.map .str))]))])
    | _ => (s, [.send (.error (some id) (-32600) "already initialized" (refusal))])
  else
    match s.phase with
    | .ready _ =>
      if method = "sessions/unsubscribe" then unsubscribe s id params
      else
        if (methods.lookup method).isSome then
          match parse method params with
          | some (req, bytes) => performs s id method req bytes
          | none => (s, [.send (.error (some id) (-32602) "invalid params" (refusal))])
        else (s, [.send (.error (some id) (-32601) "method not found" (refusal))])
    | _ => (s, [.send (notInitialized id)])

/-- An answer as a member: `closed`, with the answer the command line exits with for what the watch
found, its name and its code, and how a session it found ended. -/
def closedMembers (found : Api.Found) : List (String × Json) :=
  [("closed",
      .obj
        (answerMembers (Api.answer found) ++
          match found with
          | .ended ending =>
            [("ending",
                Record.json
                  ((Linger.Display.Listing.records [Linger.Session.endingFields ending]).headD []))]
          | _ => []))]

/-- An update's params with more members after its own. -/
def Json.withMembers : Json → List (String × Json) → Json
  | .obj members, more => .obj (members ++ more)
  | value, _ => value

/-- What `said` shows of a log of what a request said: its last lines, as clean text, and how many
before them it dropped. -/
def saidMembers (said : Log String) : List (String × Json) :=
  [("said", .arr (said.tail.map fun text => .str (Linger.Display.Listing.clean text))),
    ("saidDropped", .number (toString said.dropped))]

/-- What a connection does with a watch's look: the first one answers the watch's request, a
screen's with the screen and a history's with nothing, and holds what it found, and a later one
replaces a screen's latest look, or adds the lines that left to a history's log, and sends
nothing. -/
def watched (s : State) (id : Id) (screen : Screen) (left : Log Line) : State × List Effect :=
  match s.phase, s.watching id with
  | .ready _, some (.asked false) =>
    (s.setWatch id (.screen screen screen), [.send (.result id (result .done screen.members))])
  | .ready _, some (.asked true) =>
    (s.setWatch id (.history (Log.append historyCap {} left)),
      [.send (.result id (result .done []))])
  | .ready _, some (.screen told _) => (s.setWatch id (.screen told screen), [])
  | .ready _, some (.history pending) =>
    (s.setWatch id (.history (Log.append historyCap pending left)), [])
  | _, _ => (s, [])

/-- What a free writer sends a watch: a screen's changes since what its subscriber was last told,
when any, or a history's lines and drops since its last update, when any; then it has told them. -/
def flushed (s : State) (id : Id) : State × List Effect :=
  match s.phase, s.watching id with
  | .ready _, some (.screen told latest) =>
    (s.setWatch id (.screen latest latest),
      if told = latest then []
      else
        [.send (.notify "session/screen/changed" (Screen.update id (Screen.changes told latest)))])
  | .ready _, some (.history pending) =>
    (s.setWatch id (.history {}),
      if pending.tail = [] ∧ pending.dropped = 0 then []
      else [.send (.notify "session/history/changed" (Log.update id pending))])
  | _, _ => (s, [])

/-- What a connection does when a watch ends: one not answered yet is answered with what it found
and what it said; an open one sends its last update, `closed` with what it found; and it holds the
watch no more. -/
def unwatched (s : State) (id : Id) (found : Api.Found) (said : Log String) : State × List Effect :=
  match s.phase, s.watching id with
  | .ready _, some (.asked _) =>
    (s.dropWatch id, [.send (.result id (result found (saidMembers said)))])
  | .ready _, some (.screen told latest) =>
    (s.dropWatch id,
      [.send
          (.notify "session/screen/changed"
            ((Screen.update id (Screen.changes told latest)).withMembers (closedMembers found)))])
  | .ready _, some (.history pending) =>
    (s.dropWatch id,
      [.send
          (.notify "session/history/changed"
            ((Log.update id pending).withMembers (closedMembers found)))])
  | _, _ => (s, [])

/-- **What a connection does with an event.** Before it is ready it writes nothing but errors and
the result of `initialize`, and performs nothing, and it sends `sessions/changed` only to the open
subscription (`serve_negotiated`): a listing's records replace the latest it holds and send nothing,
and each time the writer is free it sends the records that differ from those it last told the
subscriber, and the keys that went, when any do (`changed_exactly`, `table_converges`). -/
def step (s : State) : Event → State × List Effect
  | .received (.invalid id unparsed) =>
    (s,
      [.send
          (if unparsed then .error none (-32700) "parse error" (refusal)
          else .error id (-32600) "invalid request" (refusal))])
  | .received (.notification method _) =>
    match s.phase with
    | .negotiated version =>
      if method = "initialized" then ({ s with stage := .ready version }, []) else (s, [])
    | _ => (s, [])
  | .received (.request id method params) => request s id method params
  | .opened id records =>
    match s.phase with
    | .ready _ =>
      if s.subscription = some id then
        ({ s with
            toldRecords := some records, latestRecords := some records },
          [])
      else (s, [])
    | _ => (s, [])
  | .sampled records =>
    match s.phase with
    | .ready _ =>
      if s.subscription.isSome ∧ s.told.isSome then ({ s with latestRecords := some records }, [])
      else (s, [])
    | _ => (s, [])
  | .writable =>
    match s.phase, s.subscription, s.told, s.latest with
    | .ready _, some id, some told, some latest =>
      ({ s with toldRecords := some latest },
        if changes told latest = [] ∧ removed told latest = [] then []
        else
          [.send
              (.notify "sessions/changed" (update id (changes told latest) (removed told latest)))])
    | _, _, _, _ => (s, [])
  | .watched id screen left => watched s id screen left
  | .flush id => flushed s id
  | .unwatched id found said => unwatched s id found said

/-! ## Messages as lines -/

/-- What a line from the client is: a request, with an id, a notification, without one, or no
message, a line that is not JSON or JSON that is no JSON-RPC 2.0 request object; none for a line of
whitespace alone, which is no message at all. -/
def decode (line : String) : Option Message :=
  if line.all fun c => c = ' ' ∨ c = '\t' ∨ c = '\r' then none
  else
    some
      (match Json.parse line with
      | none => .invalid none true
      | some (.obj members) =>
        let id := (members.lookup "id").bind Id.of
        if (members.lookup "jsonrpc").bind Json.text? ≠ some "2.0" then .invalid id false
        else
          match (members.lookup "method").bind Json.text?, members.lookup "id" with
          | none, _ => .invalid id false
          | some method, none => .notification method ((members.lookup "params").getD (.obj []))
          | some method, some _ =>
            match id with
            | some id => .request id method ((members.lookup "params").getD (.obj []))
            | none => .invalid none false
      | some _ => .invalid none false)

/-- A message as JSON-RPC 2.0's object. -/
def Outgoing.json : Outgoing → Json
  | .result id value => .obj [("jsonrpc", .str "2.0"), ("id", id.json), ("result", value)]
  | .error id code message data =>
    .obj
      [("jsonrpc", .str "2.0"), ("id", (id.map Id.json).getD .null),
        ("error",
          .obj [("code", .number (toString code)), ("message", .str message), ("data", data)])]
  | .notify method params =>
    .obj [("jsonrpc", .str "2.0"), ("method", .str method), ("params", params)]

/-- The line `serve` writes for a message: its JSON text, which holds no newline, then one. -/
def line (out : Outgoing) : String := (Json.render out.json).push '\n'

/-- Text as `serve` sends it: every control character, C0, DEL and C1, as U+FFFD, as listings and
`info` records give it (`Render.textChar`). -/
def clean (text : String) : String := Linger.Display.Listing.clean text

/-- Listing records as `serve` sends them: each key and value clean text (`clean`). -/
def records (rows : List (List (String × String))) : List (List (String × String)) :=
  Linger.Display.Listing.records rows

/-- The members a request's result shows of how a session ended, when it found that it ended:
`ending`, the record of it `ls` gives (`Session.endingFields`). -/
def endingMembers : Api.Found → List (String × Json)
  | .ended ending =>
    [("ending", Record.json ((records [Linger.Session.endingFields ending]).headD []))]
  | _ => []

/-! ## Lines -/

/-- The longest line `serve` reads, in bytes, its newline aside: a longer one is no message, and
its bytes are dropped as they come. -/
def lineCap : Nat := 1048576

/-- A line `serve` read: its bytes, or a line longer than `lineCap`. -/
inductive Received where
  /-- The bytes of a line, its newline aside. -/
  | text (bytes : List UInt8)
  /-- A line longer than `lineCap`. -/
  | overlong

/-- The line being read: its bytes so far, last first, how many, and whether it has passed
`lineCap`, after which its bytes are dropped. -/
structure Lines where
  /-- The line's bytes so far, last first. -/
  pending : List UInt8 := []
  /-- How many bytes `pending` holds. -/
  size : Nat := 0
  /-- Whether the line has passed `lineCap`. -/
  over : Bool := false

/-- The line being read after one more byte, and the line it ends, at a newline. -/
def Lines.push (l : Lines) (b : UInt8) : Lines × Option Received :=
  if b = 10 then ({}, some (if l.over then .overlong else .text l.pending.reverse))
  else
    if l.over then (l, none)
    else
      if l.size < lineCap then
        ({ l with
            pending := b :: l.pending, size := l.size + 1 },
          none)
      else ({ over := true }, none)

/-- The line being read after `bytes`, and the lines they end, in order. -/
def Lines.feed (l : Lines) (bytes : List UInt8) : Lines × List Received :=
  let (last, ended) :=
    bytes.foldl
      (fun (acc : Lines × List Received) b =>
        match acc.1.push b with
        | (next, some ended) => (next, ended :: acc.2)
        | (next, none) => (next, acc.2))
      (l, [])
  (last, ended.reverse)

/-- A line `serve` read as a message: none for a line of whitespace alone. -/
def Received.message : Received → Option Message
  | .text bytes =>
    ((String.fromUTF8? (ByteArray.mk bytes.toArray)).map decode).getD (some (.invalid none true))
  | .overlong => some (.invalid none false)

end Linger.App.Serve
