module

public import Linger.App.CoreSpec
import Linger.App.CoreCode.Base64
import Linger.App.CoreCode.Codec
import Linger.App.CoreCode.Api
import Linger.Os.CoreCode.Answer
import Linger.Session.CoreCode
import Linger.Session.CoreCode.Wire
import Linger.Display.CoreCode.Listing
import Linger.Target.CoreCode.Remote
import Linger.Target.CoreCode.Name
import Terminal.CoreCode.Mediation
public import Terminal.CoreCode.Vt
import Terminal.CoreCode.Render

public section

/-! # Linger.App.Serve — linger's operations as JSON-RPC 2.0, one message a line

`linger serve` reads JSON-RPC 2.0 messages from standard input and writes its own to standard
output, one canonical JSON value a line, ExactJSON's (`Lines`, `decode`, `line`): a line that is
not canonical gets error -32700, with ExactJSON's reason in its `data`, and changes nothing
(`serve_refuses_uncanonical`). A connection is a state machine
(`step`): it answers `initialize` with the version it chooses of those it speaks, and with an
error any other request until the client says `initialized`; then each request of a method
`methods` lists is the request of its command line (`Call.words`, `parse`), its params read exactly
as their type (`exactly`), which the shell performs as the command line does and answers with its
result (`result`): the answer the command line would exit with, its name and its code, then what
the request shows. A method it does not answer, params it does not take, among them params with a
member the method does not define, and a line that is no request get JSON-RPC's errors, with
linger's answer, `usage`, in their `data`. An attach's conversation, `session/input`,
`session/resize` and `session/detach` naming it by its subscription, relays its keys and its size
to its daemon and ends it (`converse`), and the reads of its connection are its stream
(`readAttach`). -/

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
subscriber was last told, an open history with lines it has not sent or a count of drops, or an
open attach with bytes waiting for its subscriber. -/
def Watch.due : Watch → Bool
  | .screen told latest => told != latest
  | .history pending => !pending.tail.isEmpty || pending.dropped != 0
  | .asked _ => false
  | .attaching => false
  | .stream _ pending => !pending.isEmpty

/-- Whether what waits for the subscriber of the attach `id` has reached `cap` bytes, so that the
attach's connection is read no further until its writer sends it: the bound that makes a reader that
does not read cost its own attach, which its daemon then cuts off, as it cuts off any client. -/
def State.holdsBack (s : State) (id : Id) (cap : Nat) : Bool :=
  match s.watching id with
  | some (.stream _ pending) => cap ≤ pending.length
  | _ => false

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

/-- **The call a method and its params are**: the call of the method whose params are exactly
`params`, read as its type writes them (`exactly`); none for a method `methods` does not list, and
for params no call of it has, among them params with a member it does not define. -/
def Call.read (method : String) (params : ExactJSON.Value) : Option Call :=
  if method = "sessions/list" then (exactly params).map Call.list
  else
    if method = "sessions/subscribe" then (exactly params).map Call.subscribe
    else
      if method = "session/screen" then (exactly params).map Call.screen
      else
        if method = "session/history" then (exactly params).map Call.history
        else
          if method = "session/attach" then (exactly params).map Call.attach
          else
            if method = "session/start" then (exactly params).map Call.start
            else
              if method = "session/resume" then (exactly params).map Call.resume
              else
                if method = "session/send" then (exactly params).map Call.send
                else
                  if method = "session/detach" then (exactly params).map Call.detach
                  else
                    if method = "session/kill" then (exactly params).map Call.kill
                    else
                      if method = "session/rename" then (exactly params).map Call.rename
                      else
                        if method = "session/capture" then (exactly params).map Call.capture
                        else
                          if method = "session/resize" then (exactly params).map Call.resize
                          else
                            if method = "session/wait" then (exactly params).map Call.wait
                            else
                              if method = "session/upgrade" then (exactly params).map Call.upgrade
                              else none

/-- **A method's request is its command line's**: the request `Api.parse` reads from the words of
the call the method and its params are (`Call.read`, `Call.words`), with the standard input it
gives (`Call.input`); none for a method `methods` does not list or params it does not take. -/
def parse (method : String) (params : ExactJSON.Value) : Option (Api.Request × List UInt8) :=
  (Call.read method params).bind fun call =>
    (Api.parse call.words).bind fun request => call.input.map ((request, ·))

/-- An answer's result: its name and its code, and what `shows` shows. -/
def answered (answer : Os.Answer) (shows : Shows) : Result :=
  { toShows := shows, answer := answerName answer, code := answer.code.toNat }

/-- **The result of a performed request**: the answer the command line exits with for what it
found (`Api.answer`), its name and its code, then what it shows. -/
def result (found : Api.Found) (shows : Shows) : ExactJSON.Value :=
  ExactJSON.toValue (answered (Api.answer found) shows)

/-- The `data` of an error: linger's answer, `usage`, as a command line it does not take gets,
and what `extra` shows. -/
def refusal (extra : Shows := {}) : ExactJSON.Value := ExactJSON.toValue (answered .usage extra)

/-- The error that answers a request a connection takes no request but `initialize` before. -/
private def notInitialized (id : Id) : Outgoing :=
  .error (some id) (-32002) "not initialized" (refusal)

/-- `sessions/unsubscribe` of the subscription its params name: the sessions table's, a watch's,
or both when they share the id, each closed; a watch not answered yet is answered `done`, as a
detach ends an attach. Params that are not exactly a subscription's are invalid. -/
def unsubscribe (s : State) (id : Id) (params : ExactJSON.Value) : State × List Effect :=
  match (exactly params : Option Subscription) with
  | some ⟨key⟩ =>
    if s.subscription = some key ∨ (s.watching key).isSome then
      ((if s.subscription = some key then
              { s with
                open? := none, toldRecords := none, latestRecords := none }
            else s).dropWatch
          key,
        (match s.watching key with
          | some (.asked _) | some .attaching => [.send (.result key (result .done {}))]
          | _ => []) ++
          [.send (.result id (result .done {}))])
    else (s, [.send (.error (some id) (-32602) "no such subscription" (refusal))])
  | none => (s, [.send (.error (some id) (-32602) "invalid params" (refusal))])

/-- What a watch's request asks for: an attach for `session/attach`, and otherwise a watch of a
history, for `session/history`, or of a screen. -/
def Watch.asking (method : String) : Watch :=
  if method = "session/attach" then .attaching else .asked (method = "session/history")

/-- What a connection does with a request it performs: a `sessions/subscribe` opens its
subscription, and a watch or an attach is asked for under its id, unless the connection holds
`maxWatches` or a subscription under the id already, when it is refused. -/
def performs (s : State) (id : Id) (method : String) (req : Api.Request) (bytes : List UInt8) :
    State × List Effect :=
  if method = "sessions/subscribe" then
    ({ s with
        open? := some id, toldRecords := none, latestRecords := none },
      [.perform id method req bytes])
  else
    if method = "session/screen" ∨ method = "session/history" ∨ method = "session/attach" then
      if s.watches.length < maxWatches ∧ s.subscription ≠ some id ∧ (s.watching id).isNone then
        ({ s with watches := s.watches ++ [(id, Watch.asking method)] },
          [.perform id method req bytes])
      else (s, [.send (.result id (result .refused {}))])
    else (s, [.perform id method req bytes])

/-- Whether a request is part of an attach's conversation, which names the attach by its
subscription: `session/input`, and `session/resize` or `session/detach` with a `subscription`,
which without one are the command line's `resize` and `detach`. -/
def converses (method : String) (params : ExactJSON.Value) : Bool :=
  method = "session/input" ||
    (method = "session/resize" || method = "session/detach") &&
      (member? "subscription" params).isSome

/-- The attach a request of an attach's conversation names and the messages it writes on the
attach's connection, its params read exactly as their type writes them (`exactly`): the keys
`session/input`'s `data` encodes in base64, as the input frames `send` cuts (`Wire.inputFrames`),
`session/resize`'s size, one the emulator keeps as it is, as `resize` takes it, and nothing for
`session/detach`; none for params it does not take. -/
def conversed (method : String) (params : ExactJSON.Value) : Option (Id × List Session.Wire.Msg) :=
  if method = "session/input" then
    (exactly params : Option Keys).bind fun keys =>
      (Base64.decode keys.data.toList).map fun bytes =>
        (keys.subscription, Session.Wire.inputFrames bytes)
  else
    if method = "session/resize" then
      (exactly params : Option Sized).bind fun sized =>
        if
            Terminal.Vt.clampDim sized.cols = sized.cols ∧
              Terminal.Vt.clampDim sized.rows = sized.rows then
          some (sized.subscription, [.resize sized.cols.toUInt32 sized.rows.toUInt32])
        else none
    else (exactly params : Option Subscription).map fun named => (named.subscription, [])

/-- **A request of an attach's conversation**, of the attach its params name by its subscription:
`session/input` writes its keys on the attach's connection and `session/resize` its terminal's size,
as an attach client does, and `session/detach` ends the attach, as an attach client's leaving does,
answering one not answered yet `done`; each is answered `done`, one that names no attach open is
refused, and params it does not take are invalid. -/
def converse (s : State) (id : Id) (method : String) (params : ExactJSON.Value) :
    State × List Effect :=
  match conversed method params with
  | none => (s, [.send (.error (some id) (-32602) "invalid params" (refusal))])
  | some (key, messages) =>
    match s.watching key with
    | some .attaching =>
      if method = "session/detach" then
        (s.dropWatch key,
          [.send (.result key (result .done {})), .send (.result id (result .done {}))])
      else (s, [.send (.error (some id) (-32602) "no such subscription" (refusal))])
    | some (.stream _ _) =>
      if method = "session/detach" then (s.dropWatch key, [.send (.result id (result .done {}))])
      else (s, [.relay key messages, .send (.result id (result .done {}))])
    | _ => (s, [.send (.error (some id) (-32602) "no such subscription" (refusal))])

/-- What a connection does with a request: `initialize` once, before anything else, then the
methods `methods` lists, each performed as its command line's request (`parse`), a
`sessions/subscribe` opening its subscription, a watch or an attach asked for, `sessions/unsubscribe`
of an open one, and the requests of an attach's conversation (`converse`). -/
private def request (s : State) (id : Id) (method : String) (params : ExactJSON.Value) :
    State × List Effect :=
  if method = "initialize" then
    match s.phase with
    | .fresh =>
      match (exactly params : Option Initialize) with
      | some asked =>
        if asked.protocolVersion ∈ versions then
          ({ s with stage := .negotiated asked.protocolVersion },
            [.send
                (.result id
                  (ExactJSON.toValue
                    (Welcome.of asked.protocolVersion Terminal.Mediation.versionNumber)))])
        else
          (s,
            [.send
                (.error (some id) (-32602) "unsupported protocol version"
                  (refusal { supported? := some versions }))])
      | none => (s, [.send (.error (some id) (-32602) "invalid params" (refusal))])
    | _ => (s, [.send (.error (some id) (-32600) "already initialized" (refusal))])
  else
    match s.phase with
    | .ready _ =>
      if method = "sessions/unsubscribe" then unsubscribe s id params
      else
        if converses method params then converse s id method params
        else
          if (methods.lookup method).isSome then
            match parse method params with
            | some (req, bytes) => performs s id method req bytes
            | none => (s, [.send (.error (some id) (-32602) "invalid params" (refusal))])
          else (s, [.send (.error (some id) (-32601) "method not found" (refusal))])
    | _ => (s, [.send (notInitialized id)])

/-- The record of how a session ended that a request found, when it found that it ended: the record
`ls` gives of it (`Session.endingFields`). -/
def endingRecord : Api.Found → Option Record
  | .ended ending => (Linger.Display.Listing.records [Linger.Session.endingFields ending]).head?
  | _ => none

/-- How a watch ended, its last update's `closed`: the answer the command line exits with for what
the watch found, its name and its code, and how a session it found ended. -/
def closedResult (found : Api.Found) : Result :=
  answered (Api.answer found) { ending? := endingRecord found }

/-- What a result shows of a log of what a request said: its last lines, as clean text, and how
many before them it dropped. -/
def saidShows (said : Log String) : Shows :=
  { said? := some (said.tail.map Linger.Display.Listing.clean), saidDropped? := some said.dropped }

/-- What a connection does with a watch's look: the first one answers the watch's request, a
screen's with the screen and a history's with nothing, and holds what it found, and a later one
replaces a screen's latest look, or adds the lines that left to a history's log, and sends
nothing. -/
def watched (s : State) (id : Id) (screen : Screen) (left : Log Line) : State × List Effect :=
  match s.phase, s.watching id with
  | .ready _, some (.asked false) =>
    (s.setWatch id (.screen screen screen), [.send (.result id (result .done screen.shows))])
  | .ready _, some (.asked true) =>
    (s.setWatch id (.history (Log.append historyCap {} left)),
      [.send (.result id (result .done {}))])
  | .ready _, some (.screen told _) => (s.setWatch id (.screen told screen), [])
  | .ready _, some (.history pending) =>
    (s.setWatch id (.history (Log.append historyCap pending left)), [])
  | _, _ => (s, [])

/-- The params of `session/output`: the subscription it updates, the id of the request that opened
the attach, the bytes it carries, as base64 `data` (`Base64.encode`), and, on its last update,
how the attach ended. -/
def Output.update (id : Id) (bytes : List UInt8) (closed : Option Result := none) :
    ExactJSON.Value :=
  ExactJSON.toValue
    ({ closed? := closed, data := Base64.encode bytes, subscription := id } : Output)

/-- The params of `session/screen/changed` of an update: the subscription it updates, the lines
that changed, each under its number, the numbers of the lines that went, the cursor and the title
when they changed, and, on its last update, how the watch ended. -/
def Screen.changed (id : Id) (u : Screen.Update) (closed : Option Result := none) :
    ExactJSON.Value :=
  ExactJSON.toValue
    ({ closed? := closed, cursor? := u.cursor, removed := u.removed,
       rows := u.lines.map fun (y, line) => line.row y, subscription := id, title? := u.title } :
      ScreenChanged)

/-- The params of `session/history/changed` of a log: the subscription it updates, the lines that
left the screen, oldest first, how many before them it dropped, and, on its last update, how the
watch ended. -/
def Log.changed (id : Id) (log : Log Line) (closed : Option Result := none) : ExactJSON.Value :=
  ExactJSON.toValue
    ({ closed? := closed, dropped := log.dropped, lines := log.tail.map Line.scrolled,
       subscription := id } :
      HistoryChanged)

/-- The params of `sessions/changed`: the records that replace those under their keys, the keys
that go, and the subscription it updates. -/
def changed (id : Id) (records : List Record) (gone : List String) : ExactJSON.Value :=
  ExactJSON.toValue ({ records, removed := gone, subscription := id } : Changed)

/-- What an attach found when the first of `messages` that ends it (`Wire.Msg.ends`) did, as an
attach client reads it: how the program ended, the status of an older daemon's report, that a
signal saved the session, or, for a refusal or none, `refused`. -/
def stopFound (messages : List Session.Wire.Msg) : Api.Found :=
  match messages.find? Session.Wire.Msg.ends with
  | some (.ended outcome) => .ended (.program outcome)
  | some (.exited status) => .status status
  | some (.saved signal) => .ended (.saved signal)
  | _ => .refused

/-- What a read of an attach's connection does, the attach holding the decoder `dec` and `pending`
for its subscriber: the messages the read's bytes end decode (`Wire.Decoder.feed`) add the bytes an
attach client writes of them (`Wire.shown`) after what waits; when one of them ends the attach it
sends what waits as the stream's last update, with `closed` and what the attach found, and holds
the attach no more, and when the framing breaks, where an attach client writes nothing of the read
and loses the connection, it sends what waited so, `closed` with `refused`. -/
def streamed (s : State) (id : Id) (dec : Session.Wire.Decoder) (pending bytes : List UInt8) :
    State × List Effect :=
  let decoded := dec.feed bytes
  if decoded.1.errored then
    (s.dropWatch id,
      [.send (.notify "session/output" (Output.update id pending (some (closedResult .refused))))])
  else
    let waiting := pending ++ Session.Wire.shown decoded.2
    if decoded.2.any Session.Wire.Msg.ends then
      (s.dropWatch id,
        [.send
            (.notify "session/output"
              (Output.update id waiting (some (closedResult (stopFound decoded.2)))))])
    else (s.setWatch id (.stream decoded.1 waiting), [])

/-- **The read a screen an attach shows is**, as a daemon sends an attach its repaint: the screen's
bytes as output frames, each holding at most a frame's worth (`Wire.inputChunks`), in order. -/
def paint (screen : List UInt8) : List UInt8 :=
  ((Linger.Session.Wire.inputChunks screen).map Linger.Session.Wire.Msg.output).flatMap
    Linger.Session.Wire.encode

/-- What a connection does with a read of an attach's connection: the first answers the attach's
request `done`, and each is `streamed`. -/
def readAttach (s : State) (id : Id) (bytes : List UInt8) : State × List Effect :=
  match s.phase, s.watching id with
  | .ready _, some .attaching =>
    ((streamed s id {} [] bytes).1,
      .send (.result id (result .done {})) :: (streamed s id {} [] bytes).2)
  | .ready _, some (.stream dec pending) => streamed s id dec pending bytes
  | _, _ => (s, [])

/-- What a free writer sends a watch: a screen's changes since what its subscriber was last told,
when any, a history's lines and drops since its last update, when any, or the bytes waiting for an
attach's subscriber, when any; then it has told them. -/
def flushed (s : State) (id : Id) : State × List Effect :=
  match s.phase, s.watching id with
  | .ready _, some (.screen told latest) =>
    (s.setWatch id (.screen latest latest),
      if told = latest then []
      else
        [.send (.notify "session/screen/changed" (Screen.changed id (Screen.changes told latest)))])
  | .ready _, some (.history pending) =>
    (s.setWatch id (.history {}),
      if pending.tail = [] ∧ pending.dropped = 0 then []
      else [.send (.notify "session/history/changed" (Log.changed id pending))])
  | .ready _, some (.stream dec pending) =>
    (s.setWatch id (.stream dec []),
      if pending = [] then [] else [.send (.notify "session/output" (Output.update id pending))])
  | _, _ => (s, [])

/-- What a connection does when a watch ends: one not answered yet is answered with what it found
and what it said; an open one sends its last update, `closed` with what it found; and it holds the
watch no more. -/
def unwatched (s : State) (id : Id) (found : Api.Found) (said : Log String) : State × List Effect :=
  match s.phase, s.watching id with
  | .ready _, some (.asked _) | .ready _, some .attaching =>
    (s.dropWatch id, [.send (.result id (result found (saidShows said)))])
  | .ready _, some (.stream _ pending) =>
    (s.dropWatch id,
      [.send (.notify "session/output" (Output.update id pending (some (closedResult found))))])
  | .ready _, some (.screen told latest) =>
    (s.dropWatch id,
      [.send
          (.notify "session/screen/changed"
            (Screen.changed id (Screen.changes told latest) (some (closedResult found))))])
  | .ready _, some (.history pending) =>
    (s.dropWatch id,
      [.send
          (.notify "session/history/changed" (Log.changed id pending (some (closedResult found))))])
  | _, _ => (s, [])

/-- **What a connection does with an event.** Before it is ready it writes nothing but errors and
the result of `initialize`, and performs nothing, and it sends `sessions/changed` only to the open
subscription (`serve_negotiated`): a listing's records replace the latest it holds and send nothing,
and each time the writer is free it sends the records that differ from those it last told the
subscriber, and the keys that went, when any do (`changed_exactly`, `table_converges`); a read of an
attach's connection keeps what an attach client would write of it for the attach's subscriber
(`serve_attach_exact`). -/
def step (s : State) : Event → State × List Effect
  | .received (.invalid id unparsed) =>
    (s,
      [.send
          (match unparsed with
          | some reason => .error none (-32700) "parse error" (refusal { reason? := some reason })
          | none => .error id (-32600) "invalid request" (refusal))])
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
              (.notify "sessions/changed"
                (changed id (changes told latest) (removed told latest)))])
    | _, _, _, _ => (s, [])
  | .watched id screen left => watched s id screen left
  | .flush id => flushed s id
  | .unwatched id found said => unwatched s id found said
  | .read id bytes => readAttach s id bytes

/-! ## Messages as lines -/

/-- The members a JSON-RPC 2.0 request or notification defines. -/
def envelope : List String := ["id", "jsonrpc", "method", "params"]

/-- **What a line from the client is**: a request, with an id, a notification, without one, or no
message: a line that is not canonical JSON, with the reason ExactJSON gives (`Value.parse`), or a
canonical text that is no JSON-RPC 2.0 request object, among them an object with a member JSON-RPC
does not define. -/
def decode (line : String) : Message :=
  match ExactJSON.Value.parse line with
  | .error reason => .invalid none (some reason)
  | .ok (.table members) =>
    let fields := members.toList
    let id := (fields.lookup "id").bind Id.of
    if !(fields.all fun field => envelope.contains field.1) then .invalid id none
    else
      if fields.lookup "jsonrpc" != some (.string "2.0") then .invalid id none
      else
        match fields.lookup "method", fields.lookup "id" with
        | some (.string method), none =>
          .notification method ((fields.lookup "params").getD (.table #[]))
        | some (.string method), some _ =>
          match id with
          | some id => .request id method ((fields.lookup "params").getD (.table #[]))
          | none => .invalid none none
        | _, _ => .invalid id none
  | .ok _ => .invalid none none

/-- A message as JSON-RPC 2.0's object, its members by increasing key. -/
def Outgoing.json : Outgoing → ExactJSON.Value
  | .result id value => .table #[("id", id.json), ("jsonrpc", .string "2.0"), ("result", value)]
  | .error id code message data =>
    .table
      #[("error", .table #[("code", .integer code), ("data", data), ("message", .string message)]),
        ("id", (id.map Id.json).getD .null), ("jsonrpc", .string "2.0")]
  | .notify method params =>
    .table #[("jsonrpc", .string "2.0"), ("method", .string method), ("params", params)]

/-- The line `serve` writes for a message: its JSON text (`Value.render`), which holds no C0
control, DEL, C1 control, U+2028 or U+2029 as itself (ExactJSON's `render_no_control`), so no
newline, then one. -/
def line (out : Outgoing) : String := (ExactJSON.Value.render out.json).push '\n'

/-- Text as `serve` sends it: every control character, C0, DEL and C1, as U+FFFD, as listings and
`info` records give it (`Render.textChar`). -/
def clean (text : String) : String := Linger.Display.Listing.clean text

/-- Listing rows as `serve` sends them: their records, each key and value clean text
(`Listing.records`). -/
def records (rows : List (List (String × String))) : List Record :=
  Linger.Display.Listing.records rows

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

/-- A line `serve` read as a message: its text's (`decode`), and a line that is not UTF-8 is no
canonical text. -/
def Received.message : Received → Message
  | .text bytes =>
    match String.fromUTF8? (ByteArray.mk bytes.toArray) with
    | some line => decode line
    | none => .invalid none (some "a line that is not UTF-8")
  | .overlong => .invalid none none

/-! ## Remote hosts through `serve`

A command on a remote session calls its host's `serve` with the method and params of its request
there (`Remote.call`), after the handshake (`Remote.lines`), and reads the host's answer of what
the host wrote (`Remote.heard`): the answer of the call, by name and code (`answerNamed`), with the
members of its result; a host that refused `serve` with a usage answer, as a linger from before it
does, is refused. A remote attach relays the host's stream to an attach client as frames
(`Remote.relay`) and the client's keys, size and leaving as the requests of the attach's
conversation (`Remote.up`). -/

/-- A request, with this id, as the line linger writes a host's `serve`, its members by increasing
key. -/
def Remote.request (id : Nat) (method : String) (params : ExactJSON.Value) : String :=
  (ExactJSON.Value.render
        (.table
          #[("id", .integer id), ("jsonrpc", .string "2.0"), ("method", .string method),
            ("params", params)])).push
    '\n'

/-- A notification as the line linger writes a host's `serve`. -/
def Remote.notification (method : String) (params : ExactJSON.Value) : String :=
  (ExactJSON.Value.render
        (.table #[("jsonrpc", .string "2.0"), ("method", .string method), ("params", params)])).push
    '\n'

/-- The handshake linger writes a host's `serve`: `initialize`, request 1, asking for the version
this linger speaks, and `initialized`. -/
def Remote.handshake : String :=
  Remote.request 1 "initialize"
      (ExactJSON.toValue
        ({ capabilities? := some {}, clientInfo? := some { name := "linger", version? := none },
           protocolVersion := "1" } :
          Initialize)) ++
    Remote.notification "initialized" (ExactJSON.toValue ({} : NoParams))

/-- **The lines linger writes a host's `serve` for a call**: the handshake, then the call, request
2; then its standard input ends, and `serve` answers what it read and ends. -/
def Remote.lines (method : String) (params : ExactJSON.Value) : String :=
  Remote.handshake ++ Remote.request 2 method params

/-- A method's params that name only a session. -/
def Remote.named (name : String) : ExactJSON.Value := ExactJSON.toValue ({ name } : Named)

/-- `session/attach`'s params: the session, read-only on request, and its command, when one is
given. -/
def Remote.attaching (name : String) (readOnly : Bool) (command : List String) : ExactJSON.Value :=
  ExactJSON.toValue
    ({ command? := if command.isEmpty then none else some command, name,
       readOnly? := if readOnly then some true else none } :
      Attaching)

/-- **The call a request at a host's session makes**, the session `name` there, its standard
input `input`: the method of the request's operation and the params that carry each of its
arguments (`Remote.asked`), as JSON, so no word reaches a shell; none for a request no method
performs on one session. -/
def Remote.call (request : Api.Request) (name : String) (input : List UInt8) :
    Option (String × ExactJSON.Value) :=
  match request with
  | .attach readOnly _ command => some ("session/attach", Remote.attaching name readOnly command)
  | .list (.named _ _) =>
    some ("sessions/list", ExactJSON.toValue ({ names? := some [name] } : Listed))
  | .list _ => none
  | .start _ program args =>
    some ("session/start", ExactJSON.toValue ({ args? := some args, name, program } : Starting))
  | .resume _ => some ("session/resume", Remote.named name)
  | .send _ (.text words) =>
    some
      ("session/send",
        ExactJSON.toValue
          ({ data := Base64.encode (String.intercalate " " words).toUTF8.toList, name } : Sending))
  | .send _ .stdin =>
    some ("session/send", ExactJSON.toValue ({ data := Base64.encode input, name } : Sending))
  | .detach _ => some ("session/detach", Remote.named name)
  | .kill _ => some ("session/kill", Remote.named name)
  | .rename _ new => some ("session/rename", ExactJSON.toValue ({ name, new } : Renaming))
  | .capture history _ =>
    some ("session/capture", ExactJSON.toValue ({ history? := some history, name } : Capturing))
  | .resize _ cols rows =>
    some ("session/resize", ExactJSON.toValue ({ cols, name, rows } : Resizing))
  | .wait _ => some ("session/wait", Remote.named name)
  | .upgrade _ => some ("session/upgrade", Remote.named name)
  | .serve => none

/-- Whether a host's `serve` shook hands (`Remote.Shook`): its result of `initialize` is exactly a
`Welcome` of a version this linger speaks. -/
def Remote.shook (messages : List ExactJSON.Value) : Bool :=
  match (Remote.answerOf messages 1 "result").bind (exactly (α := Welcome)) with
  | some welcome => versions.contains welcome.protocolVersion
  | none => false

/-- Whether `initialize`'s error, in a host's messages, is the usage answer. -/
def Remote.refusedUsage (messages : List ExactJSON.Value) : Bool :=
  match ((Remote.answerOf messages 1 "error").bind (member? "data")).bind (member? "answer") with
  | some (.string "usage") => true
  | _ => false

/-- Whether a host refused `serve` with a usage answer (`Remote.Usage`). -/
def Remote.usage (messages : List ExactJSON.Value) (status : UInt32) : Bool :=
  !Remote.shook messages && (status == 2 || Remote.refusedUsage messages)

/-- The answer named `name` whose code is `code`, as a result gives an answer (`answered`): none
for a name no answer has, or a code that is not the named answer's. -/
def answerNamed (name : String) (code : Nat) : Option Os.Answer :=
  (([.done, .notDone, .usage, .timedOut, .failed, .cannotRun, .notFound, .cancelled] ++
          (if 128 ≤ code ∧ code < 384 then
            [.stopped (code - 128).toUInt8, .saved (code - 128).toUInt8]
          else []) ++
          if code < 4294967296 then [.program code.toUInt32] else [] :
        List Os.Answer)).find?
    fun answer => answerName answer == name && answer.code.toNat == code

/-- The answer a result's `answer` and `code` give, by name and code, and what it shows, of a value
read exactly as a result (`exactly`). -/
def Remote.answerIn (value : ExactJSON.Value) : Option (Os.Answer × Shows) :=
  (exactly value : Option Result).bind fun result =>
    (answerNamed result.answer result.code).map ((·, result.toShows))

/-- What answered the call, request 2: its result, or, where no result did, its error's `data`. -/
def Remote.callAnswer (messages : List ExactJSON.Value) : Option ExactJSON.Value :=
  (Remote.answerOf messages 2 "result").or
    ((Remote.answerOf messages 2 "error").bind (member? "data"))

/-- **What a host's `serve` told linger of its call**, of the messages it wrote and its command's
exit status: the answer of the call and what its result shows, once it shook hands; a refusal when
it refused `serve` with a usage answer; and otherwise nothing linger reads. -/
def Remote.heard (messages : List ExactJSON.Value) (status : UInt32) : Remote.Heard :=
  if Remote.shook messages then
    match (Remote.callAnswer messages).bind Remote.answerIn with
    | some (answer, shows) => .answered answer shows
    | none => .silent
  else if Remote.usage messages status then .refused else .silent

/-- A host's row of a record its `sessions/list` returned: `name@host`, its command as clean text,
its state, and the status and attention its record gives (`Listing.rowStatus`). -/
def Remote.row (host : String) (record : Record) : Record :=
  let live := (record.text? "state").getD "live" == "live"
  Linger.Display.Listing.Record.ofRow
    ([("name", record.key ++ "@" ++ host),
        ("cmd", Linger.Target.Remote.scrub ((record.text? "cmd").getD "")),
        ("state", if live then "live" else "resumable")] ++
      Linger.Display.Listing.statusFields
        (Linger.Display.Listing.rowStatus
          (.remote live ((record.text? "attention").getD "") ((record.text? "status").getD ""))))

/-- **A host's rows**: one for each record its `sessions/list` returned whose name a target takes
(`Name.accept`), in order, named `name@host`. -/
def Remote.rows (host : String) (records : List Record) : List Record :=
  (records.filter fun record => Linger.Target.Name.accept record.key == some record.key).map
    (Remote.row host)

/-- A host's record of one of its sessions, as `ls name@host` lists it: every field the host gave,
its name `name@host`; none for a record whose name a target does not take. -/
def Remote.record (host : String) (record : Record) : Option Record :=
  if Linger.Target.Name.accept record.key == some record.key then
    some (record.insert "name" (.text (record.key ++ "@" ++ host)))
  else none

/-- What a host's answer says it said, each line as its host's: `host: ` and the line, the host as
clean text. -/
def Remote.said (host : String) (shows : Shows) : List String :=
  (shows.said?.getD []).map fun text =>
    Linger.Target.Remote.scrub host ++ ": " ++ Linger.Target.Remote.scrub text

/-- How a session ended, of the record a host's answer gives of it (`Session.endingFields`): none
for a record no ending gives. -/
def Remote.endingOf (fields : Record) : Option Linger.Session.Ending :=
  let small (field : Option Linger.Display.Listing.Field) : Option UInt8 :=
    match field with
    | some (.count n) => if n < 256 then some n.toUInt8 else none
    | _ => none
  match fields["saved"]? with
  | some n => (small (some n)).map .saved
  | none =>
    if fields.text? "outcome" == some "unknown" then some (.program .unknown)
    else
      match fields["signal"]? with
      | some n => (small (some n)).map fun signal => .program (.signaled signal)
      | none =>
        match fields["exit"]? with
        | some n => (small (some n)).map fun code => .program (.exited code)
        | none => if fields.isEmpty then some .dismissed else none

/-- **What a remote command found**, of the host's answer and what its result shows: how the
session ended, when the result says it and its answer is the host's, and otherwise the host's
answer as it gave it. Either way, its answer is the host's. -/
def Remote.found (answer : Os.Answer) (shows : Shows) : Api.Found :=
  match shows.ending?.bind Remote.endingOf with
  | some ending => if ending.answer = answer then .ended ending else .heard answer
  | none => .heard answer

/-! ## A remote attach -/

/-- The frames of output bytes: runs of at most `Wire.inputChunk` bytes, in order. -/
def Remote.outputFrames (bytes : List UInt8) : List Linger.Session.Wire.Msg :=
  (Linger.Session.Wire.inputChunks bytes).map .output

/-- `the far attach ended`, in ASCII: what a refusal that ends a remote attach says. -/
def Remote.endedText : List UInt8 :=
  [116, 104, 101, 32, 102, 97, 114, 32, 97, 116, 116, 97, 99, 104, 32, 101, 110, 100, 101, 100]

/-- The message that ends an attach as the host's stream's `closed` says it ended, read exactly as a
result (`exactly`): how its program ended, or that a signal saved it, as its daemon would say, and
otherwise a refusal, whose answer the bridge keeps. -/
def Remote.ending (closed : ExactJSON.Value) : Linger.Session.Wire.Msg :=
  match ((exactly closed : Option Result).bind (·.ending?)).bind Remote.endingOf with
  | some (.program outcome) => .ended outcome
  | some (.saved signal) => .saved signal
  | _ => .err Remote.endedText

/-- A string value's text. -/
def Remote.text? : ExactJSON.Value → Option String
  | .string text => some text
  | _ => none

/-- An array of strings, their texts. -/
def Remote.texts? : ExactJSON.Value → Option (List String)
  | .array items => items.toList.mapM Remote.text?
  | _ => none

/-- **What linger relays to its attach client of a line the host's `serve` wrote** for the attach
`id`: an update of the attach's stream, `session/output` naming it, as the frames of the bytes it
carries, then, when it carries `closed`, the message that ends the attach (`Remote.ending`); the
answer of the attach's request, when it is no `done`, as a refusal that says what the host said;
and nothing of any other line. -/
def Remote.relay (id : Id) (message : ExactJSON.Value) : List Linger.Session.Wire.Msg :=
  match member? "method" message, member? "params" message with
  | some (.string "session/output"), some params =>
    if (member? "subscription" params).bind Id.of = some id then
      let bytes :=
        match member? "data" params with
        | some (.string text) => (Base64.decode text.toList).getD []
        | _ => []
      Remote.outputFrames bytes ++
        match member? "closed" params with
        | some closed => [Remote.ending closed]
        | none => []
    else []
  | _, _ =>
    if (member? "id" message).bind Id.of = some id then
      match member? "result" message with
      | some result =>
        if (member? "answer" result).bind Remote.text? = some "done" then []
        else
          let said := ((member? "said" result).bind Remote.texts?).getD []
          let answer := ((member? "answer" result).bind Remote.text?).getD "unknown"
          [.err
              ((Linger.Target.Remote.scrub
                      (if said.isEmpty then s!"the attach was refused: {answer}"
                      else String.intercalate "; " said)).take
                  1024).copy.toUTF8.toList]
      | none =>
        let error := ((member? "error" message).bind (member? "message")).bind Remote.text?
        [.err
            ((Linger.Target.Remote.scrub (error.getD "the attach was refused")).take
                1024).copy.toUTF8.toList]
    else []

/-- **The params of the `session/input` that carries keys** to the attach `id`: the keys in
base64, and its subscription. -/
def Remote.keys (id : Id) (bytes : List UInt8) : ExactJSON.Value :=
  ExactJSON.toValue ({ data := Base64.encode bytes, subscription := id } : Keys)

/-- `session/resize` of the attach `id`, request `next`, to a terminal's size, the emulator's, at
most 1000 either way (`Vt.clampDim`). -/
def Remote.sized (id : Id) (next : Nat) (cols rows : UInt32) : String :=
  Remote.request next "session/resize"
    (ExactJSON.toValue
      ({ cols := Terminal.Vt.clampDim cols.toNat, rows := Terminal.Vt.clampDim rows.toNat,
         subscription := id } :
        Sized))

/-- What linger writes the host's `serve` of a message an attach client sends the attach `id`,
`next` the id of the next request: `session/attach` of the session `name`, with its mode and its
command, then, for a writable attach whose terminal has a size, `session/resize` to it
(`Remote.sized`); the keys as `session/input`; the terminal's size as `session/resize`; and nothing
of any other message. -/
def Remote.up (id : Id) (name : String) (command : List String) (next : Nat) :
    Linger.Session.Wire.Msg → List String
  | .attach mode cols rows =>
    let readOnly := mode == .readOnly
    let attached := Remote.request 2 "session/attach" (Remote.attaching name readOnly command)
    if readOnly || cols == 0 || rows == 0 then [attached]
    else [attached, Remote.sized id next cols rows]
  | .input bytes => [Remote.request next "session/input" (Remote.keys id bytes)]
  | .resize cols rows => if cols == 0 || rows == 0 then [] else [Remote.sized id next cols rows]
  | _ => []

/-- What linger writes the host's `serve` when the attach `id`'s client leaves: `session/detach`
of it, the session running on. -/
def Remote.leave (id : Id) (next : Nat) : String :=
  Remote.request next "session/detach" (ExactJSON.toValue ({ subscription := id } : Subscription))

end Linger.App.Serve
