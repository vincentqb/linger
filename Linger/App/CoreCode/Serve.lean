module

public import Linger.App.CoreSpec
public import Linger.App.CoreCode.Json
import Linger.App.CoreCode.Api
import Linger.Os.CoreCode.Answer
import Linger.Session.CoreCode
import Terminal.CoreCode.Render
import Terminal.CoreCode.Mediation

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

/-- A connection's state: where it stands in its handshake. -/
structure StateRec where
  /-- Where the handshake stands. -/
  stage : Phase := .fresh

/-- A connection's state. -/
abbrev State : Type := StateRec

/-- A connection before any message. -/
def State.init : State := {}

/-- Where a connection stands in its handshake. -/
def State.phase (s : State) : Phase := s.stage

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

/-- What a connection does with a request: `initialize` once, before anything else, then the
methods `methods` lists, each performed as its command line's request (`parse`). -/
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
      if (methods.lookup method).isSome then
        match parse method params with
        | some (req, bytes) => (s, [.perform id method req bytes])
        | none => (s, [.send (.error (some id) (-32602) "invalid params" (refusal))])
      else (s, [.send (.error (some id) (-32601) "method not found" (refusal))])
    | _ => (s, [.send (notInitialized id)])

/-- **What a connection does with an event.** Before it is ready it writes nothing but errors and
the result of `initialize`, and performs nothing (`serve_negotiated`). -/
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

/-! ## Messages as lines -/

/-- A JSON value as a request id. -/
def Id.of : Json → Option Id
  | .number text => some (.number text)
  | .str text => some (.str text)
  | _ => none

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
def clean (text : String) : String := text.map Terminal.Render.textChar

/-- Listing records as `serve` sends them: each key and value clean text (`clean`). -/
def records (rows : List (List (String × String))) : List (List (String × String)) :=
  rows.map fun row => row.map fun (key, value) => (clean key, clean value)

/-- A record as a JSON object, a string member for each field. -/
def Record.json (row : List (String × String)) : Json :=
  .obj (row.map fun (key, value) => (key, .str value))

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
inductive Line where
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
def Lines.push (l : Lines) (b : UInt8) : Lines × Option Line :=
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
def Lines.feed (l : Lines) (bytes : List UInt8) : Lines × List Line :=
  let (last, ended) :=
    bytes.foldl
      (fun (acc : Lines × List Line) b =>
        match acc.1.push b with
        | (next, some ended) => (next, ended :: acc.2)
        | (next, none) => (next, acc.2))
      (l, [])
  (last, ended.reverse)

end Linger.App.Serve
