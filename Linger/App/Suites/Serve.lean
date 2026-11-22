module

public import Verify.Harness
public import Linger.App.CoreSpec
public import Linger.App.CoreCode.Json
import Linger.Selector.CoreCode.Picker

public section

/-! # `linger serve`: linger's operations as JSON-RPC 2.0 over a child's pipes

A client runs `linger serve` as a child with its three streams on pipes, in the suite's
namespace, and speaks JSON-RPC 2.0 to it, one message a line. Before the handshake a request is
refused with -32002 and starts nothing, and an `initialize` that asks for a version `serve` does
not speak is refused with the versions it speaks; `initialize` then answers with the version and
the methods, and until `initialized` a request is still refused. After it, the client lists,
starts a session, sends it input as base64, captures its screen and reads what it printed, waits
for its program's ending and kills another, and subscribes to the sessions' table, which sends
`sessions/changed` when a record changes, but not for a quiet session, and nothing once closed: each result carries the answer the command line
exits with, by name and code. A method `serve` does not answer, params it does not take and a line
that is no JSON get JSON-RPC's errors. Once its standard input ends, `serve` exits 0. -/

namespace Linger.App.Suites.Serve

open Verify.Harness
open Os.Shell
open Linger.App.Serve

/-- A `linger serve` child: its process, the handle of its standard input while the suite holds it
open, and the lines it wrote so far. -/
structure Peer where
  /-- The child, its standard input taken. -/
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }
  /-- Its standard input, until the suite closes it. -/
  input : IO.Ref (Option IO.FS.Handle)
  /-- The lines it wrote so far. -/
  lines : IO.Ref (Array String)

/-- Start `linger serve` in the suite's namespace, reading what it writes on a thread of its own. -/
def Peer.start (e : Env) : IO Peer := do
  let child0 ←
    IO.Process.spawn
        { cmd := e.bin, args := #["serve"], env := e.procEnv, stdin := .piped, stdout := .piped,
          stderr := .piped }
  let (handle, child) ← child0.takeStdin
  let input ← IO.mkRef (some handle)
  let lines ← IO.mkRef (#[] : Array String)
  let out := child.stdout
  discard <|
      IO.asTask
        (do
          let mut reading := true
          while reading do
            let line ← out.getLine
            if line.isEmpty then
              reading := false
            else
              lines.modify (·.push line))
        Task.Priority.dedicated
  return { child, input, lines }

/-- Write one line to the peer. -/
def Peer.say (p : Peer) (line : String) : IO Unit := do
  if let some handle← p.input.get then
    handle.putStr (line ++ "\n")
    handle.flush

/-- A request, as JSON-RPC 2.0's object. -/
def request (id : Nat) (method : String) (params : Json) : String :=
  Json.render
    (.obj
      [("jsonrpc", .str "2.0"), ("id", .number (toString id)), ("method", .str method),
        ("params", params)])

/-- A notification, as JSON-RPC 2.0's object. -/
def notification (method : String) : String :=
  Json.render (.obj [("jsonrpc", .str "2.0"), ("method", .str method), ("params", .obj [])])

/-- The value at a path of members. -/
def at? : Json → List String → Option Json
  | value, [] => some value
  | value, key :: rest => (value.member? key).bind (at? · rest)

/-- The text of the number or string at a path. -/
def textAt? (value : Json) (path : List String) : Option String :=
  match at? value path with
  | some (.number text) => some text
  | some (.str text) => some text
  | _ => none

/-- The message the peer wrote whose id is `id`, once it has written it, within `ms`. -/
def Peer.answer (p : Peer) (id : Nat) (ms : Nat := patienceMs) : IO (Option Json) := do
  let found ← IO.mkRef (none : Option Json)
  discard <|
      waitFor ms do
        for line in ← p.lines.get do
          if let some message := Json.parse line then
            if textAt? message ["id"] == some (toString id) then
              found.set (some message)
              return true
        return false
  found.get

/-- Close the peer's standard input and give its exit status, or none if it outlived `hangMs`. -/
def Peer.close (p : Peer) : IO (Option UInt32) := do
  p.input.set none
  waitOrKill p.child hangMs

/-- The answer of a result, by name and code. -/
def answerOf (message : Option Json) : Option (String × String) := do
  let message ← message
  let name ← textAt? message ["result", "answer"]
  let code ← textAt? message ["result", "code"]
  pure (name, code)

/-- The code of an error. -/
def errorOf (message : Option Json) : Option String := message.bind (textAt? · ["error", "code"])

/-- The names of a result's records. -/
def namesOf (message : Option Json) : List String :=
  match message.bind (at? · ["result", "records"]) with
  | some (.arr records) => records.filterMap (textAt? · ["name"])
  | _ => []

/-- The params of a request for the session `name`, with `more` members. -/
def named (name : String) (more : List (String × Json) := []) : Json :=
  .obj (("name", .str name) :: more)

/-- The screen a capture's result shows, as text. -/
def screenOf (message : Option Json) : String :=
  match (message.bind (textAt? · ["result", "data"])).bind (Base64.decode ·.toList) with
  | some bytes => (String.fromUTF8? (ByteArray.mk bytes.toArray)).getD ""
  | none => ""

/-- The handshake, a request before it, a version mismatch and a request between `initialize`
and `initialized`, each refused and changing nothing. -/
private def handshake (e : Env) (p : Peer) : IO Unit := do
  p.say
      (request 1 "session/start"
        (.obj [("name", .str "early"), ("program", .str "/bin/sleep"), ("args", .arr [.str "30"])]))
  let early ← p.answer 1
  expect
      (errorOf early == some "-32002" &&
        textAt? (early.getD .null) ["error", "data", "answer"] == some "usage")
      s!"a request before initialize gets -32002, linger's answer usage ({errorOf early})"
  p.say
      (request 2 "initialize"
        (.obj
          [("protocolVersion", .str "999"), ("clientInfo", .obj [("name", .str "serve-suite")]),
            ("capabilities", .obj [])]))
  let mismatch ← p.answer 2
  expect
      (errorOf mismatch == some "-32602" &&
        (match mismatch.bind (at? · ["error", "data", "supported"]) with
        | some (.arr [.str "1"]) => true
        | _ => false))
      s!"an initialize asking for a version serve does not speak gets -32602 and the versions it speaks ({errorOf mismatch})"
  p.say
      (request 3 "initialize"
        (.obj
          [("protocolVersion", .str "1"), ("clientInfo", .obj [("name", .str "serve-suite")]),
            ("capabilities", .obj [])]))
  let welcome ← p.answer 3
  let methods :=
    match welcome.bind (at? · ["result", "capabilities", "methods"]) with
    | some (.arr items) => items.filterMap Json.text?
    | _ => []
  expect
      (welcome.bind (textAt? · ["result", "protocolVersion"]) == some "1" &&
        welcome.bind (textAt? · ["result", "serverInfo", "name"]) == some "linger" &&
        methods.contains "sessions/list" &&
        methods.contains "session/wait")
      s!"initialize answers the version asked for, the server linger and its methods ({methods})"
  p.say (request 4 "sessions/list" (.obj []))
  let between ← p.answer 4
  expect (errorOf between == some "-32002")
      s!"a request between initialize and initialized gets -32002 ({errorOf between})"
  let (rc, _, _) ← e.cli #["ls", "early", "--porcelain"]
  expect (rc == 127)
      s!"the requests refused before the handshake changed nothing: no session early (ls exit {rc})"

/-- Capture `name`'s screen through the peer until it shows `text`, requests numbered from
`first`; the last capture's result. -/
private def captureUntil (p : Peer) (name text : String) (first : Nat) : IO (Option Json) := do
  let next ← IO.mkRef first
  let last ← IO.mkRef (none : Option Json)
  discard <|
      waitFor patienceMs do
        let id ← next.modifyGet fun id => (id, id + 1)
        p.say (request id "session/capture" (named name))
        let captured ← p.answer id
        last.set captured
        return (screenOf captured).contains text
  last.get

/-- The `sessions/changed` notifications the peer wrote so far. -/
def Peer.changes (p : Peer) : IO (List Json) := do
  return (← p.lines.get).toList.filterMap fun line =>
      (Json.parse line).filter fun message => textAt? message ["method"] == some "sessions/changed"

/-- The names of the records a notification carries. -/
def recordsOf (message : Json) : List String :=
  match at? message ["params", "records"] with
  | some (.arr records) => records.filterMap (textAt? · ["name"])
  | _ => []

/-- The sessions table: a subscription's result lists the sessions; starting one sends a
`sessions/changed` that names the subscription and carries its record; once its program has
printed and gone quiet, the session sends none for three listings, though its record's `idle`
ticks each second; and once `sessions/unsubscribe` closes the subscription, a session's ending
sends none. -/
private def table (p : Peer) : IO Unit := do
  p.say (notification "initialized")
  p.say (request 20 "sessions/subscribe" (.obj []))
  let opened ← p.answer 20
  expect (answerOf opened == some ("done", "0") && !(namesOf opened).contains "watched")
      s!"sessions/subscribe answers done with the sessions' records ({answerOf opened})"
  -- the program prints once, then waits for a line that never comes, so from then on only its
  -- record's `idle` changes, each second
  p.say
      (request 21 "session/start"
        (.obj
          [("name", .str "watched"), ("program", .str "/bin/sh"),
            ("args", .arr [.str "-c", .str "printf 'watched-ready'; read line"])]))
  let started ← p.answer 21
  let told ←
    waitFor patienceMs do
        return (← p.changes).any fun message =>
            match at? message ["params", "records"] with
            | some (.arr records) =>
              records.any fun record =>
                textAt? record ["name"] == some "watched" && (at? record ["idle"]).isSome
            | _ => false
  let allNamed :=
    (← p.changes).all fun message => textAt? message ["params", "subscription"] == some "20"
  expect (answerOf started == some ("done", "0") && told && allNamed)
      s!"a started session's record comes in a sessions/changed that names subscription 20 ({answerOf started}, {told}, {allNamed})"
  let before := (← p.changes).length
  let restless ←
    waitFor 3500 do
        return (← p.changes).length != before
  expect (!restless)
      s!"a quiet session sends no sessions/changed in 3.5 s, three listings, though its idle ticks ({(← p.changes).length - before} more)"
  p.say (request 22 "sessions/unsubscribe" (.obj [("subscription", .number "20")]))
  let closed ← p.answer 22
  let after := (← p.changes).length
  p.say (request 23 "session/kill" (named "watched"))
  let killed ← p.answer 23
  let heard ←
    waitFor 3500 do
        return (← p.changes).length != after
  expect (answerOf closed == some ("done", "0") && answerOf killed == some ("done", "0") && !heard)
      s!"once sessions/unsubscribe closes it, a session's ending sends no sessions/changed ({answerOf closed}, {heard})"

/-- The operations, each as a request, and the errors. -/
private def operations (e : Env) (p : Peer) : IO Unit := do
  p.say (request 5 "sessions/list" (.obj []))
  let listed ← p.answer 5
  expect (answerOf listed == some ("done", "0") && !(namesOf listed).contains "early")
      s!"sessions/list answers done, code 0, with no session early ({answerOf listed})"
  let program := "printf 'serve-ready\\n'; read line; printf 'got %s\\n' \"$line\"; exit 3"
  p.say
      (request 6 "session/start"
        (.obj
          [("name", .str "echo"), ("program", .str "/bin/sh"),
            ("args", .arr [.str "-c", .str program])]))
  let started ← p.answer 6
  let ready ← captureUntil p "echo" "serve-ready" 100
  expect (answerOf started == some ("done", "0") && (screenOf ready).contains "serve-ready")
      s!"session/start runs the program, and session/capture's base64 data shows its screen ({answerOf started})"
  p.say
      (request 7 "session/send"
        (named "echo" [("data", .str (Base64.encode "hello\r".toUTF8.toList))]))
  let sent ← p.answer 7
  let got ← captureUntil p "echo" "got hello" 200
  expect (answerOf sent == some ("done", "0") && (screenOf got).contains "got hello")
      s!"session/send delivers its base64 data as the program's input ({answerOf sent})"
  p.say (request 8 "session/wait" (named "echo"))
  let waited ← p.answer 8
  expect
      (answerOf waited == some ("program", "3") &&
        waited.bind (textAt? · ["result", "ending", "exit"]) == some "3")
      s!"session/wait answers the program's ending, program 3, as wait exits ({answerOf waited})"
  p.say
      (request 9 "session/start"
        (.obj
          [("name", .str "doomed"), ("program", .str "/bin/sleep"), ("args", .arr [.str "300"])]))
  let doomed ← p.answer 9
  p.say (request 10 "session/kill" (named "doomed"))
  let killed ← p.answer 10
  let (rc, _, _) ← e.cli #["wait", "doomed"]
  expect
      (answerOf doomed == some ("done", "0") && answerOf killed == some ("done", "0") && rc == 129)
      s!"session/kill ends the session, which wait then answers was killed ({answerOf killed}, wait exit {rc})"
  p.say (request 11 "session/teleport" (named "echo"))
  let unknown ← p.answer 11
  expect (errorOf unknown == some "-32601")
      s!"a method serve does not answer gets -32601 ({errorOf unknown})"
  p.say (request 12 "session/kill" (.obj []))
  let invalid ← p.answer 12
  expect (errorOf invalid == some "-32602")
      s!"params a method does not take get -32602 ({errorOf invalid})"
  p.say "{\"jsonrpc\": \"2.0\", \"id\": 13, \"method\": "
  let unparsed ← IO.mkRef (none : Option Json)
  discard <|
      waitFor patienceMs do
        for line in ← p.lines.get do
          if let some message := Json.parse line then
            if errorOf (some message) == some "-32700" then
              unparsed.set (some message)
              return true
        return false
  expect ((← unparsed.get).bind (at? · ["id"]) matches some .null)
      "a line that is no JSON gets -32700, with no id"

/-- The chooser and a client read the same list: the records `sessions/list` sends are, under each
name and in order, what the chooser reads from `ls --porcelain`, as it reads the listing it runs,
read without `idle`, which a second listing may read a second later. -/
private def sameList (e : Env) (p : Peer) : IO Unit := do
  p.say
      (request 29 "session/start"
        (.obj
          [("name", .str "steady"), ("program", .str "/bin/sleep"), ("args", .arr [.str "300"])]))
  let _ ← p.answer 29
  p.say (request 30 "sessions/list" (.obj []))
  let listed ← p.answer 30
  let (rc, printed, _) ← e.cli #["ls", "--porcelain"]
  let served : List (List (String × String)) :=
    match listed.bind (at? · ["result", "records"]) with
    | some (.arr records) =>
      records.filterMap fun record =>
        match record with
        | .obj members => members.mapM fun (key, value) => value.text?.map ((key, ·))
        | _ => none
    | _ => []
  let unticked (record : List (String × String)) := record.filter (·.1 != "idle")
  let name (record : List (String × String)) := (record.lookup "name").getD ""
  let read := Linger.Selector.Picker.parseSnapshot printed
  let same :=
    match read with
    | .ok snapshot =>
      rc == 0 && !served.isEmpty && snapshot.candidates == served.map name &&
        served.all fun record => unticked (snapshot.row (name record)) == unticked record
    | .error _ => false
  expect same
      s!"the chooser reads from ls --porcelain, under each name and in order, the records sessions/list sends ({served.map name})"

/-- The suite. -/
def run : IO UInt32 :=
  Env.suite "serve" fun e => do
    let p ← Peer.start e
    try
      handshake e p
      table p
      operations e p
      sameList e p
      let rc ← p.close
      expect (rc == some 0) s!"once its standard input ends, serve exits 0 ({rc})"
    finally
      reapOrKill p.child 1000
      e.endSessions

end Linger.App.Suites.Serve
