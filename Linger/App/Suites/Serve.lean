module

public import Verify.Harness
public import Linger.App.CoreSpec
public import Linger.App.CoreCode.Base64
public import Linger.Os.CoreCode.Json
import Linger.Selector.CoreCode.Picker
import Linger.Session.CoreCode.Checkpoint
import Terminal.CoreCode.Vt

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
exits with, by name and code. It watches a session's terminal as rows: the screen's table, whose
lines it keeps in a grid of its own and finds, after each step of the session's program, what
`capture` prints, with the cursor `info` reports, each update carrying only lines that changed and
the last one how the session ended; and the history's log, whose lines and drops are the lines that
scrolled off, as `capture --history` prints them. It attaches to a session as a terminal client
does: the stream's bytes, base64 in each update, open with the synchronized repaint, then carry
what the session prints; it types into the session, sizes it, detaches, and hears the session's
end in the stream's last update. A method `serve` does not answer, params it does not take and a
line that is no JSON get JSON-RPC's errors; every line the client writes is canonical JSON, and a
request that is not, one with a space, keys out of order or `1.0` for an integer, gets -32700 with
the reason and changes nothing; and `ls --porcelain` prints exactly the records `sessions/list`
returns, one canonical JSON line each. Once its standard input ends, `serve` exits 0. -/

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
              lines.modify (·.push (line.dropSuffix "\n").copy))
        Task.Priority.dedicated
  return { child, input, lines }

/-- Write one line to the peer. -/
def Peer.say (p : Peer) (line : String) : IO Unit := do
  if let some handle← p.input.get then
    handle.putStr (line ++ "\n")
    handle.flush

/-- A request, as JSON-RPC 2.0's object, in canonical text. -/
def request (id : Nat) (method : String) (params : Json) : String :=
  Json.render
    (.obj [("jsonrpc", .str "2.0"), ("id", .int id), ("method", .str method), ("params", params)])

/-- A notification, as JSON-RPC 2.0's object. -/
def notification (method : String) : String :=
  Json.render (.obj [("jsonrpc", .str "2.0"), ("method", .str method), ("params", .obj [])])

/-- The value at a path of members. -/
def at? : Json → List String → Option Json
  | value, [] => some value
  | value, key :: rest => (value.member? key).bind (at? · rest)

/-- The text of the integer or string at a path. -/
def textAt? (value : Json) (path : List String) : Option String :=
  match at? value path with
  | some (.int n) => some (toString n)
  | some (.str text) => some text
  | _ => none

/-- The message the peer wrote whose id is `id`, once it has written it, within `ms`. -/
def Peer.answer (p : Peer) (id : Nat) (ms : Nat := patienceMs) : IO (Option Json) := do
  let found ← IO.mkRef (none : Option Json)
  discard <|
      waitFor ms do
        for line in ← p.lines.get do
          if let .ok message := Json.parse line then
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
      (Json.parse line).toOption.filter fun message =>
        textAt? message ["method"] == some "sessions/changed"

/-- The names of the records a notification carries. -/
def recordsOf (message : Json) : List String :=
  match at? message ["params", "records"] with
  | some (.arr records) => records.filterMap (textAt? · ["name"])
  | _ => []

/-- The sessions table: a subscription's result lists the sessions; starting one sends a
`sessions/changed` that names the subscription and carries its record; once its program has
printed and gone quiet, the session sends none for three listings, though its record's `idle`
ticks each second and its `lastout` may read a second apart; and once `sessions/unsubscribe`
closes the subscription, a session's ending sends none. -/
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
  p.say (request 22 "sessions/unsubscribe" (.obj [("subscription", .int 20)]))
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
          if let .ok message := Json.parse line then
            if errorOf (some message) == some "-32700" then
              unparsed.set (some message)
              return true
        return false
  expect ((← unparsed.get).bind (at? · ["id"]) matches some .null)
      "a line that is no JSON gets -32700, with no id"

/-- The chooser and a client read the same list: the records `sessions/list` sends are, under each
name and in order, what the chooser reads from `ls --porcelain`, as it reads the listing it runs,
read without `idle` and `lastout`, which a second listing may read a second later. -/
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
  let unticked (record : List (String × String)) :=
    record.filter fun field => field.1 != "idle" && field.1 != "lastout"
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

/-- The `-32700` error the peer wrote since it had written `before` lines, within `ms`. -/
def Peer.unparsed (p : Peer) (before : Nat) (ms : Nat := patienceMs) : IO (Option Json) := do
  let found ← IO.mkRef (none : Option Json)
  discard <|
      waitFor ms do
        for line in (← p.lines.get).toList.drop before do
          if let .ok message := Json.parse line then
            if errorOf (some message) == some "-32700" then
              found.set (some message)
              return true
        return false
  found.get

/-- Lines that are not canonical JSON, each a request that would change a session: one with a
space after a member's colon, one whose keys are out of order and one with `1.0` where an integer
belongs, each answered -32700, with no id, its `data` linger's usage answer and the reader's reason,
and each changing nothing: no session starts, and none is resized. -/
private def refusals (e : Env) (p : Peer) : IO Unit := do
  p.say
      (request 35 "session/start"
        (.obj
          [("name", .str "fixed"), ("program", .str "/bin/sleep"), ("args", .arr [.str "300"])]))
  let started ← p.answer 35
  let cols ← e.info "fixed" "cols"
  let refused (line : String) : IO (Option Json × Option String) := do
    let before := (← p.lines.get).size
    p.say line
    let answer ← p.unparsed before
    return (answer, answer.bind (textAt? · ["error", "data", "reason"]))
  let unchanged (answer : Option Json) :=
    answer.bind (at? · ["id"]) matches some .null &&
      answer.bind (textAt? · ["error", "data", "answer"]) == some "usage"
  let (spaced, spacedWhy) ←
    refused
        "{\"id\":36,\"jsonrpc\": \"2.0\",\"method\":\"session/start\",\"params\":{\"args\":[\"300\"],\"name\":\"spaced\",\"program\":\"/bin/sleep\"}}"
  let (rc, _, _) ← e.cli #["ls", "spaced", "--porcelain"]
  expect
      (answerOf started == some ("done", "0") && unchanged spaced &&
        (spacedWhy.getD "").startsWith "at character 19: whitespace" &&
        rc == 127)
      s!"a request with a space outside its strings gets -32700, data naming the whitespace, and starts nothing ({spacedWhy}, ls exit {rc})"
  let (unsorted, unsortedWhy) ←
    refused
        "{\"jsonrpc\":\"2.0\",\"id\":37,\"method\":\"session/start\",\"params\":{\"args\":[\"300\"],\"name\":\"unsorted\",\"program\":\"/bin/sleep\"}}"
  let (rc, _, _) ← e.cli #["ls", "unsorted", "--porcelain"]
  expect
      (unchanged unsorted &&
        (unsortedWhy.getD "").startsWith
          "at character 20: the key \"id\" after \"jsonrpc\", where canonical JSON lists keys in increasing order" &&
        rc == 127)
      s!"a request whose keys are out of order gets -32700, data naming the key, and starts nothing ({unsortedWhy}, ls exit {rc})"
  let (fractional, fractionalWhy) ←
    refused
        "{\"id\":38,\"jsonrpc\":\"2.0\",\"method\":\"session/resize\",\"params\":{\"cols\":1.0,\"name\":\"fixed\",\"rows\":1}}"
  let after ← e.info "fixed" "cols"
  expect
      (unchanged fractional &&
        (fractionalWhy.getD "").startsWith
          "at character 69: a fraction or an exponent: linger's JSON numbers are integers" &&
        cols.isSome &&
        after == cols)
      s!"a request with 1.0 for an integer gets -32700, data naming the fraction, and resizes nothing ({fractionalWhy}, cols {cols} then {after})"
  let _ ← e.cli #["kill", "fixed"]

/-- `ls --porcelain` prints exactly the records `sessions/list` returns: a line for each, in order,
each the record's canonical JSON text, read without `idle` and `lastout`, which a second listing may
read a second later. -/
private def porcelainLines (e : Env) (p : Peer) : IO Unit := do
  p.say (request 39 "sessions/list" (.obj []))
  let listed ← p.answer 39
  let (rc, printed, _) ← e.cli #["ls", "--porcelain"]
  let lines := (printed.splitOn "\n").filter (!·.isEmpty)
  let served : List Json :=
    match listed.bind (at? · ["result", "records"]) with
    | some (.arr records) => records
    | _ => []
  let unticked (record : Json) : String :=
    match record with
    | .obj members => Json.render (.obj (members.filter fun m => m.1 != "idle" && m.1 != "lastout"))
    | other => Json.render other
  let exact :=
    rc == 0 && printed.endsWith "\n" && !served.isEmpty && lines.length == served.length &&
      (lines.zip served).all fun (line, record) =>
        match Json.parse line with
        | .ok got => Json.render got == line && unticked got == unticked record
        | .error _ => false
  expect exact
      s!"ls --porcelain prints a canonical JSON line for each record sessions/list returns, in order, the same object ({lines.length} lines, {served.length} records)"

/-- The notifications of `method` the peer wrote so far. -/
def Peer.notes (p : Peer) (method : String) : IO (List Json) := do
  return (← p.lines.get).toList.filterMap fun line =>
      (Json.parse line).toOption.filter fun message => textAt? message ["method"] == some method

/-- A screen as a client with no terminal keeps one: each line's row object under its number, the
cursor, and how many updates it applied, of which how many carried a line it held already. -/
structure Grid where
  /-- Each line's row object, under its number. -/
  rows : List (Nat × Json) := []
  /-- The cursor object. -/
  cursor : Json := .null
  /-- How many updates it applied. -/
  applied : Nat := 0
  /-- How many lines the updates carried that it held already, as they were. -/
  unchanged : Nat := 0

/-- The line number of a row object. -/
def lineOf (row : Json) : Option Nat := (textAt? row ["line"]).bind String.toNat?

/-- A grid with the rows of `rows` set under their numbers, counting each it held already. -/
def Grid.set (g : Grid) (rows : List Json) : Grid :=
  rows.foldl
    (fun g row =>
      match lineOf row with
      | some y =>
        { g with
          rows := (g.rows.filter (·.1 != y)) ++ [(y, row)]
          unchanged :=
            g.unchanged +
              if (g.rows.lookup y).map Json.render == some (Json.render row) then 1 else 0 }
      | none => g)
    g

/-- A grid after a `session/screen/changed`: its rows set, the lines it removes gone and its
cursor, when it carries one. -/
def Grid.apply (g : Grid) (note : Json) : Grid :=
  let rows :=
    match at? note ["params", "rows"] with
    | some (.arr rows) => rows
    | _ => []
  let gone :=
    match at? note ["params", "removed"] with
    | some (.arr items) => items.filterMap fun item => (textAt? item []).bind String.toNat?
    | _ => []
  let g := g.set rows
  { g with
    rows := g.rows.filter fun (y, _) => !gone.contains y
    cursor := (at? note ["params", "cursor"]).getD g.cursor
    applied := g.applied + 1 }

/-- A grid's lines as `capture` prints a screen: each line's text, top first, each with a line
feed. -/
def Grid.text (g : Grid) : String :=
  let ordered := (g.rows.map (·.1)).mergeSort (· ≤ ·)
  String.join (ordered.map fun y => (((g.rows.lookup y).bind (textAt? · ["text"])).getD "") ++ "\n")

/-- The cursor `info` reports for the session `name`, through `sessions/list`, request `id`. -/
private def infoCursor (p : Peer) (name : String) (id : Nat) : IO (Option (String × String)) := do
  p.say (request id "sessions/list" (.obj [("names", .arr [.str name])]))
  let listed ← p.answer id
  match listed.bind (at? · ["result", "records"]) with
  | some (.arr (record :: _)) =>
    return do
      let x ← textAt? record ["cursorx"]
      let y ← textAt? record ["cursory"]
      pure (x, y)
  | _ =>
    return none

/-- The screen's table: a client that keeps the screen as rows, with no terminal of its own, holds
after each step of the session's program the screen `capture` prints and the cursor `info`
reports; every update carries only lines that changed, a line printed in red carries a span of
foreground colour 1, and the last update closes the watch with how the session ended. -/
private def screenTable (p : Peer) : IO Unit := do
  let program :=
    "printf 'one\\ntwo\\n'; read a; printf '\\033[1;4H!\\033[2;5Hmid'; read b; " ++
      "printf '\\033[31mred\\033[0m\\n'; read c; exit 3"
  p.say
      (request 40 "session/start"
        (.obj
          [("name", .str "rows"), ("program", .str "/bin/sh"),
            ("args", .arr [.str "-c", .str program])]))
  let _ ← p.answer 40
  let _ ← captureUntil p "rows" "two" 30000
  p.say (request 41 "session/screen" (named "rows"))
  let opened ← p.answer 41
  let first :=
    match opened.bind (at? · ["result", "rows"]) with
    | some (.arr rows) => rows
    | _ => []
  let grid ←
    IO.mkRef
        (({ cursor := (opened.bind (at? · ["result", "cursor"])).getD .null } : Grid).set first)
  let seen ← IO.mkRef 0
  let next ← IO.mkRef 10000
  -- apply the updates that came since the last look, then compare the grid with a capture and
  -- the cursor with `info`, until they agree
  let agrees : IO Bool := do
    let notes ← p.notes "session/screen/changed"
    for note in notes.drop (← seen.get) do
      grid.modify (·.apply note)
    seen.set notes.length
    let id ← next.modifyGet fun id => (id, id + 2)
    p.say (request id "session/capture" (named "rows"))
    let captured ← p.answer id
    let cursor ← infoCursor p "rows" (id + 1)
    let g ← grid.get
    return screenOf captured == g.text && cursor.isSome &&
        cursor ==
          (do
            let x ← textAt? g.cursor ["x"]
            let y ← textAt? g.cursor ["y"]
            pure (x, y))
  let held ← waitFor patienceMs agrees
  expect (answerOf opened == some ("done", "0") && held)
      s!"session/screen answers with the screen, the grid capture prints and the cursor info reports ({answerOf opened}, {(← grid.get).text.length})"
  let enter := Base64.encode "\r".toUTF8.toList
  p.say (request 42 "session/send" (named "rows" [("data", .str enter)]))
  let _ ← p.answer 42
  let moved ←
    waitFor patienceMs do
        let lines := (← grid.get).text.splitOn "\n"
        return (← agrees) && lines.take 2 == ["one!", "two mid"]
  expect moved
      s!"after the program rewrites two rows at once, moving the cursor, the grid is what capture prints and its cursor info's ({(← grid.get).text.take 40})"
  p.say (request 43 "session/send" (named "rows" [("data", .str enter)]))
  let _ ← p.answer 43
  let red ←
    waitFor patienceMs do
        let agreed ← agrees
        let g ← grid.get
        return agreed &&
            g.rows.any fun (_, row) =>
              textAt? row ["text"] == some "red" &&
                (match at? row ["spans"] with
                | some (.arr [.arr [length, pen]]) =>
                  textAt? length [] == some "3" && textAt? pen ["fg"] == some "1"
                | _ => false)
  expect red
      s!"a line printed in red is what capture prints, its one span three characters of foreground colour 1 ({(← grid.get).rows.length} lines)"
  let g ← grid.get
  expect (g.applied ≥ 2 && g.unchanged == 0)
      s!"every update carried only lines that changed ({g.applied} updates, {g.unchanged} unchanged lines)"
  p.say (request 44 "session/send" (named "rows" [("data", .str enter)]))
  let _ ← p.answer 44
  let closed ←
    waitFor patienceMs do
        return (← p.notes "session/screen/changed").any fun note =>
            textAt? note ["params", "subscription"] == some "41" &&
              textAt? note ["params", "closed", "answer"] == some "program" &&
              textAt? note ["params", "closed", "code"] == some "3"
  expect closed "the watch's last update closes it with how the session ended, program 3"

/-- The history's log: the lines a client of `session/history` receives, with the count of those
it dropped, are exactly the lines that scrolled off the screen, as `capture --history` prints
them before the screen. -/
private def historyLog (p : Peer) : IO Unit := do
  let program :=
    "read a; i=1; while [ $i -le 40 ]; do printf 'scrolled %d\\n' $i; i=$((i+1)); done; read b"
  p.say
      (request 60 "session/start"
        (.obj
          [("name", .str "scroll"), ("program", .str "/bin/sh"),
            ("args", .arr [.str "-c", .str program])]))
  let _ ← p.answer 60
  p.say (request 61 "session/history" (named "scroll"))
  let opened ← p.answer 61
  p.say
      (request 62 "session/send"
        (named "scroll" [("data", .str (Base64.encode "\r".toUTF8.toList))]))
  let _ ← p.answer 62
  let got ← IO.mkRef (([] : List String), 0)
  let wanted ← IO.mkRef ([] : List String)
  let next ← IO.mkRef 20000
  let found ←
    waitFor patienceMs do
        let notes ← p.notes "session/history/changed"
        let lines :=
          notes.flatMap fun note =>
            match at? note ["params", "lines"] with
            | some (.arr lines) => lines.filterMap (textAt? · ["text"])
            | _ => []
        let dropped :=
          notes.foldl
            (fun n note => n + ((textAt? note ["params", "dropped"]).bind String.toNat?).getD 0) 0
        got.set (lines, dropped)
        let id ← next.modifyGet fun id => (id, id + 1)
        p.say (request id "session/capture" (named "scroll" [("history", .bool true)]))
        let captured := (screenOf (← p.answer id)).splitOn "\n"
        -- the history is what `capture --history` prints before the screen's 24 rows
        let history := captured.take (captured.length - 25)
        wanted.set history
        return history.any (· == "scrolled 17") && lines == history && dropped == 0
  let (lines, dropped) ← got.get
  expect (answerOf opened == some ("done", "0") && found)
      s!"session/history's lines and drops are the lines that scrolled off, as capture --history prints them ({lines.length} lines, {dropped} dropped, {(← wanted.get).length} wanted)"
  -- a burst far past what the log keeps between two looks: its lines and its counted gaps, in
  -- order, are each line that scrolled off, every line kept in its own place
  let count := 20000
  p.say
      (request 70 "session/start"
        (.obj
          [("name", .str "burst"), ("program", .str "/bin/sh"),
            ("args", .arr [.str "-c", .str s!"read a; seq 1 {count}; read b"])]))
  let _ ← p.answer 70
  p.say (request 71 "session/history" (named "burst"))
  let _ ← p.answer 71
  p.say
      (request 72 "session/send"
        (named "burst" [("data", .str (Base64.encode "\r".toUTF8.toList))]))
  let _ ← p.answer 72
  -- the echo's empty line, then each number but the last 23, which the 24-row screen still shows
  let expected := "" :: (List.range (count - 23)).map fun n => toString (n + 1)
  let places ← IO.mkRef ([] : List (Option String))
  let exact ←
    waitFor (2 * patienceMs) do
        let read :=
          ((← p.notes "session/history/changed").filter fun note =>
                textAt? note ["params", "subscription"] == some "71").flatMap
            fun note =>
            let gaps := ((textAt? note ["params", "dropped"]).bind String.toNat?).getD 0
            let kept :=
              match at? note ["params", "lines"] with
              | some (.arr lines) => lines.map (textAt? · ["text"])
              | _ => []
            List.replicate gaps none ++ kept
        places.set read
        return read.length == expected.length &&
            (read.zip expected).all fun (place, line) => place.all (· == line)
  let read ← places.get
  expect exact
      s!"a burst's history, its lines and its counted drops in order, is each line that scrolled off, every line kept in its own place ({read.length} places of {expected.length}, {(read.filter (·.isNone)).length} dropped)"

/-- The `session/output` updates the peer wrote so far for the subscription `id`, each its params. -/
def Peer.outputs (p : Peer) (id : Nat) : IO (List Json) := do
  return (← p.notes "session/output").filterMap fun note =>
      (at? note ["params"]).filter fun params =>
        textAt? params ["subscription"] == some (toString id)

/-- The bytes the updates for the subscription `id` carry, each update's `data` decoded, in order. -/
def Peer.stream (p : Peer) (id : Nat) : IO ByteArray := do
  let chunks :=
    (← p.outputs id).map fun params =>
      ((textAt? params ["data"]).bind (Base64.decode ·.toList)).getD []
  return ByteArray.mk chunks.flatten.toArray

/-- The params of a conversation request on the attach `id`, with `more` members. -/
def onAttach (id : Nat) (more : List (String × Json) := []) : Json :=
  .obj (("subscription", .int id) :: more)

/-- The byte stream of a terminal client: `session/attach` answers done and its updates carry the
session's output as base64, the synchronized repaint first; `session/input` types into the session,
`session/resize` sizes it, and `session/detach` ends the stream, after which no update names it and
the session runs on with no client; and an attached session's end sends a last update that carries
`closed` with how it ended. -/
private def attachStream (e : Env) (p : Peer) : IO Unit := do
  p.say (request 80 "session/attach" (named "typed"))
  let opened ← p.answer 80
  let painted ←
    waitFor patienceMs do
        let bytes ← p.stream 80
        return startsWithBytes bytes Terminal.Render.syncBegin &&
            hasBytes bytes Terminal.Render.syncEnd
  expect (answerOf opened == some ("done", "0") && painted)
      s!"session/attach answers done, and its stream opens with the synchronized repaint ({answerOf opened}, {(← p.stream 80).size} bytes)"
  p.say
      (request 81 "session/input"
        (onAttach 80 [("data", .str (Base64.encode "echo hi-$((40+2))\r".toUTF8.toList))]))
  let typed ← p.answer 81
  let echoed ← waitFor patienceMs (return hasText (← p.stream 80) "hi-42")
  expect (answerOf typed == some ("done", "0") && echoed)
      s!"session/input types into the session, and what it runs streams back: hi-42 ({answerOf typed})"
  p.say (request 82 "session/resize" (onAttach 80 [("cols", .int 100), ("rows", .int 30)]))
  let resized ← p.answer 82
  let sized ←
    waitFor patienceMs do
        return (← e.info "typed" "cols") == some "100" && (← e.info "typed" "rows") == some "30"
  p.say
      (request 83 "session/input"
        (onAttach 80 [("data", .str (Base64.encode "stty size\r".toUTF8.toList))]))
  let _ ← p.answer 83
  let told ← waitFor patienceMs (return hasText (← p.stream 80) "30 100")
  expect (answerOf resized == some ("done", "0") && sized && told)
      s!"session/resize sizes the session: info says 100x30, and its program reads 30 100 ({answerOf resized}, {sized}, {told})"
  p.say (request 84 "session/detach" (onAttach 80))
  let detached ← p.answer 84
  let left ← waitFor patienceMs (return (← e.info "typed" "clients") == some "0")
  let after := (← p.outputs 80).length
  let _ ← e.cli #["send", "typed", "echo still-$((20+3))\n"]
  let ran ← waitFor patienceMs (return has (← e.out #["capture", "--history", "typed"]) "still-23")
  let quiet := (← p.outputs 80).length == after
  expect (answerOf detached == some ("done", "0") && left && ran && quiet)
      s!"session/detach ends the stream: the session runs on with no client, and no update names it after ({answerOf detached}, {left}, {ran}, {quiet})"
  p.say (request 85 "session/attach" (named "typed"))
  let _ ← p.answer 85
  p.say
      (request 86 "session/input"
        (onAttach 85 [("data", .str (Base64.encode "exit 7\r".toUTF8.toList))]))
  let _ ← p.answer 86
  let closed ←
    waitFor patienceMs do
        return (← p.outputs 85).any fun params =>
            textAt? params ["closed", "answer"] == some "program" &&
              textAt? params ["closed", "code"] == some "7"
  expect closed "an attached session's end sends a last update that carries closed, program 7"

/-- `session/attach` covers every session `attach` does: a saved session resumes and streams; an
ended one's stream shows its final screen, then closes with how it ended, and the session is
discarded; and a read-only attach of a saved one shows its screen until the subscriber detaches,
leaving it saved. -/
private def everySession (e : Env) (p : Peer) : IO Unit := do
  let saved (name text : String) : IO Unit :=
    IO.FS.writeBinFile s!"{e.dir}/{name}.ckpt"
      (Linger.Session.Checkpoint.saveBytes
        ⟨(Terminal.Vt.Vt.init 40 5).feed text.toUTF8.toList, e.dir, []⟩)
  saved "kept" "KEPT-MARK"
  p.say (request 90 "session/attach" (named "kept"))
  let resumed ← p.answer 90
  let shown ← waitFor patienceMs (return hasText (← p.stream 90) "KEPT-MARK")
  p.say
      (request 91 "session/input"
        (onAttach 90 [("data", .str (Base64.encode "echo resumed-$((2+3))\r".toUTF8.toList))]))
  let typed ← waitFor patienceMs (return hasText (← p.stream 90) "resumed-5")
  p.say (request 92 "session/detach" (onAttach 90))
  let _ ← p.answer 92
  let live ← waitFor patienceMs (return (← e.info "kept" "pid").isSome)
  expect (answerOf resumed == some ("done", "0") && shown && typed && live)
      s!"session/attach of a saved session resumes it, as attach does, and streams it ({answerOf resumed})"
  let (startRc, _, _) ← e.cli #["start", "over", "/bin/sh", "-c", "echo final-$((6*7)); exit 7"]
  let (waitRc, _, _) ← e.cli #["wait", "over"]
  let kept ← System.FilePath.pathExists s!"{e.dir}/over.ckpt"
  p.say (request 93 "session/attach" (named "over"))
  let opened ← p.answer 93
  let final ← waitFor patienceMs (return hasText (← p.stream 93) "final-42")
  let closed ←
    waitFor patienceMs do
        return (← p.outputs 93).any fun params =>
            textAt? params ["closed", "answer"] == some "program" &&
              textAt? params ["closed", "code"] == some "7"
  let discarded ← waitFor patienceMs (return !(← System.FilePath.pathExists s!"{e.dir}/over.ckpt"))
  let (_, record, _) ← e.cli #["ls", "--porcelain", "over"]
  expect
      (startRc == 0 && waitRc == 7 && kept && answerOf opened == some ("done", "0") && final &&
        closed &&
        discarded &&
        has record "\"exit\":\"7\"")
      s!"session/attach of an ended session shows its final screen, closes with how it ended and discards it ({answerOf opened})"
  saved "glimpsed" "GLIMPSED-MARK"
  p.say (request 94 "session/attach" (named "glimpsed" [("readOnly", .bool true)]))
  let viewing ← p.answer 94
  let painted ← waitFor patienceMs (return hasText (← p.stream 94) "GLIMPSED-MARK")
  let stayed := !(← p.outputs 94).any fun params => (at? params ["closed"]).isSome
  p.say (request 95 "session/detach" (onAttach 94))
  let left ← p.answer 95
  let still ← System.FilePath.pathExists s!"{e.dir}/glimpsed.ckpt"
  let unstarted := (← e.info "glimpsed" "pid").isNone
  expect
      (answerOf viewing == some ("done", "0") && painted && stayed &&
        answerOf left == some ("done", "0") &&
        still &&
        unstarted)
      s!"a read-only session/attach of a saved session shows its screen until the subscriber detaches, and keeps it saved ({answerOf viewing})"

/-- The suite. -/
def run : IO UInt32 :=
  Env.suite "serve" fun e => do
    let p ← Peer.start e
    try
      handshake e p
      table p
      operations e p
      sameList e p
      refusals e p
      porcelainLines e p
      screenTable p
      historyLog p
      attachStream e p
      everySession e p
      let rc ← p.close
      expect (rc == some 0) s!"once its standard input ends, serve exits 0 ({rc})"
    finally
      reapOrKill p.child 1000
      e.endSessions

end Linger.App.Suites.Serve
