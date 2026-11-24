module

public import Linger.App.WorldCode.Api
import Linger.App.CoreCode.Serve
import Linger.App.CoreCode.Json
import Linger.Session.CoreCode
import Linger.Session.CoreCode.Wire
import Linger.Session.WorldCode.Client
import Terminal.CoreCode.Vt
import Terminal.CoreCode.Replay
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
waits and ends, finding `done`, or `refused` when its output was closed.

A watch of a session's terminal, `session/screen` or `session/history`, attaches to the session
read-only on a thread of its own, as `attach --read-only` does once its daemon has said it speaks
this version's protocol (`Api.watch`), and keeps a mirror of the terminal with linger's own
emulator, fed what the daemon sends the watcher: the repaint, up to its closing `Render.syncEnd`,
then the output as it comes, with the history emptied as it goes, the lines that leave the top kept
for a history's log. Output is the event: after a read that brought some, the watcher asks the
daemon for its `info` on the same connection, whose answer comes after that output, and where the
answer gives the size the mirror has, hands the step the screen the mirror renders there and the
lines that left since (`Event.watched`); where the size changed, it attaches again, for a repaint
at the new size. The writer sends each watch's update when nothing else waits (`Event.flush`). A
watch ends with its session, its connection or its subscription: an `info` request on its
connection wakes it when the step closes it, and when standard input ends.

An attach, `session/attach`, attaches to the session, writable unless asked to be read-only, on a
thread of its own, through `Api.perform`, as `attach` does, a saved session resumed, on a terminal
that is its subscriber (`Api.Tty`); the saved screen an attach shows, an ended session's or a
read-only attach's of a saved one, is the stream's first read, its repaint (`showOn`). It hands the
step each read of the daemon's connection, which decodes it as the attach client does and keeps
what the client would write for the writer to send (`Event.read`), and reads no further while
`attachHold` bytes wait, so that a subscriber that does not read holds back the daemon, which cuts
the connection off past its own cap, as it cuts off any client that does not read. The keys and the
size the subscriber sends, the step relays (`Effect.relay`), and the thread that read the request
writes them on the attach's connection once the step is done, in order; the attach lets its
connection go only once no relay is being written on it. -/

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
  /-- The connections the watches attach over, by the watch's id: the descriptor, and whether an
  `info` request on it waits for its answer. -/
  watchers : List (Id × UInt32 × Bool) := []
  /-- How many watches and attaches are followed. -/
  following : Nat := 0
  /-- The messages a step relays to an attach, by the connection they go on, which `run` writes,
  in order, once the step is done. -/
  relays : List (UInt32 × List Linger.Session.Wire.Msg) := []
  /-- The connections a relay is being written on, which their attach closes only once it is
  written. -/
  relaying : List UInt32 := []

/-- Write one message, a line of clean text (`Serve.line`). -/
private def emit (out : Outgoing) : IO Unit := writeAll stdoutFd (Serve.line out).toUTF8

/-- Ask the daemon of the watch under `key` for its `info`, on the watch's connection, unless a
request waits there for its answer already: the answer wakes the watcher, after the output that came
before it. -/
private def askWatcher (key : Id) : Std.AtomicT Shared IO Unit := do
  let s ← get
  match s.watchers.lookup key with
  | some (fd, false) =>
    set
        { s with
          watchers :=
            s.watchers.map fun (entry : Id × UInt32 × Bool) =>
              if entry.1 = key then (key, fd, true) else entry }
    try
      Linger.Session.Shell.Client.sendMsg fd .info
    catch _ =>
      pure ()
  | _ =>
    pure ()

/-- Step the connection with `ev`, queue what the step writes, wake the watcher of each watch the
step closed, and give back what it performs. -/
private def stepShared (ev : Event) :
    Std.AtomicT Shared IO (List (Id × String × Api.Request × List UInt8)) := do
  let shared ← get
  let (state, effects) := step shared.state ev
  let sent : List Outgoing :=
    effects.filterMap fun (effect : Effect) =>
      match effect with
      | .send out => some out
      | .perform .. | .relay .. => none
  -- a relay goes on the connection its attach registered, which stays open while it is written
  let relays : List (UInt32 × List Linger.Session.Wire.Msg) :=
    effects.filterMap fun (effect : Effect) =>
      match effect with
      | .relay key messages =>
        (shared.watchers.lookup key).map fun (entry : UInt32 × Bool) => (entry.1, messages)
      | .send _ | .perform .. => none
  set
      { shared with
        state, outbox := shared.outbox ++ sent, relays := shared.relays ++ relays
        relaying :=
          shared.relaying ++
            relays.map fun (relay : UInt32 × List Linger.Session.Wire.Msg) => relay.1 }
  for (key, _) in shared.state.watches do
    if (state.watching key).isNone then
      askWatcher key
  return effects.filterMap fun (effect : Effect) =>
      match effect with
      | .perform id method request bytes => some (id, method, request, bytes)
      | .send _ | .relay .. => none

/-- The members of a result that show what a request shows: a capture's bytes in base64,
`data`; a listing's records, `records`, each a session's fields as clean text; any other text, and
the sessions an upgrade carried over. -/
private def shownMembers : Api.Shown → List (String × Json)
  | .nothing => []
  | .bytes bytes => [("data", .str (Base64.encode bytes.toList))]
  | .rows _ rows => [("records", .arr ((Serve.records rows).map Record.json))]
  | .text text => [("text", .str (Serve.clean text))]
  | .upgraded names => [("upgraded", .arr (names.map fun name => .str (Serve.clean name)))]

/-- The writer: write what waits, in order, and, when nothing else waits, the subscriber's update
when it has one due, else a watch's, until input has ended and nothing waits, or writing fails. -/
private def writer (conn : Std.Mutex Shared) (wake : Std.Condvar) : IO Unit := do
  let mut writing := true
  while writing do
    let next ←
      conn.atomicallyOnce wake
          (do
            let s ← get
            return !s.outbox.isEmpty || s.state.due || s.state.watchDue.isSome || s.ended ||
                s.broken)
          (do
            let s ← get
            match s.outbox with
            | out :: rest =>
              set { s with outbox := rest }
              return some out
            | [] =>
              let free := if s.state.due then some .writable else s.state.watchDue.map .flush
              match free with
              | some ev =>
                if s.ended || s.broken then
                  return none
                else
                  let (state, effects) := step s.state ev
                  set { s with state }
                  return effects.findSome? fun (effect : Effect) =>
                      match effect with
                      | .send out => some out
                      | .perform .. | .relay .. => none
              | none =>
                return none)
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

/-- The repaint a watcher reads, up to its closing `Render.syncEnd`, which no repaint holds inside
(`replay_synchronized`), and what follows it: of `bytes`, those of the repaint, those after it, and
how many bytes of `Render.syncEnd` it has matched, `matched` before them; all of it the repaint's
until it matches all of them. -/
private def splitRepaint (matched : Nat) (bytes : List UInt8) :
    List UInt8 × List UInt8 × Nat := go matched [] bytes
where
  /-- The repaint's bytes so far, last first, and the bytes still to read. -/
  go (matched : Nat) (paint : List UInt8) : List UInt8 → List UInt8 × List UInt8 × Nat
    | [] => (paint.reverse, [], matched)
    | b :: rest =>
      let next :=
        if Terminal.Render.syncEnd[matched]? = some b then matched + 1
        else if b = 0x1B then 1 else 0
      if next = Terminal.Render.syncEnd.length then ((b :: paint).reverse, rest, next)
      else go next (b :: paint) rest

/-- An `info` answer's fields, `key` TAB `value` lines. -/
private def infoFields (bytes : ByteArray) : Option (List (String × String)) := do
  let text ← String.fromUTF8? bytes
  (text.splitOn "\n").filter (· != "") |>.mapM fun line =>
      match line.splitOn "\t" with
      | [key, value] => some (key, value)
      | _ => none

/-- How a watcher's connection ended: the session's terminal changed size, so it attaches again;
the watch closed; or the watch is over, having found this. -/
private inductive Heard where
  /-- The terminal changed size. -/
  | resized
  /-- The watch closed: its subscriber let it go, or input ended. -/
  | closed
  /-- The watch is over, having found this. -/
  | over (found : Api.Found)

/-- Whether the watch under `id` is closed: the step holds it no more, or input ended or writing
failed. -/
private def watchClosed (id : Id) : Std.AtomicT Shared IO Bool := do
  let s ← get
  return (s.state.watching id).isNone || s.ended || s.broken

/-- Hand the step a watch's look, the screen the mirror renders and the lines that left it, and,
when the look answers the watch's request, count that request answered. -/
private def look (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id) (opened : IO.Ref Bool)
    (mirror : Terminal.Vt.Vt) (left : Log Line) : IO Unit := do
  conn.atomically do
      let asked :=
        match (← get).state.watching id with
        | some (.asked _) => true
        | _ => false
      discard <| stepShared (.watched id (Screen.render mirror) left)
      if asked then
        modify fun s => { s with inFlight := s.inFlight - 1 }
        opened.set true
  wake.notifyAll

/-- Follow a session over the connection `fd`, whose `info` answer gave `fields`: attach read-only
at the terminal's size, mirror the repaint and the output that follows it, and, after a read that
brought output, ask for `info` and take a look where its answer confirms the mirror's size. -/
private def followOn (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id) (history : Bool)
    (opened : IO.Ref Bool) (fd : UInt32) (fields : List (String × String)) : IO Heard := do
  let some cols := (fields.lookup "cols").bind String.toNat? | return .over .refused
  let some rows := (fields.lookup "rows").bind String.toNat? | return .over .refused
  conn.atomically
      (modify fun s => { s with watchers := s.watchers.filter (·.1 != id) ++ [(id, fd, false)] })
  Linger.Session.Shell.Client.sendMsg fd (.attach .readOnly (UInt32.ofNat cols) (UInt32.ofNat rows))
  let mut mirror := Terminal.Vt.Vt.init cols rows
  let mut matched := 0
  let mut painting := true
  let mut dirty := false
  let mut left : Log Line := {}
  let mut info := ByteArray.empty
  let mut ending : Option Api.Found := none
  let mut dec : Linger.Session.Wire.Decoder := {}
  repeat
    let _ ← poll #[fd] #[POLLIN] (-1)
    let chunk ←
      try
        read fd 65536
      catch _ =>
        pure none
    let some bytes := chunk |
      do
        -- the daemon closed the connection: once it has said how the session ended, the last
        -- look is the screen the output before the ending left
        if let some found := ending then
          if !painting then
            look conn wake id opened mirror left
          return .over found
        return .over .refused
    let (next, messages) := dec.feed bytes.toList
    dec := next
    if dec.errored then
      return .over .refused
    for message in messages do
      match message with
      | .output payload =>
        let (paint, live) ←
          if painting then
            let (paint, live, m) := splitRepaint matched payload
            matched := m
            if m = Terminal.Render.syncEnd.length then
              painting := false
              dirty := true
            pure (paint, live)
          else
            pure ([], payload)
        mirror := mirror.observe paint
        if history then
          let (fed, kept) := feedLeaving mirror live left
          mirror := fed
          left := kept
        else
          mirror := mirror.observe live
        if !live.isEmpty then
          dirty := true
      | .infoReply payload =>
        if info.size + payload.length > Linger.Session.infoReplyCap then
          return .over .refused
        info := info ++ ByteArray.mk payload.toArray
      | .done =>
        let answered := infoFields info
        info := ByteArray.empty
        let closed ←
          conn.atomically do
              modify fun s =>
                  { s with
                    watchers :=
                      s.watchers.map fun (entry : Id × UInt32 × Bool) =>
                        if entry.1 = id then (id, entry.2.1, false) else entry }
              watchClosed id
        if closed then
          return .closed
        let sized :=
          (answered.bind fun fields =>
              (fields.lookup "cols").bind String.toNat? |>.map fun c =>
                (c, ((fields.lookup "rows").bind String.toNat?).getD 0)) ==
            some (mirror.colCount, mirror.rowCount)
        if !sized then
          return .resized
        if !painting then
          look conn wake id opened mirror left
          left := {}
      | .ended outcome =>
        ending := some (.ended (.program outcome))
      | .saved signal =>
        ending := some (.ended (.saved signal))
      | .err _ =>
        return .over .refused
      | _ =>
        pure ()
    if ← conn.atomically (watchClosed id) then
      return .closed
    if dirty && !painting && ending.isNone then
      conn.atomically (askWatcher id)
      dirty := false
  return .over .refused

/-- Follow the session `watched` leads to, over one connection after another while its terminal
changes size; what the watch found once it is over, and `done` once it closed. -/
private def follow (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id) (history : Bool)
    (opened : IO.Ref Bool) (watched : Api.Watched) : IO Api.Found := do
  repeat
    if ← conn.atomically (watchClosed id) then
      return .done
    let some (fd, fields) ← watched.connect | return .refused
    let heard ←
      try
        followOn conn wake id history opened fd fields
      catch _ =>
        pure (.over .refused)
      finally
        conn.atomically (modify fun s => { s with watchers := s.watchers.filter (·.1 != id) })
        close fd
    match heard with
    | .resized =>
      pure ()
    | .closed =>
      return .done
    | .over found =>
      return found
  return .refused

/-- Follow a watch, `session/screen` or `session/history`, of the session its request names, as
`attach --read-only` connects to it (`Api.watch`), with what it says kept for its result, then
tell the step how it ended (`Event.unwatched`). -/
private def followWatch (env : Api.Env) (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id)
    (method : String) (request : Api.Request) : IO Unit := do
  conn.atomically (modify fun s => { s with following := s.following + 1 })
  let said ← IO.mkRef ({} : Log String)
  let opened ← IO.mkRef false
  let env := { env with say := fun s => said.modify (Log.push saidCap · s.text) }
  let target :=
    match request with
    | .attach _ target _ => target
    | _ => ""
  let found ←
    try
      Api.watch env target (follow conn wake id (method = "session/history") opened)
    catch _ =>
      pure .unknown
  let wasOpened ← opened.get
  conn.atomically do
      discard <| stepShared (.unwatched id found (← said.get))
      modify fun s =>
          { s with
            inFlight := if wasOpened then s.inFlight else s.inFlight - 1
            following := s.following - 1 }
  wake.notifyAll

/-- How many bytes may wait for an attach's subscriber before `serve` reads the attach's connection
no further (`State.holdsBack`): one read's worth, so that a subscriber that does not read holds back
the daemon, which cuts the connection off past its own cap, as it cuts off any client that does not
read. -/
def attachHold : Nat := 65536

/-- Converse with a session's daemon over `fd`, as the attach `id`: attach in `mode` with no size of
its own (`Msg.attach`, 0×0), as a terminal that has none yet does, until the subscriber says its
size, and hand the step each read of the connection, which decodes it and sends what an attach
client writes of it to the subscriber (`Event.read`), reading no further while `attachHold` bytes
wait for the subscriber; the step writes the subscriber's keys and size on the connection
(`Effect.relay`). The attach ends when the step holds it no more, the attach's end or its
subscriber's having closed it, or when the daemon closes the connection, which is lost. The first
read answers the attach's request, which then counts as answered. -/
private def converseOn (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id)
    (opened : IO.Ref Bool) (fd : UInt32) (mode : Linger.Session.Mode) :
    IO Linger.Session.Shell.Client.Outcome := do
  try
    conn.atomically
        (modify fun s => { s with watchers := s.watchers.filter (·.1 != id) ++ [(id, fd, false)] })
    Linger.Session.Shell.Client.sendMsg fd (.attach mode 0 0)
    repeat
      let closed ←
        conn.atomicallyOnce wake
            (do
              let s ← get
              return (← watchClosed id) || !s.state.holdsBack id attachHold)
            (watchClosed id)
      if closed then
        return .detached
      let _ ← poll #[fd] #[POLLIN] (-1)
      let chunk ←
        try
          read fd 65536
        catch _ =>
          pure none
      let some bytes := chunk | return .lost "connection lost"
      conn.atomically do
          let asked :=
            match (← get).state.watching id with
            | some .attaching => true
            | _ => false
          discard <| stepShared (.read id bytes.toList)
          if asked then
            modify fun s => { s with inFlight := s.inFlight - 1 }
            opened.set true
      wake.notifyAll
    return .detached
  finally
    -- no relay is written on the connection once it is let go
    conn.atomicallyOnce wake (return !(← get).relaying.contains fd)
        (modify fun s => { s with watchers := s.watchers.filter (·.1 != id) })
    close fd

/-- The bytes of a saved terminal's repaint, as its daemon would send an attach of it: one
synchronized update of the screen, its title and its modes (`Replay.start`). -/
private def repaintOf (vt : Terminal.Vt.Vt) : IO (List UInt8) := do
  let mut plan := Terminal.Replay.start vt
  let mut bytes : Array UInt8 := #[]
  repeat
    match Terminal.Replay.next 65536 plan with
    | none =>
      break
    | some (chunk, next) =>
      bytes := bytes ++ chunk.toArray
      plan := next
  return bytes.toList

/-- Show a saved session's screen to the attach `id`'s subscriber as the attach's stream, its
first read (`Event.read`) the screen's repaint (`repaintOf`) as output frames (`paint`), as its
daemon would send them, which answers the attach's request; with `hold`, keep it shown until the
step holds the attach no more, its subscriber having let it go or input having ended. -/
private def showOn (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id) (opened : IO.Ref Bool)
    (vt : Terminal.Vt.Vt) (hold : Bool) : IO Linger.Session.Shell.Client.Outcome := do
  let shown := paint (← repaintOf vt)
  conn.atomically do
      let asked :=
        match (← get).state.watching id with
        | some .attaching => true
        | _ => false
      discard <| stepShared (.read id shown)
      if asked then
        modify fun s => { s with inFlight := s.inFlight - 1 }
        opened.set true
  wake.notifyAll
  if hold then
    conn.atomicallyOnce wake (watchClosed id) (pure ())
  return .detached

/-- Follow an attach, `session/attach`, of the session its request names, as `attach` attaches to
it (`Api.perform`), on a terminal that is the attach's subscriber (`Api.Tty`, `converseOn`), with
what it says kept for its result, then tell the step how it ended (`Event.unwatched`). -/
private def followAttach (env : Api.Env) (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id)
    (request : Api.Request) : IO Unit := do
  conn.atomically (modify fun s => { s with following := s.following + 1 })
  let said ← IO.mkRef ({} : Log String)
  let opened ← IO.mkRef false
  let env :=
    { env with
      say := fun s => said.modify (Log.push saidCap · s.text)
      tty :=
        some
          { attach := fun _ fd mode => converseOn conn wake id opened fd mode
            view := fun _ vt hold => showOn conn wake id opened vt hold } }
  let found ←
    try
      (·.found) <$> Api.perform env request
    catch _ =>
      pure .unknown
  let wasOpened ← opened.get
  conn.atomically do
      discard <| stepShared (.unwatched id found (← said.get))
      modify fun s =>
          { s with
            inFlight := if wasOpened then s.inFlight else s.inFlight - 1
            following := s.following - 1 }
  wake.notifyAll

/-- Perform a request as the command line does, with `bytes` for its standard input and what it
says kept for its result, and queue its result: the answer it found, what it shows, how a
session it found ended, and what it said. A `sessions/subscribe`'s listing is the table its
subscriber first holds, and starts the sampler when none runs. -/
private def answer (env : Api.Env) (conn : Std.Mutex Shared) (wake : Std.Condvar) (id : Id)
    (method : String) (request : Api.Request) (bytes : List UInt8) : IO Unit := do
  if method = "session/screen" ∨ method = "session/history" then
    followWatch env conn wake id method request
    return
  if method = "session/attach" then
    followAttach env conn wake id request
    return
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
        let (performs, relays) ←
          conn.atomicallyOnce wake
              (do
                let s ← get
                return s.broken || s.inFlight + s.outbox.length < maxInFlight)
              (do
                if (← get).broken then
                  return ([], [])
                let performs ← stepShared (.received message)
                let relays := (← get).relays
                modify fun s =>
                    { s with
                      inFlight := s.inFlight + performs.length, relays := [] }
                return (performs, relays))
        wake.notifyAll
        for (id, method, request, bytes) in performs do
          discard <| IO.asTask (answer env conn wake id method request bytes) .dedicated
        -- an attach's keys and size, in order, on the connection its attach keeps open for them
        for (fd, messages) in relays do
          try
            for message in messages do
              Linger.Session.Shell.Client.sendMsg fd message
          catch _ =>
            pure ()
          conn.atomically (modify fun s => { s with relaying := s.relaying.erase fd })
          wake.notifyAll
      if ← conn.atomically (return (← get).broken) then
        reading := false
  conn.atomicallyOnce wake
      (do
        let s ← get
        return s.inFlight == 0 || s.broken)
      (do
        modify fun s => { s with ended := true }
        for (key, _) in (← get).watchers do
          askWatcher key)
  wake.notifyAll
  discard <| IO.wait writing
  conn.atomicallyOnce wake (return !(← get).sampling && (← get).following == 0) (pure ())
  return if (← conn.atomically get).broken then .refused else .done

end Linger.App.Serve.Shell
