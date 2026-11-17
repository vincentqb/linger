module

public import Linger.Os.CoreSpec
public import Linger.Target.CoreSpec
public import Terminal.CoreSpec

public section

/-! # What session headlines are stated in

The values a session exchanges with its clients and its runtime (messages, client records,
events and effects, and the end record a name keeps), what a command answers for each way a
session ends, what a session hears of its shell's commands from the shell's marks, the caps its
state keeps and how long its changes may go unsaved, the time its
events tell it, and predicates over the session's operations, which they take as parameters:
which messages fit a frame or look at the session, and what a decoder reads from
a chunked stream, the bounds a state
keeps, the events a session handles when every effect succeeds, the reachable states of the
daemon's byte queues, and a model of how daemons and offline readers claim a session's
resources, and the names that lead to sessions' IDs; and the wrong transition, decision,
drivers, renames, start and resolution the kills put in place of the program's. Bodies are exposed: each definition here is its own specification. What the headlines
assume of the world, the effect executor's answers among it, is in `Linger.Session.WorldSpec`. -/

namespace Linger.Session

/-- How a session's program ended, as linger saw it. -/
inductive Outcome where
  /-- The program exited with this code. -/
  | exited (code : UInt8)
  /-- A signal with this number killed the program. -/
  | signaled (signal : UInt8)
  /-- linger did not see how the program ended. -/
  | unknown
  deriving Repr, DecidableEq, Inhabited

/-- The exit status a caller sees for a program that ended this way, as a shell reports it: the
code, 128 plus the signal's number, or 125, the status a wrapper reports for its own failure,
when linger did not see the end. -/
@[expose]
def Outcome.status : Outcome → UInt32
  | .exited code => code.toUInt32
  | .signaled signal => 128 + signal.toUInt32
  | .unknown => 125

/-- The answer that tells how a program ended: its status, as a shell reports it, or, when linger
did not see the end, that linger could not find out. -/
@[expose]
def Outcome.answer : Outcome → Os.Answer
  | .unknown => .failed
  | outcome => .program outcome.status

/-- What a daemon last saw of its program: the progress it declared (`!`, `⣷`, `⣤`), whether its
shell's marks say a command runs (`⣷`), whether new lines entered the session's history since it
was last looked at (`⣿`), and whether, since then, the program rang the bell or posted a desktop
notification (`⚑`), as `info` reports `progress`, `running`, `unseen` and `asks`. -/
structure Seen where
  /-- The progress the program last declared, ConEmu's OSC `9;4`; `none` when it declared none
  or removed it. -/
  progress : Option Terminal.Mediation.Progress
  /-- The shell's marks say a command runs: a `C` that no `D` or `A` has followed. -/
  running : Bool
  /-- New lines entered the session's history since the session was last looked at. -/
  unseen : Bool
  /-- A bell or a notification since the session was last looked at. -/
  asks : Bool
  deriving Repr, DecidableEq

/-- A command's ending, as its shell reported it with its marks: the command line the `C` that
started it gave, and the exit status its `D` gave, when that `D` gave one. -/
structure Finished where
  /-- The command line the `C` gave, as the mediator read it. -/
  cmdline : Terminal.Mediation.Cmdline
  /-- The exit status the `D` gave, as the shell reports it. -/
  status : Option Nat
  deriving Repr, DecidableEq

/-- What a session heard of its shell's commands, from the shell's OSC 133 marks: the command
line of the command that runs, while a `C` started one that no `D` or `A` has followed, and the
ending of the last command that finished since the session was last looked at. -/
structure Commands where
  /-- The command a `C` started, with its command line, until a `D` or an `A` follows it. -/
  running : Option Terminal.Mediation.Cmdline := none
  /-- The ending of the last command that finished since the session was last looked at. -/
  finished : Option Finished := none
  deriving Repr, DecidableEq

/-- What a mark tells a session of its shell's commands, as the marks' standard means it, from
what the session heard before: `A`, a prompt, means no command runs, so a `D` after it is no
ending; `B` tells nothing; `C` starts a command, which replaces an ending nobody saw; and `D` is
the ending of the command a `C` started, with the status it gives, while with no command running
it is no ending. -/
@[expose]
def Commands.hear (c : Commands) : Terminal.Mediation.Mark → Commands
  | .prompt => { c with running := none }
  | .input => c
  | .runs cmdline => { running := some cmdline, finished := none }
  | .finished status =>
    match c.running with
    | some cmdline => { running := none, finished := some ⟨cmdline, status⟩ }
    | none => c

/-- What a connection may do, as it asks when it attaches: type into the session, or only watch
it. A connection that never attached, as `send` and `kill` open, is writable. -/
inductive Mode where
  /-- Its keystrokes reach the program, and it may end the session and disconnect every
  client. -/
  | writable
  /-- It watches: its keystrokes are dropped, and its requests to change the session refused. -/
  | readOnly
  deriving Repr, DecidableEq, Inhabited

/-- What a name's end record says. -/
inductive Record where
  /-- A session took the name, and its program had not ended when this was written; with
  `seen`, what its daemon then saw of the output. -/
  | running (seen : Option Seen)
  /-- The program of the session that last held the name ended this way. -/
  | ended (outcome : Outcome)
  /-- The daemon of the session that last held the name was stopped by this signal, as the system
  stops it at logout or shutdown, and saved the session first, as it stood when the signal came:
  its program did not end by itself, and `resume` runs it again from that screen. -/
  | saved (signal : UInt8)
  /-- A kill dismissed the saved tmux pane of this name, which linger only read: no session took
  the name and no program ran, so nothing ended. -/
  | dismissed
  deriving Repr, DecidableEq

/-- How a session ended, as linger tells whoever asks: its program ended, or its daemon was
stopped by a signal first and saved it. A saved session's program has no outcome to report: its
daemon ended it, and `resume` runs it again. -/
inductive Ending where
  /-- The program ended this way, by itself or once a kill stopped it; `unknown` when linger did
  not see how. -/
  | program (outcome : Outcome)
  /-- The daemon was stopped by this signal, and saved the session. -/
  | saved (signal : UInt8)
  /-- No session ended: a kill dismissed the saved tmux pane of this name, which linger never
  ran. -/
  | dismissed
  deriving Repr, DecidableEq

/-- The end record a session that ended this way leaves its name. -/
@[expose]
def Ending.record : Ending → Record
  | .program outcome => .ended outcome
  | .saved signal => .saved signal
  | .dismissed => .dismissed

/-- The answer that tells how a session ended: its program's, as `Outcome.answer` gives it, or,
for a session a signal to its daemon saved, `saved` with that signal, whose status says which
signal, as a shell reports a job that signal stopped, and never a status of its program, which
did not end by itself and runs again on `resume`; and, for a dismissed tmux pane, that no
session has the name, `notFound`, as for a name no session ever took: linger never ran it, and a
dismissal hides it, so no signal and no status of a program is true of it. -/
@[expose]
def Ending.answer : Ending → Os.Answer
  | .program outcome => outcome.answer
  | .saved signal => .saved signal
  | .dismissed => .notFound

/-- What linger keeps of its sessions, by the key each file is kept under: one fact a file, a
live session's socket and its notification socket, a saved session's checkpoint and the end record of the last session to
hold a key, each keyed by the session's ID, which also marks a saved tmux pane as dealt with,
the names directory's entries, each a name and the ID it leads to, and the lock files a process
takes to act on an ID, which mean nothing of their own. -/
structure Records where
  /-- The IDs of the sockets in the runtime directory. -/
  sockets : List String
  /-- The IDs of the checkpoints in the state directory. -/
  checkpoints : List String
  /-- The IDs of the end records in the state directory. -/
  endings : List String
  /-- The names of the names directory's entries and the IDs they lead to. -/
  entries : List String := []
  /-- The names of the lock files, in the runtime directory and the state directory's `.locks`. -/
  locks : List String := []
  /-- The IDs of the notification sockets in the runtime directory, each a live session's, at
  the path its program's `NOTIFY_SOCKET` names. -/
  notifies : List String := []
  deriving Repr, DecidableEq

/-- Whether linger keeps a record of `key`, a name or an ID: its socket, its notification socket,
its checkpoint, its end record, or an entry of the names directory that names it or leads to
it. -/
@[expose]
def Records.holds (r : Records) (key : String) : Bool :=
  r.sockets.contains key || r.notifies.contains key || r.checkpoints.contains key ||
    r.endings.contains key ||
    r.entries.contains key

end Linger.Session

namespace Linger.Session.Start

/-- Whether a variable is linger's own: its name begins `LINGER_`. Linger reads its own from the
command that runs it, and a session's program sees none of them but the session's
`LINGER_SESSION`. -/
@[expose]
def lingers (key : String) : Bool := key.startsWith "LINGER_"

/-- What `start` does with the name it is given. -/
inductive Plan where
  /-- No session holds the name: take it. -/
  | take
  /-- A live session holds the name: refuse, and say so. -/
  | running
  /-- A saved session holds the name: refuse, and say so, without resuming it. -/
  | saved
  deriving Repr, DecidableEq

/-! ### A request's answer

A command that asks a daemon for a program, as `start` and `resume` do, waits a bounded time for
the daemon's report. When that wait runs out, the two race for the request's ticket: the daemon
takes it at its commit point, before the session is visible, and the command takes it when it
stops waiting. Whoever takes it decides whether the program runs, so the command's answer cannot
contradict what happens. -/

/-- Who took a request's ticket. -/
inductive Taker where
  /-- The daemon, at its commit point: it runs the program, or reports why it could not. -/
  | daemon
  /-- The command, when its wait ran out: the daemon runs nothing. -/
  | command
  deriving Repr, DecidableEq

/-- What a command answers about the program it asked for. -/
inductive Answer where
  /-- The program runs. -/
  | started
  /-- The program does not run. -/
  | notStarted
  deriving Repr, DecidableEq

/-- A request for a program, as the command and its daemon move it on. -/
structure Request where
  /-- Who took the ticket, once someone has. -/
  taker : Option Taker := none
  /-- Whether the daemon has decided: run the program, or not. -/
  settled : Bool := false
  /-- Whether the program runs. -/
  runs : Bool := false
  /-- What the command answered, once it has. -/
  answer : Option Answer := none
  deriving Repr, DecidableEq

/-- How a request moves on, given the daemon's decision whether to run the program from whether
it took the ticket (`proceeds`), and the command's answer from whether it took the ticket and
whether the program runs (`answer`). Taking the ticket is one atomic step for either side, as
unlinking one file name is: of two unlinks of a name, one succeeds. -/
inductive Step (proceeds : Bool → Bool) (answer : Bool → Bool → Answer) :
    Request → Request → Prop where
  /-- The daemon reaches its commit point first and takes the ticket. -/
  |
  daemonTakes (r : Request) (free : r.taker = none) :
    Step proceeds answer r { r with taker := some .daemon }
  /-- Once someone took the ticket, the daemon decides, once: it runs the program when it took
  the ticket, decides to, and the program could start (`ok`). -/
  |
  daemonDecides (r : Request) (taken : r.taker.isSome = true) (fresh : r.settled = false)
    (ok : Bool) :
    Step proceeds answer r
      { r with
        settled := true, runs := proceeds (r.taker == some .daemon) && ok }
  /-- The command's wait runs out first: it takes the ticket and answers. -/
  |
  commandTakes (r : Request) (free : r.taker = none) (unanswered : r.answer = none) :
    Step proceeds answer r
      { r with
        taker := some .command, answer := some (answer true r.runs) }
  /-- The daemon took the ticket: the command answers once the daemon has decided. -/
  |
  commandAnswers (r : Request) (lost : r.taker = some .daemon) (decided : r.settled = true)
    (unanswered : r.answer = none) :
    Step proceeds answer r { r with answer := some (answer false r.runs) }

/-- The states a request reaches from its start, by either side's steps in any order. -/
inductive Reachable (proceeds : Bool → Bool) (answer : Bool → Bool → Answer) : Request → Prop where
  /-- Nobody has taken the ticket. -/
  | init : Reachable proceeds answer {}
  /-- One step further. -/
  |
  step {r s : Request} :
    Reachable proceeds answer r → Step proceeds answer r s → Reachable proceeds answer s

end Linger.Session.Start

namespace Linger.Session.Stop

/-! ### How a session's processes end

A session's program leads its own terminal session and its own process group. When the session
ends, by a kill or by the program's own end, its daemon signals the program's process group, and
the rest of its terminal session, with each `Send` of the session's ending in turn, then writes
the end record. A process that left the terminal session with `setsid` is out of reach. -/

/-- How long the processes of an ending session have, after the signal that asks them to end,
before SIGKILL ends what remains: a second. -/
@[expose]
def grace : Nat := 1000

/-- Whom one signal of an ending reaches. -/
inductive Target where
  /-- The program alone, by its pid. -/
  | program
  /-- The program's whole process group, which it leads, by one signal to the group, and the
  rest of its terminal session. -/
  | group
  deriving DecidableEq, Repr

/-- One signal of an ending: whom it reaches, which signal, and how many milliseconds the daemon
then waits for them to end. -/
structure Send where
  /-- Whom the signal reaches. -/
  target : Target
  /-- The signal's number. -/
  signal : UInt32
  /-- How long the daemon then waits, in milliseconds. -/
  wait : Nat
  deriving DecidableEq, Repr

/-- Whether a signal to `target` reaches the process `pid`, of the program `program` whose process
group `inGroup program` tells: the program alone, or every process the group signal reaches. -/
@[expose]
def reach (program : Nat) (inGroup : Nat → Nat → Bool) : Target → Nat → Bool
  | .program, pid => pid == program
  | .group, pid => inGroup program pid

/-- Of the processes `alive`, those still running after `send`: `reaches send.target pid` says
whether its signal reaches `pid`, and `gone signal ms pid` whether `pid` has ended `ms`
milliseconds after `signal` reached it. -/
@[expose]
def survivors (reaches : Target → Nat → Bool) (gone : UInt32 → Nat → Nat → Bool) (alive : List Nat)
    (send : Send) : List Nat :=
  alive.filter fun pid => !(reaches send.target pid && gone send.signal send.wait pid)

/-- A wrong ending: SIGHUP and then SIGKILL to the program alone, as a stop that knows only its
pid sends them. The headline that an ending leaves no process of the program's group running is
shown to reject it. -/
@[expose]
def pidOnly : List Send := [⟨.program, 1, grace⟩, ⟨.program, 9, grace⟩]

end Linger.Session.Stop

namespace Linger.Session.Wire

/-- The protocol level a daemon speaks, which `info` reports as `protocol`, so a client can
refuse a request an older daemon cannot serve before sending it. Level 1 refuses a message it
does not know; level 2 also says how a program ended (`Msg.ended`); level 3 attaches with the
mode the client asks for (`Msg.attach`, tag 18) and reads the attach of levels 1 and 2, tag 3,
which carried only a size, as a message it does not know, so across a mismatch either side
refuses the other's attach; level 4 also says when a signal stopped the daemon, which saved the
session (`Msg.saved`, tag 19), where an older client would hear only that its connection was
lost. A daemon that reports no level predates the field and drops an unknown message
silently. An attach refuses a daemon of any earlier level, as one that reports none. -/
@[expose]
def protocol : Nat := 4

/-- Largest payload a frame may carry. Reads from the OS are ≤ 64 KiB, so honest senders stay
far below; a frame claiming more is either corruption or an attack, and the decoder turns it
into a connection error rather than memory growth. -/
@[expose]
def maxPayload : Nat := 262144

/-- The message vocabulary. Payload-carrying constructors keep raw
bytes; numeric fields are encoded LE at the payload layer. `unknown`
makes the decoder total: a tag from a newer peer is data. -/
inductive Msg where
  /-- client → daemon: bytes for the pty (keystrokes, pastes). -/
  | input (bytes : List UInt8)
  /-- daemon → client: bytes from the pty (also used for history/restore). -/
  | output (bytes : List UInt8)
  /-- client → daemon: my terminal is now cols×rows, 0 in either for a terminal with no size. -/
  | resize (cols rows : UInt32)
  /-- client → daemon: I am a live client with these rights, on a cols×rows terminal; stream
  output to me. -/
  | attach (mode : Mode) (cols rows : UInt32)
  /-- client → daemon: disconnect every attached client (incl. me). -/
  | detachAll
  /-- client → daemon: terminate the session. -/
  | kill
  /-- client → daemon: describe yourself (one-shot). -/
  | info
  /-- daemon → client: `k\tv\n` lines, one per field of the session's record. -/
  | infoReply (bytes : List UInt8)
  /-- client → daemon: send scrollback and the screen as output frames, then `done`. -/
  | history
  /-- daemon → client: the session ended, with the status a shell would report for its
  program (`Outcome.status`). -/
  | exited (status : UInt32)
  /-- client → daemon: hold this connection open until the child exits. -/
  | wait
  /-- daemon → client: end of a request/reply exchange. -/
  | done
  /-- daemon → client: request failed, human-readable reason. -/
  | err (msg : List UInt8)
  /-- client → daemon: send the current screen (grid only, plain text) as
  output frames, then `done`. `linger capture` — and it marks the session
  seen (a capture is a look). -/
  | screen
  /-- daemon → client: how the session's program ended, sent just before `exited`, which
  carries the same ending as the status a shell would report. -/
  | ended (outcome : Outcome)
  /-- daemon → client: this signal stopped the daemon, which saved the session before its
  program ended; no status follows, since the program has none to report. -/
  | saved (signal : UInt8)
  /-- client → daemon: replace your image with the program at this path, which carries the
  session over without ending it (`linger upgrade`). -/
  | upgrade (exe : List UInt8)
  /-- any tag this version does not know: skipped, never fatal. -/
  | unknown (tag : UInt8) (payload : List UInt8)
  deriving Repr, DecidableEq, Inhabited

/-- Decoder state. Both ends drop a connection whose decoder errored, rather than buffer
its input without bound. -/
structure Decoder where
  /-- Bytes of the incomplete frame; decoding keeps them within `4 + maxPayload`. -/
  buf : List UInt8 := []
  /-- An oversize frame arrived. The flag never clears, and no later chunk is decoded. -/
  errored : Bool := false
  deriving Repr, DecidableEq, Inhabited

/-- A message the encoder may send: its bytes fit one frame's payload, and an `unknown` message
carries a tag this version leaves unassigned, 3, the attach of levels 1 and 2, 11 to 13, the
label requests of versions before the session record had fields of its own, 21, the description
request of versions before a session's name said what it is, or one above, so that it cannot read
back as a known one. -/
@[expose]
def Msg.Fits : Msg → Prop
  | .input bytes | .output bytes | .infoReply bytes | .err bytes | .upgrade bytes =>
    bytes.length ≤ maxPayload
  | .unknown tag payload =>
    payload.length ≤ maxPayload ∧ (tag = 3 ∨ (11 ≤ tag.toNat ∧ tag.toNat ≤ 13) ∨ 21 ≤ tag.toNat)
  | _ => True

/-- A request that looks at the session: an attach, which shows its screen, or a capture of
it. -/
@[expose]
def Msg.Looks : Msg → Prop
  | .attach _ _ _ | .screen => True
  | _ => False

/-- A message with the bytes an `input` carries left out, so that two messages the same but for
the input a person typed read the same. -/
@[expose]
def Msg.blind : Msg → Msg
  | .input _ => .input []
  | m => m

/-- What a decoder reads from chunks fed one after another, starting in state `d`, as the
runtime's read loop feeds one chunk each poll round: the state after the last chunk, and every
message read, in order. -/
@[expose]
def feedAll (feed : Decoder → List UInt8 → Decoder × List Msg) (d : Decoder) :
    List (List UInt8) → Decoder × List Msg
  | [] => (d, [])
  | c :: cs =>
    let r := feed d c
    let rest := feedAll feed r.1 cs
    (rest.1, r.2 ++ rest.2)

end Linger.Session.Wire

namespace Linger.Session

open Linger.Session.Wire (Msg)

/-- Most connections a session holds; a session refuses and closes one more. The daemon
stops accepting at the same count. -/
@[expose]
def maxClients : Nat := 16

/-- Most fields a session's record holds of its own, its description and an import's
provenance: describing a session past it is refused, and booting keeps only the first this many
restored fields. -/
@[expose]
def maxFields : Nat := 64

/-- The keys of the fields a session's record holds of its own: `description`, which an older
linger's `describe` set and no command sets now, and the `tmux.` fields with which a tmux import
records the pane it came from, which only the import sets. -/
@[expose]
def recordField (key : String) : Bool := key == "description" || key.startsWith "tmux."

/-- How long a session's changes may go unsaved: a session asks for a checkpoint save no later
than this after the first change no save holds, and saves on its own at most once in it. A
minute, in natural-number milliseconds, so that adding it to a deadline cannot wrap. -/
@[expose]
def ckptIntervalMs : Nat := 60000

/-- What a client attached to a session, or waiting for its end, hears when the session ends this
way: how its program ended and then the status a shell would report for that, or that a signal
stopped the daemon, which saved the session; nothing for a dismissed tmux pane, which no daemon
ran. -/
@[expose]
def Ending.told : Ending → List Msg
  | .program outcome => [.ended outcome, .exited outcome.status]
  | .saved signal => [.saved signal]
  | .dismissed => []

/-- One connection's record: its identity, rights, terminal size, attach and request state, and
its undecoded input. -/
structure Client where
  /-- The connection's identifier, as in `Event.connected`. -/
  id : Nat
  /-- Terminal width from the latest attach or resize message, 0 for a terminal with no size. -/
  cols : UInt32 := 80
  /-- Terminal height from the latest attach or resize message, 0 for a terminal with no size. -/
  rows : UInt32 := 24
  /-- The connection attached and receives the session's output. -/
  attached : Bool := false
  /-- What the connection may do: the mode it attached with, and `writable` before it attaches.
  Its rights come from this alone, never from its size. -/
  mode : Mode := .writable
  /-- Attach order: of the attached writable clients whose terminals have a size, the newest
  sizes the session. -/
  seq : Nat := 0
  /-- `linger wait` parked here until the child exits. -/
  waiting : Bool := false
  /-- An `info`, `history`, `screen` or control `resize` from the current read
  was answered. One request per read: clients wait for the reply before the
  next request, and later requests decoded from the same read are refused. -/
  answered : Bool := false
  /-- Partial frames from this connection. No session state holds an errored decoder: the
  session closes the connection instead. -/
  decoder : Wire.Decoder := {}
  deriving Repr, Inhabited

/-- What the operating system reports of the foreground of a session's terminal: the leader of
its foreground process group, with the words that process runs with and its directory, as the
world claim `Pty.Foreground` says. -/
structure Foreground where
  /-- The process's id, which is its group's. -/
  pid : Nat
  /-- Its words, its program's name first. -/
  argv : List String
  /-- The directory it runs in. -/
  dir : String
  deriving DecidableEq, Repr

/-- What the daemon read of the world as it was about to answer a request: the clocks, so that
`info` can say how long ago the program last wrote, its terminal's foreground, so that `info` can
say what runs there, and whether its terminal echoes what is typed. -/
structure Observation where
  /-- The monotonic clock in milliseconds, as `.tick` reads it. -/
  nowMs : Nat
  /-- The real-time clock, in seconds since the epoch. -/
  wallS : Nat
  /-- Whether the session's program is its login shell: it started with no command. -/
  login : Bool
  /-- The terminal's foreground, when the operating system reports one. -/
  foreground : Option Foreground
  /-- Whether the terminal echoes what is typed, its `ECHO` flag as the program last set it, when
  the operating system reports it. -/
  echo : Option Bool := none
  deriving DecidableEq, Repr

/-- What the runtime feeds in. All byte payloads are `List UInt8`; the
runtime converts at the fd boundary. -/
inductive Event where
  /-- A connection was accepted. -/
  | connected (id : Nat)
  /-- A connection sent bytes. -/
  | bytes (id : Nat) (chunk : List UInt8)
  /-- A connection ended, or the runtime retired it. -/
  | closed (id : Nat)
  /-- The child wrote output to the pty. -/
  | ptyOut (chunk : List UInt8)
  /-- The session's program ended this way. The runtime reports it as soon as it reaps the
  program, whether or not anything else still holds the pty. -/
  | childExited (outcome : Outcome)
  /-- The session's program ended this way once the daemon stopped it, as a kill asks: the
  runtime's answer to `Effect.stopProgram`. -/
  | stopped (outcome : Outcome)
  /-- The daemon heard this terminating signal, SIGHUP, SIGINT, SIGQUIT or SIGTERM, as the system
  sends at logout or shutdown: the environment stopping linger, not the program ending. -/
  | signal (signal : UInt8)
  /-- A poll round ended; `nowMs` is the monotonic clock in milliseconds. -/
  | tick (nowMs : Nat)
  /-- The daemon read the world, as it does before it answers a request: what `info` then
  reports of the session's present. -/
  | observed (observation : Observation)
  /-- The last `.checkpoint` effect failed to save. -/
  | checkpointFailed
  /-- The program sent the session this notification, one datagram to the socket its
  `NOTIFY_SOCKET` names, as `sd_notify` sends one, of at most `Notify.cap` bytes. -/
  | notified (datagram : List UInt8)
  deriving Repr

/-- The most bytes of one notification a daemon reads: a read takes one datagram, and the kernel
discards the rest of a longer one. -/
@[expose]
def Notify.cap : Nat := 4096

/-- The most assignments of one notification a session reads. -/
@[expose]
def Notify.keys : Nat := 64

/-- The most notifications a daemon reads in one poll round; the rest wait for the next. -/
@[expose]
def Notify.perRound : Nat := 16

/-- A notification's lines, split at each newline. -/
@[expose]
def Notify.lines : List UInt8 → List (List UInt8)
  | [] => [[]]
  | b :: rest =>
    if b = 0x0A then [] :: Notify.lines rest
    else
      match Notify.lines rest with
      | line :: more => (b :: line) :: more
      | [] => [[b]]

/-- The assignment a line makes: its key, before its first `=`, and its value, after it; none
for a line with no `=`. -/
@[expose]
def Notify.assignment : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: rest =>
    if b = 0x3D then some ([], rest)
    else (Notify.assignment rest).map fun (key, value) => (b :: key, value)

/-- The assignments a notification makes, as `sd_notify` sends them: its lines, each a key, `=`
and a value, the first `Notify.keys` of them; a line with no `=` makes none. -/
@[expose]
def Notify.assignments (datagram : List UInt8) : List (List UInt8 × List UInt8) :=
  ((Notify.lines datagram).filterMap Notify.assignment).take Notify.keys

/-- `READY`, the key that says a program is ready. -/
@[expose]
def Notify.readyKey : List UInt8 := [0x52, 0x45, 0x41, 0x44, 0x59]

/-- `STATUS`, the key whose value is a program's status text. -/
@[expose]
def Notify.statusKey : List UInt8 := [0x53, 0x54, 0x41, 0x54, 0x55, 0x53]

/-- Whether a program said it is ready in the notifications `sent`: one of them assigns
`READY=1`. Every other assignment, `RELOADING=1`, `STOPPING=1`, `MAINPID=` and `WATCHDOG=1`
among them, tells a session nothing. -/
@[expose]
def Notify.ready (sent : List (List UInt8)) : Bool :=
  sent.any fun d => (Notify.assignments d).contains (Notify.readyKey, [0x31])

/-- The status text a program last gave in the notifications `sent`, in order: the value of the
last `STATUS=` assignment, `none` before any. -/
@[expose]
def Notify.status (sent : List (List UInt8)) : Option (List UInt8) :=
  ((sent.flatMap Notify.assignments).filterMap fun (key, value) =>
      if key = Notify.statusKey then some value else none).getLast?

/-- The notifications a session's events bring it, in order. -/
@[expose]
def Notify.heard : List Event → List (List UInt8)
  | [] => []
  | .notified d :: evs => d :: Notify.heard evs
  | _ :: evs => Notify.heard evs

/-- What a session's program owns, as its session keeps it, each field from the one source its
standard names: its window's title, which OSC 0 and OSC 2 set on the session's terminal; whether
it rang the bell or posted a desktop notification, a BEL, an OSC 9 that is no ConEmu sub-command
or an OSC 777 `notify`, since the session was last looked at, and that notification's text; what
its shell's OSC 133 marks told of its commands; what the operating system last reported of its
terminal, its foreground and its echo among it; whether it said it is ready and the status
text it last gave, through `sd_notify`'s socket; and the progress it last declared with ConEmu's
OSC `9;4`. No other output and no client writes one; a look clears what is told only until
someone sees it (`step_owned`). -/
structure Owned where
  /-- The window's title, as the session's terminal holds it. -/
  title : String
  /-- A bell or a notification since the session was last looked at. -/
  asks : Bool
  /-- The text of the last notification since the session was last looked at. -/
  notice : Option (List UInt8)
  /-- What the shell's marks told of its commands. -/
  commands : Commands
  /-- What the operating system last reported of the session's terminal. -/
  observed : Option Observation
  /-- The program said it is ready. -/
  ready : Bool
  /-- The status text the program last gave. -/
  status : Option (List UInt8)
  /-- The progress the program last declared, `none` before any or once it removed it. -/
  progress : Option Terminal.Mediation.Progress
  deriving Repr, DecidableEq

/-- A wrong reading of a session: its program works, as a command running does, while it wrote
within the last three seconds, as the `idle` field its `fields` report says, the window rule
before programs declared their work. The headlines that a session works exactly while its program says so, and that its
status never changes as time passes, are shown to reject it. -/
@[expose]
def Seen.windowed {S : Type} (fields : S → List (String × String)) (seen : S → Seen) (s : S) :
    Seen :=
  { seen s with
    running :=
      (seen s).running || ((fields s).lookup "idle").any fun age => age.toNat?.any (· < 3) }

/-- A wrong reading of a session: an error its program declared is read as progress under way,
`⣷`. The headline that each declared state has its own status is shown to reject it. -/
@[expose]
def Seen.errorWorks {S : Type} (seen : S → Seen) (s : S) : Seen :=
  { seen s with
    progress := if (seen s).progress = some .error then some .normal else (seen s).progress }

/-- A wrong reading of a session: a pause its program declared is read as progress under way,
`⣷`. The headline that each declared state has its own status is shown to reject it. -/
@[expose]
def Seen.pauseWorks {S : Type} (seen : S → Seen) (s : S) : Seen :=
  { seen s with
    progress := if (seen s).progress = some .paused then some .normal else (seen s).progress }

/-- A wrong reading of a session: any output since the last look is unseen, as the `behind` count
its `fields` report says, a title or a line rewritten in place among it. The headline that a
session's unseen lines are those that entered its history is shown to reject it. -/
@[expose]
def Seen.anyOutput {S : Type} (fields : S → List (String × String)) (seen : S → Seen) (s : S) :
    Seen :=
  { seen s with unseen := ((fields s).lookup "behind").any fun count => count.toNat?.any (0 < ·) }

/-- What one chunk of output tells of what the program owns, as the terminal package's mediator
heard it: the title the terminal holds after it, whether it rang the bell or posted a
notification, the text of its last notification, its last progress report, and the shell's marks,
in order, each as `Commands.hear` says it tells; `seen` says that a client is attached, which sees
the output as it arrives, so that it leaves no ask, no notification and no ending to tell. A
progress report sets the progress, or removes it, whoever watches. -/
@[expose]
def Owned.hear (o : Owned) (title : String) (asks : Bool) (notice : Option (List UInt8))
    (progress : Option (Option Terminal.Mediation.Progress)) (marks : List Terminal.Mediation.Mark)
    (seen : Bool) : Owned :=
  { o with
    title, asks := !seen && (o.asks || asks), notice := if seen then none else notice.or o.notice,
    progress := progress.getD o.progress,
    commands :=
      { running := (marks.foldl Commands.hear o.commands).running,
        finished := if seen then none else (marks.foldl Commands.hear o.commands).finished } }

/-- What a look leaves of what the program owns: no ask, no notification and no ending to tell,
the rest as it was. -/
@[expose]
def Owned.look (o : Owned) : Owned :=
  { o with
    asks := false, notice := none, commands := { o.commands with finished := none } }

/-- What the daemon's reading of the world leaves of what the program owns: that reading. -/
@[expose]
def Owned.observe (o : Owned) (observation : Observation) : Owned :=
  { o with observed := some observation }

/-- What a notification the program sent leaves of what it owns: ready once it said so, and the
status text it gave last, the rest as it was. -/
@[expose]
def Owned.notify (o : Owned) (datagram : List UInt8) : Owned :=
  { o with
    ready := o.ready || Notify.ready [datagram], status := (Notify.status [datagram]).or o.status }

/-- The time a session's events have told it: the latest time among their ticks, or 0 before
any tick. A daemon's ticks read the monotonic clock as each poll round ends, so this is the time
of the last tick, and an event after them happened no earlier. -/
@[expose]
def clock : List Event → Nat
  | [] => 0
  | .tick now :: evs => max now (clock evs)
  | _ :: evs => clock evs

/-- What the runtime executes, given the type of a captured repaint. -/
inductive Effect (Plan : Type) where
  /-- Send one message to a connection. -/
  | send (id : Nat) (m : Msg)
  /-- Stream a captured repaint to a connection ahead of its later output. -/
  | replay (id : Nat) (plan : Plan)
  /-- Close a connection. -/
  | close (id : Nat)
  /-- Write bytes to the child through the pty. -/
  | writePty (bytes : List UInt8)
  /-- Set the pty's window size. -/
  | resizePty (cols rows : UInt32)
  /-- End the program: each signal of the session's ending in turn, SIGHUP first, to its whole
  process group and every other process of its terminal session, until they end. The runtime
  answers how the program ended. -/
  | stopProgram
  /-- Save a checkpoint of the session. -/
  | checkpoint
  /-- Delete the session's checkpoint. -/
  | dropCheckpoint
  /-- Leave this as the name's end record, which the daemon writes before it gives the name
  up. -/
  | record (record : Record)
  /-- Stop the daemon; no later event is handled. -/
  | exit
  /-- Replace the daemon's image with the program at `exe`, which carries the session over, and
  answer connection `id`: once the new image serves, or with why the old one keeps serving. -/
  | upgrade (id : Nat) (exe : List UInt8)
  deriving Repr, DecidableEq

/-- Whether a session's ending is seen as it happens, among these connections: one of them is
attached, of either mode, and so is told how the session ended right after the screen it shows.
A watcher is told the same ending as a typist, so it sees it too. A connection that only waits
for the ending, as `wait` opens, hears the outcome but is shown no screen, and does not see it. -/
@[expose]
def seenBy (roster : List Client) : Bool := roster.any (·.attached)

/-- An effect with the bytes it writes to the program left out, so that a write of what a person
typed reads the same whatever they typed. -/
@[expose]
def Effect.blind {Plan : Type} : Effect Plan → Effect Plan
  | .writePty _ => .writePty []
  | e => e

/-- A read that holds whole frames, `encode` of messages that fit one, one after another, as a
client sends them; any other event. -/
@[expose]
def Framed (encode : Wire.Msg → List UInt8) : Event → Prop
  | .bytes _ chunk => ∃ ms : List Wire.Msg, chunk = ms.flatMap encode ∧ ∀ m ∈ ms, m.Fits
  | _ => True

/-- Two traces of events that differ at most in the input clients type: event by event, the same
event, or two reads by one connection, each of whole frames of messages that fit one, the same
messages but for the bytes their `input` messages carry. -/
inductive Typed (encode : Wire.Msg → List UInt8) : List Event → List Event → Prop where
  /-- No events. -/
  | nil : Typed encode [] []
  /-- The same event, then traces that differ at most in input. -/
  |
  same (ev : Event) {evs evs' : List Event} (rest : Typed encode evs evs') :
    Typed encode (ev :: evs) (ev :: evs')
  /-- Two reads by one connection that differ in the input they carry alone, then traces that
  differ at most in input. -/
  |
  input (id : Nat) (ms ms' : List Wire.Msg) (fits : ∀ m ∈ ms, m.Fits) (fits' : ∀ m ∈ ms', m.Fits)
    (blind : ms.map Wire.Msg.blind = ms'.map Wire.Msg.blind) {evs evs' : List Event}
    (rest : Typed encode evs evs') :
    Typed encode (.bytes id (ms.flatMap encode) :: evs) (.bytes id (ms'.flatMap encode) :: evs')

/-- How an event ends the session, if it does, when `seen` says whether its ending is seen as it
happens (`seenBy`): how the session ended, and whether its last screen stays saved. A program's
own end leaves the session as its result exactly while nobody has seen it: seen as it happens, it
is discarded as a kill discards it, and with nobody attached its last screen is saved until the
first attach shows it (`Linger.App.Recovery.visit`). A terminating signal to the daemon leaves it
saved to resume, which is no ending, seen or not; a kill discards it. -/
@[expose]
def Event.ends (seen : Bool) : Event → Option (Ending × Bool)
  | .childExited outcome => some (.program outcome, !seen)
  | .stopped outcome => some (.program outcome, false)
  | .signal number => some (.saved number, true)
  | _ => none

/-- Whether an effect sends a frame of a rendered reply: an `output` frame of a history or
screen capture, or a frame of an `info` reply. -/
@[expose]
def Effect.rendered {Plan : Type} : Effect Plan → Bool
  | .send _ (.output _) | .send _ (.infoReply _) => true
  | _ => false

/-- Whether an effect resizes the pty. -/
@[expose]
def Effect.resizes {Plan : Type} : Effect Plan → Bool
  | .resizePty _ _ => true
  | _ => false

/-- Whether an effect streams a repaint. -/
@[expose]
def Effect.replays {Plan : Type} : Effect Plan → Bool
  | .replay .. => true
  | _ => false

/-- The session after a trace of events, given its transition: each event starts from the state
the previous one left, and the effects come out in the order the events asked for them. -/
@[expose]
def trace {S E F : Type} (step : S → E → S × List F) (s : S) : List E → S × List F
  | [] => (s, [])
  | ev :: evs =>
    let r := step s ev
    let rest := trace step r.1 evs
    (rest.1, r.2 ++ rest.2)

/-- ConEmu's report that removes the progress: `ESC ] 9 ; 4 ; 0 BEL`. -/
@[expose]
def clearProgress : List UInt8 := [0x1B, 0x5D, 0x39, 0x3B, 0x34, 0x3B, 0x30, 0x07]

/-- A wrong transition: `step`, which loses a declared state at the next output, as if the
program had removed it, though it sent no `0`. The headline that each declared state holds until
the program sends another is shown to reject it. -/
@[expose]
def forgetsProgress {S P : Type} (step : S → Event → S × List (Effect P)) (s : S) :
    Event → S × List (Effect P)
  | .ptyOut chunk => step s (.ptyOut (clearProgress ++ chunk))
  | ev => step s ev

/-- A wrong transition: `step` with each effect `drop` picks removed, its states unchanged. The
headlines about program output and about an attach's repaint are shown to reject it, without
output frames and without repaints. -/
@[expose]
def without {S E Plan : Type} (drop : Effect Plan → Bool) (step : S → E → S × List (Effect Plan))
    (s : S) (ev : E) : S × List (Effect Plan) := ((step s ev).1, (step s ev).2.filter (!drop ·))

/-- A wrong transition: `step`, which also reads a program's notifications from its output, as
if each chunk the program wrote to its terminal were a datagram to its notification socket. The
headline that a program's readiness and status are what it sent is shown to reject it. -/
@[expose]
def outputNotifies {S F : Type} (step : S → Event → S × List F) (s : S) : Event → S × List F
  | .ptyOut chunk =>
    ((step (step s (.ptyOut chunk)).1 (.notified chunk)).1,
      (step s (.ptyOut chunk)).2 ++ (step (step s (.ptyOut chunk)).1 (.notified chunk)).2)
  | ev => step s ev

/-- A wrong transition: `step`, after which a read's bytes are kept by `keep` too, as a checkpoint
that appended the last input would keep them. The headline that input is never recorded is shown
to reject it. -/
@[expose]
def keepsInput {S F : Type} (step : S → Event → S × List F) (keep : S → List UInt8 → S) (s : S) :
    Event → S × List F
  | .bytes id chunk => (keep (step s (.bytes id chunk)).1 chunk, (step s (.bytes id chunk)).2)
  | ev => step s ev

/-- The session bounds, read through a state's client roster, record fields and pty scanner: the
roster and the fields within their caps, every client's frame decoder healthy and
holding at most one frame, and the scanner within its caps. -/
structure Bounds {S : Type} (roster : S → List Client) (fields : S → List (String × String))
    (scanner : S → Terminal.Mediation.Scan) (s : S) : Prop where
  /-- At most `maxClients` clients. -/
  clientsLe : (roster s).length ≤ maxClients
  /-- At most `maxFields` fields. -/
  fieldsLe : (fields s).length ≤ maxFields
  /-- Every client's decoder is healthy and holds at most one frame. -/
  decOk : ∀ c ∈ roster s, c.decoder.errored = false ∧ c.decoder.buf.length ≤ 4 + Wire.maxPayload
  /-- The pty scanner is within its caps. -/
  scanOk : (scanner s).Bounded

end Linger.Session

namespace Linger.Session

/-- Writes of one kind a daemon does off its loop, so that a slow disk holds up no answer and no
output: the one running, on a thread of its own, and the latest one asked for while it ran, which
runs when it ends, in place of any asked for before it. -/
structure Offloop (R W : Type) where
  /-- The write running. -/
  running : Option R := none
  /-- The latest write asked for while one ran. -/
  waiting : Option W := none

/-- What a daemon's off-loop writes become once it asks for `w`: its decision `ask` says whether
`w` waits or which write starts now, and `start` runs a write on a thread of its own. -/
@[expose]
def Offloop.run {R W : Type} (ask : Offloop R W → W → Offloop R W × Option W) (start : W → R)
    (o : Offloop R W) (w : W) : Offloop R W :=
  match ask o w with
  | (o, none) => o
  | (o, some w) => { o with running := some (start w) }

/-- A wrong decision: it starts every write it is asked for at once, so that no write waits and
none is coalesced. The headline about off-loop writes is shown to reject it. -/
@[expose]
def Offloop.eager {R W : Type} (o : Offloop R W) (w : W) : Offloop R W × Option W := (o, some w)

/-- What a daemon's off-loop writes of one kind hear: a write asked for, or the end of the one
running. -/
inductive Offloop.Op (W : Type) where
  /-- The daemon asks for this write. -/
  | ask (w : W)
  /-- The running write ended. -/
  | done

/-- Whether an event is the end of the running write. -/
@[expose]
def Offloop.Op.isDone {W : Type} : Offloop.Op W → Bool
  | .ask _ => false
  | .done => true

/-- A daemon's off-loop writes of one kind, each its own result, and the writes started so far,
once it hears `op`: its decisions `ask`, for a write asked for, and `done`, when the running one
ends, say which write starts now, if any, and that write then runs. -/
@[expose]
def Offloop.cycle {W : Type} (ask : Offloop W W → W → Offloop W W × Option W)
    (done : Offloop W W → Offloop W W × Option W) (o : Offloop W W × List W) (op : Offloop.Op W) :
    Offloop W W × List W :=
  match
    (match op with
    | .ask w => ask o.1 w
    | .done => done o.1) with
  | (s, none) => (s, o.2)
  | (s, some w) => ({ s with running := some w }, o.2 ++ [w])

/-- How a program has set its terminal to hand it input. -/
inductive Pty.Mode where
  /-- Raw, as `cfmakeraw` and `stty raw -echo` leave it: no line editing, echo, signal, flow
  control or end-of-file characters, and no byte translated or stripped. -/
  | raw
  /-- Any other setting, among them the cooked mode a terminal starts in, whose line discipline
  edits lines and turns ^C, ^Z and ^\ into signals instead of input. -/
  | other
  deriving Repr, DecidableEq

/-- Why a program could not start in a new terminal, with the operating system's words. -/
inductive Spawn.Failure where
  /-- Its directory could not be entered. -/
  | directory (why : String)
  /-- No program of its name was found. -/
  | notFound (why : String)
  /-- Its program was found and could not be run. -/
  | notRunnable (why : String)
  deriving Repr, DecidableEq

/-- What a program's start resets, of the process state it would otherwise inherit from the
process that starts it, and through that process from the command that asked for the session: a
handler ends at exec by itself, but an ignored signal, the signal mask and each open descriptor
survive exec. -/
structure Spawn.Reset where
  /-- Every signal goes back to its default action. -/
  dispositions : Bool
  /-- No signal stays blocked. -/
  mask : Bool
  /-- No descriptor stays open from 3 up, past the three of the program's terminal. -/
  descriptors : Bool
  deriving Repr, DecidableEq

/-- What one of a started program's descriptors refers to. -/
inductive Spawn.Descriptor where
  /-- The terminal of the program's session. -/
  | terminal
  /-- Any other open file, such as one the command that asked for the session left open. -/
  | other
  deriving Repr, DecidableEq

/-- What a program sees of its start: its words, the directory it runs in, each environment
variable's value, `none` for a variable that is unset, and the signals and descriptors it starts
with. -/
structure Spawn.Started where
  /-- Its words, its program's name first. -/
  argv : List String
  /-- The directory it runs in. -/
  dir : String
  /-- Each environment variable's value. -/
  env : String → Option String
  /-- Whether it ignores each signal, by number. One it does not ignore has its default action,
  since no handler survives exec. -/
  ignored : Nat → Bool
  /-- Whether it blocks each signal, by number. -/
  blocked : Nat → Bool
  /-- What each descriptor, by number, refers to, `none` for one that is closed. -/
  descriptor : Nat → Option Spawn.Descriptor

end Linger.Session

namespace Linger.Session.Driver

/-- A transport operation reports whether its target disconnected; a checkpoint
reports whether saving failed; stopping the program reports how it ended. Other effects cannot
enqueue feedback. -/
abbrev Reply {Plan : Type} : Effect Plan → Type
  | .send .. | .replay .. | .close .. | .checkpoint => Bool
  | .stopProgram => Outcome
  | _ => Unit

/-- The reply of an effect that succeeded, when a stopped program ended as `ending` says: its
target stayed connected, its checkpoint was saved, or its program ended that way. -/
@[expose]
def success {Plan : Type} (ending : Outcome) : (eff : Effect Plan) → Reply eff
  | .send .. | .replay .. | .close .. | .checkpoint => false
  | .stopProgram => ending
  | .writePty .. | .resizePty .. | .dropCheckpoint | .record _ | .exit | .upgrade .. => ()

/-- What an effect that succeeded feeds back to the session: a stop's reply, how its program
ended, as the event `stopped ending`, and nothing for any other effect, since its target stayed
connected and its checkpoint was saved. -/
@[expose]
def fedBack {Plan : Type} (ending : Outcome) : Effect Plan → List Event
  | .stopProgram => [.stopped ending]
  | _ => []

/-- A transition whose effects each carry the state its event leaves, the state a driver executes
them with. -/
@[expose]
def withState {S E F : Type} (step : S → E → S × List F) (s : S) (ev : E) : S × List (S × F) :=
  ((step s ev).1, (step s ev).2.map ((step s ev).1, ·))

/-- The events a session handles when a driver hands it `events` and every effect succeeds:
`Handles step ending s events handled exits` says that from state `s` a session with transition
`step` handles `handled`, which is `events` in order, each followed by what its effects feed back
before the next (`fedBack ending`). An event whose effects ask the daemon to exit is the last one
handled, and `exits` says whether one did. At most one `handled` and `exits` fit `s` and
`events`. -/
inductive Handles {S Plan : Type} (step : S → Event → S × List (Effect Plan)) (ending : Outcome) :
    S → List Event → List Event → Bool → Prop where
  /-- No event is left, and none asked the daemon to exit. -/
  | done (s : S) : Handles step ending s [] [] false
  /-- An event whose effects ask the daemon to exit is the last one handled. -/
  |
  exit (s : S) (ev : Event) (rest : List Event) (asks : Effect.exit ∈ (step s ev).2) :
    Handles step ending s (ev :: rest) [ev] true
  /-- Any other event is handled, then what its effects feed back, then the events after it. -/
  |
  next (s : S) (ev : Event) (rest handled : List Event) (exits : Bool)
    (stays : Effect.exit ∉ (step s ev).2)
    (later :
      Handles step ending (step s ev).1 ((step s ev).2.flatMap (fedBack ending) ++ rest) handled
        exits) :
    Handles step ending s (ev :: rest) (ev :: handled) exits

/-- The driver's state between events. -/
structure Result (S World : Type) where
  /-- The session state. -/
  st : S
  /-- The interpreter's world. -/
  world : World
  /-- An event's effects requested exit, so no later event is consumed. -/
  exiting : Bool := false

/-- A wrong driver: it ignores its interpreter and its events and lands on `target`. The
headline about the event driver is shown to reject it. -/
@[expose]
def jump {S Plan : Type} (target : S) {m : Type → Type} [Monad m] {World : Type}
    (_ : S → World → (eff : Effect Plan) → m (World × Reply eff)) (r : Result S World)
    (_ : List Event) : m (Result S World) := pure { r with st := target }

/-- A wrong driver: it stops the daemon whatever its events. The headline about disconnects and
failed saves is shown to reject it. -/
@[expose]
def halt {S Plan : Type} {m : Type → Type} [Monad m] {World : Type}
    (_ : S → World → (eff : Effect Plan) → m (World × Reply eff)) (r : Result S World)
    (_ : List Event) : m (Result S World) := pure { r with exiting := true }

/-- A wrong driver: it does nothing, handing the session no event and executing no effect, and
returns its input. The headline that the driver runs the session's trace is shown to reject it. -/
@[expose]
def inert {S Plan : Type} {m : Type → Type} [Monad m] {World : Type}
    (_ : S → World → (eff : Effect Plan) → m (World × Reply eff)) (r : Result S World)
    (_ : List Event) : m (Result S World) := pure r

end Linger.Session.Driver

namespace Linger.Session.Checkpoint

/-- What a checkpoint holds, given the terminal type: the terminal, the working directory and
the fields of the session's record. It derives no `Inhabited`: a default terminal is a choice, not a state the
emulator reaches. -/
structure Ckpt (V : Type) where
  /-- The terminal state; its parser state is not saved. -/
  vt : V
  /-- The directory the restored session's child starts in. -/
  cwd : String
  /-- The fields of the session's record, as key/value pairs whose keys are `recordField`s. -/
  fields : List (String × String)

/-- `v` is the terminal of a checkpoint `load` returns for some bytes: a terminal a resumed
session can start from. -/
@[expose]
def Decoded {V : Type} (load : ByteArray → Option (Ckpt V)) (v : V) : Prop :=
  ∃ bytes c, load bytes = some c ∧ c.vt = v

/-- The description a tmux import gives a session whose fields are `labels`: the window's name,
which tmux shows, from the field `tmux.window-title` when it is not empty, and none otherwise. A
record an older linger wrote without a description reads with this one. -/
@[expose]
def importDescription (labels : List (String × String)) : List (String × String) :=
  match labels.lookup "tmux.window-title" with
  | some title => if title.isEmpty then [] else [("description", title)]
  | none => []

end Linger.Session.Checkpoint

namespace Linger.Session.Handoff

/-- One connection a daemon hands its new image, by descriptor number: the bytes it still owes
the connection, its framing included, and, for one the session already closed, the time by the
monotonic clock until which it may still finish them. -/
structure Conn where
  /-- The connection's descriptor, which is its identifier in the session. -/
  fd : Nat
  /-- The bytes the daemon still owes it, in order. -/
  owed : List UInt8
  /-- When it must have finished them, for a connection the session closed; `none` for one it
  still serves. -/
  closeBy : Option Nat
  deriving DecidableEq, Repr

/-- What a daemon hands its new image beside the session's state: the descriptors it keeps open
across the exec, by number, its program's id, what it still owes its program and its
connections, and who asked. -/
structure World where
  /-- The listening socket at the session's path. -/
  listenFd : Nat
  /-- The pty master of the session's terminal. -/
  ptyFd : Nat
  /-- The session's program, the daemon's child. -/
  childPid : Nat
  /-- The signal pipe's read end and write end. -/
  signals : Nat × Nat
  /-- The descriptors that hold the session's locks. -/
  locks : List Nat
  /-- Every connection the daemon owns, in admission order. -/
  conns : List Conn
  /-- The bytes the daemon still owes its program, in order. -/
  ptyIn : List UInt8
  /-- Whether the session's program is its login shell: it started with no command. -/
  login : Bool
  /-- The connection that asked for the upgrade, which the new image answers. -/
  asker : Nat
  deriving DecidableEq, Repr

/-- Every descriptor a handoff names, which its new image reads from: the listening socket, the
pty, both ends of the signal pipe, the locks and every connection. -/
@[expose]
def World.fds (w : World) : List Nat :=
  [w.listenFd, w.ptyFd, w.signals.1, w.signals.2] ++ w.locks ++ w.conns.map (·.fd)

/-- What begins every handoff: `"LNGH"`, then its format's number, one byte. -/
@[expose]
def magic : List UInt8 := [0x4C, 0x4E, 0x47, 0x48]

/-- The format of the handoffs this version writes. -/
@[expose]
def version : Nat := 4

/-- The formats of the handoffs this version reads, the one it writes among them: a newer
version reads every older format it lists here, and a daemon hands its session only to a
binary that lists the format it writes. -/
@[expose]
def formats : List Nat := [1, 2, 3, 4]

/-- The first bytes of a handoff of format `v`. -/
@[expose]
def header (v : Nat) : List UInt8 := magic ++ [UInt8.ofNat v]

end Linger.Session.Handoff

/-! ## Reachable queue states

A queue starts empty and moves only through the given operations, so each predicate covers
every queue a plain importer can hold when the queue type is sealed. -/

namespace Linger.Session.Buf

/-- The pty-input queue's reachable states: it starts `empty` and moves only through capped
`offer`s and flush `advance`s. -/
inductive InputReach {B : Type} (empty : B) (offer : Nat → B → ByteArray → B × Bool)
    (advance : B → Nat → B) (cap : Nat) : B → Prop where
  /-- The queue every session starts with. -/
  | empty : InputReach empty offer advance cap empty
  /-- A capped offer, whether it queued the frame or dropped it. -/
  |
  offer (b : B) (more : ByteArray) :
    InputReach empty offer advance cap b → InputReach empty offer advance cap (offer cap b more).1
  /-- A flush that removes the bytes written. -/
  |
  advance (b : B) (n : Nat) :
    InputReach empty offer advance cap b → InputReach empty offer advance cap (advance b n)

/-- The client-output queue's **retained** states: it starts `empty`, and an `enqueue` that
reports "cut" gets the client dropped from the roster — so a queue the daemon keeps holds only
enqueues that reported `false`, plus flush advances. The not-cut hypothesis on the constructor
IS the append-then-cut discipline. -/
inductive OutputReach {B : Type} (empty : B) (enqueue : Nat → B → ByteArray → B × Bool)
    (advance : B → Nat → B) (cap : Nat) : B → Prop where
  /-- The queue every connection starts with. -/
  | empty : OutputReach empty enqueue advance cap empty
  /-- An append that left the client connected. -/
  |
  enqueue (b : B) (more : ByteArray) :
    OutputReach empty enqueue advance cap b →
      (enqueue cap b more).2 = false → OutputReach empty enqueue advance cap (enqueue cap b more).1
  /-- A flush that removes the bytes written. -/
  |
  advance (b : B) (n : Nat) :
    OutputReach empty enqueue advance cap b → OutputReach empty enqueue advance cap (advance b n)

/-- The pty-input queue's history: the input it `accepted`, the bytes it handed the kernel
(`written`), and the queue, as capped offers and flushes move it. A flush hands the kernel the
first `n` bytes of what the queue holds (`pending`), then drops them. -/
inductive InputLife {B : Type} (empty : B) (offer : Nat → B → ByteArray → B × Bool)
    (advance : B → Nat → B) (pending : B → ByteArray) (cap : Nat) :
    ByteArray → ByteArray → B → Prop where
  /-- The queue every session starts with: nothing accepted, nothing written. -/
  | empty : InputLife empty offer advance pending cap .empty .empty empty
  /-- An offer: its frame joins the accepted input unless the queue refused it. -/
  |
  offer (accepted written : ByteArray) (b : B) (more : ByteArray) :
    InputLife empty offer advance pending cap accepted written b →
      InputLife empty offer advance pending cap
        (if (offer cap b more).2 then accepted else accepted ++ more) written (offer cap b more).1
  /-- A flush of `n` bytes. -/
  |
  advance (accepted written : ByteArray) (b : B) (n : Nat) :
    InputLife empty offer advance pending cap accepted written b →
      InputLife empty offer advance pending cap accepted (written ++ (pending b).extract 0 n)
        (advance b n)

end Linger.Session.Buf

/-! ## Claiming a session's resources

A resource identifies a stable lock inode, not a pathname string. The operating system decides which
attempts to take a lock succeed (`grant`), and the world claim `Exclusive`
(`Linger.Session.WorldSpec`) says that it grants only a free lock. A failed attempt leaves the state
unchanged, so a starting daemon that retries a held lock for a short time takes only `unchanged`
steps until it acquires. A daemon or offline reader enters when linger's decision `enters`, given
which of the lease's two locks it holds, lets it, and releases a lock only after leaving and
completing its cleanup.

The model permits acquisition, release and later reuse by different processes. The runtime
takes each lock with `flock` and asks the decision before it acts; that correspondence is tested
and source-gated, not proved. -/

namespace Linger.Session.Claim

/-- The socket and checkpoint resources a daemon or offline reader claims together. -/
structure Lease where
  /-- The socket's lock inode. -/
  socket : Nat
  /-- The checkpoint's lock inode. -/
  checkpoint : Nat
  deriving DecidableEq

/-- `resource` is the lease's socket or checkpoint resource. -/
@[expose]
def Lease.Uses (lease : Lease) (resource : Nat) : Prop :=
  resource = lease.socket ∨ resource = lease.checkpoint

/-- `locks` maps each resource to the actor holding its lock; `active` maps each actor to
the lease it has entered. -/
structure State where
  /-- The actor holding each resource's lock. -/
  locks : Nat → Option Nat
  /-- The lease each actor has entered. -/
  active : Nat → Option Lease

/-- No lock is held and no actor has entered. -/
@[expose]
def initial : State := ⟨fun _ => none, fun _ => none⟩

/-- `map` updated at `key` to `value`. -/
@[expose]
def put {α : Type} (map : Nat → α) (key : Nat) (value : α) : Nat → α := fun index =>
  if index = key then value else map index

/-- One step of any process, given which lock attempts the operating system grants (`grant`) and
linger's decision to enter a lease from whether the process holds its socket and its checkpoint
lock (`enters`). `enter` covers both daemon ownership and an offline reader's critical section.
`leave` means all resource access and cleanup have finished. -/
inductive Step (grant : State → Nat → Nat → Bool) (enters : Bool → Bool → Bool) :
    State → State → Prop where
  /-- The operating system grants an actor a resource's lock. -/
  |
  acquire (s : State) (actor resource : Nat) (granted : grant s actor resource = true) :
    Step grant enters s { s with locks := put s.locks resource (some actor) }
  /-- An idle actor enters a lease when linger decides it may. -/
  |
  enter (s : State) (actor : Nat) (lease : Lease) (idle : s.active actor = none)
    (decided :
      enters (s.locks lease.socket == some actor) (s.locks lease.checkpoint == some actor) = true) :
    Step grant enters s { s with active := put s.active actor (some lease) }
  /-- An actor leaves its lease after finishing all access and cleanup. -/
  |
  leave (s : State) (actor : Nat) : Step grant enters s { s with active := put s.active actor none }
  /-- An idle actor releases a lock it holds. -/
  |
  release (s : State) (actor resource : Nat) (owned : s.locks resource = some actor)
    (idle : s.active actor = none) :
    Step grant enters s { s with locks := put s.locks resource none }
  /-- A failed acquisition, or any step that changes nothing. -/
  | unchanged (s : State) : Step grant enters s s

/-- The states reached from `initial` by finitely many `Step`s. -/
inductive Reachable (grant : State → Nat → Nat → Bool) (enters : Bool → Bool → Bool) :
    State → Prop where
  /-- The start: nothing held, nobody active. -/
  | initial : Reachable grant enters initial
  /-- One more step from a reachable state. -/
  |
  next {before after} (reached : Reachable grant enters before)
    (step : Step grant enters before after) : Reachable grant enters after

end Linger.Session.Claim

namespace Linger.Session.Names

/-! ## Names and IDs

A session's ID is fixed when the session is created: it keys the session's socket, checkpoint,
end record and locks, and it is the `LINGER_SESSION` its program sees. Its name is a handle that
leads to its ID, which `rename` changes. A session created under a name that is no session's ID
takes that name for its ID, as every session did before names could change, so the files an
older linger keyed by name keep the meaning they had; a name whose ID a renamed session holds
gets a fresh ID, a dot and hexadecimal digits, which no name can be. The names table holds an
entry for each session whose name is not its ID: the name, and the ID it leads to. Any other
valid name leads to the ID that is that name, unless an entry leads to that ID, which a rename
then gave another name. -/

/-- The names table: each entry a name and the ID it leads to. -/
abbrev Table : Type := List (String × String)

/-- A lowercase hexadecimal digit. -/
@[expose]
def hexDigit (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- A fresh ID: a dot, then one or more lowercase hexadecimal digits. No name begins with a dot
(`Target.Name.Valid`), so no fresh ID is a name. -/
@[expose]
def Fresh (id : String) : Prop :=
  ∃ digits : List Char, id.toList = '.' :: digits ∧ digits ≠ [] ∧ ∀ c ∈ digits, hexDigit c = true

/-- A table the names directory can hold, and linger keeps: each name at most once, as a
directory holds it, and each ID at most once. -/
@[expose]
def Wf (t : Table) : Prop := (t.map (·.1)).Nodup ∧ (t.map (·.2)).Nodup

/-- What places a name in the names directory: a start that must give a session a fresh ID
creates its entry, as a rename of a session whose name is its ID does (`create`), and a rename of
a session with an entry moves that entry (`move`). -/
inductive Op where
  /-- Create an entry, from a temporary file that holds the ID. -/
  | create
  /-- Move an entry to the new name. -/
  | move
  deriving DecidableEq, Repr

/-- How a name is placed on disk: a link (`Os.Shell.linkNew`), a rename that may not replace
(`Os.Shell.renameNew`), or a rename that replaces, as rename(2) does. -/
inductive Call where
  /-- link(2), which never replaces a name. -/
  | link
  /-- A rename that may not replace a name. -/
  | renameNew
  /-- rename(2), which replaces whatever the new name named. -/
  | replace
  deriving DecidableEq, Repr

/-- What a call leaves of the names of a directory, which named `names`, when the operating
system places names as `placed` says (`Os.Place.NoReplace`); `none` when it fails. A rename that
replaces makes `dst` name `src`'s file whatever `dst` named. -/
@[expose]
def Call.run
    (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)) :
    Call → (String → Option Nat) → String → String → Option (String → Option Nat)
  | .link, names, src, dst => placed false names src dst
  | .renameNew, names, src, dst => placed true names src dst
  | .replace, names, src, dst =>
    some fun p => if p = dst then names src else if p = src then none else names p

/-- A wrong rename: it gives the session its new name for its ID too, so the ID changes. -/
@[expose]
def renameReid (t : Table) (old new _id : String) : Table :=
  (new, new) :: t.filter (fun e => e.1 != old)

/-- A wrong start: it takes the name for the new session's ID even when a renamed session holds
that ID, so two sessions would share it. -/
@[expose]
def claimSelf (t : Table) (name _id : String) : Table := (name, name) :: t

/-- A wrong resolution: the entry for the name, else the ID that is the name, even when a rename
gave that ID's session another name, so the old name still reaches it. -/
@[expose]
def resolveStale (t : Table) (name : String) : Option String :=
  (t.lookup name).orElse fun _ => some name

/-- A wrong reverse lookup: every ID shows as itself. -/
@[expose]
def nameOfBare (_t : Table) (id : String) : Option String := some id

end Linger.Session.Names

namespace Linger.Session.Names.Rename

/-- Why `rename` refuses. -/
inductive Refusal where
  /-- The new name is not a valid name. -/
  | invalid
  /-- No live or saved session has the old name. -/
  | missing
  /-- A live or saved session has the new name, an ended one still listed included. -/
  | taken
  /-- The session's daemon was started by an older linger, which keeps no name but its ID. -/
  | older
  deriving DecidableEq, Repr

/-- What `rename` does with a name. -/
inductive Plan where
  /-- Refuse, saying why, and change nothing. -/
  | refuse (why : Refusal)
  /-- Give the session the new name. -/
  | move
  deriving DecidableEq, Repr

end Linger.Session.Names.Rename
