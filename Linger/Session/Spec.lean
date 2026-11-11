module

public import Linger.Terminal.Spec
import SoftwareChallenge.Commands

public section

/-! # What session headlines are stated in

The values a session exchanges with its clients and its runtime (messages, client records,
events and effects, and the end record a name keeps), the caps its state keeps, the contract on
the effect interpreter, and predicates over the session's operations, which they take as
parameters: which messages fit a frame and what a decoder reads from a chunked stream, the
bounds a state keeps, the reachable states of the daemon's byte queues, and a model of how
daemons and offline readers claim a session's resources. Bodies are exposed: each definition
here is its own specification. -/

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

/-- What a daemon last saw of its program's output: whether output is fresh (`⣷`), and whether
some arrived since the session was last looked at (`⣿`), as `info` reports `fresh` and
`unseen`. -/
structure Seen where
  /-- Output within the freshness window. -/
  fresh : Bool
  /-- Output since the session was last looked at. -/
  unseen : Bool
  deriving Repr, DecidableEq

/-- What a name's end record says. -/
inductive Record where
  /-- A session took the name, and its program had not ended when this was written; with
  `seen`, what its daemon then saw of the output. -/
  | running (seen : Option Seen)
  /-- The program of the session that last held the name ended this way. -/
  | ended (outcome : Outcome)
  deriving Repr, DecidableEq

end Linger.Session

namespace Linger.Session.Start

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

namespace Linger.Session.Wire

/-- The protocol level a daemon speaks, which `info` reports as `protocol`, so a client can
refuse a request an older daemon cannot serve before sending it. Level 1 refuses a message it
does not know; level 2 also says how a program ended (`Msg.ended`). A daemon that reports no
level predates the field and drops an unknown message silently. -/
@[expose]
def protocol : Nat := 2

/-- Largest payload a frame may carry. Reads from the OS are ≤ 64 KiB, so honest senders stay
far below; a frame claiming more is either corruption or an attack, and the decoder turns it
into a connection error rather than memory growth. -/
@[expose]
def maxPayload : Nat := 262144

/-- The message vocabulary. Payload-carrying constructors keep raw
bytes; numeric fields are encoded LE at the payload layer. `unknown`
makes the decoder total (§Frame): a tag from a newer peer is data. -/
inductive Msg where
  /-- client → daemon: bytes for the pty (keystrokes, pastes). -/
  | input (bytes : List UInt8)
  /-- daemon → client: bytes from the pty (also used for history/restore). -/
  | output (bytes : List UInt8)
  /-- client → daemon: my terminal is now cols×rows. -/
  | resize (cols rows : UInt32)
  /-- client → daemon: I am a live client; stream output to me. -/
  | attach (cols rows : UInt32)
  /-- client → daemon: disconnect every attached client (incl. me). -/
  | detachAll
  /-- client → daemon: terminate the session. -/
  | kill
  /-- client → daemon: describe yourself (one-shot). -/
  | info
  /-- daemon → client: `k\tv\n` lines (fields + labels). -/
  | infoReply (bytes : List UInt8)
  /-- client → daemon: send scrollback and the screen as output frames, then `done`. -/
  | history
  /-- daemon → client: the session ended, with the status a shell would report for its
  program (`Outcome.status`). -/
  | exited (status : UInt32)
  /-- client → daemon: hold this connection open until the child exits. -/
  | wait
  /-- client → daemon: set one `k=v` label. -/
  | labelSet (kv : List UInt8)
  /-- client → daemon: remove one label by key. -/
  | labelUnset (k : List UInt8)
  /-- client → daemon: remove all labels. -/
  | labelClear
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
  /-- any tag this version does not know: skipped, never fatal (§Frame). -/
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
carries a tag this version leaves unassigned, so that it cannot read back as a known one. -/
@[expose]
def Msg.Fits : Msg → Prop
  | .input bytes | .output bytes | .infoReply bytes | .labelSet bytes | .labelUnset bytes |
    .err bytes => bytes.length ≤ maxPayload
  | .unknown tag payload => payload.length ≤ maxPayload ∧ 17 < tag.toNat
  | _ => True

/-- A request to change a session's labels: set one, remove one, or remove them all. -/
@[expose]
def Msg.ChangesLabels : Msg → Prop
  | .labelSet _ | .labelUnset _ | .labelClear => True
  | _ => False

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

/-- Most labels a session holds: setting one more is refused, and booting keeps only the
first this many restored labels. -/
@[expose]
def maxLabels : Nat := 64

/-- One connection's record: its identity, terminal size, attach and request state, and
its undecoded input. -/
structure Client where
  /-- The connection's identifier, as in `Event.connected`. -/
  id : Nat
  /-- Terminal width from the latest attach or resize message. -/
  cols : UInt32 := 80
  /-- Terminal height from the latest attach or resize message. -/
  rows : UInt32 := 24
  /-- The connection attached and receives the session's output. -/
  attached : Bool := false
  /-- attached with a real size (read-only observers attach 0×0 and
  never influence the pty size). -/
  sizer : Bool := false
  /-- attach order; the highest attached sizer owns the size. -/
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
  /-- A poll round ended; `nowMs` is the monotonic clock in milliseconds. -/
  | tick (nowMs : Nat)
  /-- The last `.checkpoint` effect failed to save. -/
  | checkpointFailed
  deriving Repr

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
  /-- Ask the program to end: SIGHUP to it and to every process of its terminal session. -/
  | killChild
  /-- Save a checkpoint of the session. -/
  | checkpoint
  /-- Delete the session's checkpoint. -/
  | dropCheckpoint
  /-- Stop the daemon; no later event is handled. -/
  | exit
  deriving Repr, DecidableEq

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

/-- The session after a trace of events, given its transition: each event starts from the state
the previous one left, and the effects come out in the order the events asked for them. -/
@[expose]
def trace {S E F : Type} (step : S → E → S × List F) (s : S) : List E → S × List F
  | [] => (s, [])
  | ev :: evs =>
    let r := step s ev
    let rest := trace step r.1 evs
    (rest.1, r.2 ++ rest.2)

/-- The session bounds, read through a state's client roster, labels and pty scanner: the
roster and the label store within their caps, every client's frame decoder healthy and
holding at most one frame, and the scanner within its caps. -/
structure Bounds {S : Type} (roster : S → List Client) (labels : S → List (String × String))
    (scanner : S → Terminal.Mediation.Scan) (s : S) : Prop where
  /-- At most `maxClients` clients. -/
  clientsLe : (roster s).length ≤ maxClients
  /-- At most `maxLabels` labels. -/
  labelsLe : (labels s).length ≤ maxLabels
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

/-- The file system keeps what linger saves as a name's end record whole: once linger saved
`bytes`, writing them to a temporary file and renaming that over the record, a reader reads
exactly `bytes` until linger saves or removes the record again. A reader that sees part of a
record, an older one, or a mix of two falsifies it. -/
WorldClaim Record.Kept (afterSave : List UInt8 → Option (List UInt8)) :=
  ∀ bytes, afterSave bytes = some bytes

/-- The kernel passes the bytes linger writes to a session's pty to its program, in order, as
it passes a terminal's input: `reads written` is what the program reads, in raw mode, once
linger wrote `written`. A byte lost, added or moved on the way falsifies it. -/
WorldClaim Pty.Delivers (reads : ByteArray → ByteArray) := ∀ written, reads written = written

/-- Why a program could not start in a new terminal, with the operating system's words. -/
inductive Spawn.Failure where
  /-- Its directory could not be entered. -/
  | directory (why : String)
  /-- No program of its name was found. -/
  | notFound (why : String)
  /-- Its program was found and could not be run. -/
  | notRunnable (why : String)
  deriving Repr, DecidableEq

/-- What a program sees of its start: its words, the directory it runs in, and each environment
variable's value, `none` for a variable that is unset. -/
structure Spawn.Started where
  /-- Its words, its program's name first. -/
  argv : List String
  /-- The directory it runs in. -/
  dir : String
  /-- Each environment variable's value. -/
  env : String → Option String

/-- The operating system runs what linger asks, and nothing else. A program that `start dir prog
args extra` starts sees the words `prog` and then `args`, runs in `dir`, and reads each variable
as the last pair of `extra` that sets it, or else as `inherited` has it: the environment of the
command that asked for the session, which its daemon runs with. A program that cannot start is
`none`. A started program that sees other words, another directory or another value falsifies
it. -/
WorldClaim Spawn.Runs (inherited : String → Option String)
  (start : String → String → Array String → List (String × String) → Option Spawn.Started) :=
  ∀ dir prog args extra started,
    start dir prog args extra = some started →
      started.argv = prog :: args.toList ∧
        started.dir = dir ∧
        ∀ key, started.env key = (extra.reverse.lookup key).orElse fun _ => inherited key

/-- SIGKILL ends every process it reaches within a second. `after sig ms alive` is what still
runs of the processes `alive` once linger sent them signal `sig` and waited `ms` milliseconds:
the processes of the program's terminal session that run as linger's user, which are all a
signal reaches. A signal ends some of them, all or none, and brings none back; SIGKILL ends them
all once linger waited a second. A process that outlives that wait, as one stuck in the kernel
does, falsifies it. A process that left the session with `setsid`, or runs as another user, is
not one of `alive`; on macOS, and on Linux before 5.3, a pid freed and reused between reading
its session and signalling it could receive the signal. -/
WorldClaim Signal.Ends (after : UInt32 → Nat → List Nat → List Nat) :=
  (∀ sig ms alive, ∀ p ∈ after sig ms alive, p ∈ alive) ∧
    ∀ ms alive, 1000 ≤ ms → after 9 ms alive = []

/-- poll(2) sleeps until an event or its timeout. `returns timeout` is when a poll with that
timeout, whose descriptors stay quiet, returns: after `timeout` milliseconds for a timeout from 0
to the largest `Int32`, and never for -1. A quiet poll that returns early, or that a timeout of
-1 lets return, falsifies it; so would a signal that interrupts it, but the only signal a daemon
handles, SIGCHLD, also makes its child-end descriptor ready. -/
WorldClaim Poll.Sleeps (returns : Int32 → Option Nat) :=
  returns (-1) = none ∧ ∀ ms ≤ 2147483647, returns (Int32.ofNat ms) = some ms

/-- A receiver that has parsed the repaint of a terminal a session can hold, taken between
control sequences and characters, keeps showing what the terminal shows as the same output
then reaches both: after any output, every row agrees. A repaint taken inside a control
sequence or a character is outside it: the receiver would read the sequence's rest as text. -/
Conjecture KeepsShowing {V P : Type} (live : V → Prop) (feed : V → List UInt8 → V)
  (colCount rowCount : V → Nat) (getRow : V → Nat → Terminal.Vt.Row) (atBoundary : V → Bool)
  (start : V → P) (next : Nat → P → Option (Terminal.Render.Bytes × P)) :=
  ∀ (budget : Nat) (v w : V) (later : List UInt8),
    0 < budget →
      live v →
      live w →
      colCount w = colCount v →
      rowCount w = rowCount v →
      atBoundary v = true →
      ∃ bytes,
        Terminal.Replay.Emits next budget (start v) bytes ∧
          ∀ y < rowCount (feed v later),
            getRow (feed (feed w bytes) later) y = getRow (feed v later) y

end Linger.Session

namespace Linger.Session.Driver

/-- A transport operation reports whether its target disconnected; a checkpoint
reports whether saving failed. Other effects cannot enqueue feedback. -/
abbrev Reply {Plan : Type} : Effect Plan → Type
  | .send .. | .replay .. | .close .. | .checkpoint => Bool
  | _ => Unit

/-- The reply of an effect that succeeded: its target stayed connected, or the checkpoint was
saved. -/
@[expose]
def success {Plan : Type} : (eff : Effect Plan) → Reply eff
  | .send .. | .replay .. | .close .. | .checkpoint => false
  | .writePty .. | .resizePty .. | .killChild | .dropCheckpoint | .exit => ()

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

/-- The external contract excludes unreported exceptions; it permits every
disconnect/checkpoint-failure result. This is a premise about primitive
execution, not an assumption that the event driver succeeds. A primitive that raises
instead of returning a result falsifies it. -/
WorldClaim Responds {S World Plan ε : Type}
  (execute : S → World → (eff : Effect Plan) → Except ε (World × Reply eff)) :=
  ∀ st world eff, ∃ answer, execute st world eff = .ok answer

end Linger.Session.Driver

namespace Linger.Session.Checkpoint

/-- What a checkpoint holds, given the terminal type: the terminal, the working directory and
the labels. It derives no `Inhabited`: a default terminal is a choice, not a state the
emulator reaches. -/
structure Ckpt (V : Type) where
  /-- The terminal state; its parser state is not saved. -/
  vt : V
  /-- The directory the restored session's child starts in. -/
  cwd : String
  /-- The session's labels, as key/value pairs. -/
  labels : List (String × String)

/-- `v` is the terminal of a checkpoint `load` returns for some bytes: a terminal a resumed
session can start from. -/
@[expose]
def Decoded {V : Type} (load : ByteArray → Option (Ckpt V)) (v : V) : Prop :=
  ∃ bytes c, load bytes = some c ∧ c.vt = v

end Linger.Session.Checkpoint

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

A resource identifies a stable lock inode, not a pathname string. The operating system decides
which attempts to take a lock succeed (`grant`), and `Exclusive` claims that it grants only a free
lock. A failed attempt leaves the state unchanged, so a starting daemon that retries a held lock
for a short time takes only `unchanged` steps until it acquires. A daemon or offline reader
enters when linger's decision `enters`, given which of the lease's two locks it holds, lets it,
and releases a lock only after leaving and completing its cleanup.

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

/-- The operating system grants a lock only when no process holds it, as `flock` does on a lock
file that is never unlinked or replaced. Two processes holding one lock file's lock at once
falsify it. -/
WorldClaim Exclusive (grant : State → Nat → Nat → Bool) :=
  ∀ s actor resource, grant s actor resource = true → s.locks resource = none

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
