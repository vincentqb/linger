module

public import Linger.Os.CoreSpec
public import Linger.Session.CoreSpec
public import Linger.Display.CoreSpec
public import ExactJSON.Value

public section

/-! # What command-line headlines are stated in

The executor a command line reaches and where each command line goes, the operations of the
session model and one row of the command table, an operation's one command, what a command
does with a name's saved session and what an attach to it does, what `wait` hears on each look
at a name and does next, what `kill` hears on each look at a name once a daemon has taken its
request and does next, and the steps of `capture` of a saved session, which of them hold the
name's locks and which wait on a party outside linger, and what a daemon's `info` answer says
that decides whether an attach hands the daemon over to the attaching binary. What a command
answers is the operating system's vocabulary, `Linger.Os.Answer`, which the selector answers in
too. -/

namespace Linger.App.Entry

/-- The executor that receives a command line: the interactive selector or the session CLI. -/
inductive Route where
  /-- `attach` without a target: open the selector, read-only on request. -/
  | selector (readOnly : Bool)
  /-- Every other command line, with its exact arguments; an empty one becomes `--help`. -/
  | session (args : List String)
  deriving BEq, Repr

/-- Where a command line goes: bare invocation explains the CLI, as `--help` does, `attach` alone
opens the selector, read-only on request, and every other command line reaches the session CLI
with its exact words. -/
@[expose]
def Route.of (args : List String) : Route :=
  if args = [] then .session ["--help"]
  else
    if args = ["attach"] then .selector false
    else if args = ["attach", "--read-only"] then .selector true else .session args

end Linger.App.Entry

namespace Linger.App.Commands

/-- The operations of the session model, each with the meaning it has for a session, in the order
help lists them. A command exists only for an `Op`, and each `Op` has exactly one command, spelled
one way: adding a command adds an `Op` here, which changes what linger claims. -/
inductive Op where
  /-- Connect this terminal to a session, starting one under the name when there is none, and
  resuming the latest tmux-resurrect save's pane of that name when no record names it, or choose
  one when no name is given; read-only on request. -/
  | attach
  /-- Report sessions: every local one, with the panes of the latest tmux-resurrect save no
  record names, the named ones, the remote hosts' too, the attention counts, or the names and
  directories as a tmux-resurrect save. -/
  | list
  /-- Start a program, exactly as named, in a new session. -/
  | start
  /-- Run a saved or ended session's program again, from its saved screen and directory, or a
  shell from a saved tmux pane's. -/
  | resume
  /-- Deliver bytes to a session's program as its input. -/
  | send
  /-- Disconnect every client attached to a session; the session runs on. -/
  | detach
  /-- End a session, discard a saved or ended one, or hide a saved tmux pane for good. -/
  | kill
  /-- Give a session a new name; its ID, and so everything else of it, stays. -/
  | rename
  /-- Read a session's screen, or its history. -/
  | capture
  /-- Set the terminal size of a session no client is attached to. -/
  | resize
  /-- Wait for sessions' programs to end, and answer how they ended. -/
  | wait
  /-- Carry live sessions over to this linger's image, their programs running on. -/
  | upgrade
  /-- Answer the operations above, one JSON-RPC 2.0 request each, on standard input and output,
  for a client that runs linger as a child with pipes (`Serve.methods`). -/
  | serve
  deriving Repr, DecidableEq

/-- Every operation, once each, in the order of its constructors. -/
@[expose]
def Op.all : List Op :=
  [.attach, .list, .start, .resume, .send, .detach, .kill, .rename, .capture, .resize, .wait,
    .upgrade, .serve]

/-- One row of the command table: the one command of an operation. -/
structure Command where
  /-- The word that names the command, its only spelling. -/
  word : String
  /-- The operation it performs. -/
  op : Op
  /-- The arguments it takes, as help and its usage error show them. -/
  args : String
  /-- What it does, in a few words. -/
  summary : String
  deriving Repr, DecidableEq

/-- The command table before commands were one to one with operations, a wrong part: each of a
command's spellings its own row, and `info` and `get` readers of what `ls` reports. Every
operation has a command in it, but some have several. -/
@[expose]
def aliased : List Command :=
  [("attach", .attach), ("a", .attach), ("ls", .list), ("list", .list), ("l", .list),
        ("start", .start), ("resume", .resume), ("send", .send), ("s", .send), ("detach", .detach),
        ("d", .detach), ("kill", .kill), ("k", .kill), ("info", .list), ("i", .list),
        ("capture", .capture), ("c", .capture), ("resize", .resize), ("wait", .wait), ("w", .wait),
        ("get", .list), ("g", .list), ("rename", .rename), ("upgrade", .upgrade)].map
    fun (word, op) => { word, op, args := "", summary := "" }

end Linger.App.Commands

namespace Linger.App.Fields

/-- What a field is to its reader: shown in a human row as clean text, or exact, a machine's,
which only `--porcelain` gives and no human row shows. -/
inductive Kind where
  /-- Shown in human rows, as clean text. -/
  | human
  /-- Exact: an ID, a process, a path, a protocol or a format, for porcelain readers alone. -/
  | machine
  deriving DecidableEq, Repr

/-- Who writes a field, its one owner: the user, through the one command of this operation; the
session's program, through what it writes to its terminal; or linger, from what it observes and
keeps. Only a field the user owns has a command that writes it. -/
inductive Owner where
  /-- The user, through the one command of this operation. -/
  | user (op : Commands.Op)
  /-- The session's program, its shell included. -/
  | program
  /-- linger, from what it observes and keeps. -/
  | linger
  deriving DecidableEq, Repr

/-- A field of a session's record, as listings report it: its key, its kind, its owner, and its
role, what it tells, which no other field of the same owner tells. -/
structure Field where
  /-- The key listings report it under. -/
  key : String
  /-- Whether human rows show it. -/
  kind : Kind
  /-- Who writes it. -/
  owner : Owner
  /-- What it tells. -/
  role : String
  deriving DecidableEq, Repr

/-- Whether a table gives the field of this key this owner. -/
@[expose]
def owns (table : List Field) (owner : Owner) (key : String) : Bool :=
  table.any fun f => f.key == key && f.owner == owner

/-- A wrong table: today's before names said what a session is, the name and the description
both the user's, and both what the user calls the session. The headline that each owner's fields
have one role each is shown to reject it. -/
@[expose]
def namedTwice : List Field :=
  [{ key := "name", kind := .human, owner := .user .rename,
     role := "what the user calls the session" },
    { key := "description", kind := .human, owner := .user .rename,
      role := "what the user calls the session" }]

end Linger.App.Fields

namespace Linger.App

/-- What a command does with a name no live session holds, from what the name's checkpoint
file holds, given what a checkpoint holds: start a new session, resume the saved one, or start
nothing, leave the file as it is and answer why. -/
inductive Recovery (C : Type) where
  /-- Start a new session under the name. -/
  | fresh
  /-- Resume the session this checkpoint saved. -/
  | resume (c : C)
  /-- Start nothing, leave the file as it is, and answer this. -/
  | refuse (answer : Os.Answer)
  deriving Repr, DecidableEq

end Linger.App

namespace Linger.App.Visit

/-- One step of an attach to a session its checkpoint saved, which an attach takes when no
daemon answers for the name. -/
inductive Step where
  /-- Run the session's program again from its saved screen, as `resume` does. -/
  | resume
  /-- Show the saved screen until the viewer leaves with the detach key. A viewer a signal
  interrupts may not have shown it, and takes no later step. -/
  | show
  /-- Tell the viewer how the session's program ended, and answer as its ending does. -/
  | tell (outcome : Linger.Session.Outcome)
  /-- Discard the session, as `kill` discards a saved one: delete its checkpoint, when it is
  still the one shown, and leave its end record, which `wait` and `ls` read. -/
  | discard
  deriving Repr, DecidableEq

end Linger.App.Visit

namespace Linger.App.Api

/-- What `ls` reports. -/
inductive View where
  /-- The attention counts, `--summary`. -/
  | summary
  /-- The local sessions' names and directories as a tmux-resurrect save, `--resurrect`. -/
  | resurrect
  /-- Every local session, with the panes of the latest tmux-resurrect save no record names, and
  with `-r` the remote hosts' too: those named, `some []` for the remotes file's, `none` for
  none; as records with `--porcelain`. -/
  | every (porcelain : Bool) (hosts : Option (List String))
  /-- The named sessions, in the order named; as records with `--porcelain`. -/
  | named (porcelain : Bool) (names : List String)
  deriving Repr, DecidableEq

/-- What `send` delivers to a session's program. -/
inductive Input where
  /-- These words, joined by spaces, as one input. -/
  | text (words : List String)
  /-- Standard input's bytes, exactly, as they arrive, until it ends: `-`. -/
  | stdin
  deriving Repr, DecidableEq

/-- What a command line asks for: its operation, with each of the operation's options and operands
one typed parameter. A target is an exact session name or `name@host`. -/
inductive Request where
  /-- `attach`: connect this terminal to the target, read-only on request, starting the session
  with this command, or the shell when it is empty, when none holds the name. -/
  | attach (readOnly : Bool) (target : String) (command : List String)
  /-- `ls`: report sessions. -/
  | list (view : View)
  /-- `start`: run `program` with `args`, exactly, in a new session under the target. -/
  | start (target program : String) (args : List String)
  /-- `resume`: run a saved or ended session's program again. -/
  | resume (target : String)
  /-- `send`: deliver input to the session's program. -/
  | send (target : String) (input : Input)
  /-- `detach`: disconnect every client attached to the session. -/
  | detach (target : String)
  /-- `kill`: end the session, or discard a saved one or a saved tmux pane. -/
  | kill (target : String)
  /-- `rename`: give the session the name `new`. -/
  | rename (target new : String)
  /-- `capture`: read the session's screen, or its history. -/
  | capture (history : Bool) (target : String)
  /-- `resize`: set the size of a session no client is attached to. -/
  | resize (target : String) (cols rows : Nat)
  /-- `wait`: wait for the sessions' programs to end. -/
  | wait (targets : List String)
  /-- `upgrade`: carry the live sessions named, or every local one when none is, over to this
  linger's image. -/
  | upgrade (targets : List String)
  /-- `serve`: answer the JSON-RPC requests standard input carries, one message a line, until it
  ends. -/
  | serve
  deriving Repr, DecidableEq

/-- The operation a request performs. -/
@[expose]
def Request.op : Request → Commands.Op
  | .attach .. => .attach
  | .list _ => .list
  | .start .. => .start
  | .resume _ => .resume
  | .send .. => .send
  | .detach _ => .detach
  | .kill _ => .kill
  | .rename .. => .rename
  | .capture .. => .capture
  | .resize .. => .resize
  | .wait _ => .wait
  | .upgrade _ => .upgrade
  | .serve => .serve

/-- What a request does to the sessions it names, as the session model reads it: the message it
sends each one's daemon, or the transition it takes. -/
inductive Act where
  /-- Connect as a client in this mode, `Wire.Msg.attach`, starting the session with this command
  when none holds the name. -/
  | attach (mode : Session.Mode) (command : List String)
  /-- Read the sessions' records, asking each live daemon `Wire.Msg.info`, as the view says. -/
  | list (view : View)
  /-- Start a new session running this program with these arguments, as `Start.plan` decides. -/
  | start (program : String) (args : List String)
  /-- Run a saved session's program again, as `Start.resumePlan` decides. -/
  | resume
  /-- Deliver these bytes to the program, in the input frames `Wire.inputFrames` cuts, which no
  reply answers. -/
  | deliver (bytes : List UInt8)
  /-- Deliver standard input's bytes as they arrive, in the same frames. -/
  | pipe
  /-- Send each named session's daemon this one request, and answer from its reply. -/
  | ask (request : Session.Wire.Msg)
  /-- Give the session this name, as `Names.Rename.plan` decides and `Names.rename` moves it. -/
  | rename (new : String)
  /-- Ask each named session's daemon to replace its image with this linger's,
  `Wire.Msg.upgrade`. -/
  | upgrade
  /-- Read JSON-RPC requests from standard input until it ends, and take each one's transition as
  its method's command line would (`Serve.words`), answering on standard output. -/
  | serve
  deriving Repr, DecidableEq

/-- **What each request means**: the transition its operation takes. -/
@[expose]
def Request.act : Request → Act
  | .attach readOnly _ command => .attach (if readOnly then .readOnly else .writable) command
  | .list view => .list view
  | .start _ program args => .start program args
  | .resume _ => .resume
  | .send _ (.text words) => .deliver (String.intercalate " " words).toUTF8.toList
  | .send _ .stdin => .pipe
  | .detach _ => .ask .detachAll
  | .kill _ => .ask .kill
  | .rename _ new => .rename new
  | .capture history _ => .ask (if history then .history else .screen)
  | .resize _ cols rows => .ask (.resize cols.toUInt32 rows.toUInt32)
  | .wait _ => .ask .wait
  | .upgrade _ => .upgrade
  | .serve => .serve

/-- A wrong part: a route on which `detach` takes `kill`'s transition, and every other request
its own. -/
@[expose]
def Request.crossed : Request → Act
  | .detach target => (Request.kill target).act
  | request => request.act

/-- What a command found, each the condition of the answer it gives (`Found.answer`). -/
inductive Found where
  /-- It did what was asked. -/
  | done
  /-- No session has the name it was given. -/
  | missing
  /-- It did not do what was asked, and says why: the daemon refused or went silent, the
  connection was lost, the session ended first, another process holds the name, or a session
  holds a name the request was to take. -/
  | refused
  /-- An operand is not one linger takes: a malformed target or name, or a size outside the
  emulator's. -/
  | invalid
  /-- Its deadline passed first, or the daemon it began did not answer in time, so nothing
  started. -/
  | late
  /-- linger failed, or could not find out what was asked. -/
  | unknown
  /-- The program it was to run did not start, and a shell or `env -C` reports this status for
  that: 125 for a directory it cannot enter, 126 for a program it cannot run, 127 for one it
  cannot find. -/
  | unstarted (status : UInt8)
  /-- The session it attached to or waited for ended this way. -/
  | ended (ending : Session.Ending)
  /-- What it ran exited with this status, as a shell reports it: the program of a session whose
  daemon, an older linger's, told no more. -/
  | status (status : UInt32)
  /-- What a remote linger answered, through its host's `serve`: its answer, as it gave it. -/
  | heard (answer : Os.Answer)
  /-- A signal stopped it, once it had handed its terminal back. -/
  | stopped (signal : UInt8)
  deriving Repr, DecidableEq

/-- **The answer true of what a command found**, whose code is its exit status. -/
@[expose]
def Found.answer : Found → Os.Answer
  | .done => .done
  | .missing => .notFound
  | .refused => .notDone
  | .invalid => .usage
  | .late => .timedOut
  | .unknown => .failed
  | .unstarted code => if code = 126 then .cannotRun else if code = 127 then .notFound else .failed
  | .ended ending => ending.answer
  | .status code => .program code
  | .heard answer => answer
  | .stopped signal => .stopped signal

/-- One thing a command says about its request as it goes, which the command line writes to
standard error and a Lean caller reads as it likes. -/
structure Said where
  /-- What it says. -/
  text : String
  /-- Whether it says it on a terminal it has just handed back, where it starts a line of its
  own. -/
  fresh : Bool := false
  deriving Repr, DecidableEq

end Linger.App.Api

namespace Linger.App.Commands

/-- **What each operation can find**, and so the answers it gives: every operation can find
that it did what was asked, refused, met an operand linger does not take, could not find out,
relayed the status an older daemon told, or heard what a remote linger answered; each other
finding belongs to the operations named. -/
@[expose]
def Op.finds : Op → Api.Found → Bool
  | _, .done | _, .refused | _, .invalid | _, .unknown | _, .status _ | _, .heard _ => true
  | op, .missing => op != .start && op != .serve
  | op, .late => op == .start || op == .resume || op == .wait
  | op, .unstarted _ => op == .attach || op == .start || op == .resume
  | op, .ended _ => op == .attach || op == .wait
  | op, .stopped _ => op == .attach || op == .list

end Linger.App.Commands

namespace Linger.App.Wait

/-- What one look at a name tells `wait`: its daemon's reply, or, with no daemon to answer, the
name's end record or that another process holds the name. -/
inductive Heard where
  /-- The daemon said how the session ended: how its program ended, or that a signal stopped the
  daemon, which saved the session. -/
  | ended (ending : Linger.Session.Ending)
  /-- A daemon from before `Wire.Msg.ended` gave only the status a shell would report. -/
  | status (status : UInt32)
  /-- The daemon said nothing before the time limit. -/
  | silent
  /-- The daemon refused, or answered without saying how the program ended. -/
  | refused
  /-- No daemon answered, and the name's end record says this, as `Record.answer` reads it:
  `none` when no session has taken the name. -/
  | recorded (answer : Option Linger.Session.Ending)
  /-- No daemon answered, and another process holds the name, as a daemon does while it starts
  or ends. -/
  | held
  deriving Repr, DecidableEq

/-- What `wait` does after a look: answer, or look again, keeping when it first found the name
held with no daemon answering, while it still finds it so. -/
inductive Next where
  /-- The wait is over, having found this. -/
  | answer (found : Api.Found)
  /-- Look again; `heldSince` is when the name was first found held, or `none` when it was not
  on this look. -/
  | again (heldSince : Option Nat)
  deriving Repr, DecidableEq

/-- The answer a wait gives after a look, if it is over. -/
@[expose]
def Next.told : Next → Option Os.Answer
  | .answer found => some found.answer
  | .again _ => none

end Linger.App.Wait

namespace Linger.App.Kill

/-- What one look at a name tells `kill` once the daemon it asked to end the session has taken the
request: who holds the name now. A daemon gives its name up only once its session has ended, and
another session can take the name only after that, so a name no process holds, or one a newer
session holds, means that the session `kill` asked to end has ended. -/
inductive Heard where
  /-- No process holds the name: the session `kill` asked to end gave it up. -/
  | free
  /-- The daemon `kill` asked still answers for the name as itself: its session has not ended. -/
  | asked
  /-- A daemon answers for the name that is not the one `kill` asked: a newer session took the
  name, after the session `kill` asked to end gave it up. -/
  | newer
  /-- A process holds the name that `kill` cannot tell from the daemon it asked: no daemon answers
  for the name, as while that daemon removes its socket and exits, while a newer one starts or
  while a reader holds the name, or `kill` could not learn which daemon it asked. -/
  | held
  deriving Repr, DecidableEq

/-- What `kill` does after a look: answer, or look again. -/
inductive Next where
  /-- The kill is over, having found this. -/
  | answer (found : Api.Found)
  /-- Look again. -/
  | again
  deriving Repr, DecidableEq

/-- The answer a kill gives after a look, if it is over. -/
@[expose]
def Next.told : Next → Option Os.Answer
  | .answer found => some found.answer
  | .again => none

/-- The rule before the one `kill` follows, a wrong part, with its patience `patience`: only a name
no process holds was an ending, so a newer session that took the name read as the session not
ended, and so did a process `kill` cannot tell from the daemon it asked, once `patience` had
passed since the daemon took the request at `taken`. -/
@[expose]
def byLock (patience taken now : Nat) : Heard → Next
  | .free => .answer .done
  | _ => if taken + patience ≤ now then .answer .refused else .again

end Linger.App.Kill

namespace Linger.App.Capture

/-- One step of `capture` of a saved session, which a command takes when no daemon answers for
the name. -/
inductive Step where
  /-- Take both of the name's locks, as every offline reader does: one attempt each. -/
  | acquire
  /-- Read the bytes of the name's checkpoint file. -/
  | load
  /-- Render what they decode to: the saved screen or history, or why there is none. -/
  | render
  /-- Let both locks go. -/
  | release
  /-- Write what it rendered: the session to standard output, or why there is none to standard
  error. -/
  | write
  deriving Repr, DecidableEq

/-- Whether a step can wait on a party outside linger, for as long as that party likes: a write
waits for whoever reads it, as a pager that is not reading or a pipe nobody reads makes it wait
for good. The other steps wait on no one outside linger: a lock is tried once, the checkpoint is
a file on the local disk, and rendering and letting go of the locks compute and close. -/
@[expose]
def Step.waitsOutside : Step → Bool
  | .write => true
  | .acquire | .load | .render | .release => false

/-- The steps of `plan` but those that take and let go of the name's locks, in order, each with
whether it runs holding them: from an `acquire` to the next `release`, given `held`, whether the
plan holds them when it begins. -/
@[expose]
def work : (plan : List Step) → (held : Bool) → List (Step × Bool)
  | [], _ => []
  | .acquire :: rest, _ => work rest true
  | .release :: rest, _ => work rest false
  | step :: rest, held => (step, held) :: work rest held

/-- What the shell does with a run of a plan's steps: run them holding the name's locks, taken
once before the first and let go after the last however they end, or run one step without them.
-/
inductive Phase where
  /-- Take both of the name's locks, run these steps in order, and let the locks go. -/
  | locked (steps : List Step)
  /-- Run this step holding no lock. -/
  | unlocked (step : Step)
  deriving Repr, DecidableEq

/-- The steps a phase runs, each with whether it runs holding the name's locks. -/
@[expose]
def Phase.work : Phase → List (Step × Bool)
  | .locked steps => steps.map (·, true)
  | .unlocked step => [(step, false)]

end Linger.App.Capture

namespace Linger.App.Serve

open ExactJSON (Value ToValue FromValue toValue)

/-- The value of a base64 digit, in RFC 4648's alphabet: `A`–`Z`, `a`–`z`, `0`–`9`, `+` and `/`. -/
@[expose]
def Base64.digit (c : Char) : Option Nat :=
  if 'A' ≤ c ∧ c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else
    if 'a' ≤ c ∧ c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
    else
      if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat + 52)
      else if c = '+' then some 62 else if c = '/' then some 63 else none

/-- The bytes padded base64 text encodes (RFC 4648, section 4): three bytes for each four digits,
and two or one for a last group padded with one or two `=`; none for any other text. -/
@[expose]
def Base64.decode : List Char → Option (List UInt8)
  | [] => some []
  | [a, b, '=', '='] => do
    let w ← digit a
    let x ← digit b
    pure [UInt8.ofNat (w * 4 + x / 16)]
  | [a, b, c, '='] => do
    let w ← digit a
    let x ← digit b
    let y ← digit c
    pure [UInt8.ofNat (w * 4 + x / 16), UInt8.ofNat (x % 16 * 16 + y / 4)]
  | a :: b :: c :: d :: rest => do
    let w ← digit a
    let x ← digit b
    let y ← digit c
    let z ← digit d
    let tail ← decode rest
    pure
        (UInt8.ofNat (w * 4 + x / 16) ::
          UInt8.ofNat (x % 16 * 16 + y / 4) :: UInt8.ofNat (y % 4 * 64 + z) :: tail)
  | _ => none

/-- The name an answer goes by, beside its code: its constructor's. -/
@[expose]
def answerName : Os.Answer → String
  | .done => "done"
  | .notDone => "notDone"
  | .usage => "usage"
  | .timedOut => "timedOut"
  | .failed => "failed"
  | .cannotRun => "cannotRun"
  | .notFound => "notFound"
  | .cancelled => "cancelled"
  | .stopped _ => "stopped"
  | .saved _ => "saved"
  | .program _ => "program"

/-- The shape of what a method answers, one of the four leanvim states its peers in (2026-11-22),
each what a reader can rely on whatever else a peer sends; the fourth, a life, is what methods
name: a session (`Life`). -/
inductive Shape where
  /-- An ask: one request, answered once, by its id. -/
  | ask
  /-- A table: a subscription, named by the id of the request that opened it, whose updates
  replace the record at a key, so that only the latest counts and a reader that sees only the
  last update loses nothing (`View.apply`). -/
  | table
  /-- A log: a subscription whose updates append, of which a reader keeps a bounded tail and a
  count of what it dropped (`Log`). -/
  | log
  deriving Repr, DecidableEq

/-- A life: a start, then an ending, after which asks of it fail and subscriptions to it close. A
session is one: `session/start`, or `session/resume` of a saved one, starts it, and
`session/wait` answers how it ended; after that `session/send`, `session/resize` and
`session/detach` refuse it, and the sessions table keeps its record, which says how it ended,
until `session/kill` discards it and its key goes. -/
inductive Life (ε : Type) where
  /-- Started, and not ended. -/
  | live
  /-- Ended, this way. -/
  | ended (ending : ε)

/-- The methods `serve` answers as operations, each with the operation whose request it is, the
word of that operation's command and its shape: every one is an ask but `sessions/subscribe`, a
table of the sessions' records, keyed by name, the watches of a session's terminal, which
attach to it read-only as `attach --read-only` does: `session/screen`, a table of its screen's
lines, keyed by number, with its cursor and title, and `session/history`, a log of the lines that
leave the top of its screen, and `session/attach`, which attaches to it as `attach` does, a log of
the bytes its daemon sends an attach client. -/
@[expose]
def methods : List (String × Commands.Op × String × Shape) :=
  [("sessions/list", .list, "ls", .ask), ("sessions/subscribe", .list, "ls", .table),
    ("session/screen", .attach, "attach", .table), ("session/history", .attach, "attach", .log),
    ("session/attach", .attach, "attach", .log), ("session/start", .start, "start", .ask),
    ("session/resume", .resume, "resume", .ask), ("session/send", .send, "send", .ask),
    ("session/detach", .detach, "detach", .ask), ("session/kill", .kill, "kill", .ask),
    ("session/rename", .rename, "rename", .ask), ("session/capture", .capture, "capture", .ask),
    ("session/resize", .resize, "resize", .ask), ("session/wait", .wait, "wait", .ask),
    ("session/upgrade", .upgrade, "upgrade", .ask)]

/-! ## JSON

Every value `serve` writes or reads is ExactJSON's (`Value`), and its text ExactJSON's canonical
text. A method's params, a result, a session's record and each update are typed values, whose JSON
is the object of their members by increasing key, each of its type, an optional member left out
when absent, as ExactJSON's derived codecs write them; this section states each such object. -/

/-- The member `key` of an object, the first under it, and none of any other value. -/
@[expose]
def member? (key : String) : Value → Option Value
  | .table members => members.toList.lookup key
  | _ => none

/-- Strings as a JSON array. -/
@[expose]
def strings (texts : List String) : Value := .array (texts.map Value.string).toArray

/-- A member `key` that is present with this value, and none when it is absent: an optional member
as JSON writes it. -/
@[expose]
def optional {α : Type} (key : String) (json : α → Value) (o : Option α) : List (String × Value) :=
  (o.map fun a => (key, json a)).toList

/-- The protocol versions `serve` speaks. -/
@[expose]
def versions : List String := ["1"]

/-- A request's id: an integer or a string. -/
inductive Id where
  /-- An integer. -/
  | number (value : Int)
  /-- A string. -/
  | str (text : String)
  deriving Repr, DecidableEq

/-- An id as JSON: an integer, or a string. -/
@[expose]
def Id.json : Id → Value
  | .number value => .integer value
  | .str text => .string text

/-- A JSON value as a request id: an integer or a string. -/
@[expose]
def Id.of : Value → Option Id
  | .integer value => some (.number value)
  | .string text => some (.str text)
  | _ => none

/-- **An id as JSON**: an integer as an integer and a string as a string. -/
instance : ToValue Id := ⟨Id.json⟩

/-- **An id read from JSON**: an integer or a string, and no other value. -/
instance : FromValue Id where
  fromValue? value :=
    match Id.of value with
    | some id => .ok id
    | none => .error "an id that is neither an integer nor a string"

/-! ## A method's params

Each method `methods` lists takes one typed value as its params (`Call`), and each of the
requests of an attach's conversation, `initialize` and `sessions/unsubscribe` its own: a member
the method does not define, a member of another type and `null` for a member left out are no params
of it, which `serve` refuses as invalid. -/

/-- The params of a method that takes none: `{}`. -/
structure NoParams where
  deriving DecidableEq, Repr

/-- The params of a method that names a session: its name. -/
structure Named where
  /-- The session's name. -/
  name : String
  deriving DecidableEq, Repr

/-- `sessions/list`'s params: the names it lists, every session when none. -/
structure Listed where
  /-- The names, in order. -/
  names? : Option (List String)
  deriving DecidableEq, Repr

/-- `session/attach`'s params: the session, the command a new session under the name runs, the
shell when none, and whether the attach is read-only. -/
structure Attaching where
  /-- The command's words. -/
  command? : Option (List String)
  /-- The session's name. -/
  name : String
  /-- Whether the attach is read-only. -/
  readOnly? : Option Bool
  deriving DecidableEq, Repr

/-- `session/start`'s params: the session's name, its program and the program's arguments. -/
structure Starting where
  /-- The program's arguments. -/
  args? : Option (List String)
  /-- The session's name. -/
  name : String
  /-- The program. -/
  program : String
  deriving DecidableEq, Repr

/-- `session/send`'s params: the bytes in base64, and the session. -/
structure Sending where
  /-- The bytes, in base64. -/
  data : String
  /-- The session's name. -/
  name : String
  deriving DecidableEq, Repr

/-- `session/rename`'s params: the session's name, and its new one. -/
structure Renaming where
  /-- The session's name. -/
  name : String
  /-- Its new name. -/
  new : String
  deriving DecidableEq, Repr

/-- `session/capture`'s params: whether with the history, and the session. -/
structure Capturing where
  /-- Whether the capture holds the history. -/
  history? : Option Bool
  /-- The session's name. -/
  name : String
  deriving DecidableEq, Repr

/-- `session/resize`'s params of a session by name: its columns, its name and its rows. -/
structure Resizing where
  /-- The columns. -/
  cols : Nat
  /-- The session's name. -/
  name : String
  /-- The rows. -/
  rows : Nat
  deriving DecidableEq, Repr

/-- The params that name a subscription: `sessions/unsubscribe`'s, and `session/detach`'s of an
attach. -/
structure Subscription where
  /-- The id of the request that opened the subscription. -/
  subscription : Id
  deriving DecidableEq, Repr

/-- `session/input`'s params: the keys in base64, and the attach they go to. -/
structure Keys where
  /-- The keys, in base64. -/
  data : String
  /-- The attach, by the id of the request that opened it. -/
  subscription : Id
  deriving DecidableEq, Repr

/-- `session/resize`'s params of an attach: its terminal's columns and rows, and the attach. -/
structure Sized where
  /-- The columns. -/
  cols : Nat
  /-- The rows. -/
  rows : Nat
  /-- The attach, by the id of the request that opened it. -/
  subscription : Id
  deriving DecidableEq, Repr

/-- Who a client or a server is: its name, and its version when it gives one. -/
structure Info where
  /-- The name. -/
  name : String
  /-- The version. -/
  version? : Option String
  deriving DecidableEq, Repr

/-- `initialize`'s params: what the client can do, none of which `serve` reads, who it is and the
protocol version it speaks. -/
structure Initialize where
  /-- What the client can do: `{}`. -/
  capabilities? : Option NoParams
  /-- Who the client is. -/
  clientInfo? : Option Info
  /-- The protocol version the client speaks. -/
  protocolVersion : String
  deriving DecidableEq, Repr

/-- `{}`. -/
@[expose]
def NoParams.json (_ : NoParams) : Value := .table #[]

/-- A name as params: `{"name"}`. -/
@[expose]
def Named.json (p : Named) : Value := .table #[("name", .string p.name)]

/-- `sessions/list`'s params as JSON. -/
@[expose]
def Listed.json (p : Listed) : Value := .table (optional "names" strings p.names?).toArray

/-- `session/attach`'s params as JSON. -/
@[expose]
def Attaching.json (p : Attaching) : Value :=
  .table
    (optional "command" strings p.command? ++ [("name", Value.string p.name)] ++
        optional "readOnly" Value.boolean p.readOnly?).toArray

/-- `session/start`'s params as JSON. -/
@[expose]
def Starting.json (p : Starting) : Value :=
  .table
    (optional "args" strings p.args? ++
        [("name", Value.string p.name), ("program", Value.string p.program)]).toArray

/-- `session/send`'s params as JSON. -/
@[expose]
def Sending.json (p : Sending) : Value :=
  .table #[("data", .string p.data), ("name", .string p.name)]

/-- `session/rename`'s params as JSON. -/
@[expose]
def Renaming.json (p : Renaming) : Value :=
  .table #[("name", .string p.name), ("new", .string p.new)]

/-- `session/capture`'s params as JSON. -/
@[expose]
def Capturing.json (p : Capturing) : Value :=
  .table (optional "history" Value.boolean p.history? ++ [("name", Value.string p.name)]).toArray

/-- `session/resize`'s params of a session by name as JSON. -/
@[expose]
def Resizing.json (p : Resizing) : Value :=
  .table #[("cols", .integer p.cols), ("name", .string p.name), ("rows", .integer p.rows)]

/-- The params that name a subscription as JSON. -/
@[expose]
def Subscription.json (p : Subscription) : Value := .table #[("subscription", p.subscription.json)]

/-- `session/input`'s params as JSON. -/
@[expose]
def Keys.json (p : Keys) : Value :=
  .table #[("data", .string p.data), ("subscription", p.subscription.json)]

/-- `session/resize`'s params of an attach as JSON. -/
@[expose]
def Sized.json (p : Sized) : Value :=
  .table
    #[("cols", .integer p.cols), ("rows", .integer p.rows), ("subscription", p.subscription.json)]

/-- Who a client or a server is, as JSON. -/
@[expose]
def Info.json (p : Info) : Value :=
  .table ([("name", Value.string p.name)] ++ optional "version" Value.string p.version?).toArray

/-- `initialize`'s params as JSON. -/
@[expose]
def Initialize.json (p : Initialize) : Value :=
  .table
    (optional "capabilities" NoParams.json p.capabilities? ++
        optional "clientInfo" Info.json p.clientInfo? ++
        [("protocolVersion", Value.string p.protocolVersion)]).toArray

/-- **A request of a method `methods` lists**: the method, as one constructor each, and its typed
params. -/
inductive Call where
  /-- `sessions/list`. -/
  | list (params : Listed)
  /-- `sessions/subscribe`. -/
  | subscribe (params : NoParams)
  /-- `session/screen`. -/
  | screen (params : Named)
  /-- `session/history`. -/
  | history (params : Named)
  /-- `session/attach`. -/
  | attach (params : Attaching)
  /-- `session/start`. -/
  | start (params : Starting)
  /-- `session/resume`. -/
  | resume (params : Named)
  /-- `session/send`. -/
  | send (params : Sending)
  /-- `session/detach` of a session by name. -/
  | detach (params : Named)
  /-- `session/kill`. -/
  | kill (params : Named)
  /-- `session/rename`. -/
  | rename (params : Renaming)
  /-- `session/capture`. -/
  | capture (params : Capturing)
  /-- `session/resize` of a session by name. -/
  | resize (params : Resizing)
  /-- `session/wait`. -/
  | wait (params : Named)
  /-- `session/upgrade`. -/
  | upgrade (params : Named)
  deriving DecidableEq, Repr

/-- A call's method. -/
@[expose]
def Call.method : Call → String
  | .list _ => "sessions/list"
  | .subscribe _ => "sessions/subscribe"
  | .screen _ => "session/screen"
  | .history _ => "session/history"
  | .attach _ => "session/attach"
  | .start _ => "session/start"
  | .resume _ => "session/resume"
  | .send _ => "session/send"
  | .detach _ => "session/detach"
  | .kill _ => "session/kill"
  | .rename _ => "session/rename"
  | .capture _ => "session/capture"
  | .resize _ => "session/resize"
  | .wait _ => "session/wait"
  | .upgrade _ => "session/upgrade"

/-- **A call's params as JSON**: its typed params' object. -/
@[expose]
def Call.params : Call → Value
  | .list p => p.json
  | .subscribe p => p.json
  | .screen p | .history p | .resume p | .detach p | .kill p | .wait p | .upgrade p => p.json
  | .attach p => p.json
  | .start p => p.json
  | .send p => p.json
  | .rename p => p.json
  | .capture p => p.json
  | .resize p => p.json

/-- The words of a call's command line after its command's: its options from its params and its
target last, after `--` where the command reads one, so that a name that starts with `-` stays a
name. `session/send` is `send NAME -`, whose standard input is `input`'s, a watch is
`attach --read-only -- NAME` and an attach `attach -- NAME`, read-only on request, its command after
the name. -/
@[expose]
def Call.operands : Call → List String
  | .list p => ["--porcelain", "--"] ++ p.names?.getD []
  | .subscribe _ => ["--porcelain"]
  | .screen p | .history p => ["--read-only", "--", p.name]
  | .attach p =>
    (if p.readOnly?.getD false then ["--read-only"] else []) ++ ["--", p.name] ++ p.command?.getD []
  | .start p => [p.name, p.program] ++ p.args?.getD []
  | .resume p | .detach p | .kill p | .wait p | .upgrade p => [p.name]
  | .send p => [p.name, "-"]
  | .rename p => [p.name, p.new]
  | .capture p => (if p.history?.getD false then ["--history"] else []) ++ ["--", p.name]
  | .resize p => [p.name, toString p.cols, toString p.rows]

/-- **The command line a call is**: its method's command word (`methods`), then its operands. -/
@[expose]
def Call.words (call : Call) : List String :=
  ((methods.lookup call.method).map fun (_, word, _) => word).getD "" :: call.operands

/-- The standard input a call's command line reads: the bytes `session/send`'s `data` encodes in
base64 (`Base64.decode`), none for text that is no base64, and nothing for any other method. -/
@[expose]
def Call.input : Call → Option (List UInt8)
  | .send p => Base64.decode p.data.toList
  | _ => some []

/-! ## The sessions table -/

/-- A record of the sessions table: a session's record, as `ls --porcelain` gives it. -/
abbrev Record : Type := Linger.Display.Listing.Record

/-- The key a record is kept under: its session's name. -/
@[expose]
def Record.key (record : Record) : String := Linger.Display.Listing.Record.key record

/-- A record as an update reads it: without the two fields that read the clock, `idle`, which
changes each second a session is quiet, and `lastout`, the wall clock less `idle`, which two
listings of a quiet session may read a second apart, since the two clocks tick apart. -/
@[expose]
def Record.reading (record : Record) : Record := (record.erase "idle").erase "lastout"

/-- **A record as JSON**: an object of its fields by increasing key, each as its kind writes it, as
ExactJSON writes a dictionary (`codec_extTreeMap`). -/
@[expose]
def Record.json (record : Record) : Value :=
  .table (record.toList.map fun (key, field) => (key, toValue field)).toArray

/-- The records of `latest` that `told` holds no record of under their key, or holds otherwise,
read without the clock (`Record.reading`). -/
@[expose]
def changes (told latest : List Record) : List Record :=
  latest.filter fun record =>
    (told.find? (·.key == record.key)).map Record.reading != some record.reading

/-- The keys of `told`'s records that `latest` holds no record under. -/
@[expose]
def removed (told latest : List Record) : List String :=
  (told.map Record.key).filter fun key => !latest.any (·.key == key)

/-- The params of `sessions/changed`: the records that replace those under their keys, the keys
that go, and the subscription it updates, by the id of the request that opened it. -/
structure Changed where
  /-- The records that replace those under their keys. -/
  records : List Record
  /-- The keys that go. -/
  removed : List String
  /-- The subscription, by the id of the request that opened it. -/
  subscription : Id

/-- `sessions/changed`'s params as JSON. -/
@[expose]
def Changed.json (c : Changed) : Value :=
  .table
    #[("records", .array (c.records.map Record.json).toArray), ("removed", strings c.removed),
      ("subscription", c.subscription.json)]

/-- **The params of `sessions/changed`**: the records that replace those under their keys, the
keys that go, and the subscription it updates, the request id that opened it. -/
@[expose]
def update (id : Id) (records : List Record) (gone : List String) : Value :=
  Changed.json { records, removed := gone, subscription := id }

/-- A table as a reader holds it, the record under each key: here the first of `records` under
it. -/
@[expose]
def View.of (records : List Record) (key : String) : Option Record := records.find? (·.key == key)

/-- A table after an update, as a reader applies one: none under a key it removes, and under any
other key its record, or else the one held before. -/
@[expose]
def View.apply (view : String → Option Record) (records : List Record) (gone : List String)
    (key : String) : Option Record :=
  if gone.contains key then none else (records.find? (·.key == key)).or (view key)

/-- A log as a reader keeps one: the last entries appended, at most its cap, and how many before
them it dropped. -/
structure Log (α : Type) where
  /-- The last entries, oldest first. -/
  tail : List α := []
  /-- How many entries before them were dropped. -/
  dropped : Nat := 0

/-- A wrong part: a log that keeps every entry, whatever its cap. -/
@[expose]
def Log.keepAll {α : Type} (_ : Nat) (log : Log α) (entry : α) : Log α :=
  { log with tail := log.tail ++ [entry] }

/-! ## A session's terminal as rows

A client with no terminal of its own follows a session's terminal as rows: the screen as a table
keyed by line number, with the cursor and the window title under keys of their own, and the lines
that leave the top of the screen as a log. A line is its text, exactly as `capture` prints the row,
and the runs of the pens its characters are drawn with, which run on past the text over blanks
drawn with a pen other than the default, so that a reader can draw a coloured bar that ends in
blanks. -/

/-- A run of a line's characters drawn with one pen: how many characters, and the pen. -/
structure Span where
  /-- How many characters the run covers. -/
  length : Nat
  /-- The pen they are drawn with. -/
  pen : Terminal.Vt.Pen
  deriving DecidableEq

/-- A line of a terminal as a reader holds it: its text, in UTF-8, and the runs of the pens its
characters are drawn with, in order. -/
structure Line where
  /-- The text, as `capture` prints the row: its characters, trailing blanks trimmed. -/
  text : List UInt8
  /-- The runs of its characters' pens (`Line.pens`). -/
  spans : List Span
  deriving DecidableEq

/-- The cursor as a reader holds it: its column and row, from 0, and whether it shows. -/
structure Cursor where
  /-- The column, from 0. -/
  x : Nat
  /-- The row, from 0. -/
  y : Nat
  /-- Whether it shows (DECTCEM). -/
  visible : Bool
  deriving DecidableEq

/-- A screen as a reader holds it: its lines, top first, keyed by their number, the cursor and the
window title. -/
structure Screen where
  /-- The lines, top first. -/
  lines : List Line
  /-- The cursor. -/
  cursor : Cursor
  /-- The window title, as clean text. -/
  title : String
  deriving DecidableEq

/-- A cell's characters, each with whether it is a blank and with the cell's pen: the character
it draws and each combining mark after it, and none for the shadow of a wide character, as
`capture` reads them. -/
@[expose]
def cellPens (c : Terminal.Vt.Cell) : List (Bool × Terminal.Vt.Pen) :=
  if c.width = 0 then []
  else (decide (c.base = ' '), c.pen) :: c.marks.map fun m => (decide (m = ' '), c.pen)

/-- **The pens a line's spans cover**: the pens of the row's characters, in order, up to the last
that is not a blank drawn with the default pen. -/
@[expose]
def Line.pens (row : Terminal.Vt.Row) : List Terminal.Vt.Pen :=
  ((row.toList.flatMap cellPens).reverse.dropWhile fun c => c.1 && c.2 == {}).reverse.map (·.2)

/-- The pens of runs, one per character, in order. -/
@[expose]
def Span.expand (spans : List Span) : List Terminal.Vt.Pen :=
  spans.flatMap fun s => List.replicate s.length s.pen

/-- Runs that are maximal: each covers a character, and no two in turn share a pen. -/
@[expose]
def Span.Compact (spans : List Span) : Prop :=
  (∀ s ∈ spans, 0 < s.length) ∧ ∀ pair ∈ spans.zip spans.tail, pair.1.pen ≠ pair.2.pen

/-- An update of a screen table: the lines that changed, each with its number, the numbers of the
lines that went, and the cursor and the title when they changed. -/
structure Screen.Update where
  /-- The lines that changed, each with its number. -/
  lines : List (Nat × Line)
  /-- The numbers of the lines that went. -/
  removed : List Nat
  /-- The cursor, when it changed. -/
  cursor : Option Cursor
  /-- The window title, when it changed. -/
  title : Option String
  deriving DecidableEq

/-- A screen's line under a number as a reader holds it after an update: none where the update
removes it, else the line the update carries under it, else the one held before. -/
@[expose]
def Screen.View.line (told : Screen) (u : Screen.Update) (y : Nat) : Option Line :=
  if y ∈ u.removed then none else (u.lines.lookup y).or told.lines[y]?

/-- **An update that is exact from `told` to `latest`**: it brings a reader holding `told` to
`latest`, under every line number and in its cursor and title, and carries exactly what changed:
each line whose number `told` holds otherwise or not at all, once, the numbers of the lines that
went, once each, and the cursor and the title only when they changed. -/
@[expose]
def Screen.Exact (told latest : Screen) (u : Screen.Update) : Prop :=
  (∀ y, Screen.View.line told u y = latest.lines[y]?) ∧
    u.cursor.getD told.cursor = latest.cursor ∧
    u.title.getD told.title = latest.title ∧
    (∀ y line, (y, line) ∈ u.lines ↔ latest.lines[y]? = some line ∧ told.lines[y]? ≠ some line) ∧
    (u.lines.map (·.1)).Nodup ∧
    (∀ y, y ∈ u.removed ↔ told.lines[y]?.isSome ∧ latest.lines[y]? = none) ∧
    u.removed.Nodup ∧
    u.cursor = (if told.cursor = latest.cursor then none else some latest.cursor) ∧
    u.title = (if told.title = latest.title then none else some latest.title)

/-- A wrong part: an update that carries every line of the latest screen, changed or not, and its
cursor and title. -/
@[expose]
def Screen.everyLine (_ latest : Screen) : Screen.Update :=
  { lines := latest.lines.zipIdx.map fun (line, y) => (y, line), removed := [],
    cursor := some latest.cursor, title := some latest.title }

/-- A wrong part: an update that carries only the first line that changed. -/
@[expose]
def Screen.firstChange (told latest : Screen) : Screen.Update :=
  {
    lines :=
      ((latest.lines.zipIdx.filter fun (line, y) => told.lines[y]? != some line).map
            fun (line, y) => (y, line)).take
        1,
    removed := [], cursor := if told.cursor = latest.cursor then none else some latest.cursor,
    title := if told.title = latest.title then none else some latest.title }

/-- A wrong part: a second renderer of a terminal's screen, of the rows `rows` reads from it, which
writes each cell's character as it is, keeping trailing blanks, and draws no pens. -/
@[expose]
def Screen.untrimmed {V : Type} (rows : V → List Terminal.Vt.Row) (v : V) : Screen :=
  {
    lines :=
      (rows v).map fun row =>
        { text := row.toList.flatMap fun c => String.utf8EncodeChar c.base, spans := [] },
    cursor := { x := 0, y := 0, visible := true }, title := "" }

/-- The size of the log a watch of a session's history keeps between two updates: the last this
many lines that left the screen, and a count of those before them. -/
@[expose]
def historyCap : Nat := 1000

/-- A log as a reader reads it: a gap for each entry dropped, then each entry kept, in order. -/
@[expose]
def Log.reads {α : Type} (log : Log α) : List (Option α) :=
  List.replicate log.dropped none ++ log.tail.map some

/-- **What a reader reads shows exactly the entries**, in order: one place for each, which holds
the entry or a gap where it was dropped. -/
@[expose]
def Log.Masks {α : Type} : List (Option α) → List (Option α) → Prop
  | [], [] => True
  | shown :: rest, entry :: entries => (shown = entry ∨ shown = none) ∧ Log.Masks rest entries
  | _, _ => False

/-- What a connection holds for a watch, a subscription to a session's terminal: asked for and not
answered yet, a screen's or a history's; open on a screen, which its subscriber was last told and
the latest look found; open on a history, with the lines that left the screen since the last
update, a bounded tail and a count of those it dropped; or an attach, asked for and not answered
yet, or open, with how far its connection's frames are read and the bytes that wait for its
subscriber. -/
inductive Watch where
  /-- Asked for, of a history or else of a screen, and not answered yet. -/
  | asked (history : Bool)
  /-- Open on a screen: what its subscriber was last told, and what the latest look found. -/
  | screen (told latest : Screen)
  /-- Open on a history: the lines that left since the last update. -/
  | history (pending : Log Line)
  /-- An attach asked for and not answered yet. -/
  | attaching
  /-- An attach open: the decoder of its connection's frames, and the bytes that wait for its
  subscriber, in order. -/
  | stream (decoder : Session.Wire.Decoder) (pending : List UInt8)

/-- The two lowercase hexadecimal digits of a byte. -/
@[expose]
def hexByte (b : UInt8) : String :=
  let digit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)
  String.ofList [digit (b.toNat / 16), digit (b.toNat % 16)]

/-- A colour a pen draws with as its JSON holds it: a palette index, or a 24-bit colour as
`#rrggbb`. -/
inductive Hue where
  /-- A palette index. -/
  | index (value : Nat)
  /-- A 24-bit colour, `#rrggbb`. -/
  | rgb (text : String)
  deriving DecidableEq, Repr

/-- A colour as JSON: a palette index as an integer and a 24-bit colour as a string. -/
@[expose]
def Hue.json : Hue → Value
  | .index value => .integer value
  | .rgb text => .string text

/-- **A colour as JSON**: a palette index an integer, a 24-bit colour its `#rrggbb` string. -/
instance : ToValue Hue := ⟨Hue.json⟩

/-- **A colour read from JSON**: a natural integer a palette index and a string a 24-bit
colour. -/
instance : FromValue Hue where
  fromValue?
    | .integer value =>
      if 0 ≤ value then .ok (.index value.toNat) else .error "a palette index below 0"
    | .string text => .ok (.rgb text)
    | _ => .error "a colour that is neither an index nor a string"

/-- A terminal's colour as its pen's JSON holds it: none for the default. -/
@[expose]
def Hue.of : Terminal.Vt.Color → Option Hue
  | .default => none
  | .idx i => some (.index i.toNat)
  | .rgb r g b => some (.rgb ("#" ++ hexByte r ++ hexByte g ++ hexByte b))

/-- A pen as JSON holds it: its colours, `fg` and `bg`, when not the default, and each attribute
it sets. -/
structure Style where
  /-- The background colour. -/
  bg? : Option Hue := none
  /-- Whether it blinks. -/
  blink? : Option Bool := none
  /-- Whether it is bold. -/
  bold? : Option Bool := none
  /-- Whether it is dim. -/
  dim? : Option Bool := none
  /-- The foreground colour. -/
  fg? : Option Hue := none
  /-- Whether it is italic. -/
  italic? : Option Bool := none
  /-- Whether it is reversed. -/
  reverse? : Option Bool := none
  /-- Whether it strikes its text through. -/
  strike? : Option Bool := none
  /-- Whether it underlines. -/
  underline? : Option Bool := none
  deriving DecidableEq, Repr

/-- A pen's style as JSON. -/
@[expose]
def Style.json (p : Style) : Value :=
  .table
    (optional "bg" Hue.json p.bg? ++ optional "blink" Value.boolean p.blink? ++
        optional "bold" Value.boolean p.bold? ++
        optional "dim" Value.boolean p.dim? ++
        optional "fg" Hue.json p.fg? ++
        optional "italic" Value.boolean p.italic? ++
        optional "reverse" Value.boolean p.reverse? ++
        optional "strike" Value.boolean p.strike? ++
        optional "underline" Value.boolean p.underline?).toArray

/-- An attribute as a style holds it: `true` when set, and left out otherwise. -/
@[expose]
def setFlag (set : Bool) : Option Bool := if set then some true else none

/-- **A pen as JSON holds it**, compactly: `fg` and `bg` when they are not the default, and each of
`bold`, `dim`, `italic`, `underline`, `blink`, `reverse` and `strike` that is set, as `true`; the
default pen is `{}`. -/
@[expose]
def Style.of (p : Terminal.Vt.Pen) : Style :=
  { bg? := Hue.of p.bg, blink? := setFlag p.blink, bold? := setFlag p.bold, dim? := setFlag p.dim,
    fg? := Hue.of p.fg, italic? := setFlag p.italic, reverse? := setFlag p.reverse,
    strike? := setFlag p.strike, underline? := setFlag p.underline }

/-- A run as JSON holds it: its length and its pen's style. -/
@[expose]
def Span.wire (s : Span) : Nat × Style := (s.length, Style.of s.pen)

/-- A run as JSON: `[length, style]`. -/
@[expose]
def spanJson (s : Nat × Style) : Value := .array #[.integer s.1, s.2.json]

/-- A line's text as JSON holds it: its UTF-8, `""` for bytes that are not. -/
@[expose]
def Line.textOf (line : Line) : String :=
  (String.fromUTF8? (ByteArray.mk line.text.toArray)).getD ""

/-- A screen's line as JSON holds it: its number, its runs and its text. -/
structure Numbered where
  /-- The line's number, from 0 at the top. -/
  line : Nat
  /-- Its runs, each `[length, style]`. -/
  spans : List (Nat × Style)
  /-- Its text. -/
  text : String
  deriving DecidableEq, Repr

/-- A screen's line as JSON: `{line, spans, text}`. -/
@[expose]
def Numbered.json (r : Numbered) : Value :=
  .table
    #[("line", .integer r.line), ("spans", .array (r.spans.map spanJson).toArray),
      ("text", .string r.text)]

/-- A line under its number as JSON holds it. -/
@[expose]
def Line.row (y : Nat) (line : Line) : Numbered :=
  { line := y, spans := line.spans.map Span.wire, text := line.textOf }

/-- A line that left a screen as JSON holds it: its runs and its text. -/
structure Scrolled where
  /-- Its runs, each `[length, style]`. -/
  spans : List (Nat × Style)
  /-- Its text. -/
  text : String
  deriving DecidableEq, Repr

/-- A line that left a screen as JSON: `{spans, text}`. -/
@[expose]
def Scrolled.json (r : Scrolled) : Value :=
  .table #[("spans", .array (r.spans.map spanJson).toArray), ("text", .string r.text)]

/-- A line that left a screen as JSON holds it. -/
@[expose]
def Line.scrolled (line : Line) : Scrolled :=
  { spans := line.spans.map Span.wire, text := line.textOf }

/-- The cursor as JSON: `{visible, x, y}`. -/
@[expose]
def Cursor.json (c : Cursor) : Value :=
  .table #[("visible", .boolean c.visible), ("x", .integer c.x), ("y", .integer c.y)]

/-- What a result shows beside its answer, each member only when it shows it: a screen's `cursor`,
`rows` and `title`, a capture's bytes in base64, `data`, how a session ended, `ending`, why a line
or params were refused, `reason`, a listing's `records`, the last lines a request said, `said`, and
how many before them it dropped, `saidDropped`, the versions `serve` speaks, `supported`, any other
text, `text`, and the sessions an upgrade carried over, `upgraded`. -/
structure Shows where
  /-- A screen's cursor. -/
  cursor? : Option Cursor := none
  /-- A capture's bytes, in base64. -/
  data? : Option String := none
  /-- How a session ended, as `ls` gives it. -/
  ending? : Option Record := none
  /-- Why a line or params were refused. -/
  reason? : Option String := none
  /-- A listing's records. -/
  records? : Option (List Record) := none
  /-- A screen's lines, top first. -/
  rows? : Option (List Numbered) := none
  /-- The last lines a request said. -/
  said? : Option (List String) := none
  /-- How many lines before them it dropped. -/
  saidDropped? : Option Nat := none
  /-- The protocol versions `serve` speaks. -/
  supported? : Option (List String) := none
  /-- Any other text. -/
  text? : Option String := none
  /-- A screen's window title. -/
  title? : Option String := none
  /-- The sessions an upgrade carried over. -/
  upgraded? : Option (List String) := none

/-- What a result shows as its members, by increasing key. -/
@[expose]
def Shows.members (s : Shows) : List (String × Value) :=
  optional "cursor" Cursor.json s.cursor? ++ optional "data" Value.string s.data? ++
    optional "ending" Record.json s.ending? ++
    optional "reason" Value.string s.reason? ++
    optional "records" (fun records => .array (records.map Record.json).toArray) s.records? ++
    optional "rows" (fun rows => .array (rows.map Numbered.json).toArray) s.rows? ++
    optional "said" strings s.said? ++
    optional "saidDropped" (fun (n : Nat) => Value.integer n) s.saidDropped? ++
    optional "supported" strings s.supported? ++
    optional "text" Value.string s.text? ++
    optional "title" Value.string s.title? ++
    optional "upgraded" strings s.upgraded?

/-- **What answers a request**: the answer its command line would exit with, by name and code, and
what it shows. -/
structure Result extends Shows where
  /-- The answer's name (`answerName`). -/
  answer : String
  /-- The answer's code. -/
  code : Nat

/-- **A result as JSON**: `answer` and `code`, then what it shows, by increasing key. -/
@[expose]
def Result.json (r : Result) : Value :=
  .table
    ([("answer", Value.string r.answer), ("code", Value.integer r.code)] ++
        r.toShows.members).toArray

/-- **What the result of `session/screen` shows of a screen**: its `rows`, each line under its
number, top first, its `cursor` and its `title`. -/
@[expose]
def Screen.shows (screen : Screen) : Shows :=
  { cursor? := some screen.cursor,
    rows? := some (screen.lines.zipIdx.map fun (line, y) => line.row y),
    title? := some screen.title }

/-- The params of `session/screen/changed`: how the watch ended, on its last update, the cursor and
the title when they changed, the numbers of the lines that went, the lines that changed, each under
its number, and the subscription it updates, by the id of the request that opened it. -/
structure ScreenChanged where
  /-- How the watch ended, on its last update. -/
  closed? : Option Result := none
  /-- The cursor, when it changed. -/
  cursor? : Option Cursor := none
  /-- The numbers of the lines that went. -/
  removed : List Nat
  /-- The lines that changed, each under its number. -/
  rows : List Numbered
  /-- The subscription, by the id of the request that opened it. -/
  subscription : Id
  /-- The window title, when it changed. -/
  title? : Option String := none

/-- `session/screen/changed`'s params as JSON. -/
@[expose]
def ScreenChanged.json (u : ScreenChanged) : Value :=
  .table
    (optional "closed" Result.json u.closed? ++ optional "cursor" Cursor.json u.cursor? ++
        [("removed", .array (u.removed.map fun (y : Nat) => .integer y).toArray),
          ("rows", .array (u.rows.map Numbered.json).toArray),
          ("subscription", u.subscription.json)] ++
        optional "title" Value.string u.title?).toArray

/-- **The params of `session/screen/changed`**: the subscription it updates, the id of the request
that opened it, the `rows` that changed, each under its number, the numbers of the lines that
went, `removed`, and the `cursor` and the `title` when they changed. -/
@[expose]
def Screen.update (id : Id) (u : Screen.Update) : Value :=
  ScreenChanged.json
    { cursor? := u.cursor, removed := u.removed, rows := u.lines.map fun (y, line) => line.row y,
      subscription := id, title? := u.title }

/-- The params of `session/history/changed`: how the watch ended, on its last update, how many
lines it dropped before those it carries, the lines that left the screen, oldest first, and the
subscription it updates, by the id of the request that opened it. -/
structure HistoryChanged where
  /-- How the watch ended, on its last update. -/
  closed? : Option Result := none
  /-- How many lines it dropped before those it carries. -/
  dropped : Nat
  /-- The lines that left the screen, oldest first. -/
  lines : List Scrolled
  /-- The subscription, by the id of the request that opened it. -/
  subscription : Id

/-- `session/history/changed`'s params as JSON. -/
@[expose]
def HistoryChanged.json (u : HistoryChanged) : Value :=
  .table
    (optional "closed" Result.json u.closed? ++
        [("dropped", .integer u.dropped), ("lines", .array (u.lines.map Scrolled.json).toArray),
          ("subscription", u.subscription.json)]).toArray

/-- **The params of `session/history/changed`**: the subscription it updates, the id of the request
that opened it, the `lines` that left the screen since the last update, oldest first, and how many
before them it `dropped`. -/
@[expose]
def Log.update (id : Id) (log : Log Line) : Value :=
  HistoryChanged.json
    { dropped := log.dropped, lines := log.tail.map Line.scrolled, subscription := id }

/-- The params of `session/output`: how the attach ended, on its last update, the bytes it carries
in base64, and the subscription it updates, by the id of the request that opened the attach. -/
structure Output where
  /-- How the attach ended, on its last update. -/
  closed? : Option Result := none
  /-- The bytes, in base64. -/
  data : String
  /-- The subscription, by the id of the request that opened the attach. -/
  subscription : Id

/-- `session/output`'s params as JSON. -/
@[expose]
def Output.json (u : Output) : Value :=
  .table
    (optional "closed" Result.json u.closed? ++
        [("data", .string u.data), ("subscription", u.subscription.json)]).toArray

/-- What one line from the client is, as `serve` reads it. -/
inductive Message where
  /-- A request, which one response answers, by its id. -/
  | request (id : Id) (method : String) (params : Value)
  /-- A notification, which nothing answers. -/
  | notification (method : String) (params : Value)
  /-- No message: a line that is not canonical JSON, with the reason the reader gave, or a
  canonical text that is no request, with the id it carried, if any. -/
  | invalid (id : Option Id) (unparsed : Option String)

/-- A wrong part: a reading of lines that takes one that is not canonical JSON as JSON that is no
request, without the reader's reason, and reads any other line as `decode` does. -/
@[expose]
def unreasoned (decode : String → Message) (line : String) : Message :=
  match decode line with
  | .invalid id (some _) => .invalid id none
  | message => message

/-- What `serve` writes, one line each. -/
inductive Outgoing where
  /-- The result of the request with this id. -/
  | result (id : Id) (value : Value)
  /-- The error that answers the request with this id, or a line whose id it could not read, with
  a JSON-RPC code, a message and linger's answer in `data`. -/
  | error (id : Option Id) (code : Int) (message : String) (data : Value)
  /-- A notification. -/
  | notify (method : String) (params : Value)

/-- Where a connection stands in its handshake: before `initialize`, answered with the version it
chose and waiting for `initialized`, or ready. -/
inductive Phase where
  /-- No `initialize` answered yet. -/
  | fresh
  /-- `initialize` answered with this version; `initialized` not heard yet. -/
  | negotiated (version : String)
  /-- `initialized` heard: the connection speaks this version. -/
  | ready (version : String)
  deriving Repr, DecidableEq

/-- What a connection hears. -/
inductive Event where
  /-- A line from the client, as `serve` read it. -/
  | received (message : Message)
  /-- The records the listing of the subscription the request with this id opened found, which
  its result tells the subscriber: the table as the subscriber first holds it. -/
  | opened (id : Id) (records : List Record)
  /-- The records a later listing found. -/
  | sampled (records : List Record)
  /-- The writer wrote everything it took, and takes another message. -/
  | writable
  /-- A watch's look at its session's terminal, where the session's daemon confirmed the
  terminal's size: the screen it renders there (`Screen.render`) and the lines that left its top
  since the watch's last look (`Line.of`), as a log keeps them: the last at most `historyCap`, and a
  count of those it dropped before them. The first look answers the request that asked for the
  watch. -/
  | watched (id : Id) (screen : Screen) (left : Log Line)
  /-- The writer wrote everything it took, and takes the update of the watch with this id. -/
  | flush (id : Id)
  /-- The watch with this id ended: its session ended, its connection was lost, or it never
  opened, as `found` says, with what it said, which answers the request that asked for it when it
  never opened. -/
  | unwatched (id : Id) (found : Api.Found) (said : Log String)
  /-- The bytes one read took from the connection of the attach with this id: what its daemon
  sent, as an attach client reads them. -/
  | read (id : Id) (bytes : List UInt8)

/-- What a connection does. -/
inductive Effect where
  /-- Write this message. -/
  | send (message : Outgoing)
  /-- Perform this request, the command line's (`words`) with this standard input (`input`), as
  the command line does, and answer the request with this id from its reply. -/
  | perform (id : Id) (method : String) (request : Api.Request) (input : List UInt8)
  /-- Write these messages, in order, on the connection of the attach with this id, as an attach
  client writes its keys and its terminal's size. -/
  | relay (id : Id) (messages : List Session.Wire.Msg)

/-- What `serve` can do, as `initialize`'s result says: the methods it answers and the
notifications it may send. -/
structure Abilities where
  /-- The methods it answers. -/
  methods : List String
  /-- The notifications it may send. -/
  notifications : List String
  deriving DecidableEq, Repr

/-- What `serve` can do as JSON. -/
@[expose]
def Abilities.json (a : Abilities) : Value :=
  .table #[("methods", strings a.methods), ("notifications", strings a.notifications)]

/-- `initialize`'s result: what `serve` can do, the protocol version chosen, and who the server is.
-/
structure Welcome where
  /-- What `serve` can do. -/
  capabilities : Abilities
  /-- The protocol version chosen. -/
  protocolVersion : String
  /-- Who the server is. -/
  serverInfo : Info
  deriving DecidableEq, Repr

/-- `initialize`'s result as JSON. -/
@[expose]
def Welcome.json (w : Welcome) : Value :=
  .table
    #[("capabilities", w.capabilities.json), ("protocolVersion", .string w.protocolVersion),
      ("serverInfo", w.serverInfo.json)]

/-- What `initialize`'s result says: the protocol version chosen, the server, `linger` at its
version, and its capabilities, the methods it answers and the notifications it may send. -/
@[expose]
def Welcome.of (version linger : String) : Welcome :=
  { capabilities :=
      { methods := "initialize" :: methods.map (·.1) ++ ["sessions/unsubscribe", "session/input"]
        notifications :=
          ["sessions/changed", "session/screen/changed", "session/history/changed",
            "session/output"] }
    protocolVersion := version, serverInfo := { name := "linger", version? := some linger } }

/-- **The result of `initialize`**: the protocol version chosen, the server, `linger` at its
version, and its capabilities, the methods it answers and the notifications it may send. -/
@[expose]
def welcome (version linger : String) : Value := (Welcome.of version linger).json

/-- What a connection may write before it is ready: an error, or the result of `initialize`. -/
@[expose]
def Effect.Negotiating : Effect → Prop
  | .send (.error ..) => True
  | .send (.result _ value) => ∃ version linger, value = welcome version linger
  | _ => False

/-- Whether an effect answers the request with this id: a response to it, or performing it, whose
reply the response gives. -/
@[expose]
def Effect.Answers (id : Id) : Effect → Prop
  | .send (.result answered _) => answered = id
  | .send (.error answered ..) => answered = some id
  | .perform answered .. => answered = id
  | .send (.notify ..) => False
  | .relay .. => False

/-- A wrong part: a connection that answers every request at once with an empty result, whatever
its handshake says, and otherwise steps as `step` does. -/
@[expose]
def eager {σ : Type} (step : σ → Event → σ × List Effect) (s : σ) : Event → σ × List Effect
  | .received (.request id _ _) => (s, [.send (.result id .null)])
  | ev => step s ev

/-- A wrong part: a connection that sends an update each time the writer is free, whether or not
a subscription is open or anything changed, and otherwise steps as `step` does. -/
@[expose]
def chatty {σ : Type} (step : σ → Event → σ × List Effect) (s : σ) : Event → σ × List Effect
  | .writable => ((step s .writable).1, [.send (.notify "sessions/changed" (.table #[]))])
  | ev => step s ev

/-- A wrong part: a connection that queues each listing's records as an update when it comes,
whether or not the writer is free, and otherwise steps as `step` does. -/
@[expose]
def queued {σ : Type} (step : σ → Event → σ × List Effect) (s : σ) : Event → σ × List Effect
  | .sampled records =>
    ((step s (.sampled records)).1,
      (step s (.sampled records)).2 ++
        [.send
            (.notify "sessions/changed"
              (.table #[("records", .array (records.map Record.json).toArray)]))])
  | ev => step s ev

/-- **A connection negotiates before it acts, and notifies only subscriptions open**, of the
connection whose first state is `init`, whose states read as `phase`, `subscription` and
`watching` and whose transition is `step`, at `s` hearing `ev`: it starts before its handshake;
until it is ready it writes nothing but errors and the result of `initialize`, and performs
nothing; it is ready only once the client said `initialized` after `initialize` was answered;
`initialize`'s result goes only to `initialize`, with the version the client asked for, one it
speaks; it answers or performs every request; each notification names a subscription open, of its
kind; it relays messages only to an attach open; the sessions table opens only by its
`sessions/subscribe`, which opens it in a ready connection, and a watch only by its request; and
`sessions/unsubscribe` closes the subscription it names. -/
@[expose]
def Negotiated {σ : Type} (init : σ) (phase : σ → Phase) (subscription : σ → Option Id)
    (watching : σ → Id → Option Watch) (step : σ → Event → σ × List Effect) (s : σ) (ev : Event) :
    Prop :=
  phase init = .fresh ∧
    ((∀ version, phase s ≠ .ready version) → ∀ e ∈ (step s ev).2, e.Negotiating) ∧
    (∀ version,
      phase (step s ev).1 = .ready version →
        phase s = .ready version ∨
          phase s = .negotiated version ∧
            ∃ params, ev = .received (.notification "initialized" params)) ∧
    (∀ id version linger,
      Effect.send (.result id (welcome version linger)) ∈ (step s ev).2 →
        version ∈ versions ∧
          ∃ params : Initialize,
            ev = .received (.request id "initialize" params.json) ∧
              params.protocolVersion = version) ∧
    (∀ id method params,
      ev = .received (.request id method params) → ∃ e ∈ (step s ev).2, e.Answers id) ∧
    (∀ e ∈ (step s ev).2,
      ∀ method params,
        e = .send (.notify method params) →
          ∃ id,
            member? "subscription" params = some id.json ∧
              (method = "sessions/changed" ∧ subscription s = some id ∨
                method = "session/screen/changed" ∧
                  (∃ told latest, watching s id = some (.screen told latest)) ∨
                method = "session/history/changed" ∧
                  (∃ pending, watching s id = some (.history pending)) ∨
                method = "session/output" ∧
                  (watching s id = some .attaching ∨
                    ∃ decoder pending, watching s id = some (.stream decoder pending)))) ∧
    (∀ e ∈ (step s ev).2,
      ∀ id messages,
        e = .relay id messages →
          ∃ decoder pending, watching s id = some (.stream decoder pending)) ∧
    (∀ id,
      subscription (step s ev).1 = some id →
        subscription s = some id ∨
          ∃ params version,
            phase s = .ready version ∧ ev = .received (.request id "sessions/subscribe" params)) ∧
    (∀ id version,
      phase s = .ready version →
        ev = .received (.request id "sessions/subscribe" (NoParams.json {})) →
        subscription (step s ev).1 = some id) ∧
    (∀ id request version,
      phase s = .ready version →
        subscription s = some id →
        ev = .received (.request request "sessions/unsubscribe" (Subscription.json ⟨id⟩)) →
        subscription (step s ev).1 = none) ∧
    (∀ id,
      (watching (step s ev).1 id).isSome →
        (watching s id).isSome ∨
          ∃ params version,
            phase s = .ready version ∧
              (ev = .received (.request id "session/screen" params) ∨
                ev = .received (.request id "session/history" params) ∨
                ev = .received (.request id "session/attach" params))) ∧
    ∀ id request version,
      phase s = .ready version →
        (watching s id).isSome →
        ev = .received (.request request "sessions/unsubscribe" (Subscription.json ⟨id⟩)) →
        watching (step s ev).1 id = none

/-- **A screen's table is exact**, of the connection whose states read as `watching`, whose
transition is `step`, whose results are `result` and whose updates are `changes`, at `s` for the
watch `id`: a screen's first look answers its request with the whole screen, which its subscriber
then holds; a later look sends nothing and replaces the latest screen, keeping what the subscriber
was told; a free writer sends exactly the changes, when the latest screen differs from what the
subscriber was told, and has then told it; and the changes from `told` to `latest` are exact
(`Screen.Exact`). -/
@[expose]
def ScreenTable {σ : Type} (watching : σ → Id → Option Watch) (step : σ → Event → σ × List Effect)
    (result : Api.Found → Shows → Value) (changes : Screen → Screen → Screen.Update) (s : σ)
    (id : Id) (told latest screen : Screen) (left : Log Line) : Prop :=
  (watching s id = some (.asked false) →
      (step s (.watched id screen left)).2 = [.send (.result id (result .done screen.shows))] ∧
        watching (step s (.watched id screen left)).1 id = some (.screen screen screen)) ∧
    (watching s id = some (.screen told latest) →
      (step s (.watched id screen left)).2 = [] ∧
        watching (step s (.watched id screen left)).1 id = some (.screen told screen) ∧
        (step s (.flush id)).2 =
          (if told = latest then []
          else
            [.send (.notify "session/screen/changed" (Screen.update id (changes told latest)))]) ∧
        watching (step s (.flush id)).1 id = some (.screen latest latest)) ∧
    Screen.Exact told latest (changes told latest)

/-- A wrong part: a connection that forgets how many lines a watch's look dropped, and otherwise
steps as `step` does. -/
@[expose]
def uncounted {σ : Type} (step : σ → Event → σ × List Effect) (s : σ) : Event → σ × List Effect
  | .watched id screen left => step s (.watched id screen { left with dropped := 0 })
  | ev => step s ev

/-- **A history's log counts what it drops**, of the connection whose states read as `watching`,
whose transition is `step` and whose results are `result`, at `s` for the watch `id`: a history's
first look answers its request, and it and each later look, which sends nothing, leave a log whose
reading masks what the log read before, then what the look's log of the lines that left reads
(`Log.Masks`), so every line dropped on the way is a counted gap; and a free writer sends the log
when it holds a line or a drop, and then holds none. -/
@[expose]
def HistoryLog {σ : Type} (watching : σ → Id → Option Watch) (step : σ → Event → σ × List Effect)
    (result : Api.Found → Shows → Value) (s : σ) (id : Id) (pending : Log Line) (screen : Screen)
    (left : Log Line) : Prop :=
  (watching s id = some (.asked true) →
      (step s (.watched id screen left)).2 = [.send (.result id (result .done {}))] ∧
        ∃ kept,
          watching (step s (.watched id screen left)).1 id = some (.history kept) ∧
            Log.Masks kept.reads left.reads) ∧
    (watching s id = some (.history pending) →
      (step s (.watched id screen left)).2 = [] ∧
        (∃ kept,
          watching (step s (.watched id screen left)).1 id = some (.history kept) ∧
            Log.Masks kept.reads (pending.reads ++ left.reads)) ∧
        (step s (.flush id)).2 =
          (if pending.tail = [] ∧ pending.dropped = 0 then []
          else [.send (.notify "session/history/changed" (Log.update id pending))]) ∧
        watching (step s (.flush id)).1 id = some (.history {}))

/-! ## A session's terminal as bytes

A client that is a terminal follows a session as an attach client does: `session/attach` attaches
to it writable, as `attach` does, and each update of its stream, `session/output`, carries in base64
bytes its daemon sent the attach, its repaint, then its output as it comes, in order, every one,
with nothing else. `session/input`, `session/resize` and `session/detach`, each naming the attach
by its subscription, carry its keys, its terminal's size and its leaving to the daemon, as an
attach client's terminal does. A reader that does not read is cut off as an attach client is:
`serve` reads the attach's connection no further while what waits for its subscriber passes a
bound, so the daemon, which owes a client no more than its cap, cuts the connection, and the
stream's last update says so. -/

/-- **An update of an attach's stream carries `bytes`**: its params name the subscription `id`, and
their `data` is text that decodes as base64 (`Base64.decode`) to exactly those bytes. -/
@[expose]
def Carries (id : Id) (bytes : List UInt8) (params : Value) : Prop :=
  member? "subscription" params = some id.json ∧
    ∃ text, member? "data" params = some (.string text) ∧ Base64.decode text.toList = some bytes

/-- **What one read of an attach's connection does**, for the attach `id`, whose connection's
frames `dec` has read so far and whose subscriber `pending` waits for, when it took `bytes`, of
which `feed` decodes messages as an attach client decodes them: when the connection's framing
breaks, where an attach client writes nothing of the read and loses its connection, it sends one
last update, which carries what waited and `closed`, and holds the attach no more; when one of the
messages ends the attach (`Wire.Msg.ends`), it sends one last update, which carries what waited and
the bytes an attach client writes of the messages (`Wire.shown`), and `closed`, and holds the
attach no more; otherwise it sends nothing and holds the attach open, its decoder past them and
those bytes waiting after what waited. -/
@[expose]
def Streamed
    (feed : Session.Wire.Decoder → List UInt8 → Session.Wire.Decoder × List Session.Wire.Msg)
    (id : Id) (dec : Session.Wire.Decoder) (pending bytes : List UInt8) (sent : List Effect)
    (after : Option Watch) : Prop :=
  if (feed dec bytes).1.errored then
    after = none ∧
      ∃ params,
        sent = [.send (.notify "session/output" params)] ∧
          Carries id pending params ∧ (member? "closed" params).isSome
  else
    if (feed dec bytes).2.any Session.Wire.Msg.ends then
      after = none ∧
        ∃ params,
          sent = [.send (.notify "session/output" params)] ∧
            Carries id (pending ++ Session.Wire.shown (feed dec bytes).2) params ∧
            (member? "closed" params).isSome
    else
      sent = [] ∧
        after = some (.stream (feed dec bytes).1 (pending ++ Session.Wire.shown (feed dec bytes).2))

/-- **An attach's stream is exact, for every session an attach reaches**, of the connection whose
states read as `watching`, whose transition is `step` and whose results are `result`, at `s` for
the attach `id`, where `feed` decodes what a daemon sends as an attach client decodes it, `paint`
frames a screen an attach shows, `answerOf` gives the answer of what an attach found and `code` an
answer's code. A live session's reads are its daemon's, a saved one's those of the daemon that
resumes it, as `attach` resumes it (`Recovery.visit`), and a remote one's the frames its host's
stream is relayed as (`Remote.Relays`); an ended one shows its final screen as one read, and then
ends, having found how its program ended. The first read of the attach's connection answers its
request, and every read is `Streamed`, so its subscriber gets the bytes an attach client writes of
what the daemon sent, the repaint and the output after it, in order, every one and nothing else; a
shown screen's read answers the request and leaves exactly the screen's bytes waiting; a free
writer sends what waits, as one update without `closed`, when anything waits, and then nothing
waits; and when the attach ends, having found `found`, one not yet opened answers its request with
what it found, and an open one sends one last update, which carries what waits and `closed`, whose
answer and code are those of what it found, and the connection holds it no more. -/
@[expose]
def AttachStream {σ : Type} (watching : σ → Id → Option Watch) (step : σ → Event → σ × List Effect)
    (result : Api.Found → Shows → Value) (answerOf : Api.Found → Os.Answer)
    (code : Os.Answer → UInt32) (paint : List UInt8 → List UInt8)
    (feed : Session.Wire.Decoder → List UInt8 → Session.Wire.Decoder × List Session.Wire.Msg)
    (s : σ) (id : Id) (dec : Session.Wire.Decoder) (pending bytes screen : List UInt8)
    (found : Api.Found) (said : Log String) : Prop :=
  (watching s id = some .attaching →
      (∃ rest,
          (step s (.read id bytes)).2 = .send (.result id (result .done {})) :: rest ∧
            Streamed feed id {} [] bytes rest (watching (step s (.read id bytes)).1 id)) ∧
        (step s (.read id (paint screen))).2 = [.send (.result id (result .done {}))] ∧
        watching (step s (.read id (paint screen))).1 id = some (.stream {} screen) ∧
        (∃ shows,
          (step s (.unwatched id found said)).2 = [.send (.result id (result found shows))]) ∧
        watching (step s (.unwatched id found said)).1 id = none) ∧
    (watching s id = some (.stream dec pending) →
      Streamed feed id dec pending bytes (step s (.read id bytes)).2
          (watching (step s (.read id bytes)).1 id) ∧
        (pending = [] → (step s (.flush id)).2 = []) ∧
        (pending ≠ [] →
          ∃ params,
            (step s (.flush id)).2 = [.send (.notify "session/output" params)] ∧
              Carries id pending params ∧ member? "closed" params = none) ∧
        watching (step s (.flush id)).1 id = some (.stream dec []) ∧
        (∃ (params : Value) (closed : Result),
          (step s (.unwatched id found said)).2 = [.send (.notify "session/output" params)] ∧
            Carries id pending params ∧
            member? "closed" params = some closed.json ∧
            closed.answer = answerName (answerOf found) ∧
            closed.code = (code (answerOf found)).toNat) ∧
        watching (step s (.unwatched id found said)).1 id = none)

/-- A wrong part: a shown screen read as its bytes, unframed, which an attach client's decoder
reads as frames. -/
@[expose]
def unframed (screen : List UInt8) : List UInt8 := screen

/-- A wrong part: the answer `done`, whatever an attach found. -/
@[expose]
def doneAnyway (_ : Api.Found) : Os.Answer := .done

/-- A wrong part: a connection whose attach drops what its first read took, the bytes that open
the daemon's repaint, and otherwise steps as `step` does. -/
@[expose]
def unpainted {σ : Type} (watching : σ → Id → Option Watch) (step : σ → Event → σ × List Effect)
    (s : σ) : Event → σ × List Effect
  | .read id bytes =>
    match watching s id with
    | some .attaching => step s (.read id [])
    | _ => step s (.read id bytes)
  | ev => step s ev

/-! ## Remote hosts through `serve`

A command reaches a remote session as any client reaches linger: it runs `serve` on the session's
host, through the host's transport, shakes hands with it, and calls the method of the request the
host performs there (`Remote.asked`), so a remote session is a session, the host's linger doing what
the command line does there, and the command finds what the host answered (`Remote.Answered`), and
says what the host said as its host's. A host whose `serve` does not shake hands, as a linger from
before `serve` answers a command line it does not take, with a usage answer (`Remote.Usage`), is
refused, saying so, and `ls -r`, which calls `sessions/list` of each host, lists it as a host that
does not answer, saying why. A remote attach is an attach client's conversation with the host's
`session/attach`: linger relays each update of its stream to the client as the frames of the bytes
it carries (`Remote.Relays`), and each key the client types as one `session/input`. -/

/-- **The request a host performs for one of a request's targets**, the session `name` there, with
the standard input the command line has, `input`: the same request, its target `name` alone, a
listing's as records (`--porcelain`), and `send`'s input as the bytes it delivers, which
`session/send` carries; none for a request no method performs on one session, `ls` of every
session, its counts or a save, and `serve`, and for one no command line is: a read-only attach with
a command, a size `resize` does not take and a `wait` of a name that starts with `-`. -/
@[expose]
def Remote.asked (request : Api.Request) (name : String) (input : List UInt8) :
    Option (Api.Request × List UInt8) :=
  match request with
  | .attach readOnly _ command =>
    if readOnly = true ∧ command ≠ [] then none else some (.attach readOnly name command, [])
  | .list (.named _ _) => some (.list (.named true [name]), [])
  | .list _ => none
  | .start _ program args => some (.start name program args, [])
  | .resume _ => some (.resume name, [])
  | .send _ (.text words) => some (.send name .stdin, (String.intercalate " " words).toUTF8.toList)
  | .send _ .stdin => some (.send name .stdin, input)
  | .detach _ => some (.detach name, [])
  | .kill _ => some (.kill name, [])
  | .rename _ new => some (.rename name new, [])
  | .capture history _ => some (.capture history name, [])
  | .resize _ cols rows =>
    if Terminal.Vt.clampDim cols = cols ∧ Terminal.Vt.clampDim rows = rows then
      some (.resize name cols rows, [])
    else none
  | .wait _ => if name.startsWith "-" = true then none else some (.wait [name], [])
  | .upgrade _ => some (.upgrade [name], [])
  | .serve => none

/-- The member `key` of the first message among `messages` whose `id` is the integer `n`, and that
has one. -/
@[expose]
def Remote.answerOf (messages : List Value) (n : Int) (key : String) : Option Value :=
  (messages.find? fun message =>
        (member? "id" message).bind Id.of == some (.number n) && (member? key message).isSome).bind
    (member? key)

/-- **A host's `serve` shook hands**: it answered `initialize`, request 1, with its result, exactly
a `Welcome` of a version this linger speaks. -/
@[expose]
def Remote.Shook (messages : List Value) : Prop :=
  ∃ welcome : Welcome,
    Remote.answerOf messages 1 "result" = some welcome.json ∧ welcome.protocolVersion ∈ versions

/-- **What a host answered the call**, request 2, of the answers whose codes `code` gives: its
result, exactly a `Result` whose `answer` and `code` are the answer's name and code, and which shows
`shows`; or, where no result answered it, the `data` of the error that did, in the same form, as a
method a `serve` does not answer or params it does not take get. -/
@[expose]
def Remote.Answered (code : Os.Answer → UInt32) (messages : List Value) (answer : Os.Answer)
    (shows : Shows) : Prop :=
  ∃ result : Result,
    (Remote.answerOf messages 2 "result").or
          ((Remote.answerOf messages 2 "error").bind (member? "data")) =
        some result.json ∧
      result.answer = answerName answer ∧ result.code = (code answer).toNat ∧ result.toShows = shows

/-- **The records a host's `sessions/list` returned**: it answered the call `done`, showing these
records. -/
@[expose]
def Remote.Lists (code : Os.Answer → UInt32) (messages : List Value) (records : List Record) :
    Prop := ∃ shows, Remote.Answered code messages .done shows ∧ shows.records? = some records

/-- **A host refused `serve` with a usage answer**: it did not shake hands, and its command exited
with the usage answer's status, 2, as the command line of a linger from before `serve` answers a
word it does not take, or its `serve` answered `initialize` with an error whose `data` is the usage
answer, as one that speaks no version this linger does. -/
@[expose]
def Remote.Usage (messages : List Value) (status : UInt32) : Prop :=
  ¬Remote.Shook messages ∧
    (status = 2 ∨
      ∃ error data,
        Remote.answerOf messages 1 "error" = some error ∧
          member? "data" error = some data ∧ member? "answer" data = some (.string "usage"))

/-- What a host's `serve` told linger of its call. -/
inductive Remote.Heard where
  /-- It shook hands, and answered the call with this answer, showing this. -/
  | answered (answer : Os.Answer) (shows : Shows)
  /-- It refused `serve` with a usage answer: a linger without `serve`, which linger refuses. -/
  | refused
  /-- It answered nothing linger reads. -/
  | silent

/-- **A remote request is its host's, and its answer the host's, attributed**, of the call linger
makes for a request at the session `name` with the standard input `input`, `call`, how a host's
`serve` reads a method and its params, `parse`, how linger reads what a host's `serve` wrote and its
command's exit status, `heard`, the answers' codes, `code`, what a command finds of a host's answer
and what its result shows, `found`, the answer of what a command finds, `answerOf`, the lines a
command says of what the host `host` said, `said`, and how a name or a line is made clean text,
`clean`: the host reads the call as exactly the request it performs for that session
(`Remote.asked`), none when there is none; linger reads an answer exactly when the host shook hands
and answered the call with it, and a refusal exactly when the host refused `serve` with a usage
answer; what the command finds answers exactly as the host answered; and the command says each line
the host said, in order, as the host's: its name, then the line. -/
@[expose]
def Remote.Exact (call : Api.Request → String → List UInt8 → Option (String × Value))
    (parse : String → Value → Option (Api.Request × List UInt8))
    (heard : List Value → UInt32 → Remote.Heard) (code : Os.Answer → UInt32)
    (found : Os.Answer → Shows → Api.Found) (answerOf : Api.Found → Os.Answer)
    (said : String → Shows → List String) (clean : String → String) (request : Api.Request)
    (name : String) (input : List UInt8) (messages : List Value) (status : UInt32)
    (answer : Os.Answer) (shows : Shows) (host : String) : Prop :=
  (call request name input).bind (fun called => parse called.1 called.2) =
      Remote.asked request name input ∧
    (heard messages status = .answered answer shows ↔
      Remote.Shook messages ∧ Remote.Answered code messages answer shows) ∧
    (heard messages status = .refused ↔ Remote.Usage messages status) ∧
    answerOf (found answer shows) = answer ∧
    said host shows = (shows.said?.getD []).map fun text => clean host ++ ": " ++ clean text

/-- **A remote host's rows are exactly what its `sessions/list` returns, named `name@host`**, of
how `heard` reads what a host's `serve` wrote and its command's exit status, how `rows` makes a
host's rows of the records it listed, which names `accept` takes and the answers' codes, `code`:
linger reads records of a host's answer exactly when the host shook hands and its `sessions/list`
returned them (`Remote.Lists`), and the host's rows are its records whose names `accept` takes, in
order, each named `name@host`. -/
@[expose]
def Remote.Rows (heard : List Value → UInt32 → Remote.Heard)
    (rows : String → List Record → List Record) (accept : String → Option String)
    (code : Os.Answer → UInt32) (host : String) (messages : List Value) (status : UInt32)
    (records : List Record) : Prop :=
  ((∃ shows, heard messages status = .answered .done shows ∧ shows.records? = some records) ↔
      Remote.Shook messages ∧ Remote.Lists code messages records) ∧
    (rows host records).map Record.key =
      (records.filter fun record => accept record.key == some record.key).map fun record =>
        record.key ++ "@" ++ host

/-- A wrong part: a reading that takes request 2's result as `done`, listing no records, when its
`answer` says so, whatever request 1 got, and reads any other answer as silent. -/
@[expose]
def Remote.unshaken (messages : List Value) (_ : UInt32) : Remote.Heard :=
  match (Remote.answerOf messages 2 "result").bind (member? "answer") with
  | some (.string "done") => .answered .done { records? := some [] }
  | _ => .silent

/-- The notification that carries an update of an attach's stream, `session/output`, with these
params. -/
@[expose]
def Remote.output (params : Value) : Value :=
  .table #[("jsonrpc", .string "2.0"), ("method", .string "session/output"), ("params", params)]

/-- **A remote attach shows exactly the bytes the host's `session/attach` sends, and sends it exactly
the keys typed**, of what linger relays to its attach client of each line a host's `serve` writes
for the attach `id`, `relay`, and the params of the `session/input` linger writes for keys,
`keys`: of a stream of updates, each with the bytes it carries (`Carries`), none but the last
`closed`, the messages linger relays each fit a frame, and an attach client writes of them exactly
those bytes, in order (`Wire.shown`); an update that carries `closed` is relayed with a message that
ends the attach (`Wire.Msg.ends`) when it names the attach; and the keys an attach client types
reach the host as one `session/input` that carries exactly them. -/
@[expose]
def Remote.Relays (relay : Id → Value → List Session.Wire.Msg) (keys : Id → List UInt8 → Value)
    (id : Id) (stream : List (Value × List UInt8)) (typed : List UInt8) : Prop :=
  ((∀ update ∈ stream, Carries id update.2 update.1) →
      (∀ update ∈ stream.dropLast, member? "closed" update.1 = none) →
      (∀ m ∈ stream.flatMap (fun update => relay id (Remote.output update.1)), m.Fits) ∧
        Session.Wire.shown (stream.flatMap fun update => relay id (Remote.output update.1)) =
          (stream.map (·.2)).flatten) ∧
    (∀ params,
      member? "subscription" params = some id.json →
        (member? "closed" params).isSome → ∃ m ∈ relay id (Remote.output params), m.ends = true) ∧
    Carries id typed (keys id typed)

/-- A wrong part: a relay that writes an update's `data` as the text it is, a byte a character,
its base64 undecoded, and ends the attach on `closed`. -/
@[expose]
def Remote.undecoded (_ : Id) (message : Value) : List Session.Wire.Msg :=
  match (member? "params" message).bind (member? "data") with
  | some (.string text) =>
    [.output (text.toList.map fun c => c.toNat.toUInt8)] ++
      (if ((member? "params" message).bind (member? "closed")).isSome then [.err []] else [])
  | _ => []

end Linger.App.Serve

namespace Linger.App

/-! ## Faults and what they may cost -/

/-- A fault linger contains: one of its own processes fails, or a party it talks to stops
answering or reading. -/
inductive Fault where
  /-- A daemon crashes: its process ends without its session's ending, as a crash, SIGKILL or a
  power loss ends it. -/
  | daemonCrash
  /-- A client dies: its connection ends at any point of what it was doing. -/
  | clientDeath
  /-- A client sends more than its session's program reads, or stops reading what it is sent. -/
  | slowClient
  /-- A daemon does not answer, before its reply or part way through it. -/
  | stuckDaemon
  /-- A remote host does not answer. -/
  | remoteHost
  /-- Optional work is slow: a disk that saves slowly, or a reader that does not read what a
  capture writes. -/
  | optionalWork
  deriving DecidableEq, Repr

/-- What a fault may cost. -/
inductive Fault.Cost where
  /-- Its own session and no other, since a daemon holds its own session alone. -/
  | session
  /-- Its own client, and of the daemon and `serve` no more than the caps of what they keep for
  it. -/
  | client
  /-- No session and no client: the work that needs none of it waits on it no longer than a
  declared bound. -/
  | bound
  deriving DecidableEq, Repr

/-- What each fault may cost: a daemon that crashes or does not answer, and a remote host that
does not answer, their own sessions; a client that dies or reads slowly its own client; and
optional work a declared bound. -/
@[expose]
def Fault.cost : Fault → Fault.Cost
  | .daemonCrash | .stuckDaemon | .remoteHost => .session
  | .clientDeath | .slowClient => .client
  | .optionalWork => .bound

/-- A wrong transition: `step`, which also stops the daemon when a client's connection ends, so
that a client's death costs its whole session. The headline that a fault costs at most its own
session or client is shown to reject it. -/
@[expose]
def Fault.exitsOnClose {S P : Type} (step : S → Session.Event → S × List (Session.Effect P))
    (s : S) : Session.Event → S × List (Session.Effect P)
  | .closed id => ((step s (.closed id)).1, (step s (.closed id)).2 ++ [.exit])
  | ev => step s ev

/-- **A fault costs at most its own session or client, plus a declared bound elsewhere**, of the
program whose parts these are, where `afterCrash` is what a crash leaves at a checkpoint's path, as
`Session.Disk.Durable` speaks of it: a fault at its own cost (`Fault.cost`) is contained when the
claims that bound it hold, and a fault at another cost is not, so the claim fixes each cost. A
daemon that crashes costs its own session back to its last save: resuming gives back the last save
whose flushes returned, or the one then running, never a fresh session, and a session asks for a
save within `ckptIntervalMs` of every change no save holds, by the clock its ticks give it. A client
that dies costs its own client: its connection's end drops it alone from the roster, keeps the
terminal and the record, and asks for no more than a save and the report that the program lost
focus. A client that floods its session or stops reading costs its own client: the pty's input queue
and every client's output queue the daemon keeps owe at most their caps; `serve` holds what it last
told a subscriber and the latest records, never a queue, and its free writer brings the subscriber's
view to the latest; and a log keeps its last entries, at most its cap, and counts the ones it
dropped. A daemon that does not answer costs its own row, a live socket that sent nothing, which
reads `?` with no attention, and a remote host that does not answer its own record, an observation
with no answer, which reads the same. Optional work costs no session or client: a capture holds the
name's locks only while it loads and renders, and the writes a daemon does off its loop coalesce,
the last asked for the last to start. -/
@[expose]
def Fault.Contained {V S P B σ : Type}
    (decide : Bool → Option ByteArray → Recovery (Session.Checkpoint.Ckpt V))
    (saveBytes : Session.Checkpoint.Ckpt V → ByteArray)
    (loadBytes : ByteArray → Option (Session.Checkpoint.Ckpt V)) (init : Nat → Nat → V)
    (feed : V → List UInt8 → V) (resize : V → Nat → Nat → V) (quiesce : V → V)
    (step : S → Session.Event → S × List (Session.Effect P))
    (boot : V → List (String × String) → List (String × String) → S) (terminal : S → V)
    (fieldList : S → List (String × String)) (nextTick : S → Option Nat)
    (roster : S → List Session.Client) (empty : B) (offer enqueue : Nat → B → ByteArray → B × Bool)
    (advance : B → Nat → B) (owedLen : B → Nat) (serve : σ → Serve.Event → σ × List Serve.Effect)
    (phase : σ → Serve.Phase) (subscription : σ → Option Serve.Id)
    (told latest : σ → Option (List Serve.Record))
    (push : {α : Type} → Nat → Serve.Log α → α → Serve.Log α)
    (rowStatus : Display.Listing.Row → Display.Status.Status)
    (classify : Display.Status.Obs → Display.Status.Status)
    (phases : List Capture.Step → List Capture.Phase) (plan : List Capture.Step)
    (ask : {R W : Type} → Session.Offloop R W → W → Session.Offloop R W × Option W)
    (done : {R W : Type} → Session.Offloop R W → Session.Offloop R W × Option W)
    (afterCrash : Option ByteArray → ByteArray → Bool → Option ByteArray) :
    Fault → Fault.Cost → Prop
  | .daemonCrash, .session =>
    (∀ (create synced : Bool) (old new : Session.Checkpoint.Ckpt V),
        Terminal.Vt.Live init feed resize quiesce (Session.Checkpoint.Decoded loadBytes) old.vt →
          Terminal.Vt.Live init feed resize quiesce (Session.Checkpoint.Decoded loadBytes) new.vt →
          ∃ c,
            decide create (afterCrash (some (saveBytes old)) (saveBytes new) synced) = .resume c ∧
              (c = { new with vt := quiesce new.vt } ∨
                synced = false ∧ c = { old with vt := quiesce old.vt })) ∧
      ∀ (vt : V) (fields metaKv : List (String × String)) (pre post : List Session.Event)
        (ev : Session.Event),
        terminal (step (Session.trace step (boot vt fields metaKv) pre).1 ev).1 ≠
              terminal (Session.trace step (boot vt fields metaKv) pre).1 ∨
            fieldList (step (Session.trace step (boot vt fields metaKv) pre).1 ev).1 ≠
              fieldList (Session.trace step (boot vt fields metaKv) pre).1 →
          Session.Effect.checkpoint ∉
            (Session.trace step (Session.trace step (boot vt fields metaKv) pre).1 (ev :: post)).2 →
          ∃ due,
            due ≤ Session.clock pre + Session.ckptIntervalMs ∧
              (∃ wake,
                nextTick
                      (Session.trace step (Session.trace step (boot vt fields metaKv) pre).1
                          (ev :: post)).1 =
                    some wake ∧
                  wake ≤ due) ∧
              ∀ now,
                due ≤ now →
                  Session.Effect.checkpoint ∈
                    (step
                        (Session.trace step (Session.trace step (boot vt fields metaKv) pre).1
                            (ev :: post)).1
                        (.tick now)).2
  | .clientDeath, .client =>
    ∀ (s : S) (id : Nat),
      roster (step s (.closed id)).1 = (roster s).filter (·.id != id) ∧
        terminal (step s (.closed id)).1 = terminal s ∧
        fieldList (step s (.closed id)).1 = fieldList s ∧
        ∀ eff ∈ (step s (.closed id)).2, eff = .checkpoint ∨ eff = .writePty [0x1B, 0x5B, 0x4F]
  | .slowClient, .client =>
    (∀ {cap : Nat} {b : B}, Session.Buf.InputReach empty offer advance cap b → owedLen b ≤ cap) ∧
      (∀ {cap : Nat} {b : B},
        Session.Buf.OutputReach empty enqueue advance cap b → owedLen b ≤ cap) ∧
      (∀ (s : σ) (version : String) (id : Serve.Id) (was now rows : List Serve.Record),
        phase s = .ready version →
          subscription s = some id →
          told s = some was →
          latest s = some now →
          (now.map Serve.Record.key).Nodup →
          (serve s (.opened id rows)).2 = [] ∧
            told (serve s (.opened id rows)).1 = some rows ∧
            latest (serve s (.opened id rows)).1 = some rows ∧
            (serve s (.sampled rows)).2 = [] ∧
            subscription (serve s (.sampled rows)).1 = some id ∧
            told (serve s (.sampled rows)).1 = some was ∧
            latest (serve s (.sampled rows)).1 = some rows ∧
            ∀ params,
              Serve.Effect.send (.notify "sessions/changed" params) ∈ (serve s .writable).2 →
                ∃ records gone,
                  params = Serve.update id records gone ∧
                    ∀ key,
                      (Serve.View.apply (Serve.View.of was) records gone key).map
                          Serve.Record.reading =
                        (Serve.View.of now key).map Serve.Record.reading) ∧
      ∀ {α : Type} (cap : Nat) (entries : List α),
        (entries.foldl (push cap) {}).tail = entries.drop (entries.length - cap) ∧
          (entries.foldl (push cap) {}).dropped = entries.length - cap ∧
          (entries.foldl (push cap) {}).tail.length + (entries.foldl (push cap) {}).dropped =
            entries.length
  | .stuckDaemon, .session => rowStatus (.live []) = ⟨.none, .unknown⟩
  | .remoteHost, .session => classify { known := false } = ⟨.none, .unknown⟩
  | .optionalWork, .bound =>
    ((∀ steps, (phases steps).flatMap Capture.Phase.work = Capture.work steps false) ∧
        (Capture.work plan false).map Prod.fst = [.load, .render, .write] ∧
        (.load, true) ∈ Capture.work plan false ∧
        ∀ step, (step, true) ∈ Capture.work plan false → step.waitsOutside = false) ∧
      ∀ {W : Type} (earlier : List (Session.Offloop.Op W)) (w : W) (ends : Nat),
        (((earlier ++ (.ask w : Session.Offloop.Op W) :: List.replicate ends .done).foldl
                  (Session.Offloop.cycle ask done) ({}, [])).2.getLast? =
              some w ∨
            ends = 0 ∧
              ((earlier ++ (.ask w : Session.Offloop.Op W) :: List.replicate ends .done).foldl
                    (Session.Offloop.cycle ask done) ({}, [])).1.waiting =
                some w) ∧
          ∀ ops : List (Session.Offloop.Op W),
            (ops.foldl (Session.Offloop.cycle ask done) ({}, [])).2.length ≤
              (ops.filter Session.Offloop.Op.isDone).length + 1
  | _, _ => False

end Linger.App

namespace Linger.App.Handover

/-! ## Whether an attach hands the session's daemon over to the attaching binary -/

/-- What a daemon's `info` answer says that decides whether an attach hands the daemon over: the
handoff format it writes and its build number, each when it reports it as a number. -/
structure Daemon where
  /-- The handoff format the daemon writes, which it reports as `handoff`. -/
  handoff : Option Nat
  /-- The daemon's build number, which it reports as `build`: the step of linger's history its
  binary was built at. A daemon an older linger started reports none. -/
  build : Option Nat
  deriving Repr, DecidableEq

/-- A daemon as the fields of its `info` answer describe it. -/
@[expose]
def Daemon.ofInfo (fields : List (String × String)) : Daemon :=
  { handoff := (fields.lookup "handoff").bind String.toNat?
    build := (fields.lookup "build").bind String.toNat? }

/-- Whether the daemon can hand its session to this version's binary: it writes a handoff format
this version reads. -/
@[expose]
def Daemon.hands (d : Daemon) : Bool := d.handoff.any (Session.Handoff.formats.contains ·)

/-- Whether the daemon's binary is older than build `b`: it reports a lower build number, or
none, as a daemon an older linger started does. -/
@[expose]
def Daemon.older (d : Daemon) (b : Nat) : Bool := d.build.all (· < b)

/-- What an attach does with the session's daemon before it attaches. -/
inductive Plan where
  /-- Hand the daemon over to the attaching binary, by the handoff `linger upgrade` asks for. -/
  | handOver
  /-- Leave the daemon as it is. -/
  | keep
  deriving Repr, DecidableEq

/-- The build of the session's daemon after an attach by build `b` that planned `p` for the
daemon `d`, which `took` the handoff or not: `b` when the attach handed the daemon over and the
daemon took it, the new image being the attaching binary, and `d`'s own otherwise, since a
daemon that refuses a handoff serves on as it was (`upgrade_probes`). -/
@[expose]
def after (p : Plan) (took : Bool) (d : Daemon) (b : Nat) : Option Nat :=
  match p, took with
  | .handOver, true => some b
  | _, _ => d.build

/-- A wrong plan, which a kill names: hand over every daemon that can hand its session to this
binary, whatever its build, so an attach would hand a daemon over to an equal or a lower build. -/
@[expose]
def anyBuild (mode : Session.Mode) (_ : Nat) (fields : List (String × String)) : Plan :=
  if mode = .writable ∧ (Daemon.ofInfo fields).hands = true then .handOver else .keep

/-- A wrong plan, which a kill names: hand an older daemon over on a read-only attach too. -/
@[expose]
def anyMode (_ : Session.Mode) (b : Nat) (fields : List (String × String)) : Plan :=
  if (Daemon.ofInfo fields).hands = true ∧ (Daemon.ofInfo fields).older b = true then .handOver
  else .keep

end Linger.App.Handover
