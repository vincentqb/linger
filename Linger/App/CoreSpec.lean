module

public import Linger.Os.CoreSpec
public import Linger.Session.CoreSpec

public section

/-! # What command-line headlines are stated in

The executor a command line reaches, where a command line of plain words goes, the operations of
the session model and one row of the command table, an operation's one command, what a command
does with a name's saved session and what an attach to it does, what `wait` hears on each look
at a name and does next, what `kill` hears on each look at a name once a daemon has taken its
request and does next, and the steps of `capture` of a saved session, which of them hold the
name's locks and which wait on a party outside linger. What a command answers is the operating
system's vocabulary, `Linger.Os.Answer`, which the selector answers in too. -/

namespace Linger.App.Entry

/-- The executor that receives a command line: the interactive selector or the session CLI, or a
usage error for an encoded command line that does not decode. -/
inductive Route where
  /-- `attach` without a target: open the selector, read-only on request. -/
  | selector (readOnly : Bool)
  /-- Every other command line, with its exact arguments; an empty one becomes `--help`. -/
  | session (args : List String)
  /-- An encoded command line whose words do not decode: a usage error, exit status 2. -/
  | malformed
  deriving BEq, Repr

/-- Where a command line goes, once its words are the ones its sender meant: bare invocation
explains the CLI, as `--help` does, `attach` alone opens the selector, read-only on request, and
every other command line reaches the session CLI with its exact words. -/
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
  /-- What it ran exited with this status, as a shell reports it: a remote linger, through its
  host's transport, or the program of a session whose daemon, an older linger's, told no more. -/
  | status (status : UInt32)
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
that it did what was asked, refused, met an operand linger does not take, could not find out, or
relayed a remote linger's status; each other finding belongs to the operations named. -/
@[expose]
def Op.finds : Op → Api.Found → Bool
  | _, .done | _, .refused | _, .invalid | _, .unknown | _, .status _ => true
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

/-- A JSON value (RFC 8259), as `serve` reads and writes one. A number keeps the text it was
written in, so that a request's id goes back exactly as it came. -/
inductive Json where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (value : Bool)
  /-- A number, as written. -/
  | number (text : String)
  /-- A string. -/
  | str (value : String)
  /-- An array. -/
  | arr (items : List Json)
  /-- An object, its members in order. -/
  | obj (members : List (String × Json))
  deriving Inhabited

/-- The member of an object under `key`, the first one when it has several, and none of any other
value. -/
@[expose]
def Json.member? (key : String) : Json → Option Json
  | .obj members => members.lookup key
  | _ => none

/-- A string's text. -/
@[expose]
def Json.text? : Json → Option String
  | .str value => some value
  | _ => none

/-- A number written as a natural number, in decimal digits alone. -/
@[expose]
def Json.nat? : Json → Option Nat
  | .number text => if text.toList.all Char.isDigit then text.toNat? else none
  | _ => none

/-- A boolean. -/
@[expose]
def Json.flag? : Json → Option Bool
  | .bool value => some value
  | _ => none

/-- An array of strings, their texts. -/
@[expose]
def Json.texts? : Json → Option (List String)
  | .arr items => items.mapM Json.text?
  | _ => none

/-- The member `key` of `params`, as `read` takes it: none when it is missing, `null` or not
what `read` takes. -/
@[expose]
def Json.need {α : Type} (params : Json) (key : String) (read : Json → Option α) : Option α :=
  (params.member? key).bind read

/-- The member `key` of `params`, as `read` takes it, or `default` when it is missing or `null`;
none when it is something `read` does not take. -/
@[expose]
def Json.opt {α : Type} (params : Json) (key : String) (read : Json → Option α) (default : α) :
    Option α :=
  match params.member? key with
  | none | some .null => some default
  | some value => read value

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

/-- The methods `serve` answers as operations, each with the operation whose request it is and the
word of that operation's command: every one is an ask, a request answered once, by its id. -/
@[expose]
def methods : List (String × Commands.Op × String) :=
  [("sessions/list", .list, "ls"), ("session/start", .start, "start"),
    ("session/resume", .resume, "resume"), ("session/send", .send, "send"),
    ("session/detach", .detach, "detach"), ("session/kill", .kill, "kill"),
    ("session/rename", .rename, "rename"), ("session/capture", .capture, "capture"),
    ("session/resize", .resize, "resize"), ("session/wait", .wait, "wait")]

/-- The standard input a method's command line reads: the bytes `session/send`'s `data` encodes
in base64 (`Base64.decode`), and none for any other method. -/
@[expose]
def input (method : String) (params : Json) : Option (List UInt8) :=
  if method = "session/send" then
    (params.need "data" Json.text?).bind fun data => Base64.decode data.toList
  else some []

/-- The words of a method's command line after its command's: its options from the params'
members and its target last, after `--` where the command reads one, so that a name that starts
with `-` stays a name; none for params the method does not take. `session/send` is `send NAME -`,
whose standard input is `input`'s. -/
@[expose]
def operands (method : String) (params : Json) : Option (List String) :=
  if method = "sessions/list" then
    (params.opt "names" Json.texts? []).map fun names => ["--porcelain", "--"] ++ names
  else
    if method = "session/start" then do
      let name ← params.need "name" Json.text?
      let program ← params.need "program" Json.text?
      let args ← params.opt "args" Json.texts? []
      pure ([name, program] ++ args)
    else
      if method = "session/rename" then do
        let name ← params.need "name" Json.text?
        let new ← params.need "new" Json.text?
        pure [name, new]
      else
        if method = "session/capture" then do
          let name ← params.need "name" Json.text?
          let history ← params.opt "history" Json.flag? false
          pure ((if history then ["--history"] else []) ++ ["--", name])
        else
          if method = "session/resize" then do
            let name ← params.need "name" Json.text?
            let cols ← params.need "cols" Json.nat?
            let rows ← params.need "rows" Json.nat?
            pure [name, toString cols, toString rows]
          else
            if method = "session/send" then
              (params.need "name" Json.text?).map fun name => [name, "-"]
            else (params.need "name" Json.text?).map fun name => [name]

/-- **The command line a method and its params are**: its operation's command word (`methods`),
then its `operands`; none for a method `methods` does not list or params it does not take. -/
@[expose]
def words (method : String) (params : Json) : Option (List String) :=
  (methods.lookup method).bind fun (_, word) => (operands method params).map (word :: ·)

/-- The protocol versions `serve` speaks. -/
@[expose]
def versions : List String := ["1"]

/-- A request's id: a number, as written, or a string. -/
inductive Id where
  /-- A number, as written. -/
  | number (text : String)
  /-- A string. -/
  | str (text : String)
  deriving Repr, DecidableEq

/-- An id as JSON. -/
@[expose]
def Id.json : Id → Json
  | .number text => .number text
  | .str text => .str text

/-- What one line from the client is, as `serve` reads it. -/
inductive Message where
  /-- A request, which one response answers, by its id. -/
  | request (id : Id) (method : String) (params : Json)
  /-- A notification, which nothing answers. -/
  | notification (method : String) (params : Json)
  /-- No message: a line that is not JSON, when `unparsed`, or JSON that is no request, with the
  id it carried, if any. -/
  | invalid (id : Option Id) (unparsed : Bool)

/-- What `serve` writes, one line each. -/
inductive Outgoing where
  /-- The result of the request with this id. -/
  | result (id : Id) (value : Json)
  /-- The error that answers the request with this id, or a line whose id it could not read, with
  a JSON-RPC code, a message and linger's answer in `data`. -/
  | error (id : Option Id) (code : Int) (message : String) (data : Json)
  /-- A notification. -/
  | notify (method : String) (params : Json)

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

/-- What a connection does. -/
inductive Effect where
  /-- Write this message. -/
  | send (message : Outgoing)
  /-- Perform this request, the command line's (`words`) with this standard input (`input`), as
  the command line does, and answer the request with this id from its reply. -/
  | perform (id : Id) (method : String) (request : Api.Request) (input : List UInt8)

/-- The result of `initialize`: the protocol version chosen, the server, `linger` at its version,
and its capabilities, the methods it answers and the notifications it may send. -/
@[expose]
def welcome (version linger : String) : Json :=
  .obj
    [("protocolVersion", .str version),
      ("serverInfo", .obj [("name", .str "linger"), ("version", .str linger)]),
      ("capabilities",
        .obj
          [("methods", .arr (("initialize" :: methods.map (·.1)).map .str)),
            ("notifications", .arr [])])]

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

/-- A wrong part: a connection that answers every request at once with an empty result, whatever
its handshake says, and otherwise steps as `step` does. -/
@[expose]
def eager {σ : Type} (step : σ → Event → σ × List Effect) (s : σ) : Event → σ × List Effect
  | .received (.request id _ _) => (s, [.send (.result id .null)])
  | ev => step s ev

end Linger.App.Serve
