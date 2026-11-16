module

public import Linger.Os.CoreSpec
public import Linger.Session.CoreSpec

public section

/-! # What command-line headlines are stated in

The executor a command line reaches, where a command line of plain words goes, the operations of
the session model and one row of the command table, an operation's one command, what a command
does with a name's saved session and what an attach to it does, what `wait` hears on each look
at a name and does next, and the steps of `capture` of a saved session, which of them hold the
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
  /-- Set or clear a session's description. -/
  | describe
  /-- Carry live sessions over to this linger's image, their programs running on. -/
  | upgrade
  deriving Repr, DecidableEq

/-- Every operation, once each, in the order of its constructors. -/
@[expose]
def Op.all : List Op :=
  [.attach, .list, .start, .resume, .send, .detach, .kill, .rename, .capture, .resize, .wait,
    .describe, .upgrade]

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
command's spellings its own row, `info` and `get` readers of what `ls` reports, and `set`,
`unset` and `clear` writers of the labels `describe` writes one of. Every operation has a command
in it, but some have several. -/
@[expose]
def aliased : List Command :=
  [("attach", .attach), ("a", .attach), ("ls", .list), ("list", .list), ("l", .list),
        ("start", .start), ("resume", .resume), ("send", .send), ("s", .send), ("detach", .detach),
        ("d", .detach), ("kill", .kill), ("k", .kill), ("info", .list), ("i", .list),
        ("capture", .capture), ("c", .capture), ("resize", .resize), ("wait", .wait), ("w", .wait),
        ("get", .list), ("g", .list), ("set", .describe), ("unset", .describe), ("un", .describe),
        ("clear", .describe), ("cl", .describe), ("describe", .describe), ("upgrade", .upgrade)].map
    fun (word, op) => { word, op, args := "", summary := "" }

end Linger.App.Commands

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
  /-- The wait is over, with this answer. -/
  | answer (answer : Os.Answer)
  /-- Look again; `heldSince` is when the name was first found held, or `none` when it was not
  on this look. -/
  | again (heldSince : Option Nat)
  deriving Repr, DecidableEq

end Linger.App.Wait

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

end Linger.App.Capture
