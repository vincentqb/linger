module

public import Linger.Session.Spec

public section

/-! # What command-line headlines are stated in

The executor a command line reaches, where a command line of plain words goes, one row of the
command table, the answers a command's exit status gives, what a command does with a name's
saved session, and what `wait` hears on each look at a name and does next. -/

namespace Linger.App.Entry

/-- The executor that receives a command line: the interactive selector, tmux save
interchange or the session CLI, or a usage error for an encoded command line that does not
decode. -/
inductive Route where
  /-- `attach` or `a` without a target: open the selector, read-only on request. -/
  | selector (readOnly : Bool)
  /-- Save interchange, given the arguments after `tmux`. -/
  | tmux (args : List String)
  /-- Every other command line, with its exact arguments; an empty one becomes `help`. -/
  | session (args : List String)
  /-- An encoded command line whose words do not decode: a usage error, exit status 2. -/
  | malformed
  deriving BEq, Repr

/-- Where a command line goes, once its words are the ones its sender meant: bare invocation
explains the CLI, `attach` or `a` alone opens the selector, read-only on request, `tmux` hands
the rest to save interchange, and every other command line reaches the session CLI with its
exact words. -/
@[expose]
def Route.of (args : List String) : Route :=
  if args = [] then .session ["help"]
  else
    if args = ["attach"] ∨ args = ["a"] then .selector false
    else
      if args = ["attach", "--read-only"] ∨ args = ["a", "--read-only"] then .selector true
      else if args.head? = some "tmux" then .tmux args.tail else .session args

end Linger.App.Entry

namespace Linger.App.Commands

/-- One row of the command table. -/
structure Command where
  /-- The word that names the command. -/
  word : String
  /-- Its other spellings, each a word no other command uses. -/
  aliases : List String := []
  /-- The arguments it takes, as help and its usage error show them. -/
  args : String
  /-- What it does, in a few words. -/
  summary : String
  deriving Repr, DecidableEq

end Linger.App.Commands

namespace Linger.App

/-- What a command answers, as its exit status gives it: an answer of linger's own, or the
status of the program the command waited for. The statuses are a shell's, and a program may
exit with one linger also uses, as with `timeout` and `env`, so a status alone cannot tell the
two apart; `info` and the porcelain output say exactly. -/
inductive Answer where
  /-- It did what was asked. -/
  | done
  /-- It did not, refused or failed, and linger says why. -/
  | notDone
  /-- Its command line is not one linger takes. -/
  | usage
  /-- Its time limit passed first. -/
  | timedOut
  /-- linger failed, or could not find out what was asked. -/
  | failed
  /-- The program it was to run cannot be run. -/
  | cannotRun
  /-- The program, or the session, it names does not exist. -/
  | notFound
  /-- A signal interrupted it. -/
  | interrupted
  /-- The program it waited for ended with this status, as a shell reports it: the program's
  code, or 128 plus the number of the signal that killed it. -/
  | program (status : UInt32)
  deriving Repr, DecidableEq

/-- Whether an answer is linger's own, and not a program's status. -/
@[expose]
def Answer.Own : Answer → Prop
  | .program _ => False
  | _ => True

/-- The answer that tells how a program ended: its status, as a shell reports it, or, when linger
did not see the end, that linger could not find out. -/
@[expose]
def Answer.ofOutcome : Linger.Session.Outcome → Answer
  | .unknown => .failed
  | outcome => .program outcome.status

/-- What a command does with a name no live session holds, from what the name's checkpoint
file holds, given what a checkpoint holds: start a new session, resume the saved one, or start
nothing, leave the file as it is and answer why. -/
inductive Recovery (C : Type) where
  /-- Start a new session under the name. -/
  | fresh
  /-- Resume the session this checkpoint saved. -/
  | resume (c : C)
  /-- Start nothing, leave the file as it is, and answer this. -/
  | refuse (answer : Answer)
  deriving Repr, DecidableEq

end Linger.App

namespace Linger.App.Wait

/-- What one look at a name tells `wait`: its daemon's reply, or, with no daemon to answer, the
name's end record or that another process holds the name. -/
inductive Heard where
  /-- The daemon said how the session's program ended. -/
  | ended (outcome : Linger.Session.Outcome)
  /-- A daemon from before `Wire.Msg.ended` gave only the status a shell would report. -/
  | status (status : UInt32)
  /-- The daemon said nothing before the time limit. -/
  | silent
  /-- The daemon refused, or answered without saying how the program ended. -/
  | refused
  /-- No daemon answered, and the name's end record says this, as `Record.answer` reads it:
  `none` when no session has taken the name. -/
  | recorded (answer : Option Linger.Session.Outcome)
  /-- No daemon answered, and another process holds the name, as a daemon does while it starts
  or ends. -/
  | held
  deriving Repr, DecidableEq

/-- What `wait` does after a look: answer, or look again, keeping when it first found the name
held with no daemon answering, while it still finds it so. -/
inductive Next where
  /-- The wait is over, with this answer. -/
  | answer (answer : Answer)
  /-- Look again; `heldSince` is when the name was first found held, or `none` when it was not
  on this look. -/
  | again (heldSince : Option Nat)
  deriving Repr, DecidableEq

end Linger.App.Wait
