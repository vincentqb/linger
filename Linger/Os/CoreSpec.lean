module

public section

/-! # What exit-status headlines are stated in

The answers a command gives, as its exit status gives them: an answer of linger's own, the
signal that stopped it or the session it attached to or waited for, or the status of the program
the command waited for. An exit status is the operating system's, and the selector answers as
the session commands do, so the answers sit in the bottom layer, where
every component that answers can name them; and the codes linger gave before a status said which
signal it stood for, which the kills put in place of the program's. -/

namespace Linger.Os

/-- What a command answers, as its exit status gives it: an answer of linger's own, the signal
that stopped it or the session it attached to or waited for, or the status of the program the
command waited for. The statuses are a shell's, and a program may exit with one linger also uses,
as with `timeout` and `env`, so a status alone cannot tell the two apart; the porcelain output
says exactly. -/
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
  /-- Its chooser was cancelled, by a key or by the end of its input, as fzf answers a chooser
  cancelled with Esc or ^C. -/
  | cancelled
  /-- The signal with this number stopped it, once it had handed its terminal back: it ends as
  the signal ends a program that does not catch it, which a shell reports as 128 plus the
  number. -/
  | stopped (signal : UInt8)
  /-- The session it attached to or waited for was saved when the signal with this number
  stopped its daemon, which a shell reports as it reports a job that signal stopped, 128 plus the
  number. -/
  | saved (signal : UInt8)
  /-- The program it waited for ended with this status, as a shell reports it: the program's
  code, or 128 plus the number of the signal that killed it. -/
  | program (status : UInt32)
  deriving Repr, DecidableEq

/-- Whether an answer is linger's own, and not the status a signal or a program gives. -/
@[expose]
def Answer.Own : Answer → Prop
  | .stopped _ | .saved _ | .program _ => False
  | _ => True

/-- The codes linger gave before a status said which signal it stood for: every signal that
stopped a command, or a session's daemon, gave 130, the status of SIGINT, which a cancelled
chooser also gives. -/
@[expose]
def Answer.lumped : Answer → UInt32
  | .done => 0
  | .notDone => 1
  | .usage => 2
  | .timedOut => 124
  | .failed => 125
  | .cannotRun => 126
  | .notFound => 127
  | .cancelled | .stopped _ | .saved _ => 130
  | .program status => status

end Linger.Os
