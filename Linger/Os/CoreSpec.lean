module

public section

/-! # What exit-status headlines are stated in

The answers a command gives, as its exit status gives them: an answer of linger's own, or the
status of the program the command waited for. An exit status is the operating system's, and the
selector and the tmux interchange answer as the session commands do, so the answers sit in the
bottom layer, where every component that answers can name them. -/

namespace Linger.Os

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
  /-- A signal interrupted it, or its chooser was cancelled. -/
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

end Linger.Os
