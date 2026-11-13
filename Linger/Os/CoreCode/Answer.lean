module

public import Linger.Os.CoreSpec

public section

/-! # Linger.Os.Answer — the exit statuses of linger's commands

**One vocabulary.** Every command answers with an `Answer` and exits with its code (`code`), the
session commands, the selector and the tmux interchange alike: each of linger's own answers has
one code, the one `linger help` lists for it (`legend`), and a program's status passes through.
Help lists each of linger's answers once (`listed`). -/

namespace Linger.Os.Answer

/-- The exit status that gives an answer: a shell's conventions, as `timeout(1)` and `env`
follow them, for linger's own answers, and the program's status for a program's. -/
def code : Answer → UInt32
  | .done => 0
  | .notDone => 1
  | .usage => 2
  | .timedOut => 124
  | .failed => 125
  | .cannotRun => 126
  | .notFound => 127
  | .interrupted => 130
  | .program status => status

/-- linger's own answers, in the order `linger help` lists them. -/
def listed : List Answer :=
  [.done, .notDone, .usage, .timedOut, .failed, .cannotRun, .notFound, .interrupted]

/-- What an answer means, in the words `linger help` gives it. -/
def meaning : Answer → String
  | .done => "done"
  | .notDone => "refused or failed"
  | .usage => "usage"
  | .timedOut => "timed out"
  | .failed => "linger failed"
  | .cannotRun => "cannot run"
  | .notFound => "not found"
  | .interrupted => "interrupted"
  | .program _ => "the program's own"

/-- The lines `linger help` prints for linger's own answers: one per answer, its code and then
what it means. -/
def legend : List String :=
  listed.map fun answer =>
    let shown := toString answer.code
    shown.pushn ' ' (5 - shown.length) ++ answer.meaning

/-- The answer an exit status gives when that status is all linger has, as for a daemon's report
of a program that could not start or a listing that failed: the listed answer with that code,
and otherwise a program's status. Its code is the status (`code_ofCode`). -/
def ofCode (status : UInt32) : Answer := (listed.find? (·.code == status)).getD (.program status)

end Linger.Os.Answer
