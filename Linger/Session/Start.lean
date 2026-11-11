module

public import Linger.Session.Spec
import Terminal.Mediation

public section

/-! # Linger.Session.Start — what `start` and `resume` do with a name

`start` runs a program in a new session under a name no session holds. It never takes a name
from a live session or from a saved one, and never resumes one (`plan`). `resume` runs a saved
session's program again and never starts a new session (`resumePlan`). The daemon decides
holding the name, and tells the command that started it what it did (`Report`), through a file
that command named. -/

namespace Linger.Session.Start

/-- What `start` does with a name, given whether a live session and a saved one hold it. A live
session comes first: its daemon owns the saved state too. -/
def plan (live saved : Bool) : Plan := if live then .running else if saved then .saved else .take

/-- What `resume` does with a name. -/
inductive Resumption where
  /-- A live session holds the name: its program already runs, and nothing changes. -/
  | running
  /-- A saved session holds the name, an ended one included: its program runs again, in its
  saved directory and on its last screen. -/
  | resume
  /-- No session holds the name, and none starts. -/
  | missing
  deriving Repr, DecidableEq

/-- What `resume` does with a name, given whether a live session and a saved one hold it: it
starts only a saved session, never a new one, and a live session comes first. -/
def resumePlan (live saved : Bool) : Resumption :=
  if live then .running else if saved then .resume else .missing

/-- What a daemon started for `start` tells the command that started it. -/
inductive Report where
  /-- The program runs in the new session. -/
  | started
  /-- A live session holds the name, so nothing started. -/
  | running
  /-- A saved session holds the name, so nothing started. -/
  | saved
  /-- The program could not start: `status` is what a shell or `env` reports for that, and
  `why` says why. -/
  | failed (status : UInt8) (why : List UInt8)
  deriving Repr, DecidableEq

/-- The report's bytes; `decode` reads them back (`decode_encode`). -/
def Report.encode : Report → List UInt8
  | .started => [0]
  | .running => [1]
  | .saved => [2]
  | .failed status why => 3 :: status :: why

/-- The report these bytes hold, or `none` for bytes no report has. -/
def Report.decode : List UInt8 → Option Report
  | [0] => some .started
  | [1] => some .running
  | [2] => some .saved
  | 3 :: status :: why => some (.failed status why)
  | _ => none

/-- The program a daemon starts, and its arguments: a command's first word and the rest of its
words, verbatim and with no shell between, or without a command the session's shell, alone. -/
def programOf (shell : String) : List String → String × Array String
  | [] => (shell, #[])
  | program :: words => (program, words.toArray)

/-- The variables a session's program reads unlike the command that asked for the session: the
session's name, and the terminal linger is, with linger's version. -/
def environment (name : String) : List (String × String) :=
  [("LINGER_SESSION", name), ("TERM", "xterm-256color"), ("TERM_PROGRAM", "linger"),
    ("TERM_PROGRAM_VERSION", Terminal.Mediation.versionNumber)]

/-- The status `start` returns for a program that could not start, as a shell or `env -C`
reports it: 125 when its directory cannot be entered, 127 when no program of its name is found,
and 126 when the program cannot be run. -/
def failureStatus : Spawn.Failure → UInt8
  | .directory _ => 125
  | .notFound _ => 127
  | .notRunnable _ => 126

/-- What a session's `info` reports of its start for its whole life: its name, its program's
pid, when it started, its command, the directory its program runs in, and, for a resume that runs
it elsewhere than its saved directory, that directory. -/
def metadata (name pid created cmd dir : String) (saved : Option String) : List (String × String) :=
  [("name", name), ("pid", pid), ("created", created), ("cmd", cmd), ("start_dir", dir)] ++
    match saved with
    | some savedDir => if savedDir = dir then [] else [("saved_dir", savedDir)]
    | none => []

/-- The daemon's decision at its commit point: it goes on to run the program exactly when it took
the request's ticket, and starts nothing when the command that asked took it first. -/
def proceeds (took : Bool) : Bool := took

/-- What a command answers once its request is decided, from whether the command took the ticket
and whether the program runs: that it runs only when the daemon took the ticket and ran it, and
otherwise that it does not. -/
def answer (took runs : Bool) : Answer := if !took && runs then .started else .notStarted

end Linger.Session.Start
