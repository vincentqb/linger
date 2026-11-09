module

public import Linger.Session.Spec

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

end Linger.Session.Start
