module

public import Linger.Session.Spec

public section

/-! # Linger.Session.Start — what `start` does with a name

`start` runs a program in a new session under a name no session holds. It never takes a name
from a live session or from a saved one, and never resumes one (`plan`). The daemon decides
holding the name, and tells the command that started it what it did (`Report`), through a file
that command named. -/

namespace Linger.Session.Start

/-- What `start` does with a name, given whether a live session and a saved one hold it. A live
session comes first: its daemon owns the saved state too. -/
def plan (live saved : Bool) : Plan := if live then .running else if saved then .saved else .take

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
