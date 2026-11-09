module

public import Linger.Session.Spec
import Linger.Session.Wire

public section

/-! # Linger.Session.Record — what a name's end record says

A session writes its name's end record when it takes the name, before its program starts, and
again when the program ends, with how it ended, before it gives the name up. While the program
runs, its daemon also writes what it last saw of the output whenever that changes, so a summary
reads the record instead of waking the daemon to ask. The record stays until the next session
takes the name, so a reader learns from it how the last session's program ended, however long
ago (`answer`). Only a running record needs the name held to read: whether its daemon still
lives decides its answer (`settled`).

Format: the magic `LNGE`, version 1, then 0 for a running program, or 1 and the ending as
`Wire.outcomeBytes` writes it; or version 2, 0 and one byte of what the daemon saw (1 for fresh
output, 2 for unseen output), for a running program whose daemon says so. -/

namespace Linger.Session

/-- What a daemon last saw of its program's output: whether output is fresh (`⣷`), and whether
some arrived since the session was last looked at (`⣿`), as `info` reports `fresh` and
`unseen`. -/
structure Seen where
  /-- Output within the freshness window. -/
  fresh : Bool
  /-- Output since the session was last looked at. -/
  unseen : Bool
  deriving Repr, DecidableEq

/-- What a name's end record says. -/
inductive Record where
  /-- A session took the name, and its program had not ended when this was written; with
  `seen`, what its daemon then saw of the output. -/
  | running (seen : Option Seen)
  /-- The program of the session that last held the name ended this way. -/
  | ended (outcome : Outcome)
  deriving Repr, DecidableEq

namespace Record

/-- The byte of what a daemon saw: 1 for fresh output, plus 2 for unseen output. -/
def seenByte (seen : Seen) : UInt8 := (if seen.fresh then 1 else 0) + (if seen.unseen then 2 else 0)

/-- The record's bytes; `decode` reads them back (`decode_encode`). -/
def encode : Record → List UInt8
  | .running none => [0x4C, 0x4E, 0x47, 0x45, 1, 0]
  | .running (some seen) => [0x4C, 0x4E, 0x47, 0x45, 2, 0, seenByte seen]
  | .ended outcome => [0x4C, 0x4E, 0x47, 0x45, 1, 1] ++ Wire.outcomeBytes outcome

/-- The record these bytes hold, or `none` for bytes no version 1 or 2 record has. -/
def decode : List UInt8 → Option Record
  | [0x4C, 0x4E, 0x47, 0x45, 1, 0] => some (.running none)
  | [0x4C, 0x4E, 0x47, 0x45, 2, 0, flags] =>
    if flags < 4 then some (.running (some ⟨flags &&& 1 != 0, flags &&& 2 != 0⟩)) else none
  | [0x4C, 0x4E, 0x47, 0x45, 1, 1, kind, code] => some (.ended (Wire.readOutcome [kind, code]))
  | _ => none

/-- What a running record says its daemon saw, for a reader that would otherwise ask the daemon:
`none` for any other record, or for bytes that are no record, which leaves the reader to ask. -/
def published (bytes : List UInt8) : Option Seen :=
  match decode bytes with
  | some (.running seen) => seen
  | _ => none

/-- What a reader holding the name learns from the name's end record file: with no file, that no
session has taken the name (`none`); from an ended record, how its program ended; and from a
running record, whose session gave the name up without saying how its program ended, or from
bytes that are no record, that the ending is unknown. -/
def answer : Option (List UInt8) → Option Outcome
  | none => none
  | some bytes =>
    match decode bytes with
    | some (.ended outcome) => some outcome
    | _ => some .unknown

/-- What a reader learns from the record file without holding the name: `answer`'s answer when
there is no file or the record says how its program ended, which stays true until the next
session replaces the record (`settled_answer`); `none` for a running record, or bytes that are
no record, whose answer depends on whether the session's daemon still holds the name. -/
def settled : Option (List UInt8) → Option (Option Outcome)
  | none => some none
  | some bytes =>
    match decode bytes with
    | some (.ended outcome) => some (some outcome)
    | _ => none

end Record

end Linger.Session
