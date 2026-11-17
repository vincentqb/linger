module

public import Linger.Session.CoreSpec
import Linger.Session.CoreCode.Wire

public section

/-! # Linger.Session.Record — what a name's end record says

A session writes its name's end record when it takes the name, before its program starts, and
again when the session ends, before it gives the name up: with how its program ended, or, when a
signal stopped its daemon, that the daemon saved the session first. While the program runs, its
daemon also writes what it last saw of the output whenever that changes, so a summary reads the
record instead of waking the daemon to ask. The record stays until the next session takes the
name, so a reader learns from it how the last session ended, however long ago (`answer`). Only a
running record needs the name held to read: whether its daemon still lives decides its answer
(`settled`).

Format: the magic `LNGE`, version 1, then 0 for a running program, 1 and the ending as
`Wire.outcomeBytes` writes it, 2 and the number of the signal that stopped the daemon, for a
session it saved, or 3, for a saved tmux pane a kill dismissed, which no program ran; or version 3,
0 and one byte of what the daemon saw (1 for a command its shell's marks say runs, 2 for new lines
in the history, 4 for a bell or a notification since the last look, and 8 times the progress its
program declared, 0 for none and 1 to 4 for ConEmu's states), for a running program whose daemon
says so. A reader from before saved sessions reads one as no record, so it answers that
the ending is unknown, and lists it resumable, and a reader from before dismissals reads one as no
record too. Version 2, whose byte said whether output was recent and whether any arrived unseen,
is read as no record, as a reader from before version 3 reads a version 3 record, so each asks the
daemon. The record says nothing of how the shell's last command
ended: that is no status, and the summary that reads the record shows statuses alone, so what it
reads is what asking would tell it (`rowStatus_published`). -/

namespace Linger.Session

namespace Record

/-- A declared progress state's number in ConEmu's report, 0 for none. -/
def progressCode : Option Terminal.Mediation.Progress → UInt8
  | none => 0
  | some .normal => 1
  | some .error => 2
  | some .indeterminate => 3
  | some .paused => 4

/-- Back from `progressCode`; any other number is no progress. -/
def progressOfCode : UInt8 → Option Terminal.Mediation.Progress
  | 1 => some .normal
  | 2 => some .error
  | 3 => some .indeterminate
  | 4 => some .paused
  | _ => none

/-- The byte of what a daemon saw: 1 for a command running, plus 2 for new lines in the history,
plus 4 for an ask, plus 8 times the declared progress's number. -/
def seenByte (seen : Seen) : UInt8 :=
  8 * progressCode seen.progress + (if seen.running then 1 else 0) +
    (if seen.unseen then 2 else 0) +
    (if seen.asks then 4 else 0)

/-- The record's bytes; `decode` reads them back (`decode_encode`). -/
def encode : Record → List UInt8
  | .running none => [0x4C, 0x4E, 0x47, 0x45, 1, 0]
  | .running (some seen) => [0x4C, 0x4E, 0x47, 0x45, 3, 0, seenByte seen]
  | .ended outcome => [0x4C, 0x4E, 0x47, 0x45, 1, 1] ++ Wire.outcomeBytes outcome
  | .saved signal => [0x4C, 0x4E, 0x47, 0x45, 1, 2, signal]
  | .dismissed => [0x4C, 0x4E, 0x47, 0x45, 1, 3]

/-- The record these bytes hold, or `none` for bytes no version 1 or 3 record has. -/
def decode : List UInt8 → Option Record
  | [0x4C, 0x4E, 0x47, 0x45, 1, 0] => some (.running none)
  | [0x4C, 0x4E, 0x47, 0x45, 3, 0, flags] =>
    if flags < 40 then
      some
        (.running
          (some ⟨progressOfCode (flags / 8), flags &&& 1 != 0, flags &&& 2 != 0, flags &&& 4 != 0⟩))
    else none
  | [0x4C, 0x4E, 0x47, 0x45, 1, 1, kind, code] => some (.ended (Wire.readOutcome [kind, code]))
  | [0x4C, 0x4E, 0x47, 0x45, 1, 2, signal] => some (.saved signal)
  | [0x4C, 0x4E, 0x47, 0x45, 1, 3] => some .dismissed
  | _ => none

/-- What a running record says its daemon saw, for a reader that would otherwise ask the daemon:
`none` for any other record, or for bytes that are no record, which leaves the reader to ask. -/
def published (bytes : List UInt8) : Option Seen :=
  match decode bytes with
  | some (.running seen) => seen
  | _ => none

/-- What a reader holding the name learns from the name's end record file: with no file, that no
session has taken the name (`none`); from an ended record, how its program ended; from a saved
record, that a signal stopped its daemon, which saved the session, and no outcome of its
program; from a dismissed record, that a kill dismissed a saved tmux pane and nothing ended; and
from a running record, whose session gave the name up without saying how it ended,
or from bytes that are no record, that its program's ending is unknown. -/
def answer : Option (List UInt8) → Option Ending
  | none => none
  | some bytes =>
    match decode bytes with
    | some (.ended outcome) => some (.program outcome)
    | some (.saved signal) => some (.saved signal)
    | some .dismissed => some .dismissed
    | _ => some (.program .unknown)

/-- What a reader learns from the record file without holding the name: `answer`'s answer when
there is no file or the record says how the session ended, which stays true until the next
session replaces the record (`settled_answer`); `none` for a running record, or bytes that are
no record, whose answer depends on whether the session's daemon still holds the name. -/
def settled : Option (List UInt8) → Option (Option Ending)
  | none => some none
  | some bytes =>
    match decode bytes with
    | some (.ended outcome) => some (some (.program outcome))
    | some (.saved signal) => some (some (.saved signal))
    | some .dismissed => some (some .dismissed)
    | _ => none

end Record

end Linger.Session
