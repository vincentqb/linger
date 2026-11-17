module

public import Linger.Display.CoreSpec
import Terminal.CoreCode.Title

public section

/-! # Linger.Display.Alert — another session's ask, told to the terminal of a client attached

**An alert says once that a session changed into asking.** A client attached to one session
samples the others' attention for its title once a second; from one sample to the next it names
exactly the sessions whose attention changed into asking, `⚑`, whatever their state, other than its own, whose bell and
notifications already reach its terminal, and none on the first sample, whose asks the title
counts (`announce_changes`). Each is told as one OSC 9 desktop notification, the name and the
session's notification text, or `bell`, as clean text (`notification_clean`). -/

namespace Linger.Display.Alert

open Linger.Display.Status (Attention)

/-- The sessions to tell of after a sample, from the previous one: those that ask in `current`
and did not in `previous`, other than `own`, in `current`'s order; none on the first sample,
when there is no previous one. -/
def announce (previous : Option (List (String × Attention))) (current : List (String × Attention))
    (own : String) : List String :=
  match previous with
  | none => []
  | some before =>
    (current.filter fun row => row.2 == .asked && row.1 != own && !before.contains row).map (·.1)

/-- What a notification of session `name`'s ask says: its name, then its notification's text,
or `bell` when it rang the bell, cleaned as a title is and held to a title's length. -/
def text (name notice : String) : List Char :=
  Terminal.Title.payload s!"{name}: {if notice.isEmpty then "bell" else notice}"

/-- The desktop notification that tells a terminal session `name` asks: one OSC 9, ended by ST. -/
def notification (name notice : String) : List UInt8 := (Piece.notify (text name notice)).bytes

end Linger.Display.Alert
