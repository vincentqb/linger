module

public import Linger.Display.CoreSpec

public section

/-! # What selector headlines are stated in

The actions the selector takes, the state of one selection visit, the listing it shows, what one
action leads to and what keys pressed in order lead to, the moves a wrong transition clamps, and
the events its listings follow: which of them query remote hosts. -/

namespace Linger.Selector

/-- One selector action, independent of the key that requests it. -/
inductive Key where
  /-- Append a character to the query. -/
  | text (char : Char)
  /-- Delete the query's last character. -/
  | backspace
  /-- Empty the query. -/
  | clear
  /-- Move the cursor up one row, and from the first row to the last. -/
  | up
  /-- Move the cursor down one row, and from the last row to the first. -/
  | down
  /-- Move the cursor to the first row. -/
  | first
  /-- Move the cursor to the last row. -/
  | last
  /-- Act on the selected row. -/
  | accept
  /-- Leave without a choice. -/
  | cancel
  /-- Delete the character under the cursor, or end the input when the query is empty, as Ctrl-D
  does in a line editor and in fzf (`delete-char/eof`). The cursor sits after the query, where
  there is no character, so a query stays as it is. -/
  | deleteCharEof
  /-- Clear and redraw the screen, and list the sessions again, the remote hosts' included. -/
  | refresh
  deriving BEq, Repr

end Linger.Selector

namespace Linger.Selector.Picker

/-- One selection visit over the displayed snapshot's targets. -/
structure State where
  /-- Targets of the displayed snapshot. -/
  candidates : List String
  /-- The typed text that filters rows and, when nonempty, names the creation target. -/
  query : String := ""
  /-- Index of the selected row in `items`; zero when there are none. -/
  cursor : Nat := 0
  /-- Whether `items` may offer a creation row; false for read-only visits and saved
  catalogs. -/
  allowCreate : Bool := true
  /-- Each target's description, which the query matches as it matches the target. -/
  descriptions : List (String × String) := []
  deriving BEq, Repr

/-- Exact targets plus the complete metadata records that produced them. Equality
includes metadata, so a status-only change still invalidates the displayed frame. -/
structure Snapshot where
  /-- The listing's exact targets, in order and without duplicates. -/
  candidates : List String := []
  /-- Tab-split listing lines, from which the picker reads each target's metadata. -/
  records : List (List String) := []
  /-- The columns the picker lays rows out in, fixed while a visit keeps its view; none lays them
  out for these rows. -/
  layout : Option Linger.Display.Listing.Layout := none
  deriving BEq, Repr, Inhabited

/-- The result of one action: a next state, or a decision for the executor. -/
inductive Outcome where
  /-- Keep selecting from this state. -/
  | stay (state : State)
  /-- Attach to this listed target. -/
  | attach (target : String)
  /-- Create a session with exactly this target. -/
  | create (target : String)
  /-- Leave without a choice. -/
  | cancel
  deriving BEq, Repr

/-- The outcome of pressing `keys` in order from `s`, each as `step` decides it in the state the
key before it left: a key that ends the visit ends it, and the keys after it are not pressed. -/
@[expose]
def press (step : State → Key → Outcome) (s : State) : List Key → Outcome
  | [] => .stay s
  | key :: keys =>
    match step s key with
    | .stay next => press step next keys
    | outcome => outcome

/-- A wrong transition: `step` with its moves clamped, as the chooser's were before they cycled:
up stops at the first row, and down moves only onto a row Enter acts on, so it stops at the last.
The headline that the moves cycle is shown to reject it. -/
@[expose]
def clamped (step : State → Key → Outcome) (s : State) : Key → Outcome
  | .up => .stay { s with cursor := s.cursor - 1 }
  | .down =>
    match step { s with cursor := s.cursor + 1 } .accept with
    | .stay _ => .stay s
    | _ => .stay { s with cursor := s.cursor + 1 }
  | key => step s key

/-- What a chooser's listings follow: a key it reads, or a listing it starts, each second or at
once when remote rows are due. -/
inductive Event where
  /-- The chooser read a key that requests this action. -/
  | key (key : Key)
  /-- The chooser starts a listing. -/
  | list
  deriving BEq, Repr

/-- Whether an event is a key the chooser read, rather than a listing it starts. -/
@[expose]
def Event.isKey : Event → Bool
  | .key _ => true
  | .list => false

/-- Whether a listing the chooser starts after `events`, since it opened, queries remote hosts,
as `next` decides after each event from whether they were due before it: they are when the
chooser opens. -/
@[expose]
def due (next : Bool → Event → Bool) (events : List Event) : Bool := events.foldl next true

/-- A wrong part: a chooser that reads a list of its own, one session `mine`, whatever the listing
it runs prints. -/
@[expose]
def ownList (_ : String) : Except String Snapshot :=
  .ok { candidates := ["mine"], records := [["name", "mine"]] }

end Linger.Selector.Picker
