module

public import Tools.Key
public import Linger.Core.Name

public section

/-! Pure selection over one successful listing snapshot.

Matching folds ASCII capitals with `Char.toLower`; it performs neither Unicode
case folding nor normalization. Results retain listing order and original target
strings. A separate labelled row offers creation of the exact valid query,
or the shared attach default when the query is empty.
-/

namespace Tools.Picker

def «matches» (query target : String) : Bool :=
  (query.toList.map Char.toLower).isSublist (target.toList.map Char.toLower)

/-- Exclude C0, DEL and C1 controls from both display targets and query text. -/
private def printable (char : Char) : Bool :=
  char.toNat ≥ 32 && (char.toNat < 127 || char.toNat ≥ 160)

/-- The local name must already be canonical; the host suffix remains exact. -/
private def validTarget (target : String) : Bool :=
  let parts := target.splitOn "@"
  let name := parts.headD ""
  !target.isEmpty && Linger.Core.Name.sanitize name == name && target.toList.all printable &&
    (parts.tail.isEmpty || !(String.intercalate "@" parts.tail).isEmpty)

private def parseRow (fields : List String) : Except String (Option String) :=
  if fields.head? != some "name" then .ok none
  else
    match fields with
    | [_, target] =>
      if validTarget target then .ok (some target) else .error "invalid session target in listing"
    | _ => .error "malformed name record in listing"

private def parseRows (seen rows : List String) : Except String (List String) :=
  match rows with
  | [] => .ok []
  | row :: rows =>
    match parseRow (row.splitOn "\t") with
    | .error error => .error error
    | .ok none => parseRows seen rows
    | .ok (some target) =>
      if seen.contains target then .error "duplicate session target in listing"
      else (parseRows (target :: seen) rows).map (target :: ·)

/-- Validate the complete successful command output before presenting any target.
Metadata is ignored; malformed name records or duplicates reject the whole snapshot. -/
def parseListing (text : String) : Except String (List String) := parseRows [] (text.splitOn "\n")

def visible (candidates : List String) (query : String) : List String :=
  candidates.filter (Tools.Picker.matches query)

inductive Item where
  | existing (target : String)
  | create (target : String)
  deriving BEq, Repr

/-- Existing matches come first. Creation is explicit and never rewrites the query. -/
def items (candidates : List String) (query : String) : List Item :=
  let target := if query.isEmpty then Linger.Core.Name.defaultName else query
  (visible candidates query).map Item.existing ++
    if validTarget target && !candidates.contains target then [.create target] else []

structure State where
  candidates : List String
  query : String := ""
  cursor : Nat := 0
  deriving BEq, Repr

def maxQueryLength : Nat := 256

/-- A zero cursor represents an empty result; otherwise it indexes a selectable row. -/
def State.Valid (s : State) : Prop :=
  s.cursor ≤ (items s.candidates s.query).length - 1 ∧ s.query.length ≤ maxQueryLength

def init (candidates : List String) : State := { candidates }

def selected (s : State) : Option Item := (items s.candidates s.query)[s.cursor]?

inductive Outcome where
  | stay (state : State)
  | attach (target : String)
  | create (target : String)
  | cancel
  | refresh
  deriving BEq, Repr

/-- Editing resets the cursor. Navigation clamps; acceptance acts on the selected
row. No selectable row stays editable. Effects remain the caller's job. -/
def step (s : State) (key : Tools.Key) : Outcome :=
  match key with
  | .text char =>
    if printable char && s.query.length < maxQueryLength then
      .stay
        { s with
          query := s.query.push char, cursor := 0 }
    else .stay s
  | .backspace =>
    .stay
      { s with
        query := String.ofList s.query.toList.dropLast, cursor := 0 }
  | .clear =>
    .stay
      { s with
        query := "", cursor := 0 }
  | .up => .stay { s with cursor := s.cursor - 1 }
  | .down => .stay { s with cursor := min (s.cursor + 1) ((items s.candidates s.query).length - 1) }
  | .first => .stay { s with cursor := 0 }
  | .last => .stay { s with cursor := (items s.candidates s.query).length - 1 }
  | .accept =>
    match selected s with
    | some (.existing target) => .attach target
    | some (.create target) => .create target
    | none => .stay s
  | .cancel => .cancel
  | .refresh => .refresh

end Tools.Picker
