module

public import Tools.Key
public import Tools.Fuzzy
public import Linger.Core.Name
public import Linger.Core.Listing

public section

/-! Pure selection over validated listing snapshots.

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

/-- Exact targets plus the complete metadata records that produced them. Equality
includes metadata, so a status-only change still invalidates the displayed frame. -/
structure Snapshot where
  candidates : List String := []
  records : List (List String) := []
  deriving BEq, Repr, Inhabited

/-- The target parser validates the whole output before metadata is published.
Consecutive name records and blank-separated records both delimit sessions. -/
def parseSnapshot (text : String) : Except String Snapshot :=
  (parseListing text).map fun candidates =>
    { candidates, records := (text.splitOn "\n").map (·.splitOn "\t") }

/-- Locate one validated identity without reinterpreting or normalizing its host.
The next name or blank record ends its metadata; missing status remains unknown. -/
def Snapshot.row (snapshot : Snapshot) (target : String) : List (String × String) :=
  let records := snapshot.records.dropWhile (· != ["name", target])
  ("name", target) ::
    (records.tail.takeWhile fun fields => fields != [""] && fields.head? != some "name").filterMap
      fun fields =>
      match fields with
      | [key, value] => some (key, value)
      | _ => none

def visible (candidates : List String) (query : String) : List String :=
  candidates.filter (Tools.Picker.matches query)

inductive Item where
  | existing (target : String)
  | create (target : String)
  deriving BEq, Repr

def Item.target : Item → String
  | .existing target | .create target => target

/-- Existing rows use the listing's entire presentation. Creation keeps its
explicit label and exact target, and has no invented session status. -/
def presentation (snapshot : Snapshot) (nameCol : Nat) : Item → List Linger.Core.Listing.RowPiece
  | .existing target => Linger.Core.Listing.rowPieces nameCol (snapshot.row target)
  | .create target => [{ text := s!"+ Create {target}".toList }]

/-- A displayed scalar keeps its shared row style independently of query emphasis. -/
structure HighlightedChar where
  char : Char
  status : Option Linger.Core.Status.Status
  matched : Bool
  deriving BEq, Repr

private def markPiece (marks : Array Bool) (piece : Linger.Core.Listing.RowPiece) :
    List HighlightedChar :=
  piece.text.zipIdx.map fun (char, index) =>
    { char, status := piece.status,
      matched :=
        match piece.nameSpan with
        | none => false
        | some (start, count) =>
          index ≥ start && index - start < count && marks[index - start]?.getD false }

/-- Align only existing names. The shared presentation supplies the name span;
every character and status survives, including on the unmarked creation row. -/
def highlightedPresentation (snapshot : Snapshot) (nameCol : Nat) (query : String) (item : Item) :
    List HighlightedChar :=
  let marks : List Bool :=
    match item with
    | .existing target => ((Tools.Fuzzy.align query target).map (·.marks)).getD []
    | .create _ => []
  (presentation snapshot nameCol item).flatMap (markPiece marks.toArray)

/-- A zero-width mark shares the preceding cell's pen. Carry its match back to
the base before printing; a backward pass visits every scalar once. -/
def emphasizeCells : List HighlightedChar → List HighlightedChar
  | [] => []
  | char :: chars =>
    let tail := emphasizeCells chars
    { char with
        matched :=
          char.matched ||
            tail.head?.any
              (fun next => Linger.Core.Vt.charWidth next.char == 0 && next.matched) } ::
      tail

/-- Existing matches come first. Creation, when enabled, is explicit and never
rewrites the query. Saved catalogs disable it entirely. -/
def items (candidates : List String) (query : String) (allowCreate : Bool := true) : List Item :=
  let target := if query.isEmpty then Linger.Core.Name.defaultName else query
  (visible candidates query).map Item.existing ++
    if allowCreate && validTarget target && !candidates.contains target then [.create target]
    else []

structure State where
  candidates : List String
  query : String := ""
  cursor : Nat := 0
  allowCreate : Bool := true
  deriving BEq, Repr

def maxQueryLength : Nat := 256

/-- A zero cursor represents an empty result; otherwise it indexes a selectable row. -/
def State.Valid (s : State) : Prop :=
  s.cursor ≤ (items s.candidates s.query s.allowCreate).length - 1 ∧ s.query.length ≤ maxQueryLength

def init (candidates : List String) (allowCreate : Bool := true) : State :=
  { candidates, allowCreate }

def selected (s : State) : Option Item := (items s.candidates s.query s.allowCreate)[s.cursor]?

/-- Keep the selected target across snapshots, even when its creation row becomes
an existing session. A vanished target leaves the cursor clamped in place. -/
def refresh (s : State) (candidates : List String) : State :=
  let choices := items candidates s.query s.allowCreate
  let target := (selected s).map Item.target
  let cursor :=
    (choices.findIdx? (fun item => some item.target == target)).getD
      (min s.cursor (choices.length - 1))
  { s with
    candidates, cursor }

inductive Outcome where
  | stay (state : State)
  | attach (target : String)
  | create (target : String)
  | cancel
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
  | .down =>
    .stay
      { s with
        cursor := min (s.cursor + 1) ((items s.candidates s.query s.allowCreate).length - 1) }
  | .first => .stay { s with cursor := 0 }
  | .last => .stay { s with cursor := (items s.candidates s.query s.allowCreate).length - 1 }
  | .accept =>
    match selected s with
    | some (.existing target) => .attach target
    | some (.create target) => .create target
    | none => .stay s
  | .cancel => .cancel

end Tools.Picker
