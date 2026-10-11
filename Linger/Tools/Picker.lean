module

public import Linger.Tools.Key
import Linger.Tools.Fuzzy
import Linger.Core.Name
public import Linger.Core.Listing
import Linger.Core.Remote
import Linger.Core.Vt

public section

/-! Pure selection over validated listing snapshots.

Matching folds ASCII capitals with `Char.toLower`; it performs neither Unicode
case folding nor normalization. Results retain listing order and original target
strings. A separate labelled row offers creation of the exact valid query,
or the default session name when the query is empty.
-/

namespace Linger.Tools.Picker

/-- Whether the query is a subsequence of the target after ASCII lowercase folding:
exactly the targets `Fuzzy.align` can align (`align_isSome_iff_matches`). -/
def «matches» (query target : String) : Bool :=
  (query.toList.map Char.toLower).isSublist (target.toList.map Char.toLower)

private def parseRow (fields : List String) : Except String (Option String) :=
  if fields.head? != some "name" then .ok none
  else
    match fields with
    | [_, target] =>
      if Linger.Core.Remote.targetValid target then .ok (some target)
      else .error "invalid session target in listing"
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
  /-- The listing's exact targets, in order and without duplicates. -/
  candidates : List String := []
  /-- Tab-split listing lines, from which `Snapshot.row` reads each target's metadata. -/
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

/-- Remote rows are named `name@host`. A local session name never contains `@`
(`Name.okChar`), so the character partitions every listing's rows. -/
def remoteTarget (target : String) : Bool := target.toList.contains '@'

/-- The records of the rows whose target satisfies `keep`, in order. A name record
governs itself and the records after it up to the next name record; records before
every name record follow `current`. -/
def rowRecords (keep : String → Bool) : Bool → List (List String) → List (List String)
  | _, [] => []
  | current, fields :: rest =>
    let current := if fields.head? == some "name" then keep (fields[1]?.getD "") else current
    if current then fields :: rowRecords keep current rest else rowRecords keep current rest

/-- Local rows from `latest` and remote rows from `full`, the latest listing that
queried remote hosts, so a local-only listing refreshes local rows without
discarding remote ones. Local rows come first, as `ls -r` lists them. -/
def Snapshot.withRemote (latest full : Snapshot) : Snapshot where
  candidates := latest.candidates.filter (!remoteTarget ·) ++ full.candidates.filter remoteTarget
  records :=
    rowRecords (!remoteTarget ·) true latest.records ++ rowRecords remoteTarget false full.records

/-- The candidates the query matches, in listing order. -/
def visible (candidates : List String) (query : String) : List String :=
  candidates.filter (Linger.Tools.Picker.matches query)

/-- A selectable row: a listed target or the explicit creation choice. -/
inductive Item where
  /-- A target from the listing. -/
  | existing (target : String)
  /-- Creation of a session with exactly this target. -/
  | create (target : String)
  deriving BEq, Repr

/-- The exact target the row attaches to or creates. -/
def Item.target : Item → String
  | .existing target | .create target => target

/-- Existing rows use the listing's entire presentation. Creation keeps its
explicit label and exact target, and has no invented session status. -/
def presentation (snapshot : Snapshot) (nameCol : Nat) : Item → List Linger.Core.Listing.RowPiece
  | .existing target => Linger.Core.Listing.rowPieces nameCol (snapshot.row target)
  | .create target => [{ text := s!"+ Create {target}".toList }]

/-- A displayed scalar keeps its shared row style independently of query emphasis. -/
structure HighlightedChar where
  /-- One displayed Unicode scalar. -/
  char : Char
  /-- The status whose badge style it carries; none outside the badge. -/
  status : Option Linger.Core.Status.Status
  /-- Whether it receives query emphasis. -/
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
    | .existing target => ((Linger.Tools.Fuzzy.align query target).map (·.marks)).getD []
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
    if allowCreate && Linger.Core.Remote.targetValid target && !candidates.contains target then
      [.create target]
    else []

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
  deriving BEq, Repr

/-- Typing stops extending the query at this many Unicode scalars. -/
def maxQueryLength : Nat := 256

/-- A zero cursor represents an empty result; otherwise it indexes a selectable row. -/
def State.Valid (s : State) : Prop :=
  s.cursor ≤ (items s.candidates s.query s.allowCreate).length - 1 ∧ s.query.length ≤ maxQueryLength

/-- A state over these candidates with an empty query and the cursor on the first row. -/
def init (candidates : List String) (allowCreate : Bool := true) : State :=
  { candidates, allowCreate }

/-- The row under the cursor, or none when the cursor indexes no row. -/
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

/-- Editing resets the cursor. Navigation clamps; acceptance acts on the selected
row. No selectable row stays editable. Effects remain the caller's job. -/
def step (s : State) (key : Linger.Tools.Key) : Outcome :=
  match key with
  | .text char =>
    if Linger.Tools.Input.printable char && s.query.length < maxQueryLength then
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

end Linger.Tools.Picker
