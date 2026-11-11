module

import Input
public import Linger.Selector.Spec
import Fuzzy
import Linger.Target.Name
import Linger.Display.Listing
public import Linger.Display.Spec
import Linger.Display.Status
import Linger.Target.Remote
import Terminal.Vt
import Terminal.Render
import Linger.Display.View

public section

/-! Pure selection over validated listing snapshots.

Matching folds ASCII capitals with `Char.toLower`; it performs neither Unicode
case folding nor normalization. Results retain listing order and original target
strings. A separate labelled row offers creation of the exact valid query,
or the default session name when the query is empty.
-/

namespace Linger.Selector.Picker

/-- Whether the query is a subsequence of the target after ASCII lowercase folding:
exactly the targets `Fuzzy.align` can align (`align_isSome_iff_matches`). -/
private def «matches» (query target : String) : Bool :=
  (query.toList.map Char.toLower).isSublist (target.toList.map Char.toLower)

private def parseRow (fields : List String) : Except String (Option String) :=
  if fields.head? != some "name" then .ok none
  else
    match fields with
    | [_, target] =>
      if Linger.Target.Remote.targetValid target then .ok (some target)
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
private def parseListing (text : String) : Except String (List String) :=
  parseRows [] (text.splitOn "\n")

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
private def remoteTarget (target : String) : Bool := target.toList.contains '@'

/-- The records of the rows whose target satisfies `keep`, in order. A name record
governs itself and the records after it up to the next name record; records before
every name record follow `current`. -/
private def rowRecords (keep : String → Bool) : Bool → List (List String) → List (List String)
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
private def visible (candidates : List String) (query : String) : List String :=
  candidates.filter (Linger.Selector.Picker.matches query)

/-- A selectable row: a listed target or the explicit creation choice. -/
inductive Item where
  /-- A target from the listing. -/
  | existing (target : String)
  /-- Creation of a session with exactly this target. -/
  | create (target : String)
  deriving BEq, Repr

/-- The exact target the row attaches to or creates. -/
private def Item.target : Item → String
  | .existing target | .create target => target

/-- Existing rows use the listing's entire presentation. Creation keeps its
explicit label and exact target, and has no invented session status. -/
private def presentation (snapshot : Snapshot) (nameCol : Nat) :
    Item → List Linger.Display.Listing.RowPiece
  | .existing target => Linger.Display.Listing.rowPieces nameCol (snapshot.row target)
  | .create target => [{ text := s!"+ Create {target}".toList }]

/-- A displayed scalar keeps its shared row style independently of query emphasis. -/
structure HighlightedChar where
  /-- One displayed Unicode scalar. -/
  char : Char
  /-- The status whose badge style it carries; none outside the badge. -/
  status : Option Linger.Display.Status.Status
  /-- Whether it receives query emphasis. -/
  matched : Bool
  deriving BEq, Repr

private def markPiece (marks : Array Bool) (piece : Linger.Display.Listing.RowPiece) :
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
    | .existing target => ((Fuzzy.align query target).map (·.marks)).getD []
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
            tail.head?.any (fun next => Terminal.Vt.charWidth next.char == 0 && next.matched) } ::
      tail

/-- Existing matches come first. Creation, when enabled, is explicit and never
rewrites the query. Saved catalogs disable it entirely. -/
def items (candidates : List String) (query : String) (allowCreate : Bool := true) : List Item :=
  let target := if query.isEmpty then Linger.Target.Name.defaultName else query
  (visible candidates query).map Item.existing ++
    if allowCreate && Linger.Target.Remote.targetValid target && !candidates.contains target then
      [.create target]
    else []

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

/-- Editing resets the cursor. Navigation clamps; acceptance acts on the selected
row. No selectable row stays editable. Effects remain the caller's job. -/
def step (s : State) (key : Linger.Selector.Key) : Outcome :=
  match key with
  | .text char =>
    if Input.printable char && s.query.length < maxQueryLength then
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

/-- How many listed rows the query matches: what the query line shows beside it. -/
def matchCount (s : State) : Nat := (visible s.candidates s.query).length

/-- What a picker shows, as lines of text pieces with their styles, for a terminal `rows` tall
(a style is the parameters of the SGR sequences that select it, in order):
the header, which counts every listed row and, with `statusOf`, those that ask for someone
(`View.headerParts`); the query, with how many rows it matches; the rows around the cursor; a
line that sums up the matching rows the window leaves out (`View.hidden`); and the keys. It
never has more lines than the terminal (`frameLines_length`). -/
def frameLines (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (rows : Nat) : List (List (String × List (List Nat))) :=
  let height := max 1 rows
  let choices := items state.candidates state.query state.allowCreate
  let nameCol :=
    Linger.Display.Listing.nameWidth (snapshot.candidates.map fun target => [("name", target)])
  let labels := if savedTmux then ["tmux save"] else if state.allowCreate then [] else ["read-only"]
  let title : List (List (String × List (List Nat))) :=
    if height ≥ 7 then
      -- the counts once there is a listing to count
      let header :=
        "  " ++
          String.intercalate " · "
            (if loaded then
              Linger.Display.View.headerParts labels (snapshot.candidates.map statusOf)
            else "linger" :: labels)
      let globals := snapshot.records.takeWhile (fun fields => fields.head? != some "name")
      let metadata : List String :=
        if savedTmux then
          (globals.filterMap fun fields =>
                match fields with
                | ["source", value] => some s!"  source  {value}"
                | ["saved", value] => some s!"  saved   {value}"
                | _ => none).take
            (height - 7)
        else []
      [[(header, [])]] ++ metadata.map (fun text => [(text, [[2]])]) ++ [[]]
    else []
  let query : List (List (String × List (List Nat))) :=
    if height > 1 then
      let placeholder :=
        if savedTmux then "Find a saved pane"
        else if state.allowCreate then "Find or create a session" else "Find a session"
      let line :=
        if state.query.isEmpty then [("  › ", []), (placeholder, [[2]])]
        else [("  › ", []), (state.query, []), (s!" {matchCount state}", [[2]])]
      [line] ++ if height ≥ 6 then [[]] else []
    else []
  let footerRows := if height ≥ 6 then 2 else if height > 2 then 1 else 0
  let slots := max 1 (height - (title.length + query.length) - footerRows)
  let body : List (List (String × List (List Nat))) :=
    if !loaded then
      [[(if savedTmux then "  Loading saved panes…" else "  Loading sessions…", [[2]])]]
    else
      if choices.isEmpty then
        [[(if savedTmux then "  No matching saved panes"
              else if state.allowCreate then "  No valid target" else "  No matching sessions",
              [[2]])]]
      else
        -- the matching rows a window this short leaves out are summed up on its last line
        let summarize := slots ≥ 2 && choices.length > slots
        let shown := if summarize then slots - 1 else slots
        let start := state.cursor + 1 - shown
        let window :=
          ((choices.drop start).take shown).zipIdx start |>.map fun (item, index) =>
            let chosen := index == state.cursor
            let selection := if chosen then [[7]] else []
            (if chosen then "  ▸ " else "    ", selection) ::
              (emphasizeCells (highlightedPresentation snapshot nameCol state.query item)).map
                fun char =>
                (String.singleton char.char,
                  selection ++
                    (if withColor then char.status.toList.map Linger.Display.Status.style
                    else []) ++
                    if char.matched then [[4]] else [])
        let left :=
          (choices.take start ++ choices.drop (start + shown)).filterMap fun item =>
            match item with
            | .existing target => some target
            | .create _ => none
        let (count, named) := Linger.Display.View.hidden left
        let summary :=
          s!"    … {count} more" ++
            if named.isEmpty then ""
            else ": " ++ String.intercalate " · " (named.map fun (key, n) => s!"{key} {n}")
        window ++ if summarize && !left.isEmpty then [[(summary, [[2]])]] else []
  let footer : List (List (String × List (List Nat))) :=
    if height > 2 then
      let action :=
        if !loaded then "  Type to search"
        else
          match selected state with
          | some (.existing _) =>
            if savedTmux then "  ↵ import / attach"
            else if state.allowCreate then "  ↵ attach" else "  ↵ view"
          | some (.create _) => "  ↵ create"
          | none => if state.allowCreate then "  Type a valid name" else "  Type to search"
      (if height ≥ 6 then [[]] else []) ++ [[(s!"{action}  ·  ↑↓ move  ·  esc / ^C quit", [[2]])]]
    else []
  (title ++ query ++ body ++ footer).take height

/-- A character as a frame shows it: itself when a terminal prints it, `?` otherwise. -/
private def frameChar (raw : Char) : Char := if Input.printable raw then raw else '?'

/-- The characters of one run of a frame line that fit `width` cells after `used` of them are
taken, each as `frameChar` shows it: their bytes, the cells now used, and whether the run was
cut short. -/
private def frameChars (width : Nat) : Nat → List Char → List UInt8 × Nat × Bool
  | used, [] => ([], used, false)
  | used, raw :: rest =>
    if used + Terminal.Vt.charWidth (frameChar raw) > width then ([], used, true)
    else
      let more := frameChars width (used + Terminal.Vt.charWidth (frameChar raw)) rest
      (String.utf8EncodeChar (frameChar raw) ++ more.1, more.2)

/-- What a frame writes to put `style` in effect after `active`: nothing when they are the
same, else an SGR reset and then the style's sequences. -/
private def frameSwitch (active style : List (List Nat)) : List UInt8 :=
  if style != active then ([0] :: style).flatMap Linger.Display.Listing.sgr else []

/-- The runs of one frame line from the given cells used and style in effect: each run in its
style, until a run is cut short. The bytes, and the style in effect at the end. -/
private def framePieces (width : Nat) :
    Nat → List (List Nat) → List (String × List (List Nat)) → List UInt8 × List (List Nat)
  | _, active, [] => ([], active)
  | used, active, run :: rest =>
    let chars := frameChars width used run.1.toList
    if chars.2.2 then (frameSwitch active run.2 ++ chars.1, run.2)
    else
      let more := framePieces width chars.2.1 run.2 rest
      (frameSwitch active run.2 ++ chars.1 ++ more.1, more.2)

/-- One frame line, within `width` cells, its style reset at its end. -/
private def frameLine (width : Nat) (line : List (String × List (List Nat))) : List UInt8 :=
  let body := framePieces width 0 [] line
  body.1 ++ if body.2.isEmpty then [] else Linger.Display.Listing.sgr [0]

/-- The picker frame's terminal bytes: reset the pen, home the cursor, clear the screen, then
the lines of `frameLines` separated by CR LF. Each line keeps the final column unused, so
neither a full-width name nor a resize induces an automatic line wrap. -/
def frame (state : State) (snapshot : Snapshot) (statusOf : String → Linger.Display.Status.Status)
    (loaded withColor savedTmux : Bool) (cols rows : Nat) : List UInt8 :=
  Linger.Display.Listing.sgr [0] ++ Terminal.Render.csiPlain 0x48 ++
    Terminal.Render.csiNum 2 0x4A ++
    (((frameLines state snapshot statusOf loaded withColor savedTmux rows).map
            (frameLine (cols - 1))).intersperse
        Terminal.Render.crlfB).flatten

/-- What the picker writes when it takes the terminal: the alternate screen, the cursor
hidden, bracketed paste on. -/
def enterAnsi : List UInt8 :=
  Terminal.Render.modeSet 1049 true ++ Terminal.Render.modeSet 25 false ++
    Terminal.Render.modeSet 2004 true

/-- What the picker writes when it gives the terminal back: the pen reset, bracketed paste
off, the cursor shown, the main screen. -/
def exitAnsi : List UInt8 :=
  Linger.Display.Listing.sgr [0] ++ Terminal.Render.modeSet 2004 false ++
    Terminal.Render.modeSet 25 true ++
    Terminal.Render.modeSet 1049 false

end Linger.Selector.Picker
