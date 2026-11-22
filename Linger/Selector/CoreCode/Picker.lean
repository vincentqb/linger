module

import Input.CoreCode
public import Linger.Selector.CoreSpec
import Fuzzy.CoreCode
import Linger.Target.CoreCode.Name
import Linger.Display.CoreCode.Listing
public import Linger.Display.CoreSpec
import Linger.Display.CoreCode.Status
import Linger.Target.CoreCode.Remote
import Terminal.CoreCode.Vt
import Terminal.CoreCode.Render
import Linger.Display.CoreCode.View

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

/-- A listing line's fields: its text between tabs. -/
def lineFields (line : String) : List String := (line.toList.splitOn '\t').map String.ofList

/-- A listing's lines: its text between newlines. -/
def listingLines (text : String) : List String := (text.toList.splitOn '\n').map String.ofList

private def parseRows (seen rows : List String) : Except String (List String) :=
  match rows with
  | [] => .ok []
  | row :: rows =>
    match parseRow (lineFields row) with
    | .error error => .error error
    | .ok none => parseRows seen rows
    | .ok (some target) =>
      if seen.contains target then .error "duplicate session target in listing"
      else (parseRows (target :: seen) rows).map (target :: ·)

/-- Validate the complete successful command output before presenting any target.
Metadata is ignored; malformed name records or duplicates reject the whole snapshot. -/
private def parseListing (text : String) : Except String (List String) :=
  parseRows [] (listingLines text)

/-- The target parser validates the whole output before metadata is published.
Consecutive name records and blank-separated records both delimit sessions. -/
def parseSnapshot (text : String) : Except String Snapshot :=
  (parseListing text).map fun candidates =>
    { candidates, records := (listingLines text).map lineFields }

/-- A listing line's fields as a field of a row: a key and a value, or none. -/
def fieldPair : List String → Option (String × String)
  | [key, value] => some (key, value)
  | _ => none

/-- Locate one validated identity without reinterpreting or normalizing its host.
The next name or blank record ends its metadata; missing status remains unknown. -/
def Snapshot.row (snapshot : Snapshot) (target : String) : List (String × String) :=
  let records := snapshot.records.dropWhile (· != ["name", target])
  ("name", target) ::
    (records.tail.takeWhile fun fields => fields != [""] && fields.head? != some "name").filterMap
      fieldPair

/-- The columns of a view of the snapshot's rows (`Listing.layoutOf`). -/
def Snapshot.laidOut (snapshot : Snapshot) : Linger.Display.Listing.Layout :=
  Linger.Display.Listing.layoutOf (snapshot.candidates.map snapshot.row)

/-- The snapshot with its columns fixed: `kept`'s, the name column grown to fit its names, since
a name is never cut, or, with none kept, its own rows' (`laidOut`). -/
def Snapshot.keepColumns (snapshot : Snapshot) (kept : Option Linger.Display.Listing.Layout) :
    Snapshot :=
  { snapshot with
    layout :=
      some
        (match kept with
        | some layout => { layout with nameCol := max layout.nameCol snapshot.laidOut.nameCol }
        | none => snapshot.laidOut) }

/-- Each target's description: the field `description` of its row. -/
def Snapshot.descriptions (snapshot : Snapshot) : List (String × String) :=
  snapshot.candidates.filterMap fun target =>
    ((snapshot.row target).lookup "description").map (target, ·)

/-- The snapshot whose rows show a foreground directory under `home` with `~`, as `ls` shows
it. -/
def Snapshot.atHome (home : String) (snapshot : Snapshot) : Snapshot :=
  { snapshot with
    records :=
      snapshot.records.map fun fields =>
        if fields.head? == some "fgdir" then
          ["fgdir", Linger.Display.Listing.tilde home (fields[1]?.getD "")]
        else fields }

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

/-- Whether the query finds a target: it matches the target, or the target's description. -/
private def found (descriptions : List (String × String)) (query target : String) : Bool :=
  Linger.Selector.Picker.matches query target ||
    Linger.Selector.Picker.matches query ((descriptions.lookup target).getD "")

/-- The candidates the query finds, by name or description, in listing order. -/
private def visible (candidates : List String) (query : String)
    (descriptions : List (String × String) := []) : List String :=
  candidates.filter (found descriptions query)

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
private def presentation (snapshot : Snapshot) (layout : Linger.Display.Listing.Layout) :
    Item → List Linger.Display.Listing.RowPiece
  | .existing target => Linger.Display.Listing.rowPieces layout (snapshot.row target)
  | .create target => [{ text := s!"+ Create {target}".toList }]

/-- A displayed scalar keeps its shared row style independently of query emphasis. -/
structure HighlightedChar where
  /-- One displayed Unicode scalar. -/
  char : Char
  /-- The SGR parameters of the badge style it carries; none outside the badges. -/
  style : Option (List Nat)
  /-- Whether it receives query emphasis. -/
  matched : Bool
  deriving BEq, Repr

private def markPiece (marks : Array Bool) (piece : Linger.Display.Listing.RowPiece) :
    List HighlightedChar :=
  piece.text.zipIdx.map fun (char, index) =>
    { char, style := piece.style,
      matched :=
        match piece.nameSpan with
        | none => false
        | some (start, count) =>
          index ≥ start && index - start < count && marks[index - start]?.getD false }

/-- Align only existing names. The shared presentation supplies the name span;
every character and status survives, including on the unmarked creation row. -/
def highlightedPresentation (snapshot : Snapshot) (layout : Linger.Display.Listing.Layout)
    (query : String) (item : Item) : List HighlightedChar :=
  let marks : List Bool :=
    match item with
    | .existing target => ((Fuzzy.align query target).map (·.marks)).getD []
    | .create _ => []
  (presentation snapshot layout item).flatMap (markPiece marks.toArray)

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
def items (candidates : List String) (query : String) (allowCreate : Bool := true)
    (descriptions : List (String × String) := []) : List Item :=
  let target := if query.isEmpty then Linger.Target.Name.defaultName else query
  (visible candidates query descriptions).map Item.existing ++
    if allowCreate && Linger.Target.Remote.targetValid target && !candidates.contains target then
      [.create target]
    else []

/-- Typing stops extending the query at this many Unicode scalars. -/
def maxQueryLength : Nat := 256

/-- A zero cursor represents an empty result; otherwise it indexes a selectable row. -/
def State.Valid (s : State) : Prop :=
  s.cursor ≤ (items s.candidates s.query s.allowCreate s.descriptions).length - 1 ∧
    s.query.length ≤ maxQueryLength

/-- A state over these candidates with an empty query and the cursor on the first row. -/
def init (candidates : List String) (allowCreate : Bool := true) : State :=
  { candidates, allowCreate }

/-- The row under the cursor, or none when the cursor indexes no row. -/
def selected (s : State) : Option Item :=
  (items s.candidates s.query s.allowCreate s.descriptions)[s.cursor]?

/-- Keep the selected target across snapshots, even when its creation row becomes
an existing session. A vanished target leaves the cursor clamped in place. -/
def refresh (s : State) (candidates : List String)
    (descriptions : List (String × String) := s.descriptions) : State :=
  let choices := items candidates s.query s.allowCreate descriptions
  let target := (selected s).map Item.target
  let cursor :=
    (choices.findIdx? (fun item => some item.target == target)).getD
      (min s.cursor (choices.length - 1))
  { s with
    candidates, descriptions, cursor }

/-- The rows a view shows after it showed `shown` and a listing gave `ordered`: each row of `shown`
that `ordered` still lists, where `shown` had it, so a vanished row closes up, then each row of
`ordered` that `shown` did not have, in `ordered`'s order. -/
def arrange (shown ordered : List String) : List String :=
  shown.filter (ordered.contains ·) ++ ordered.filter (!shown.contains ·)

/-- The state after a listing that gives the targets `ordered`, as a view sorts them
(`View.sort`): in that order when `resort` asks for it, as when the visit opens and on the refresh
key, and otherwise the rows already shown where they are, with new rows last (`arrange`), so the
view moves only when the person moves it. The highlight follows its target (`refresh`). -/
def relist (s : State) (resort : Bool) (ordered : List String)
    (descriptions : List (String × String)) : State :=
  refresh s (if resort then ordered else arrange s.candidates ordered) descriptions

/-- The state a visit enters with, from `s`, the state it had while its first listing ran, once
that listing gives the targets `ordered`, as a view sorts them: the rows the view it returns from
showed, `shown`, where they were, with new rows last (`arrange`), and the cursor on `focus`, the
session it returns from or the one it was opened inside, while the query is empty and the listing
still has it; otherwise on the first row. Returning is the inverse of leaving. -/
def enter (s : State) (shown : List String) (focus : Option String) (ordered : List String)
    (descriptions : List (String × String)) : State :=
  let candidates := arrange shown ordered
  { s with
    candidates, descriptions,
    cursor :=
      match focus with
      | some target =>
        if s.query.isEmpty && candidates.contains target then candidates.idxOf target else 0
      | none => 0 }

/-- Editing resets the cursor. Up and down move around the rows as a cycle, as fzf's do with
`--cycle`: up from the first row selects the last, the creation row when there is one, and down
from the last selects the first; with no row they change nothing. First and last go to either end,
and acceptance acts on the selected row. No selectable row stays editable. Ctrl-D's
`deleteCharEof` ends the visit on an empty query and otherwise leaves the state as it is: the
cursor sits after the query, with no character under it. A refresh leaves the state as it is: what
it fetches and repaints is the executor's (`fetch`). Effects remain the caller's job. -/
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
  | .up =>
    let count := (items s.candidates s.query s.allowCreate s.descriptions).length
    .stay (if count = 0 then s else { s with cursor := (s.cursor + count - 1) % count })
  | .down =>
    let count := (items s.candidates s.query s.allowCreate s.descriptions).length
    .stay (if count = 0 then s else { s with cursor := (s.cursor + 1) % count })
  | .first => .stay { s with cursor := 0 }
  | .last =>
    .stay { s with cursor := (items s.candidates s.query s.allowCreate s.descriptions).length - 1 }
  | .accept =>
    match selected s with
    | some (.existing target) => .attach target
    | some (.create target) => .create target
    | none => .stay s
  | .cancel => .cancel
  | .deleteCharEof => if s.query.isEmpty then .cancel else .stay s
  | .refresh => .stay s

/-- How many listed rows the query matches: what the query line shows beside it. -/
def matchCount (s : State) : Nat := (visible s.candidates s.query s.descriptions).length

/-- What a header says of the remote rows `snapshot` holds, when it holds any and `remoteAge`
gives how many seconds ago the listing that fetched them started: that age, in the format a row
gives the time since its session last printed (`Listing.ago`), after `remote`, the word linger
names other hosts' sessions with. A remote row's status is the one its host reported then. -/
def ageParts (snapshot : Snapshot) (remoteAge : Option Nat) : List String :=
  match remoteAge with
  | some seconds =>
    if snapshot.candidates.any remoteTarget then [s!"remote {Linger.Display.Listing.ago seconds}"]
    else []
  | none => []

/-- What a picker shows, as lines of text pieces with their styles, for a terminal `rows` tall
(a style is the parameters of the SGR sequences that select it, in order):
the header, which counts every listed row and, with `statusOf`, those that ask for someone
(`View.headerParts`), then says how old the remote rows are (`ageParts`); the query, with how
many rows it matches; the rows around the cursor; a line that sums up the matching rows the window
leaves out (`View.hidden`); and the keys. It never has more lines than the terminal
(`frameLines_length`). -/
def frameLines (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (rows : Nat) : List (List (String × List (List Nat))) :=
  let height := max 1 rows
  let choices := items state.candidates state.query state.allowCreate state.descriptions
  let layout := snapshot.layout.getD (snapshot.laidOut)
  let labels := if savedTmux then ["tmux save"] else if state.allowCreate then [] else ["read-only"]
  let title : List (List (String × List (List Nat))) :=
    if height ≥ 7 then
      -- the counts once there is a listing to count
      let header :=
        "  " ++
          String.intercalate " · "
            (if loaded then
              Linger.Display.View.headerParts labels (snapshot.candidates.map statusOf) ++
                ageParts snapshot remoteAge
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
              (emphasizeCells (highlightedPresentation snapshot layout state.query item)).map
                fun char =>
                (String.singleton char.char,
                  selection ++ (if withColor then char.style.toList else []) ++
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
      (if height ≥ 6 then [[]] else []) ++
        [[(s!"{action}  ·  ↑↓ move  ·  {if savedTmux then "" else "^L refresh  ·  "}esc / ^C quit",
              [[2]])]]
    else []
  (title ++ query ++ body ++ footer).take height

/-- A character as a frame shows it: itself when a terminal prints it, `?` otherwise. -/
private def frameChar (raw : Char) : Char := if Input.printable raw then raw else '?'

/-- A style as the pen it selects, applying its SGR parameters to the default pen as a terminal
does: a reset, bold, faint, underline, reverse and the eight foreground colours, the default
foreground, and nothing for any other parameter, which the picker does not use. -/
private def styleAttr (pen : Terminal.Vt.Pen) (n : Nat) : Terminal.Vt.Pen :=
  if n == 0 then {}
  else
    if n == 1 then { pen with bold := true }
    else
      if n == 2 then { pen with dim := true }
      else
        if n == 4 then { pen with underline := true }
        else
          if n == 7 then { pen with reverse := true }
          else
            if 30 ≤ n && n ≤ 37 then { pen with fg := .idx (UInt8.ofNat (n - 30)) }
            else if n == 39 then { pen with fg := .default } else pen

/-- The pen a style puts in effect after a reset. -/
private def stylePen (style : List (List Nat)) : Terminal.Vt.Pen := style.flatten.foldl styleAttr {}

/-- The cells of a frame line's characters, each in its pen, that fit `width` columns after
`used` of them are taken, added to `cells`, which holds the cells so far, last first. Each
character shows as `frameChar` shows it; a character of width zero joins the cell before it
when that cell is narrow and holds fewer than eight, and is dropped otherwise; the first
character that does not fit ends the line. -/
private def lineCells (width : Nat) :
    Nat → List Terminal.Vt.Cell → List (Char × Terminal.Vt.Pen) → List Terminal.Vt.Cell
  | _, cells, [] => cells
  | used, cells, (raw, pen) :: rest =>
    if Terminal.Vt.charWidth (frameChar raw) == 0 then
      match cells with
      | last :: before =>
        if last.width == 1 && last.marks.length < 8 then
          lineCells width used ({ last with marks := last.marks ++ [frameChar raw] } :: before) rest
        else lineCells width used cells rest
      | [] => lineCells width used cells rest
    else
      if used + Terminal.Vt.charWidth (frameChar raw) > width then cells
      else
        if Terminal.Vt.charWidth (frameChar raw) == 2 then
          lineCells width (used + 2)
            ({ base := ' ', marks := [], width := 0, pen } ::
              { base := frameChar raw, width := 2, pen } :: cells)
            rest
        else lineCells width (used + 1) ({ base := frameChar raw, pen } :: cells) rest

/-- One frame line as the row of cells it shows on a terminal `cols` wide: its characters
within `cols - 1` columns, so that the final column stays blank, then blanks to the width. -/
private def lineRow (cols : Nat) (line : List (String × List (List Nat))) : Terminal.Vt.Row :=
  let cells :=
    (lineCells (cols - 1) 0 []
        (line.flatMap fun run => run.1.toList.map fun char => (char, stylePen run.2))).reverse
  (cells ++ List.replicate (cols - cells.length) ({} : Terminal.Vt.Cell)).toArray

/-- What a frame shows on a terminal `cols` wide and `rows` tall: the row of each line of
`frameLines`, then blank rows, one row for each of the terminal's (at least one). -/
private def picture (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) : List Terminal.Vt.Row :=
  let lines := frameLines state snapshot statusOf loaded withColor savedTmux remoteAge rows
  (lines ++ List.replicate (max 1 rows - lines.length) []).map (lineRow cols)

/-- Each row's paint, from the pen the row before it left in effect, as a full repaint
threads them. -/
private def threadRows : List Terminal.Vt.Row → Terminal.Vt.Pen → List (List UInt8)
  | [], _ => []
  | row :: rest, pen =>
    (Terminal.Render.rowAnsi row pen).1 :: threadRows rest (Terminal.Render.rowAnsi row pen).2

/-- Each row of a frame as its own paint: the pen reset, then every cell of the row, from the
first column to the last, so a row painted over another leaves nothing of it. -/
def frameRows (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) : List (List UInt8) :=
  (picture state snapshot statusOf loaded withColor savedTmux remoteAge cols rows).map fun row =>
    Terminal.Render.csiNum 0 0x6D ++ (Terminal.Render.rowAnsi row {}).1

/-- The picker frame's terminal bytes, which paint every cell of the screen: reset the pen, home
the cursor, then each row of the frame, separated by CR LF. Each line keeps the final column
blank, so neither a full-width name nor a resize induces an automatic line wrap. -/
def frame (state : State) (snapshot : Snapshot) (statusOf : String → Linger.Display.Status.Status)
    (loaded withColor savedTmux : Bool) (remoteAge : Option Nat) (cols rows : Nat) : List UInt8 :=
  Terminal.Render.csiNum 0 0x6D ++ Terminal.Render.csiPlain 0x48 ++
    ((threadRows (picture state snapshot statusOf loaded withColor savedTmux remoteAge cols rows)
            {}).intersperse
        Terminal.Render.crlfB).flatten

/-- The rows from row `y` on of the update from the rows `before` shows there to `after`. -/
private def updateFrom : Nat → List (List UInt8) → List (List UInt8) → List UInt8
  | _, _, [] => []
  | y, before, row :: after =>
    (if before.head? = some row then [] else Terminal.Render.csiNum2 (y + 1) 1 0x48 ++ row) ++
      updateFrom (y + 1) before.tail after

/-- What turns a terminal that shows the rows `before` into one that shows `after`, rows as
`frameRows` gives them: for each row that differs, the cursor to its first column and the row's
paint, and nothing for a row that stays. -/
def update (before after : List (List UInt8)) : List UInt8 := updateFrom 0 before after

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
