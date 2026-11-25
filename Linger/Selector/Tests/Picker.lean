module

import all Linger.Selector.CoreCode.Picker
meta import Linger.Selector.CoreCode.Picker
import Linger.Display.CoreCode.Status
import ExactJSON.Codec
meta import ExactJSON.Codec

/-! Concrete selector fixtures. General contracts live in `Linger.Selector.Proofs.Picker`. -/

namespace Linger.Selector.Picker.Tests

#guard Linger.Selector.Picker.matches "WK@DV" "work@dev"

#guard Linger.Selector.Picker.matches "abc" "a---b---c"

#guard !Linger.Selector.Picker.matches "acb" "abc"

#guard !Linger.Selector.Picker.matches "aa" "a"

#guard Linger.Selector.Picker.matches "aa" "a-a"

#guard !Linger.Selector.Picker.matches "longer" "long"

#guard Linger.Selector.Picker.matches "é界" "café@世界"

-- Char.toLower folds ASCII capitals only; no Unicode normalization is implied.
#guard !Linger.Selector.Picker.matches "É" "é" && Linger.Selector.Picker.matches "É" "É"

#guard
  visible ["work", "wk", "a-w-k", "Work", "other", "work"] "WK" ==
    ["work", "wk", "a-w-k", "Work", "work"]

/-- A listing of records whose fields are these rows' text, their JSON Lines, as `ls --porcelain`
prints records, without cleaning their text. -/
def listing (records : List (List (String × String))) : String :=
  ExactJSON.encodeLines
    (records.map fun record =>
        (record.foldl (fun held field => held.insertIfNew field.1 (.text field.2)) ∅ :
          Linger.Display.Listing.Record)).toArray

/-- The targets a listing's text gives, or none when the chooser refuses it. -/
def listed (text : String) : Option (List String) :=
  (parseSnapshot text).toOption.map (·.candidates)

#guard
  listed
      (listing
        [[("name", "my work ✓"), ("pid", "123")], [("name", "+work")],
          [("name", "work@me@dev-a")]]) ==
    some ["my work ✓", "+work", "work@me@dev-a"]

-- a record without a name is no target, whatever else it holds
#guard
  listed (listing [[("unknown", "metadata")], [("names", "not-a-name")], [("name", "work@世界")]]) ==
    some ["work@世界"]

#guard ["", listing [[("pid", "123"), ("state", "running")]]].all fun text => listed text == some []

-- a line that is not a record's JSON refuses the whole listing: a blank line, text that is not
-- canonical, a field that is no flag, count or text, and a last line without its line feed
#guard
  ["\n", "name\twork\n", "{\"name\": \"work\"}\n", "{\"name\":\"work\",\"pid\":-5}\n",
        "{\"name\":\"work\",\"pid\":null}\n", "[\"work\"]\n", "{\"pid\":\"1\",\"name\":\"work\"}\n",
        "{\"name\":\"work\"}\n{\"name\":\"other\"\n", "{\"name\":\"work\"}"].all
    fun text => listed text == none

-- a record's flags and counts are JSON booleans and integers, which the chooser reads as text
#guard
  match parseSnapshot "{\"name\":\"work\",\"pid\":42,\"running\":true}\n" with
  | .ok snapshot => snapshot.row "work" == [("name", "work"), ("pid", "42"), ("running", "true")]
  | .error _ => false

#guard
  ["\x00", "\x01", "\r", "\x1b", "\x7f", "\u0085", "\u009b"].all fun control =>
    listed (listing [[("name", "work@" ++ control ++ "host")]]) == none

#guard
  ["-a b", "   ", "@host", "a\tb", String.ofList (List.replicate 121 'a'), "work@"].all
    fun target => listed (listing [[("name", target)]]) == none

#guard
  listed (listing [[("name", "work"), ("pid", "123")], [("name", "work")], [("name", "other")]]) ==
    none

#guard
  listed (listing [[("name", "work@host")], [("name", "work")], [("name", "work@other")]]) ==
    some ["work@host", "work", "work@other"]

-- A malformed later record rejects the entire listing, including its valid prefix.
#guard listed (listing [[("name", "work")]] ++ "{\"name\":\"other\",\"x\":[]}\n") == none

-- the diagnostics name no text of the listing
#guard
  [listing [[("name", "work@\x1b[2J")]], listing [[("name", "-a b")]],
        listing [[("name", "work")], [("name", "work")]], "{\"name\":\"\\u001b[2J\" }\n"].all
    fun text =>
    match parseSnapshot text with
    | .error error => error.toList.all fun char => char.toNat ≥ 32 && char.toNat < 127
    | .ok _ => false

#guard
  match
    parseSnapshot
      (listing
        [[("name", "work@host"), ("status", "working"), ("cmd", "vim"), ("pid", "42"),
            ("label.project", "demo"), ("clients", "2")],
          [("name", "other")]]) with
  | .ok snapshot =>
    snapshot.candidates == ["work@host", "other"] &&
      snapshot.row "work@host" ==
        [("clients", "2"), ("cmd", "vim"), ("label.project", "demo"), ("name", "work@host"),
          ("pid", "42"), ("status", "working")] &&
      snapshot.row "other" == [("name", "other")]
  | .error _ => false

#guard
  match
    parseSnapshot
      (listing
        [[("name", "work"), ("cmd", "vim")], [("cmd", "outside")],
          [("name", "other"), ("pid", "5")]]) with
  | .ok snapshot =>
    snapshot.row "work" == [("cmd", "vim"), ("name", "work")] &&
      snapshot.row "other" == [("name", "other"), ("pid", "5")] &&
      snapshot.row "missing" == [("name", "missing")]
  | .error _ => false

#guard
  ["status", "cmd", "pid", "label.project", "clients"].all fun key =>
    match parseSnapshot (listing [[("name", "work"), (key, "before")]]),
      parseSnapshot (listing [[("name", "work"), (key, "after")]]) with
    | .ok old, .ok fresh =>
      old.candidates == fresh.candidates && old != fresh &&
        (fresh.row "work").lookup key == some "after"
    | _, _ => false

#guard remoteTarget "work@host" && remoteTarget "work@me@host" && !remoteTarget "work"

-- A local-only listing replaces the local rows and keeps the last full listing's remote ones.
#guard
  match
    parseSnapshot
      (listing
        [[("name", "work"), ("status", "idle")], [("name", "dev@host"), ("status", "working")]]),
    parseSnapshot (listing [[("name", "fresh"), ("status", "idle")]]) with
  | .ok full, .ok latest =>
    let merged := latest.withRemote full
    merged.candidates == ["fresh", "dev@host"] &&
      merged.row "fresh" == [("name", "fresh"), ("status", "idle")] &&
      merged.row "dev@host" == [("name", "dev@host"), ("status", "working")] &&
      merged.row "work" == [("name", "work")]
  | _, _ => false

-- `ls -r` lists local rows first, so a full listing merged with itself is unchanged.
#guard
  match
    parseSnapshot
      (listing [[("name", "work"), ("cmd", "vim")], [("name", "dev@host"), ("cmd", "sh")]]) with
  | .ok full =>
    full.withRemote full == full && (full.withRemote {}).candidates == ["work"] &&
      (({} : Snapshot).withRemote full).candidates == ["dev@host"]
  | .error _ => false

#guard
  match parseSnapshot (listing [[("name", "work"), ("cmd", "vi\x1b[31m\u009b31m")]]) with
  | .ok snapshot =>
    let pieces := presentation snapshot snapshot.laidOut (.existing "work")
    pieces == Linger.Display.Listing.rowPieces snapshot.laidOut (snapshot.row "work") &&
      String.ofList (pieces.flatMap (·.text)) == "  ? work vi�[31m�31m"
  | .error _ => false

#guard
  match parseSnapshot (listing [[("name", "work")], [("name", "other")]]) with
  | .ok snapshot =>
    String.ofList ((presentation snapshot snapshot.laidOut (.existing "work")).flatMap (·.text)) ==
        "  ? work  (busy)" &&
      String.ofList
          ((presentation snapshot snapshot.laidOut (.create "work@host")).flatMap (·.text)) ==
        "+ Create work@host"
  | .error _ => false

-- The better consecutive alignment is emphasized in the name only, even when
-- the command and the description repeat the query; the description, which names the command,
-- hides it.
#guard
  match
    parseSnapshot
      (listing
        [[("name", "axab"), ("status", "working"), ("cmd", "ab"), ("description", "ab"),
            ("clients", "2")]]) with
  | .ok snapshot =>
    let chars :=
      highlightedPresentation snapshot { snapshot.laidOut with nameCol := 8 } "ab"
        (.existing "axab")
    (chars.zipIdx.filterMap fun (char, index) => if char.matched then some index else none) ==
        [6, 7] &&
      String.ofList (chars.map (·.char)) == "  ⣷ axab     ab  +2" &&
      (chars[2]?.map (·.style)) == some (some [36]) &&
      (chars.filter (·.matched)).all (fun char => char.style.isNone)
  | .error _ => false

-- The query finds a row by its description as by its name, and the snapshot carries each row's.
#guard
  match
    parseSnapshot
      (listing [[("name", "work"), ("description", "fixing the parser")], [("name", "other")]]) with
  | .ok snapshot =>
    snapshot.descriptions == [("work", "fixing the parser")] &&
      items snapshot.candidates "parser" false snapshot.descriptions == [.existing "work"] &&
      items snapshot.candidates "oth" false snapshot.descriptions == [.existing "other"] &&
      matchCount
          { (init snapshot.candidates false) with
            query := "fix", descriptions := snapshot.descriptions } ==
        1
  | .error _ => false

#guard
  (highlightedPresentation {} {} "work" (.create "work")).all (fun char => !char.matched) &&
    (highlightedPresentation {} {} "" (.existing "work")).all (fun char => !char.matched)

-- Scalar positions survive wide and combining characters without byte indexing.
#guard
  let chars := highlightedPresentation {} {} "é界" (.existing "café@世界")
  (chars.zipIdx.filterMap fun (char, index) => if char.matched then some index else none) == [7, 10]

-- An accent-only match underlines the base cell, even through another mark.
-- A following wide character starts its own cell and cannot carry emphasis back.
#guard
  let chars := highlightedPresentation {} {} "\u0301" (.existing "s@e\u0300\u0301界")
  (chars.zipIdx.filterMap fun (char, index) => if char.matched then some index else none) == [8] &&
    ((emphasizeCells chars).zipIdx.filterMap fun (char, index) =>
        if char.matched then some index else none) ==
      [6, 7, 8] &&
    ((emphasizeCells
            (highlightedPresentation {} {} "界" (.existing "s@e\u0300\u0301界"))).zipIdx.filterMap
        fun (char, index) => if char.matched then some index else none) ==
      [9]

#guard maxQueryLength == 256

#guard items [] "" == [.create "main"]

#guard items ["main", "work"] "" == [.existing "main", .existing "work"]

#guard items ["work", "other"] "w" == [.existing "work", .create "w"]

#guard items ["work", "other"] "work" == [.existing "work"]

-- Fuzzy matching folds ASCII case; creating retains the exact typed name.
#guard items ["work", "other"] "WK" == [.existing "work", .create "WK"]

#guard items ["work@host"] "work" == [.existing "work@host", .create "work"]

#guard
  ["work@host", "work@me@host", "work@世界", "two words", "世界", "+work"].all fun target =>
    items [] target == [.create target] &&
      step { candidates := [], query := target } .accept == .create target

-- Invalid creation targets remain editable; no sanitizer rewrite is hidden.
#guard
  ["-a b", "   ", "@host", "work@", "a\tb", "work@\u009b",
        String.ofList (List.replicate 121 'a')].all
    fun query =>
    items [] query == [] &&
      step { candidates := [], query } .accept == .stay { candidates := [], query }

#guard (init ["work", "other"]) == { candidates := ["work", "other"], query := "", cursor := 0 }

#guard selected (init ["work@me@dev-a", "other"]) == some (.existing "work@me@dev-a")

#guard selected (init []) == some (.create "main")

#guard selected { candidates := ["work"], cursor := 99 } == none

#guard selected { candidates := ["work"], query := "unknown" } == some (.create "unknown")

-- Refresh preserves target identity, not its former row number.
#guard
  refresh { candidates := ["work", "web"], query := "w", cursor := 1 } ["web", "other", "work"] ==
    { candidates := ["web", "other", "work"], query := "w", cursor := 0 }

-- A creation offer can become an attachment, or the reverse, without jumping.
#guard
  selected (refresh { candidates := ["work"], query := "w", cursor := 1 } ["web", "w", "work"]) ==
    some (.existing "w")

#guard
  selected
      (refresh { candidates := ["web", "w", "work"], query := "w", cursor := 1 } ["web", "work"]) ==
    some (.create "w")

-- Missing targets clamp the old cursor; empty choices and forged cursors stay safe.
#guard
  refresh { candidates := ["work", "web", "west"], query := "w", cursor := 2 } ["work"] ==
    { candidates := ["work"], query := "w", cursor := 1 }

#guard
  refresh { candidates := ["work@host"], query := "@", cursor := 0 } [] ==
    { candidates := [], query := "@", cursor := 0 }

#guard
  refresh { candidates := ["work"], cursor := 999 } ["main"] ==
    { candidates := ["main"], cursor := 0 }

#guard step (init ["work@me@dev-a"]) .accept == .attach "work@me@dev-a"

#guard step (init []) .accept == .create "main"

#guard step { candidates := ["work"], query := "new-name" } .accept == .create "new-name"

#guard step { candidates := ["work"], query := "w", cursor := 1 } .accept == .create "w"

#guard
  step { candidates := ["work"], query := "work", cursor := 1 } .accept ==
    .stay { candidates := ["work"], query := "work", cursor := 1 }

#guard step (init ["work"]) .cancel == .cancel

-- Ctrl-D ends the visit on an empty query and changes nothing after a typed one: the cursor sits
-- after the query, with no character under it.
#guard step (init ["work"]) .deleteCharEof == .cancel

#guard
  let s : State := { candidates := ["work", "web"], query := "w", cursor := 1 }
  step s .deleteCharEof == .stay s

#guard
  match step { candidates := ["work"], query := "w" } .clear with
  | .stay emptied => step emptied .deleteCharEof == .cancel
  | _ => false

-- Ctrl-L leaves the selection as it is; what it fetches and repaints is the executor's.
#guard
  let s : State := { candidates := ["work", "web"], query := "w", cursor := 1 }
  step s .refresh == .stay s

/-- A frame line's text, without its styles. -/
def lineText (line : List (String × List (List Nat))) : String := String.join (line.map (·.1))

-- The header says how long ago the listing that fetched the remote rows started, in a row's age
-- format, only when the snapshot holds remote rows; the footer names Ctrl-L as the refresh key.
#guard
  match
    parseSnapshot
      (listing
        [[("name", "work"), ("status", "idle")], [("name", "dev@host"), ("status", "working")]]),
    parseSnapshot (listing [[("name", "work"), ("status", "idle")]]) with
  | .ok remote, .ok localOnly =>
    let statusOf := fun (_ : String) =>
      ({ attention := .none, state := .idle } : Linger.Display.Status.Status)
    let lines (snapshot : Snapshot) (age : Option Nat) :=
      (frameLines (init snapshot.candidates) snapshot statusOf true false false age 12).map lineText
    ageParts remote (some 12) == ["remote 12s"] && ageParts remote (some 75) == ["remote 1m"] &&
      ageParts remote none == [] &&
      ageParts localOnly (some 12) == [] &&
      (lines remote (some 3)).head? == some "  linger · 2 · remote 3s" &&
      (lines remote none).head? == some "  linger · 2" &&
      (lines localOnly (some 3)).head? == some "  linger · 1" &&
      (lines remote (some 3)).getLast? ==
        some "  ↵ attach  ·  ↑↓ move  ·  ^L refresh  ·  esc / ^C quit" &&
      !(lines remote (some 3)).any (fun line => (line.splitOn "^R").length > 1)
  | _, _ => false

-- Only the header carries the age, so a new age changes that one row of the frame.
#guard
  match
    parseSnapshot
      (listing
        [[("name", "work"), ("status", "idle")],
          [("name", "dev@host"), ("status", "working")]]) with
  | .ok snapshot =>
    let statusOf := fun (_ : String) =>
      ({ attention := .none, state := .idle } : Linger.Display.Status.Status)
    let rows (age : Nat) :=
      frameRows (init snapshot.candidates) snapshot statusOf true false false (some age) 80 12
    ((rows 3).zip (rows 4)).zipIdx.filterMap (fun ((a, b), y) => if a == b then none else some y) ==
      [0]
  | .error _ => false

#guard
  step { candidates := ["alpha", "beta"], cursor := 1 } (.text 'a') ==
    .stay { candidates := ["alpha", "beta"], query := "a", cursor := 0 }

#guard
  step { candidates := ["café"], query := "café", cursor := 0 } .backspace ==
    .stay { candidates := ["café"], query := "caf", cursor := 0 }

#guard
  step { candidates := ["alpha", "beta"], query := "a", cursor := 1 } .clear ==
    .stay (init ["alpha", "beta"])

#guard step (init ["alpha"]) .backspace == .stay (init ["alpha"])

#guard
  ['\x00', '\n', '\r', '\x1b', '\x7f', '\u0085', '\u009b'].all fun char =>
    let s : State := { candidates := ["alpha", "beta"], query := "a", cursor := 1 }
    step s (.text char) == .stay s

#guard
  let query := String.ofList (List.replicate maxQueryLength '界')
  let s : State := { candidates := ["work"], query }
  step s (.text 'x') == .stay s

#guard
  let query := String.ofList (List.replicate (maxQueryLength - 1) 'a')
  step { candidates := [], query } (.text '界') ==
    .stay { candidates := [], query := query.push '界', cursor := 0 }

-- The moves cycle through every row, the creation row included: up from the first row selects
-- the last, and down from the last selects the first.
#guard step (init ["a", "b"]) .up == .stay { candidates := ["a", "b"], cursor := 2 }

#guard
  step { candidates := ["a", "b"], cursor := 1 } .down ==
    .stay { candidates := ["a", "b"], cursor := 2 }

#guard step { candidates := ["a", "b"], cursor := 2 } .down == .stay (init ["a", "b"])

#guard
  step { candidates := ["a", "b"], cursor := 2 } .up ==
    .stay { candidates := ["a", "b"], cursor := 1 }

#guard step (init ["a", "b"]) .down == .stay { candidates := ["a", "b"], cursor := 1 }

-- `k` moves down from row `i` of `n` select row `(i + k) % n`, and up undoes down: three rows, a
-- query's two matches and its creation row.
#guard
  let s : State := { candidates := ["work", "other", "web"], query := "w" }
  press step s (List.replicate 3 .down) == .stay s &&
    press step s (List.replicate 4 .down) == .stay { s with cursor := 1 } &&
    press step s (List.replicate 4 .up) == .stay { s with cursor := 2 } &&
    press step s (List.replicate 5 .down ++ List.replicate 5 .up) == .stay s

-- With no row, a move changes nothing, even from a forged cursor.
#guard
  [Linger.Selector.Key.up, .down].all fun key =>
    step (init [] false) key == .stay (init [] false) &&
      step { candidates := [], allowCreate := false, cursor := 3 } key ==
        .stay { candidates := [], allowCreate := false, cursor := 3 }

-- A forged cursor past the last row moves onto a row.
#guard
  step { candidates := ["a", "b"], cursor := 7, allowCreate := false } .down ==
      .stay { candidates := ["a", "b"], cursor := 0, allowCreate := false } &&
    step { candidates := ["a", "b"], cursor := 7, allowCreate := false } .up ==
      .stay { candidates := ["a", "b"], cursor := 0, allowCreate := false }

#guard step { candidates := ["a", "b"], cursor := 1 } .first == .stay (init ["a", "b"])

#guard step (init ["a", "b", "c"]) .last == .stay { candidates := ["a", "b", "c"], cursor := 3 }

#guard
  [Linger.Selector.Key.up, .down, .first, .last].all fun key =>
    step (init []) key == .stay (init [])

#guard
  step { candidates := ["a", "b", "a-b"], query := "b" } .last ==
    .stay { candidates := ["a", "b", "a-b"], query := "b", cursor := 1 }

-- Saved panes are existing choices only, including empty and unmatched saves.
#guard items [] "" false == []

#guard items ["work", "other"] "new-pane" false == []

#guard items ["work@host", "wk", "other"] "WK" false == [.existing "work@host", .existing "wk"]

#guard (init [] false).allowCreate == false && selected (init [] false) == none

#guard step (init [] false) .accept == .stay (init [] false)

#guard
  let state : State := { candidates := ["work"], query := "new-pane", allowCreate := false }
  step state .accept == .stay state

-- A cursor beyond the existing rows must not reach a hidden creation offer.
#guard
  let state : State :=
    { candidates := ["work@host"], query := "work", cursor := 1, allowCreate := false }
  selected state == none && step state .accept == .stay state

#guard
  let state : State :=
    { candidates := ["work@me@dev-a", "other"], query := "WK@DV", allowCreate := false }
  step state .accept == .attach "work@me@dev-a"

#guard
  let state : State :=
    { candidates := ["work", "web"], query := "w", cursor := 1, allowCreate := false }
  refresh state ["web", "work"] ==
      { candidates := ["web", "work"], query := "w", allowCreate := false } &&
    refresh state [] == { candidates := [], query := "w", allowCreate := false }

#guard
  step (init ["a", "b"] false) .last ==
      .stay { candidates := ["a", "b"], cursor := 1, allowCreate := false } &&
    step { candidates := ["a", "b"], cursor := 1, allowCreate := false } .down ==
      .stay (init ["a", "b"] false) &&
    step (init ["a", "b"] false) .up ==
      .stay { candidates := ["a", "b"], cursor := 1, allowCreate := false }

#guard
  let state : State := { candidates := ["work"], query := "w", allowCreate := false }
  [Linger.Selector.Key.text 'o', .backspace, .clear, .up, .down, .first, .last].all fun key =>
    match step state key with
    | .stay next => !next.allowCreate
    | _ => false

-- Global save metadata and encoded directories remain exact, inert records.
#guard
  match
    parseSnapshot
      (listing
        [[("source", "/tmp/save file"), ("saved", "2026-10-03T10:15:00Z")],
          [("name", "work"), ("status", "resumable"), ("cmd", "pane command"),
            ("directory", "\"/tmp/exact\\tpath\\n\\\"quoted\\\"\""), ("line", "4")]]) with
  | .ok snapshot =>
    snapshot.candidates == ["work"] &&
      snapshot.records.take 1 ==
        [[("saved", "2026-10-03T10:15:00Z"), ("source", "/tmp/save file")]] &&
      (snapshot.row "work").lookup "directory" == some "\"/tmp/exact\\tpath\\n\\\"quoted\\\"\"" &&
      (snapshot.row "work").lookup "line" == some "4" &&
      String.ofList
          ((presentation snapshot snapshot.laidOut (.existing "work")).flatMap (·.text)) ==
        "  " ++ String.singleton (Linger.Display.Status.icon .resumable) ++ " work pane command"
  | .error _ => false

-- A changed directory changes the snapshot even if its pane identity stays put.
#guard
  match parseSnapshot (listing [[("name", "work"), ("directory", "\"/tmp/old\"")]]),
    parseSnapshot (listing [[("name", "work"), ("directory", "\"/tmp/new\"")]]) with
  | .ok old, .ok fresh =>
    old.candidates == fresh.candidates && old != fresh &&
      (old.row "work").lookup "directory" == some "\"/tmp/old\"" &&
      (fresh.row "work").lookup "directory" == some "\"/tmp/new\""
  | _, _ => false

end Linger.Selector.Picker.Tests
