module

import Tools.Picker
public meta import Tools.Picker

/-! Concrete selector fixtures. General contracts live in `Theorems.Picker`. -/

namespace Tools.Picker.Tests

open Tools.Picker

#guard Tools.Picker.matches "" "" && Tools.Picker.matches "" "work"

#guard Tools.Picker.matches "WK@DV" "work@dev"

#guard Tools.Picker.matches "abc" "a---b---c"

#guard !Tools.Picker.matches "acb" "abc"

#guard !Tools.Picker.matches "aa" "a"

#guard Tools.Picker.matches "aa" "a-a"

#guard !Tools.Picker.matches "longer" "long"

#guard Tools.Picker.matches "é界" "café@世界"

-- Char.toLower folds ASCII capitals only; no Unicode normalization is implied.
#guard !Tools.Picker.matches "É" "é" && Tools.Picker.matches "É" "É"

#guard
  visible ["work", "wk", "a-w-k", "Work", "other", "work"] "WK" ==
    ["work", "wk", "a-w-k", "Work", "work"]

#guard visible ["-work", "+work", "work@me@dev-a"] "" == ["-work", "+work", "work@me@dev-a"]

#guard
  match parseListing "name\t-work\npid\t123\n\nname\t+work\nname\twork@me@dev-a\n" with
  | .ok targets => targets == ["-work", "+work", "work@me@dev-a"]
  | .error _ => false

#guard
  match parseListing "unknown\tmetadata\tfields\nnames\tnot-a-name\nname\twork@世界" with
  | .ok targets => targets == ["work@世界"]
  | .error _ => false

#guard
  ["", "\n", "pid\t123\nstate\trunning\n"].all fun text =>
    match parseListing text with
    | .ok targets => targets.isEmpty
    | .error _ => false

#guard
  ["name", "name\t", "name\twork\textra", "name\t\twork", "name\twork\t"].all fun text =>
    match parseListing text with
    | .error _ => true
    | .ok _ => false

#guard
  ["\x00", "\x01", "\r", "\x1b", "\x7f", "\u0085", "\u009b"].all fun control =>
    match parseListing ("name\twork@" ++ control ++ "host") with
    | .error _ => true
    | .ok _ => false

#guard
  ["bad/name", ".hidden", "@host", "a b", String.ofList (List.replicate 81 'a')].all fun target =>
    match parseListing ("name\t" ++ target) with
    | .error _ => true
    | .ok _ => false

#guard
  match parseListing "name\twork@" with
  | .error _ => true
  | .ok _ => false

#guard
  match parseListing "name\twork\npid\t123\nname\twork\nname\tother\n" with
  | .error _ => true
  | .ok _ => false

#guard
  match parseListing "name\twork@host\nname\twork\nname\twork@other\n" with
  | .ok targets => targets == ["work@host", "work", "work@other"]
  | .error _ => false

-- A malformed later record rejects the entire listing, including its valid prefix.
#guard
  match parseListing "name\twork\nname\tother\textra" with
  | .error _ => true
  | .ok _ => false

#guard
  ["name\twork@\x1b[2J", "name\tbad/name", "name\twork\nname\twork"].all fun text =>
    match parseListing text with
    | .error error => error.toList.all fun char => char.toNat ≥ 32 && char.toNat < 127
    | .ok _ => false

#guard
  match
    parseSnapshot
      "name\twork@host\nstatus\tworking\ncmd\tvim\npid\t42\nlabel.project\tdemo\nclients\t2\nname\tother\n" with
  | .ok snapshot =>
    snapshot.candidates == ["work@host", "other"] &&
      snapshot.row "work@host" ==
        [("name", "work@host"), ("status", "working"), ("cmd", "vim"), ("pid", "42"),
          ("label.project", "demo"), ("clients", "2")] &&
      snapshot.row "other" == [("name", "other")]
  | .error _ => false

#guard
  match parseSnapshot "name\twork\ncmd\tvim\n\ncmd\toutside\nname\tother\npid\t5\n" with
  | .ok snapshot =>
    snapshot.row "work" == [("name", "work"), ("cmd", "vim")] &&
      snapshot.row "other" == [("name", "other"), ("pid", "5")]
  | .error _ => false

#guard
  ["name\twork\nstatus\tidle\nname\tbad/name", "name\twork\ncmd\tvim\nname\twork",
        "name\twork\nstatus\tworking\nname\tother\textra"].all
    fun text =>
    match parseSnapshot text with
    | .error _ => true
    | .ok _ => false

#guard
  ["status", "cmd", "pid", "label.project", "clients"].all fun key =>
    match parseSnapshot s!"name\twork\n{key}\tbefore\n",
      parseSnapshot s!"name\twork\n{key}\tafter\n" with
    | .ok old, .ok fresh =>
      old.candidates == fresh.candidates && old != fresh &&
        (fresh.row "work").lookup key == some "after"
    | _, _ => false

#guard
  match parseSnapshot "name\twork\ncmd\tvi\x1b[31m\u009b31m\n" with
  | .ok snapshot =>
    let pieces := presentation snapshot 4 (.existing "work")
    pieces == Linger.Core.Listing.rowPieces 4 (snapshot.row "work") &&
      String.ofList (pieces.flatMap (·.text)) == "? work vi�[31m�31m"
  | .error _ => false

#guard
  match parseSnapshot "name\twork\nname\tother\n" with
  | .ok snapshot =>
    String.ofList ((presentation snapshot 5 (.existing "work")).flatMap (·.text)) ==
        "? work  (busy)" &&
      String.ofList ((presentation snapshot 5 (.create "work@host")).flatMap (·.text)) ==
        "+ Create work@host"
  | .error _ => false

#guard maxQueryLength == 256

#guard items [] "" == [.create "main"]

#guard items ["main", "work"] "" == [.existing "main", .existing "work"]

#guard items ["work", "other"] "w" == [.existing "work", .create "w"]

#guard items ["work", "other"] "work" == [.existing "work"]

-- Fuzzy matching folds ASCII case; creating retains the exact typed name.
#guard items ["work", "other"] "WK" == [.existing "work", .create "WK"]

#guard items ["work@host"] "work" == [.existing "work@host", .create "work"]

#guard
  ["work@host", "work@me@host", "work@世界", "-work", "+work"].all fun target =>
    items [] target == [.create target] &&
      step { candidates := [], query := target } .accept == .create target

-- Invalid creation targets remain editable; no sanitizer rewrite is hidden.
#guard
  ["bad/name", ".hidden", "@host", "work@", "a b", "work@\u009b",
        String.ofList (List.replicate 81 'a')].all
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

#guard step (init ["a", "b"]) .up == .stay (init ["a", "b"])

#guard
  step { candidates := ["a", "b"], cursor := 1 } .down ==
    .stay { candidates := ["a", "b"], cursor := 2 }

#guard
  step { candidates := ["a", "b"], cursor := 2 } .down ==
    .stay { candidates := ["a", "b"], cursor := 2 }

#guard step (init ["a", "b"]) .down == .stay { candidates := ["a", "b"], cursor := 1 }

#guard step { candidates := ["a", "b"], cursor := 1 } .first == .stay (init ["a", "b"])

#guard step (init ["a", "b", "c"]) .last == .stay { candidates := ["a", "b", "c"], cursor := 3 }

#guard [Tools.Key.up, .down, .first, .last].all fun key => step (init []) key == .stay (init [])

#guard
  step { candidates := ["a", "b", "a-b"], query := "b" } .last ==
    .stay { candidates := ["a", "b", "a-b"], query := "b", cursor := 1 }

end Tools.Picker.Tests
