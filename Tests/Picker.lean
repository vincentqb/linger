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

#guard maxQueryLength == 256

#guard (init ["work", "other"]) == { candidates := ["work", "other"], query := "", cursor := 0 }

#guard selected (init ["work@me@dev-a", "other"]) == some "work@me@dev-a"

#guard selected (init []) == none

#guard selected { candidates := ["work"], cursor := 99 } == none

#guard selected { candidates := ["work"], query := "unknown" } == none

#guard step (init ["work@me@dev-a"]) .accept == .attach "work@me@dev-a"

#guard step (init []) .accept == .stay (init [])

#guard
  step { candidates := ["work"], query := "new-name" } .accept ==
    .stay { candidates := ["work"], query := "new-name" }

#guard step (init ["work"]) .cancel == .cancel

#guard step (init ["work"]) .refresh == .refresh

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
    .stay { candidates := ["a", "b"], cursor := 1 }

#guard step (init ["a", "b"]) .down == .stay { candidates := ["a", "b"], cursor := 1 }

#guard step { candidates := ["a", "b"], cursor := 1 } .first == .stay (init ["a", "b"])

#guard step (init ["a", "b", "c"]) .last == .stay { candidates := ["a", "b", "c"], cursor := 2 }

#guard [Tools.Key.up, .down, .first, .last].all fun key => step (init []) key == .stay (init [])

#guard
  step { candidates := ["a", "b", "a-b"], query := "b" } .last ==
    .stay { candidates := ["a", "b", "a-b"], query := "b", cursor := 1 }

end Tools.Picker.Tests
