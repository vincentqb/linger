module

import Tools.Resurrect
public meta import Tools.Resurrect

/-! Concrete checks of the pure API. General kernel-checked contracts live in
`Theorems.Resurrect`; these fixtures exercise the actual string operations. -/

namespace Tools.Resurrect.Tests

open Tools.Resurrect

-- Non-pane rows are ignored, including blanks and unknown record shapes.
-- Empty commands occupy their own record; neither commands nor paths are trimmed.
#guard
  match
    parseSave "/home/me"
      ("window\tignored\n\npane\tdesk\t1\t:\t0\t0\t0\t:~/work\\ space\t0\tsh\t:\n" ++
        "state\tignored\npane\tdesk\t1\t:\t0\t1\t0\t:/tmp\t0\tvi\t:  vi 'a b'; tail x  ") with
  | .ok panes =>
    panes ==
      [{ name := "desk-w1-p0", dir := "/home/me/work space", command := "", line := 3 },
        { name := "desk-w1-p1", dir := "/tmp", command := "  vi 'a b'; tail x  ", line := 5 }]
  | .error _ => false

#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:~\t\t\t:" with
  | .ok panes => panes == [{ name := "d-w0-p0", dir := "/home/me", command := "", line := 1 }]
  | .error _ => false

-- Preserve filesystem traversal spelling; there is no lexical normalization.
#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:~/link/../work//.\t\t\t:vi" with
  | .ok panes =>
    panes == [{ name := "d-w0-p0", dir := "/home/me/link/../work//.", command := "vi", line := 1 }]
  | .error _ => false

-- Only literal backslash-space is unescaped; other backslashes and ~user remain.
#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:~user/é\\ x\\q\t\t\t:vi é\\ x" with
  | .ok panes =>
    panes == [{ name := "d-w0-p0", dir := "~user/é x\\q", command := "vi é\\ x", line := 1 }]
  | .error _ => false

-- Nonexistent/empty directories are the caller's preflight responsibility.
#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:\t\t\t:" with
  | .ok panes => panes == [{ name := "d-w0-p0", dir := "", command := "", line := 1 }]
  | .error _ => false

#guard
  match parseSave "" "window\tignored\npane\tshort" with
  | .error error => error == "malformed pane record at line 2"
  | .ok _ => false

-- Exactly eleven fields: neither a missing nor an additional tab field is accepted.
#guard
  ["pane\td\t0\t\t\t0\t\t:/tmp\t\t:", "pane\td\t0\t\t\t0\t\t:/tmp\t\t\t:\textra"].all fun row =>
    match parseSave "" row with
    | .error error => error == "malformed pane record at line 1"
    | .ok _ => false

-- Each component of the projected name must be present.
#guard
  ["pane\t\t0\t\t\t0\t\t:/tmp\t\t\t:", "pane\td\t\t\t\t0\t\t:/tmp\t\t\t:",
        "pane\td\t0\t\t\t\t\t:/tmp\t\t\t:"].all
    fun row =>
    match parseSave "" row with
    | .error error => error == "malformed pane record at line 1"
    | .ok _ => false

#guard
  ["pane\td\t0\t\t\t0\t\t/tmp\t\t\t:", "pane\td\t0\t\t\t0\t\t:/tmp\t\t\tvi"].all fun row =>
    match parseSave "" row with
    | .error error => error == "malformed pane record at line 1"
    | .ok _ => false

#guard
  match parseSave "" "pane\tbad/name\t0\t\t\t0\t\t:/tmp\t\t\t:" with
  | .error error =>
    error == "projected session is not a valid linger name at line 1: bad/name-w0-p0"
  | .ok _ => false

#guard
  match parseSave "" "pane\t.hidden\t0\t\t\t0\t\t:/tmp\t\t\t:" with
  | .error error => error == "projected session is not a valid linger name at line 1: .hidden-w0-p0"
  | .ok _ => false

-- Distinct source triples can collide under the textual projection.
#guard
  match
    parseSave ""
      ("pane\ta-wb\tc\t\t\td\t\t:/tmp\t\t\t:\n" ++ "pane\ta\tb-wc\t\t\td\t\t:/other\t\t\t:vi") with
  | .error error => error == "duplicate projected session at line 2: a-wb-wc-pd"
  | .ok _ => false

#guard
  ["", "window\tignored\nstate\tignored\n"].all fun content =>
    match parseSave "" content with
    | .error error => error == "no pane records in save"
    | .ok _ => false

-- Check after expansion: a NUL supplied through home is also rejected.
#guard
  match parseSave "/home/\x00bad" "pane\td\t0\t\t\t0\t\t:~/work\t\t\t:" with
  | .error error => error == "malformed pane record at line 1"
  | .ok _ => false

#guard
  ["pane\td\t0\t\t\t0\t\t:/tmp/\x00bad\t\t\t:", "pane\td\t0\t\t\t0\t\t:/tmp\t\t\t:vi\x00other"].all
    fun row =>
    match parseSave "" row with
    | .error error => error == "malformed pane record at line 1"
    | .ok _ => false

-- Only ASCII spaces separate words; there is no shell tokenization.
#guard
  [firstWord "", firstWord "   ", firstWord "  vi  x ", firstWord "\tvi x", firstWord "vi\tx",
      firstWord "'vi' x", firstWord "/bin/vi x", firstWord "vi\nx"] ==
    ["", "", "vi", "\tvi", "vi\tx", "'vi'", "/bin/vi", "vi\nx"]

#guard restoreCommand false { name := "a", dir := "/", command := "vi x", line := 1 } == none

#guard restoreCommand true { name := "a", dir := "/", command := "printf x", line := 1 } == none

#guard
  restoreCommand true { name := "a", dir := "/", command := "  vi 'x y'; tail z  ", line := 1 } ==
    some "  vi 'x y'; tail z  "

-- The skipped middle record never shifts the last command onto another pane.
#guard
  plan true ["b"]
      [{ name := "a", dir := "/a", command := "", line := 1 },
        { name := "b", dir := "/b", command := "vi b", line := 2 },
        { name := "c", dir := "/c", command := "tail c", line := 3 }] ==
    [{ pane := { name := "a", dir := "/a", command := "", line := 1 }, command := none },
      { pane := { name := "c", dir := "/c", command := "tail c", line := 3 },
        command := some "tail c" }]

end Tools.Resurrect.Tests
