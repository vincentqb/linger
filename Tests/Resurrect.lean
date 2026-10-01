module

import Tools.Resurrect
public meta import Tools.Resurrect

/-! Concrete checks of the pure API. General kernel-checked contracts live in
`Theorems.Resurrect`; these fixtures exercise the actual string operations. -/

namespace Tools.Resurrect.Tests

open Tools.Resurrect

-- The reserved tmux session name carries native identity without a comment row.
#guard
  match parseSave "" "pane\tlinger=dev~api+one\t0\t:\t1\t0\t1\t:/tmp\t1\tsh\t:" with
  | .ok panes => panes == [{ name := "dev.api+one", dir := "/tmp", line := 1 }]
  | .error _ => false

#guard
  ["main", "_", "a.b-c_d+e", "a..b.", String.ofList (List.replicate 80 'x')].all fun name =>
    match
      parseSave "/unused/home"
        s!"pane\t{encodeName name}\t0\t1\t:*\t0\t{name}\t:/tmp\t1\tsh\t:" with
    | .ok panes => common panes == [(name, "/tmp")]
    | .error _ => false

#guard encodeName "dev.api+one" == "linger=dev~api+one"

-- A reserved prefix never falls back to a foreign projection.
#guard
  ["linger=", "linger=~hidden", "linger=bad/name", "linger=bad=name", "linger=raw.dot",
        "linger=linger=main", "linger=" ++ String.ofList (List.replicate 81 'a')].all
    fun session =>
    match parseSave "" s!"pane\t{session}\t0\t1\t:*\t0\tname\t:/tmp\t1\tsh\t:" with
    | .error error => error.startsWith "malformed native session"
    | .ok _ => false

#guard
  [("1", "0"), ("0", "1"), ("00", "0"), ("0", "00")].all fun (window, pane) =>
    match parseSave "" s!"pane\tlinger=main\t{window}\t1\t:*\t{pane}\tmain\t:/tmp\t1\tsh\t:" with
    | .error error => error == "malformed native session at line 1: linger=main"
    | .ok _ => false

-- Duplicate detection also spans the native and ordinary foreign projections.
#guard
  match
    parseSave ""
      ("pane\tlinger=desk-w1-p0\t0\t1\t:*\t0\tname\t:/a\t1\tsh\t:\n" ++
        "pane\tdesk\t1\t:\t0\t0\t0\t:/b\t0\tsh\t:") with
  | .error error => error == "duplicate projected session at line 2: desk-w1-p0"
  | .ok _ => false

-- The text includes real pane, window and final state records with literal cwd.
#guard
  match renderSave [("dev.api+one", "/tmp/work space")] with
  | .ok text =>
    text ==
      ("pane\tlinger=dev~api+one\t0\t1\t:*\t0\tdev.api+one\t:/tmp/work space\t1\tsh\t:\n" ++
        "window\tlinger=dev~api+one\t0\t:dev.api+one\t1\t:*\teven-horizontal\toff\n" ++
        "state\tlinger=dev~api+one\tlinger=dev~api+one\n")
  | .error _ => false

-- Round trips pass through the actual serialized text and ignore the supplied home.
#guard
  ["", "/other/home", "/home/\x00bad"].all fun home =>
    let fields := [("dev.api", "/tmp/é space"), ("main", "/"), ("plus+_-", "/tmp/:~$'\";&()]")]
    match renderSave fields with
    | .error _ => false
    | .ok text =>
      match parseSave home text with
      | .error _ => false
      | .ok panes => common panes == fields && panes.map Pane.line == [1, 3, 5]

#guard
  ["/", "/one space/two", "/space /component", "/é/λ😀", "/tmp/\"quote'"].all fun dir =>
    match renderSave [("main", dir)] with
    | .ok text =>
      match parseSave "/unused" text with
      | .ok panes => common panes == [("main", dir)]
      | .error _ => false
    | .error _ => false

#guard
  match renderSave [] with
  | .error error => error == "no pane records in save"
  | .ok _ => false

#guard
  ["", ".hidden", "bad/name", "bad name", "bad=name", "bad~name",
        String.ofList (List.replicate 81 'x')].all
    fun name =>
    match renderSave [(name, "/tmp")] with
    | .error _ => true
    | .ok _ => false

#guard
  match renderSave [("main", "/a"), ("main", "/b")] with
  | .error error => error == "duplicate projected session at line 3: main"
  | .ok _ => false

#guard
  ["", "relative", "~/home", "/tmp/\\path", "/tmp/\x00path", "/tmp/\tpath", "/tmp/\npath",
        "/tmp/\rpath", "/tmp/two  spaces", "/tmp/trailing ", "/tmp/*", "/tmp/?", "/tmp/[x]",
        "/tmp/#name"].all
    fun dir =>
    match renderSave [("main", dir)] with
    | .error error => error == s!"unrepresentable cwd in tmux save: {dir}"
    | .ok _ => false

-- Keep all original bytes, even metadata and directory spellings native export rejects.
#guard
  let original :=
    "# original\npane\tdesk\t0\t:\t1\t0\t0\t:/tmp/has#hash\t1\tvi\t:vi file\nwindow\topaque\n\n"
  let baseline := [("desk-w0-p0", "/tmp/has#hash")]
  match exportSave baseline (some (original, baseline)) with
  | .ok text => text == original
  | .error _ => false

#guard
  ["/tmp/back\\slash", "/tmp/two  spaces", "/tmp/trailing ", "/tmp/*literal", "/tmp/[literal]"].all
    fun dir =>
    let baseline := [("desk-w0-p0", dir)]
    let original := s!"pane\tdesk\t0\t:\t1\t0\t0\t:{dir}\t1\tsh\t:\nunknown\tuntouched\n"
    match renderSave baseline, exportSave baseline (some (original, baseline)) with
    | .error _, .ok text => text == original
    | _, _ => false

#guard
  let baseline := [("a", "/one"), ("b", "/two"), ("c", "/three")]
  match
    exportSave [("c", "/three"), ("a", "/one"), ("b", "/two")]
      (some ("retained\nunknown\tfields\n", baseline)) with
  | .ok text => text == "retained\nunknown\tfields\n"
  | .error _ => false

-- Multiset equality counts duplicates; equal membership alone is insufficient.
#guard
  let baseline := [("a", "/one"), ("a", "/one"), ("b", "/two")]
  match exportSave [("b", "/two"), ("a", "/one"), ("a", "/one")] (some ("original", baseline)) with
  | .ok text => text == "original"
  | .error _ => false

#guard
  let baseline := [("a", "/one"), ("b", "/two")]
  match exportSave [("a", "/one"), ("a", "/one"), ("b", "/two")] (some ("original", baseline)) with
  | .error error => error == "duplicate projected session at line 3: a"
  | .ok _ => false

#guard
  let current := [("a", "/one"), ("b", "/two")]
  match exportSave current (some ("original", [("a", "/one"), ("a", "/one"), ("b", "/two")])),
    renderSave current with
  | .ok exported, .ok generated => exported == generated && exported != "original"
  | _, _ => false

-- Name, cwd, membership and name/cwd pairing all participate in the comparison.
#guard
  let baseline := [("a", "/one"), ("b", "/two")]
  [[("renamed", "/one"), ("b", "/two")], [("a", "/changed"), ("b", "/two")], [("a", "/one")],
        baseline ++ [("c", "/three")], [("a", "/two"), ("b", "/one")]].all
    fun current =>
    match exportSave current (some ("original", baseline)) with
    | .error _ => false
    | .ok text =>
      text != "original" &&
        match parseSave "/unused" text with
        | .ok panes => common panes == current
        | .error _ => false

#guard
  match exportSave [] (some ("original", [("a", "/one")])) with
  | .error error => error == "no pane records in save"
  | .ok _ => false

#guard
  match exportSave [("a", "/not  representable")] (some ("original", [("a", "/one")])) with
  | .error error => error.startsWith "unrepresentable cwd"
  | .ok _ => false

#guard
  [[], [("main", "/tmp")], [("a", "/one"), ("b", "/two")]].all fun fields =>
    match exportSave fields none, renderSave fields with
    | .ok exported, .ok generated => exported == generated
    | .error exported, .error generated => exported == generated
    | _, _ => false

#guard
  common [{ name := "a", dir := "/one", line := 99 }, { name := "a", dir := "/one", line := 1 }] ==
    [("a", "/one"), ("a", "/one")]

-- Every C0, DEL and C1 code point is replaced, not just ESC and newlines.
#guard
  diagnostic (String.ofList ((List.range 32 ++ List.range' 127 33).map Char.ofNat)) ==
    String.ofList (List.replicate 65 '?')

#guard
  ["", "/tmp/é λ😀\u00a0x !~\"\\", " \x1b[2J\u009b31m z"].map diagnostic ==
    ["", "/tmp/é λ😀\u00a0x !~\"\\", " ?[2J?31m z"]

-- Saved commands validate as input but never affect the parsed pane.
#guard
  ["vi 'a b'; tail x", "printf '%s' \"$HOME\" && custom-tool --anything",
        "  λ ./unlisted\\ path 'quoted'  ", ":~/command\\ directory"].all
    fun command =>
    match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:~/work\\ space\t\t\t:",
      parseSave "/home/me" ("pane\td\t0\t\t\t0\t\t:~/work\\ space\t\t\t:" ++ command) with
    | .ok before, .ok after => before == after
    | _, _ => false

-- Non-pane rows are ignored, including blanks and unknown record shapes.
-- Empty and nonempty saved commands are discarded; directories are not trimmed.
#guard
  match
    parseSave "/home/me"
      ("window\tignored\n\npane\tdesk\t1\t:\t0\t0\t0\t:~/work\\ space\t0\tsh\t:\n" ++
        "state\tignored\npane\tdesk\t1\t:\t0\t1\t0\t:/tmp\t0\tvi\t:  vi 'a b'; tail x  ") with
  | .ok panes =>
    panes ==
      [{ name := "desk-w1-p0", dir := "/home/me/work space", line := 3 },
        { name := "desk-w1-p1", dir := "/tmp", line := 5 }]
  | .error _ => false

#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:~\t\t\t:" with
  | .ok panes => panes == [{ name := "d-w0-p0", dir := "/home/me", line := 1 }]
  | .error _ => false

-- Preserve filesystem traversal spelling; there is no lexical normalization.
#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:~/link/../work//.\t\t\t:vi" with
  | .ok panes => panes == [{ name := "d-w0-p0", dir := "/home/me/link/../work//.", line := 1 }]
  | .error _ => false

-- Only literal backslash-space is unescaped; other backslashes and ~user remain.
#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:~user/é\\ x\\q\t\t\t:vi é\\ x" with
  | .ok panes => panes == [{ name := "d-w0-p0", dir := "~user/é x\\q", line := 1 }]
  | .error _ => false

-- Nonexistent/empty directories are the caller's preflight responsibility.
#guard
  match parseSave "/home/me" "pane\td\t0\t\t\t0\t\t:\t\t\t:" with
  | .ok panes => panes == [{ name := "d-w0-p0", dir := "", line := 1 }]
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

-- A later malformed command rejects the complete save, even though it is discarded.
#guard
  match
    parseSave "/home/me"
      ("pane\td\t0\t\t\t0\t\t:~/work\t\t\t:arbitrary command\n" ++
        "pane\td\t0\t\t\t1\t\t:/tmp\t\t\t:ignored\x00command") with
  | .error error => error == "malformed pane record at line 2"
  | .ok _ => false

-- Skipping a middle record preserves the directories, line numbers and order.
#guard
  plan ["b"]
      [{ name := "a", dir := "/a", line := 1 }, { name := "b", dir := "/b", line := 2 },
        { name := "c", dir := "/c", line := 3 }] ==
    [{ name := "a", dir := "/a", line := 1 }, { name := "c", dir := "/c", line := 3 }]

#guard
  plan ["a", "b"]
      [{ name := "a", dir := "/a", line := 1 }, { name := "b", dir := "/b", line := 2 }] ==
    []

end Tools.Resurrect.Tests
