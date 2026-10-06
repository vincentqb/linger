module

import Linger.Tools.Resurrect
public meta import Linger.Tools.Resurrect
import Linger.Core.Status
public meta import Linger.Core.Status

/-! Concrete checks of the pure API. General kernel-checked contracts live in
`Theorems.Resurrect`; these fixtures exercise the actual string operations. -/

namespace Linger.Tools.Resurrect.Tests

open Linger.Tools.Resurrect

-- Browsing uses original window context and pane order. Display text is safe,
-- while the action fields retain exact paths and source lines.
#guard
  let text :=
    "pane\tdesk\t2\t1\t:*\t1\tunused\t:/tmp/é space\r\x1b\t1\tvi\t:never run this\n" ++
      "window\tdesk\t2\t:editor\x1b[31m\t1\t:*\n" ++
      "pane\tdesk\t1\t0\t:\t0\tunused\t:/other\t0\tsh\t:\n" ++
      "window\tdesk\t1\t:shell"
  match parseSave "" text with
  | .error _ => false
  | .ok panes =>
    let rows := catalogRows text panes
    rows.map (fun row => row.lookup "name") == [some "desk-w2-p1", some "desk-w1-p0"] &&
      rows.map (fun row => row.lookup "directory") == [some "/tmp/é space\r\x1b", some "/other"] &&
      rows.map (fun row => row.lookup "line") == [some "1", some "3"] &&
      rows.all (fun row => row.lookup "status" == some (Linger.Core.Status.name .resumable)) &&
      rows.map (fun row => row.lookup "cmd") ==
        [some "desk:2 editor?[31m  ·  /tmp/é space??", some "desk:1 shell  ·  /other"]

#guard
  let pane : Pane := { name := "desk-w0-p0", dir := "/exact path\n\r\x1b", line := 3 }
  selectedPane pane.name pane.dir pane.line == some pane &&
    (catalogRows "unrelated display metadata" [pane]).head?.bind (·.lookup "directory") ==
      some pane.dir

#guard
  ["", ".hidden", "bad/name", "bad name", String.ofList (List.replicate 81 'x')].all fun name =>
    (selectedPane name "/tmp" 1).isNone

#guard (selectedPane "valid" "/bad\x00dir" 1).isNone

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

-- Export the imported name/cwd view without carrying its source metadata.
#guard
  let source :=
    "window\tdesk\t0\t:original title\r\n" ++
      "pane\tdesk\t0\t1\t:*-Z\t0\toriginal title\t:~/work\\ space\t1\tvi\t:vi 'private draft'\r\n" ++
      "unknown\tfuture metadata"
  match parseSave "/home/me" source with
  | .error _ => false
  | .ok imported =>
    let fields := common imported
    match renderSave fields with
    | .error _ => false
    | .ok text =>
      fields == [("desk-w0-p0", "/home/me/work space")] && !text.contains "original title" &&
        !text.contains "private draft" &&
        !text.contains "future metadata" &&
        match parseSave "/other/home" text with
        | .ok panes => common panes == fields
        | .error _ => false

-- Import acceptance cannot bypass the serializer's directory guard.
#guard
  let source := "pane\tdesk\t0\t1\t:*\t0\ttitle\t:/tmp/#literal\t1\tsh\t:\n"
  match parseSave "" source with
  | .error _ => false
  | .ok imported =>
    let fields := common imported
    match renderSave fields with
    | .error error => error == "unrepresentable cwd in tmux save: /tmp/#literal"
    | .ok _ => false

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

-- Flags, titles, active/current-command fields and valid saved commands have no effect.
#guard
  [("d", "d-w0-p0"), ("linger=d~api", "d.api")].all fun (session, name) =>
    [("", "", "", "", "", ":"), ("1", ":*-Z", "a title", "0", "vi", ":vi 'a b'; tail x"),
          ("0", "arbitrary flags", "another title", "1", "sh",
            ":printf '%s' \"$HOME\" && custom-tool --anything"),
          ("not active", "\x00?", "\x1b]0;λ title\x07", "unknown", "anything",
            ":  λ ./unlisted\\ path 'quoted'  ")].all
      fun (windowActive, flags, title, paneActive, currentCommand, savedCommand) =>
      match
        parseSave "/home/me"
          (s!"window\tignored\npane\t{session}\t0\t{windowActive}\t{flags}\t0\t{title}" ++
            s!"\t:~/work\\ space\t{paneActive}\t{currentCommand}\t{savedCommand}") with
      | .ok panes => panes == [{ name, dir := "/home/me/work space", line := 2 }]
      | .error _ => false

-- Discarding metadata does not hide failures in the identity or directory.
#guard
  [("bad/name", ":/tmp", "projected session is not a valid linger name at line 1: bad/name-w0-p0"),
        ("linger=raw.dot", ":/tmp", "malformed native session at line 1: linger=raw.dot"),
        ("d", "/tmp", "malformed pane record at line 1"),
        ("d", ":/tmp/\x00bad", "malformed pane record at line 1")].all
    fun (session, cwd, expected) =>
    match parseSave "" s!"pane\t{session}\t0\t\t\t0\t\t{cwd}\t\t\t:",
      parseSave "" s!"pane\t{session}\t0\t1\t:*\t0\tλ title\t{cwd}\t1\tvi\t:arbitrary command" with
    | .error before, .error after => before == expected && after == expected
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

end Linger.Tools.Resurrect.Tests
