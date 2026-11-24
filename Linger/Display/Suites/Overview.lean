module

public import Verify.Harness
import Linger.Display.CoreCode.Listing
import Terminal.CoreCode.Vt
import Linger.Session.CoreCode.Checkpoint

public section

/-! # Linger.Display.Suites.Overview — explicit `linger ls` prints a list and exits

The overview must be a plain, pipeable, self-terminating listing that never
blocks on stdin. The two exit checks run through `Env.cliTimeout`: a picker that
waited on redirected stdin would fail here, not hang the gate. `Linger.App.Suites.Manager`
separately checks bare help in every stream mode, explicit terminal selection and
`ls` with both streams on a terminal.
Selector acceptance chooses either an existing target or an explicit creation
row (`Linger/Selector/Proofs/Picker.lean`).

`cmdList` in `Linger.App.Shell` writes `terminalListing withColor width` of its rows straight to
stdout, without color or width when stdout is not a terminal, so `terminalListing false none []`
**is** the empty-state line and the suite cannot drift from its wording. A row shows the
session's present: a description an older linger saved, until a rename ends it, the program in its
terminal's foreground and that program's directory, and a shell at its prompt by its directory
alone. -/

namespace Linger.Display.Suites.Overview

open Verify.Harness
open Linger.Display.Listing (terminalListing)

/-- The row of session `name` in a plain `linger ls`, or `""` when none lists it. -/
def rowOf (e : Env) (name : String) : IO String := do
  let rows ← lines <$> e.out #["ls"]
  return (rows.find? fun row => rowName row == name).getD ""

/-- A row shows the session's present: a description an older linger saved, where the program's
title would be while the program sets none, until a rename ends it; the program in its foreground
with that program's directory; and a shell at its prompt by its directory alone. -/
def present (e : Env) : IO Unit :=
  IO.FS.withTempDir fun scratch => do
    let dir := (← IO.FS.realPath scratch).toString
    let ck : Linger.Session.Checkpoint.Ckpt Terminal.Vt.Vt :=
      { vt := Terminal.Vt.Vt.init 80 24, cwd := dir,
        fields := [("description", "fixing the parser")] }
    IO.FS.writeBinFile s!"{e.dir}/described.ckpt" (Linger.Session.Checkpoint.saveBytes ck)
    let (rrc, _, _) ← e.cli #["resume", "described"]
    let shown ← waitFor patienceMs (return has (← rowOf e "described") "fixing the parser")
    expect (rrc == 0 && shown)
        s!"an older record's description shows as the caption: {← rowOf e "described"}"
    expect ((← e.field "described" "description") == some "fixing the parser")
        "porcelain carries the description an older linger saved"
    let (nrc, _, _) ← e.cli #["rename", "described", "renamed-now"]
    let row ← rowOf e "renamed-now"
    expect
        (nrc == 0 && !has row "fixing" && row != "" &&
          (← e.field "renamed-now" "description").isNone)
        s!"a rename ends an older record's description: {row}"
    let _ ← e.typeIn "sleeper" #["cd", shellQuote dir, "&&", "sleep", "100"]
    let busy ←
      waitFor patienceMs do
          let row ← rowOf e "sleeper"
          return has row "sleep 100" && has row dir
    expect busy
        s!"a session running sleep 100 shows sleep 100 and its directory: {← rowOf e "sleeper"}"
    expect
        ((← e.field "sleeper" "fgdir") == some dir &&
          (← e.field "sleeper" "fg") == some "sleep 100")
        "porcelain carries the foreground program and its directory"
    let client ← e.spawn #["attach", "prompt"]
    let _ ← waitFor patienceMs (return (← e.info "prompt" "pid").isSome)
    client.bye
    let _ ← e.cli #["send", "prompt", s!"cd {shellQuote dir}\n"]
    let atPrompt ←
      waitFor patienceMs do
          let row ← rowOf e "prompt"
          return has row dir && !has row "/bin/sh"
    expect atPrompt
        s!"a shell at its prompt shows its directory but not its shell: {← rowOf e "prompt"}"
    e.killAll #["renamed-now", "sleeper", "prompt"]

/-- Whether a program's terminal echoes, as the program last set it, is a machine field of its
own: `ls NAME --porcelain` gives `echo true` for a program whose terminal echoes and `echo false`
once it turns echo off, and no human row shows it. The program is a script file, so that its row
names no word of what it runs. -/
def echoes (e : Env) : IO Unit :=
  IO.FS.withTempDir fun scratch => do
    let script := scratch / "quiet.sh"
    IO.FS.writeFile script "read -r line\nstty -echo\nexec sleep 100\n"
    let _ ← e.cli #["start", "hushed", "sh", script.toString]
    let on ← waitFor patienceMs (return (← e.info "hushed" "echo") == some "true")
    let _ ← e.cli #["send", "hushed", "go\n"]
    let off ← waitFor patienceMs (return (← e.info "hushed" "echo") == some "false")
    expect (on && off) "the porcelain says whether the program's terminal echoes, as it set it"
    let row ← rowOf e "hushed"
    expect (has row "sleep 100" && !has row "echo" && !has row "false")
        s!"no human row shows whether a terminal echoes: {row}"
    e.killAll #["hushed"]

/-- The display column where `needle` starts in `row`, counting each character as wide as a
terminal shows it, or none when the row lacks it. -/
def columnOf (row needle : String) : Option Nat :=
  let cs := row.toList
  (List.range cs.length).findSome? fun i =>
    if (cs.drop i).take needle.length == needle.toList then
      some ((cs.take i).map Terminal.Vt.charWidth).sum
    else none

/-- One field, one column: a row's program starts at the same display column in every row,
whatever the names' lengths and however wide the characters of the captions before it. -/
def aligned (e : Env) : IO Unit :=
  IO.FS.withTempDir fun scratch => do
    let dir := (← IO.FS.realPath scratch).toString
    for (name, caption) in [("a", "漢字"), ("longer-name", "abcdefgh")] do
      -- the caption is the title the program gives its window
      let _ ←
        e.typeIn name
            #["printf", s!"'\\033]2;{caption}\\007'", "&&", "cd", shellQuote dir, "&&", "sleep",
              "100"]
    let ready ←
      waitFor patienceMs do
          return has (← rowOf e "a") "sleep 100" && has (← rowOf e "longer-name") "sleep 100"
    let short ← rowOf e "a"
    let long ← rowOf e "longer-name"
    expect
        (ready && (columnOf short "sleep 100").isSome &&
          columnOf short "sleep 100" == columnOf long "sleep 100" &&
          columnOf short "漢字" == columnOf long "abcdefgh")
        s!"each field starts at one display column in every row: {short} / {long}"
    e.killAll #["a", "longer-name"]

/-- A row shows two facts, each in its own column: whether there is something for you, then what
the session is (`row_pair`). A program that rang while it declares itself working lists `⚑ ⣷`, one
that printed more lines than its screen holds `∙ ⣀`, a quiet program on the alternate screen, which
keeps no history, a blank mark and `⣀`, and one that ended while nobody was attached `∙ ✗`. A view
lists them by attention, then by lifecycle, then by name, and the summary counts attention alone;
the porcelain gives each column one machine field. -/
def columns (e : Env) : IO Unit := do
  let mark := fun (a : Linger.Display.Status.Attention) => Linger.Display.Status.mark a
  let icon := fun (st : Linger.Display.Status.State) => Linger.Display.Status.icon st
  let head := fun (a : Linger.Display.Status.Attention) (st : Linger.Display.Status.State) name =>
    s!"{mark a} {icon st} {name}"
  let _ ← e.cli #["start", "a-alt", "sh", "-c", "printf '\\033[?1049h'; exec sleep 100"]
  let _ ← e.cli #["start", "b-printed", "sh", "-c", "seq 100; exec sleep 100"]
  let _ ← e.cli #["start", "c-rang", "sh", "-c", "printf '\\033]9;4;3;\\007\\a'; exec sleep 100"]
  let _ ← e.cli #["start", "d-ended", "sh", "-c", "seq 100; exit 3"]
  let settled ←
    waitFor patienceMs do
        return (← e.status "c-rang") == ⟨.asked, .working⟩ &&
            (← e.status "b-printed") == ⟨.unread, .idle⟩ &&
            (← e.field "a-alt" "fg") == some "sleep 100" &&
            (← e.state "d-ended") == .exitedBad
  let rows := lines (← e.out #["ls"])
  let rowOf := fun name => (rows.find? fun row => rowName row == name).getD ""
  expect (settled && (rowOf "c-rang").startsWith (head .asked .working "c-rang"))
      s!"a session that rang while it works shows both, {mark .asked} {icon .working}: {rows}"
  expect ((rowOf "b-printed").startsWith (head .unread .idle "b-printed"))
      s!"a session that printed lines nobody saw shows {mark .unread} {icon .idle}: {rows}"
  expect ((rowOf "a-alt").startsWith (head .none .idle "a-alt"))
      s!"a quiet program on the alternate screen shows a blank mark and {icon .idle}: {rows}"
  expect ((rowOf "d-ended").startsWith (head .unread .exitedBad "d-ended"))
      s!"an ending nobody was attached to see is news, {mark .unread} {icon .exitedBad}: {rows}"
  let order := rows.map rowName
  expect (order == ["c-rang", "b-printed", "d-ended", "a-alt"])
      s!"a view lists by attention, then by lifecycle, then by name: {order}"
  let (src, summary, _) ← e.cli #["ls", "--summary"]
  expect (src == 0 && summary == Linger.Display.Status.summary [.asked, .unread, .unread] ++ "\n")
      s!"the summary counts attention alone: {summary.trimAscii}"
  let fields := (← e.row "c-rang").filter fun kv => kv.1 == "attention" || kv.1 == "status"
  expect (fields == [("attention", "asked"), ("status", "working")])
      s!"the porcelain gives each column one machine field: {fields}"
  e.killAll #["a-alt", "b-printed", "c-rang", "d-ended"]

/-- The overview suite: explicit `linger ls` lists, exits and never reads stdin. -/
def run : IO UInt32 :=
  Env.suite "overview" fun e => do
    -- With every state override absent, fallback storage is still per-user.
    let uid ← Os.Shell.getuid
    let (vrc, vout, _) ←
      e.cliEnv #[("LINGER_DIR", none), ("XDG_STATE_HOME", none), ("HOME", none)] #["--version"]
    expect (vrc == 0 && has vout s!"state:   /tmp/linger-{uid}/state/")
        "HOME-less state fallback is namespaced by uid"
    -- empty state: the explicit listing says so and exits 0 within the deadline
    let emptyLine := terminalListing false none []
    match ← e.cliTimeout #["ls"] 15000 with
    | none =>
      expect false "linger ls exits (it hung — a picker?)"
    | some (rc, out, err) =>
      expect (rc == 0 && out.toUTF8 == ByteArray.mk emptyLine.toArray && err.isEmpty)
          "linger ls prints exactly the empty overview and exits"
    -- two live sessions: both names survive in the explicit listing
    let _ ← e.typeIn "alpha" #["true"]
    let _ ← e.typeIn "beta" #["true"]
    match ← e.cliTimeout #["ls"] 15000 with
    | none =>
      expect false "linger ls exits (it hung — a picker?)"
    | some (rc, out, err) =>
      expect (rc == 0 && has out "alpha" && has out "beta" && err.isEmpty)
          "linger ls lists both live sessions"
    -- the porcelain is what a peer's `-r` parses, so assert that it PARSES as
    -- records rather than that the bytes appear
    let recs := records (← e.out #["ls", "--porcelain"])
    expect
        (recs.any (fun kv => kv.1 == "name" && kv.2 == "alpha") &&
          recs.any (fun kv => kv.1 == "state" && kv.2 == "live"))
        "porcelain carries name/state (the remote-parse contract)"
    e.killAll #["alpha", "beta"]
    -- names as people read them: a number in a name counts by its value, so w2 comes before w10
    for name in ["w10", "w2", "w1"] do
      let _ ← e.typeIn name #["true"]
    let names :=
      (records (← e.out #["ls", "--porcelain"])).filterMap fun kv =>
        if kv.1 == "name" then some kv.2 else none
    expect (names == ["w1", "w2", "w10"]) s!"ls lists w1, w2 and w10 in natural order: {names}"
    e.killAll #["w1", "w2", "w10"]
    let _ ← waitFor 5000 (return (← e.out #["ls"]).toUTF8 == ByteArray.mk emptyLine.toArray)
    -- Invalid filenames are ignored rather than rewritten into selectable aliases.
    -- Control bytes must not reach the terminal, and no resumable row may appear.
    let hostile := "ev\x1b[31mil\tfake.ckpt"
    IO.FS.writeBinFile ((System.FilePath.mk e.dir) / hostile)
        ("LINGER\x01".toUTF8 ++ ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)
    let out ← e.out #["ls"]
    expect (out.toUTF8 == ByteArray.mk emptyLine.toArray)
        "a hostile checkpoint filename neither injects an escape nor creates an alias"
    IO.FS.removeFile ((System.FilePath.mk e.dir) / hostile)
    present e
    aligned e
    echoes e
    columns e

end Linger.Display.Suites.Overview
