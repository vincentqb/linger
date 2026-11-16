module

public import Verify.Harness
import Linger.Display.CoreCode.Listing
import Terminal.CoreCode.Vt

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
session's present: its description, which `describe` sets and clears, the program in its
terminal's foreground and that program's directory, and a shell at its prompt by its directory
alone. -/

namespace Linger.Display.Suites.Overview

open Verify.Harness
open Linger.Display.Listing (terminalListing)

/-- The row of session `name` in a plain `linger ls`, or `""` when none lists it. -/
def rowOf (e : Env) (name : String) : IO String := do
  let rows ← lines <$> e.out #["ls"]
  return (rows.find? fun row => (row.splitOn " ").getD 1 "" == name).getD ""

/-- A row shows the session's present: its description, which `describe` sets and, with no
text, clears; the program in its foreground with that program's directory; and a shell at its
prompt by its directory alone. -/
def present (e : Env) : IO Unit :=
  IO.FS.withTempDir fun scratch => do
    let dir := (← IO.FS.realPath scratch).toString
    let _ ← e.typeIn "described" #["true"]
    let (drc, _, _) ← e.cli #["describe", "described", "fixing", "the", "parser"]
    let shown ← waitFor patienceMs (return has (← rowOf e "described") "fixing the parser")
    expect (drc == 0 && shown) "a described session shows its description"
    expect ((← e.field "described" "description") == some "fixing the parser")
        "porcelain carries the description as its label"
    let (crc, _, _) ← e.cli #["describe", "described"]
    let row ← rowOf e "described"
    expect
        (crc == 0 && !has row "fixing" && row != "" && (← e.field "described" "description").isNone)
        "describe with no text clears the description"
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
    e.killAll #["described", "sleeper", "prompt"]

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
      let _ ← e.typeIn name #["cd", shellQuote dir, "&&", "sleep", "100"]
      let _ ← e.cli #["describe", name, caption]
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

end Linger.Display.Suites.Overview
