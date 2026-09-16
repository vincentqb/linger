module

public import E2E.Harness
public import Linger.Core.Listing

public section

/-! # E2E.Overview — bare `linger` and `linger ls` print a list and EXIT

Ported from `tests/overview_test.py`. They are NOT an interactive full-screen
picker.

Regression guard: a first-time user once ran bare `linger`, got a full-screen TUI,
typed `ls` at it, and that created a session literally named `ls`.
`specs/archive/lean-zmx.md` records the removal; this suite is what keeps it
removed. So the overview must be a plain, pipeable, self-terminating listing that
never blocks on stdin — which is why every form runs through `Env.cliTimeout`: a
picker that sat on stdin would FAIL here, not hang the gate.

WHAT THE PORT STRENGTHENS. The empty-state check compared against the literal
`'no sessions'`; `Cli.cmdList` writes `ByteArray.mk (humanListing rows).toArray`
straight to stdout, so `humanListing []` **is** the empty-state line and the suite
can no longer drift from its wording. The porcelain check compared two substrings;
it now parses through `records`, the same reader `Env.field` and `Core.Remote` use
— the comment on the original line called it "the remote-parse contract", and a
substring test does not test parsing. -/

namespace E2E.Overview

open E2E.Harness
open Linger.Core.Status (Status)
open Linger.Core.Listing (humanListing rowStatus)

/-- Name the form under test inside the check's own label, so a failure says which
of the two spellings broke. -/
def label (args : Array String) : String :=
  if args.isEmpty then "linger (bare)" else "linger " ++ String.intercalate " " args.toList

/-- The two spellings of the overview. The bug was in the bare form and only the
bare form, which is why every listing claim is made twice. -/
def forms : List (Array String) := [#[], #["ls"]]

def run : IO UInt32 := do
  let e ← Env.make "overview"
  let mut f := 0
  -- With every state override absent, fallback storage is still per-user.
  let uid ← Linger.Posix.getuid
  let (vrc, vout, _) ←
    e.cliEnv #[("LINGER_DIR", none), ("XDG_STATE_HOME", none), ("HOME", none)] #["version"]
  f :=
    f +
      (←
        expect (vrc == 0 && has vout s!"state:   /tmp/linger-{uid}/state/")
            "HOME-less state fallback is namespaced by uid")
  -- empty state: both forms say so and exit 0, within the deadline
  let emptyLine := humanListing []
  for args in forms do
    match ← e.cliTimeout args 15000 with
    | none =>
      f := f + (← expect false s!"{label args} exits (it hung — a picker?)")
    | some (rc, out, _) =>
      f :=
        f +
          (←
            expect (rc == 0 && hasBytes out.toUTF8 emptyLine)
                s!"{label args} prints overview and exits")
  -- two live sessions: listed by name in both forms
  let _ ← e.cli #["run", "alpha", "true"]
  let _ ← e.cli #["run", "beta", "true"]
  IO.sleep 1200
  for args in forms do
    match ← e.cliTimeout args 15000 with
    | none =>
      f := f + (← expect false s!"{label args} exits (it hung — a picker?)")
    | some (rc, out, _) =>
      f :=
        f +
          (←
            expect (rc == 0 && has out "alpha" && has out "beta")
                s!"{label args} lists both live sessions")
  -- the porcelain is what a peer's `-r` parses, so assert that it PARSES as
  -- records rather than that the bytes appear
  let recs := records (← e.out #["ls", "--porcelain"])
  f :=
    f +
      (←
        expect
            (recs.any (fun kv => kv.1 == "name" && kv.2 == "alpha") &&
              recs.any (fun kv => kv.1 == "state" && kv.2 == "live"))
            "porcelain carries name/state (the remote-parse contract)")
  e.killAll #["alpha", "beta"]
  IO.sleep 500
  -- A checkpoint filename carrying an ESC and a TAB must not reach the terminal as
  -- an escape sequence. The name goes through `Listing.rowFields` → `Name.sanitize`
  -- and the whole row through `Render.utf8s`, so the control bytes cannot appear.
  -- The body is deliberately not a loadable checkpoint and does not have to be:
  -- §Row is that a row's identity comes from the filename alone — `Cli.cmdList`
  -- builds the resumable row from `Paths.listCkptNames` without opening the file.
  let hostile := "ev\x1b[31mil\tfake.ckpt"
  IO.FS.writeBinFile ((System.FilePath.mk e.dir) / hostile)
      ("LINGER\x01".toUTF8 ++ ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)
  let out ← e.out #["ls"]
  f :=
    f +
      (←
        expect (!has out "\x1b" && !has out "\t")
            "a hostile checkpoint filename cannot inject an escape into the listing")
  -- …and it still lists. The glyph half is derived: `rowStatus .stale` is what
  -- `Cli.cmdList` writes into the row's status, and `ofName_name` is why
  -- `humanRow` prints exactly that state's icon.
  f :=
    f +
      (←
        expect
            (has out "resumable" &&
              has out (String.singleton (Linger.Core.Status.icon (rowStatus .stale))))
            "the hostile checkpoint still lists (as resumable)")
  verdict e f

end E2E.Overview
