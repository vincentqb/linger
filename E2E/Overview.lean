module

public import E2E.Harness
public import Linger.Core.Listing

public section

/-! # E2E.Overview — explicit `linger ls` prints a list and exits

The overview must be a plain, pipeable, self-terminating listing that never
blocks on stdin. The two exit checks run through `Env.cliTimeout`: a picker that
waited on redirected stdin would fail here, not hang the gate. `E2E.Manager`
separately checks bare help in every stream mode, explicit terminal selection and
`ls` with both streams on a terminal.
Selector acceptance chooses either an existing target or an explicit creation
row (`Theorems/Picker.lean`).

`Cli.cmdList` writes `ByteArray.mk (humanListing rows).toArray` straight to stdout,
so `humanListing []` **is** the empty-state line and the suite cannot drift from
its wording. -/

namespace E2E.Overview

open E2E.Harness
open Linger.Core.Listing (humanListing)

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
  -- empty state: the explicit listing says so and exits 0 within the deadline
  let emptyLine := humanListing []
  match ← e.cliTimeout #["ls"] 15000 with
  | none =>
    f := f + (← expect false "linger ls exits (it hung — a picker?)")
  | some (rc, out, err) =>
    f :=
      f +
        (←
          expect (rc == 0 && out.toUTF8 == ByteArray.mk emptyLine.toArray && err.isEmpty)
              "linger ls prints exactly the empty overview and exits")
  -- two live sessions: both names survive in the explicit listing
  let _ ← e.cli #["run", "alpha", "true"]
  let _ ← e.cli #["run", "beta", "true"]
  IO.sleep 1200
  match ← e.cliTimeout #["ls"] 15000 with
  | none =>
    f := f + (← expect false "linger ls exits (it hung — a picker?)")
  | some (rc, out, err) =>
    f :=
      f +
        (←
          expect (rc == 0 && has out "alpha" && has out "beta" && err.isEmpty)
              "linger ls lists both live sessions")
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
  -- Invalid filenames are ignored rather than rewritten into selectable aliases.
  -- Control bytes must not reach the terminal, and no resumable row may appear.
  let hostile := "ev\x1b[31mil\tfake.ckpt"
  IO.FS.writeBinFile ((System.FilePath.mk e.dir) / hostile)
      ("LINGER\x01".toUTF8 ++ ByteArray.mk (List.replicate 32 (0 : UInt8)).toArray)
  let out ← e.out #["ls"]
  f :=
    f +
      (←
        expect (!has out "\x1b" && !has out "\t")
            "a hostile checkpoint filename cannot inject an escape into the listing")
  f :=
    f +
      (←
        expect (out.toUTF8 == ByteArray.mk emptyLine.toArray)
            "an invalid checkpoint filename cannot create a selectable alias")
  verdict e f

end E2E.Overview
