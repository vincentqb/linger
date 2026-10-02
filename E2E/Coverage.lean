module

meta import Theorems.Coverage

meta section

/-! # E2E.Coverage — coverage of code by claims

`Theorems.Coverage` checks exact theorem-type coverage and its fixed regression
fixtures at build time. This standalone check repeats the semantic check against
fresh sources, even with cached imports, then requires an explicit backing entry
for renderer/replay operations referenced outside their own module.
Build the program first; `tests/e2e.sh` runs this after its build. -/

namespace E2E.Coverage

open Lean Elab Command
open Theorems.Coverage

def emitters : List (String × String) :=
  [("Replay.start", "start_faithful / drain_start / start_parts"),
    ("Replay.next", "next_faithful / next_bounded / next_progress / steps_storage"),
    ("Render.charsetAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.csiB", "component of Replay.start_faithful / drain_start"),
    ("Render.csiNum", "component of Replay.start_faithful / drain_start"),
    ("Render.csiNum2", "component of Replay.start_faithful / drain_start"),
    ("Render.csiPriv", "component of Replay.start_faithful / drain_start"),
    ("Render.cursorAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.cursorPendingAnsi", "cursorPendingAnsi_feed_eq / Replay.start_faithful"),
    ("Render.digits", "digits_range / Terminal.noNl_digits"),
    ("Render.dropTrailingBlanks", "dropTrailingBlanks_subset / Listing.humanRow_printable"),
    ("Render.escB", "component of Replay.start_faithful / drain_start"),
    ("Render.modesAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.pendingAnsi", "pendingAnsi_feed_eq / Replay.start_faithful"),
    ("Render.penSgr", "component of Replay.start_faithful / drain_start"),
    ("Render.prologueAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.regionAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.rowAnsi", "rowAnsi_len_add_crlf_le_cost / Replay.rows_uncons / drain_start"),
    ("Render.savedAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.savedPendingAnsi", "savedPendingAnsi_feed_eq / Replay.start_faithful"),
    ("Render.scrollbackAnsi", "scrollbackAnsi_le / Replay.start_faithful / drain_start"),
    ("Render.tabsAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.leaveAnsi", "leave_canonical / leave_canonical_all"),
    ("Render.safeChar", "safeChar_ge / Terminal.Title.payload_safe / Listing.rowPieces_printable"),
    ("Render.utf8s", "utf8s_no_frame / Replay.text_uncons / utf8s_length_le"),
    ("Render.history", "history_framing / history_lines / history_records"),
    ("Render.screenText", "screenText_framing / screenText_lines / screenText_records")]

run_cmd
  let defs ← checkPureCoverage
  let mut fails : Array String := #[]
  IO.println s!"pure semantic coverage: {defs.size} explicit definitions, all in theorem types"
  let found ← liftIO (runtimeEmitters defs)
  IO.println s!"program renderer/replay references: {String.intercalate " " found.toList}"
  for name in found do
    match (emitters.find? (·.1 == name)).map (·.2) with
    | none =>
      fails := fails.push s!"referenced `{name}` has no backing entry"
    | some why =>
      IO.println s!"  {name}: backed — {(why.take 60).toString}…"
  for (name, _) in emitters do
    if !found.contains name then
      fails :=
        fails.push s!"`{name}` is classified but no longer referenced; delete the stale entry"
  for msg in fails do
    IO.eprintln s!"COVERAGE FAIL: {msg}"
  IO.println s!"FAILURES: {fails.size}"
  unless fails.isEmpty do
    throwError "runtime emitter classification failed"

end E2E.Coverage
