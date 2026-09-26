module

public import E2E.Harness
import Theorems.Coverage

public section

/-! # E2E.Coverage — coverage of code by claims

`Theorems.Coverage` makes the build fail unless every inventoried pure `def`
occurs as its exact fully qualified constant in a theorem type. This runtime half
discovers renderer and replay definitions referenced outside their own module
by runtime-reachable code, and requires an explicit backing entry below. It uses
the same definition census, so multiline signatures and intermediate byte
containers cannot evade classification. The semantic gate independently ensures
each definition occurs in some theorem type. -/

namespace E2E.Coverage

open E2E.Harness
open Theorems.Coverage

def emitters : List (String × String) :=
  [("Replay.start", "start_faithful / drain_start / start_parts"),
    ("Replay.next", "next_faithful / next_bounded / next_progress / steps_storage"),
    ("Replay.followingCap", "followingCap_front / followingCap_frame"),
    ("Render.charsetAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.csiB", "component of Replay.start_faithful / drain_start"),
    ("Render.csiNum", "component of Replay.start_faithful / drain_start"),
    ("Render.csiNum2", "component of Replay.start_faithful / drain_start"),
    ("Render.csiPriv", "component of Replay.start_faithful / drain_start"),
    ("Render.cursorAnsi", "component of Replay.start_faithful / drain_start"),
    ("Render.cursorPendingAnsi", "cursorPendingAnsi_feed_eq / Replay.start_faithful"),
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
    ("Render.utf8s", "utf8s_no_frame / Replay.text_uncons / utf8s_length_le"),
    ("Render.history", "history_framing / history_lines / history_records"),
    ("Render.screenText", "screenText_framing / screenText_lines / screenText_records")]

/-- Renderer and replay operations referenced anywhere runtime-reachable,
outside their defining module. Return types and line wrapping are irrelevant. -/
def runtimeEmitters (defs : Array Lean.Name) : IO (Array String) := do
  let mut refs : Array String := #[]
  let mut files ← leanFiles (System.FilePath.mk "Linger")
  files := files.push (System.FilePath.mk "Main.lean")
  for f in files do
    if !(← f.pathExists) then
      continue
    let src := stripComments (← IO.FS.readFile f)
    for family in ["Render", "Replay"] do
      if f == System.FilePath.mk s!"Linger/Core/{family}.lean" then
        continue
      for chunk in (src.splitOn s!"{family}.").tail! do
        let token := (chunk.takeWhile identChar).toString
        let name := s!"{family}.{token}"
        if defs.contains s!"Linger.Core.{name}".toName && !refs.contains name then
          refs := refs.push name
  return refs.qsort (· < ·)

public def run : IO UInt32 := do
  let mut fails : Array String := #[]
  let defs ← pureDefNames
  IO.println s!"pure semantic coverage: {defs.size} explicit definitions, all in theorem types"
  let found ← runtimeEmitters defs
  IO.println s!"runtime renderer/replay operations: {String.intercalate " " found.toList}"
  for name in found do
    match (emitters.find? (·.1 == name)).map (·.2) with
    | none =>
      fails := fails.push s!"runtime-reachable `{name}` has no backing entry"
    | some why =>
      IO.println s!"  {name}: backed — {(why.take 60).toString}…"
  for (name, _) in emitters do
    if !found.contains name then
      fails :=
        fails.push
          s!"`{name}` is classified but no longer runtime-referenced; delete the stale entry"
  for msg in fails do
    IO.eprintln s!"COVERAGE FAIL: {msg}"
  IO.println s!"FAILURES: {fails.size}"
  return if fails.isEmpty then 0 else 1

end E2E.Coverage
