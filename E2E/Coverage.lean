module

public import E2E.Harness
import Theorems.Coverage

public section

/-! # E2E.Coverage — coverage of code by claims

`Theorems.Coverage` makes the build fail unless every explicit pure-core `def`
occurs as its exact fully qualified constant in a theorem type. This runtime half
discovers every `Render.<f>` stream referenced by runtime-reachable code and
requires an explicit backing entry below. The semantic gate independently ensures
each stream definition occurs in some theorem type. -/

namespace E2E.Coverage

open E2E.Harness
open Theorems.Coverage

def emitters : List (String × String) :=
  [("restore",
      "restore_grounds / restore_u8_zero / restore_modes_any / restore_pen_any / \
       restore_sticky_any / restore_cursor_any / restore_grid_any / restore_tabs_any"),
    ("leaveAnsi", "leave_canonical / leave_canonical_all"),
    ("utf8s", "utf8s_no_ctl / utf8s_no_esc / utf8s_no_esc_bel / utf8s_no_frame"),
    ("history", "history_framing / history_lines / history_records"),
    ("screenText", "screenText_framing / screenText_lines / screenText_records")]

/-- `Render.<f>` streams referenced anywhere runtime-reachable, outside their
defining module. -/
def runtimeEmitters : IO (Array String) := do
  let mut refs : Array String := #[]
  let mut files ← leanFiles (System.FilePath.mk "Linger")
  files := files.push (System.FilePath.mk "Main.lean")
  for f in files do
    if f.fileName == some "Render.lean" && f.parent.map (·.fileName) == some (some "Core") then
      continue
    if !(← f.pathExists) then
      continue
    let src := stripComments (← IO.FS.readFile f)
    for chunk in (src.splitOn "Render.").tail! do
      let n := (chunk.takeWhile identChar).toString
      if !n.isEmpty && !refs.contains n then
        refs := refs.push n
  let renderSrc := stripComments (← IO.FS.readFile (System.FilePath.mk "Linger/Core/Render.lean"))
  let mut streams : Array String := #[]
  for line in renderSrc.splitOn "\n" do
    let l := dropModifiers line
    if l.startsWith "def " && (has l ": Bytes" || has l ": String") then
      let n := declName (l.drop 4).toString
      if !n.isEmpty then
        streams := streams.push n
  return (refs.filter (streams.contains ·)).qsort (· < ·)

public def run : IO UInt32 := do
  let mut fails : Array String := #[]
  let defs ← coreDefNames
  IO.println s!"pure-core semantic coverage: {defs.size} explicit definitions, all in theorem types"
  let found ← runtimeEmitters
  IO.println s!"runtime-emitted byte streams: {String.intercalate " " found.toList}"
  for name in found do
    match (emitters.find? (·.1 == name)).map (·.2) with
    | none =>
      fails := fails.push s!"the runtime emits `Render.{name}` but it has no backing entry"
    | some why =>
      IO.println s!"  {name}: backed — {(why.take 60).toString}…"
  for (name, _) in emitters do
    if !found.contains name then
      fails :=
        fails.push
          s!"`Render.{name}` is classified but no longer runtime-emitted; delete the stale entry"
  for msg in fails do
    IO.eprintln s!"COVERAGE FAIL: {msg}"
  IO.println s!"FAILURES: {fails.size}"
  return if fails.isEmpty then 0 else 1

end E2E.Coverage
