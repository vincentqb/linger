module

meta import Theorems.Coverage

meta section

/-! # E2E.Coverage — coverage of code by claims

`Theorems.Coverage` makes the build fail unless every inventoried pure `def`
occurs as its exact fully qualified constant in a theorem type. This standalone
check reads the built program's resolved references and requires an explicit
backing entry for renderer/replay operations used outside their own module.
Build the program first; `tests/e2e.sh` runs this after its clean build. -/

namespace E2E.Coverage

open Lean Elab Command
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
    ("Render.utf8s", "utf8s_no_frame / Replay.text_uncons / utf8s_length_le"),
    ("Render.history", "history_framing / history_lines / history_records"),
    ("Render.screenText", "screenText_framing / screenText_lines / screenText_records")]

run_cmd
  let env ← getEnv
  let defs ← liftIO (pureDefNames env)
  -- This exact fixture must compile before its two inventories can pass.
  let fixture :=
    r#"module
public import Lean
public import Linger.Runtime.CoverageShadow
public import Linger.Core.Render
public section
namespace Probe
  def indented : Nat := 0
  def
    splitName : Nat := 0
  namespace Inner
    private def «matches» : Nat := 0
  end Probe.Inner
def rootAfter : Nat := 0
namespace Probe.Inner
  def qualifiedScope : Nat := 0
  end Inner
  section Checks.Nested
    def marker : String := "/-"
    /- outer /- nested -/ comment -/
    def afterMarker : Nat := 0
    def quoted : Lean.MacroM (Lean.TSyntax `command) := `(command| def hidden : Nat := 0)
  end Checks.Nested
  def afterSection : Nat := 0
  namespace Decoy
  def same : Nat := 1
  end Decoy
  #check `(command| namespace Decoy)
  def same : Nat := 2
  #check `(command| end Decoy)
end Probe
namespace Linger.ReferenceProbe
def canonical := Linger.Core.Render.titleAnsi
def relative := Core.Render.gridAnsi
def rooted := _root_.Linger.Core.Render.restore
open Linger.Core
def short := Render.screensAnsi
open Linger.Core.Render (digits)
def unqualified := digits
open Linger.Core.Render renaming dropTrailingBlanks → trimmed
def renamed := trimmed
def field := Render.leaveAnsi.toArray
def localShadow (digits : Nat) := digits
def stringDecoy : String := "Linger.Core.Render.safeChar"
def quotedRef : Lean.MacroM (Lean.TSyntax `term) := `(term| Linger.Core.Render.colorCodes)
end Linger.ReferenceProbe
"#
  let expected :=
    #[`Probe.indented, `Probe.splitName, `Probe.Inner.matches, `rootAfter,
        `Probe.Inner.qualifiedScope, `Probe.marker, `Probe.afterMarker, `Probe.quoted,
        `Probe.afterSection, `Probe.Decoy.same, `Probe.same] ++
      #[`canonical, `relative, `rooted, `short, `unqualified, `renamed, `field, `localShadow,
            `stringDecoy, `quotedRef].map
        (`Linger.ReferenceProbe ++ ·)
  liftIO <|
      IO.FS.withTempDir fun root => do
        let shadow :=
          r#"module
public section
namespace Linger.Core.Render
private def safeChar : List UInt8 := [65]
end Linger.Core.Render
namespace Linger.ReferenceProbe
def privateShadow : List UInt8 := Linger.Core.Render.safeChar
end Linger.ReferenceProbe
"#
        let mut arts : NameMap ImportArtifacts := {}
        for (mod, content) in
          #[(`Linger.Runtime.CoverageShadow, shadow), (`CoverageFixture, fixture)] do
          let source := root / s!"{mod}.lean"
          let olean := source.withExtension "olean"
          let setup := source.withExtension "setup.json"
          IO.FS.writeFile source content
          IO.FS.writeFile setup
              (toJson ({ name := mod, importArts := arts } : ModuleSetup)).compress
          let compiled ←
            IO.Process.output
                { cmd := "lean",
                  args := #[s!"--setup={setup}", "-o", olean.toString, source.toString] }
          unless compiled.exitCode == 0 do
            throw
                (IO.userError
                  s!"coverage fixture did not compile:\n{compiled.stdout}{compiled.stderr}")
          arts :=
            arts.insert mod
              (.ofArrays
                #[#[olean, source.withExtension "olean.server",
                    source.withExtension "olean.private"],
                  #[source.withExtension "ir.sig", source.withExtension "ir"]])
        let found ← runtimeEmitters defs `CoverageFixture arts
        unless
          found ==
            #["Render.digits", "Render.dropTrailingBlanks", "Render.gridAnsi", "Render.leaveAnsi",
              "Render.restore", "Render.screensAnsi", "Render.titleAnsi"] do
          throw (IO.userError s!"resolved reference census mismatch: {found}")
  let parsed ← liftIO (Parser.testParseModule env "coverage fixture" fixture)
  let .ok names := sourceDefNames parsed
    | throwError "definition census rejected the regression fixture"
  unless names == expected do
    throwError m!"definition census mismatch: {names}"
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
