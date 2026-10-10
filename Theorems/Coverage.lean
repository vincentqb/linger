module

import all Theorems.Buf
import all Theorems.Wire
import all Theorems.Vt
import all Theorems.Terminal
import all Theorems.TerminalTitle
import all Theorems.Session
import all Theorems.Driver
import all Theorems.Name
import all Theorems.Checkpoint
import all Theorems.Remote
import all Theorems.Claim
import all Theorems.Listing
import all Theorems.Render
import all Theorems.Replay
import all Theorems.Resume
import all Theorems.Status
import all Theorems.Title
import all Theorems.Resurrect
import all Theorems.Fuzzy
import all Theorems.Picker
import all Theorems.Input
import all Theorems.Key
import all Theorems.Entry
import all Theorems.Contracts
public meta import Lean.Elab.Command
import Lean.Parser.Command

/-! # Semantic coverage gate

Every explicit `def` or `abbrev` under `Linger/Core` or `Linger/Tools` must occur
as its exact environment constant in the type of a written theorem from `Theorems`;
generated equation, congruence and induction lemmas do not count. No module
under `Linger/Core`, `Linger/Tools` or `Theorems` may declare an axiom; native
evaluation declares one for each use. The checks read only this module's import
closure, so each of those modules must be in it. This module is under the
sanctioned friend region so it can resolve private definitions and theorem
declarations without granting that access to E2E or runtime code. -/

namespace Theorems.Coverage

open Lean Elab Command

/-- Explicit `def` and `abbrev` names, with nested namespace and section scopes. -/
public meta def sourceDefNames (stx : Syntax) : Except String (Array Lean.Name) := do
  let visit (node : Syntax) :
    StateT (List Lean.Name × Array Lean.Name) (Except String) (Option Syntax) := do
    if node.isQuot then
      return some node
    let (scopes, names) ← get
    let ns := scopes.head!
    if node.isOfKind ``Parser.Command.namespace then
      -- Lean opens one scope per component, even in `namespace A.B`.
      let scopes :=
        node[1].getId.components.foldl (fun scopes part => (scopes.head! ++ part) :: scopes) scopes
      set (scopes, names)
    else if node.isOfKind ``Parser.Command.section then
      set (List.replicate (max 1 node[2][0].getId.getNumParts) ns ++ scopes, names)
    else if node.isOfKind ``Parser.Command.end then
      let count := max 1 node[1][0].getId.getNumParts
      if count ≥ scopes.length then
        throw "unmatched end in definition census"
      set (scopes.drop count, names)
    else if node.isOfKind ``Parser.Command.withWeakNamespace then
      throw "with_weak_namespace needs an explicit census scope rule"
    else if node.isOfKind ``Parser.Command.declaration then
      let decl := node[1]
      if decl.isOfKind ``Parser.Command.definition || decl.isOfKind ``Parser.Command.abbrev then
        let id := decl[1][0].getId
        if id.isAnonymous then
          throw "unrecognized definition name"
        let name :=
          if (`_root_ : Lean.Name).isPrefixOf id then id.replacePrefix `_root_ .anonymous
          else ns ++ id
        set (scopes, names.push name)
      -- Declaration bodies may quote commands without declaring them.
      return some node
    return none
  let (_, (_, names)) ← (stx.replaceM visit).run ([.anonymous], #[])
  return names

/-- Logical fully qualified names of explicit pure definitions.

Lean's parser handles layout, escaped identifiers, strings and nested comments,
and unrecognized syntax is an error; the semantic check below resolves each name
against the compiled environment. -/
public meta def pureDefNames (env : Environment) : IO (Array Lean.Name) := do
  let mut names : Array Lean.Name := #[]
  let files :=
    ((← System.FilePath.walkDir "Linger/Core") ++ (← System.FilePath.walkDir "Linger/Tools")).filter
      (·.extension == some "lean")
  for f in files do
    let found ←
      match sourceDefNames (← Parser.testParseFile env f) with
      | .ok found =>
        pure found
      | .error why =>
        throw (IO.userError s!"{f}: {why}")
    for name in found do
      if !names.contains name then
        names := names.push name
  return names.qsort (·.toString < ·.toString)

/-- Enumerate selected imported modules, retaining canonical ownership and visibility.

An imported theorem can be refined by another module; look up its current
constant information and keep only the module that owns its name. -/
meta def moduleConsts (env : Environment) (keep : Lean.Name → Bool) :
    Array (Lean.Name × ConstantInfo) :=
  Id.run do
    let mut found := #[]
    for idx in [:env.header.modules.size] do
      unless keep env.header.modules[idx]!.module do
        continue
      for name in env.header.moduleData[idx]!.constNames do
        unless env.getModuleIdxFor? name == some idx do
          continue
        if let some ci := env.find? name (skipRealize := true) then
          found := found.push (name, ci)
    return found

/-- Resolved renderer/replay references in the built program's module closure.

Reading implementation metadata stays in the friend region; callers receive
names only. Run after building the program. Alternate artifacts let the regression
check inspect a separately compiled fixture without changing the search path. -/
public meta def runtimeEmitters (defs : Array Lean.Name) (main : Lean.Name := `Main)
    (arts : NameMap ImportArtifacts := {}) : IO (Array String) := do
  let env ← importModules #[{ module := main }] {} (arts := arts)
  let mut refs : NameHashSet := {}
  for (name, ci) in moduleConsts env (fun mod => mod == main || (`Linger).isPrefixOf mod) do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.modules[idx.toNat]!.module
    if ci.isTheorem then
      continue
    let some value := ci.value? (allowOpaque := true) | continue
    for target in value.getUsedConstants do
      let some targetIdx := env.getModuleIdxFor? target | continue
      let targetMod := env.header.modules[targetIdx.toNat]!.module
      let logical := privateToUserName target
      if
          defs.contains logical && mod != targetMod &&
            [`Linger.Core.Render, `Linger.Core.Replay].any
              (fun family => family.isPrefixOf logical && family.isPrefixOf targetMod) then
        refs := refs.insert logical
  return (refs.toList.map
          (fun n => (n.replacePrefix `Linger.Core .anonymous).toString)).toArray.qsort
      (· < ·)

/-- Require every pure or proof module in the import closure and reject any axiom one
declares; then re-read the pure sources and check that each definition's exact constant
occurs in the type of a written theorem.

A written theorem has a source declaration range. Lemmas Lean generates on demand,
such as the equation lemma `simp [f]` realizes, have none and claim nothing.
Load private metadata inside this friend module, keeping the caller's imports
sealed. Return the checked census so downstream checks use the same inventory. -/
public meta def checkPureCoverage : CommandElabM (Array Lean.Name) := do
  let sourceEnv ← getEnv
  let logical ← liftIO (pureDefNames sourceEnv)
  let env ← liftIO (importModules sourceEnv.header.imports {})
  -- The axiom check reads only this import closure, so it must hold every module under the roots.
  let roots := [`Linger.Core, `Linger.Tools, `Theorems]
  let closure := (env.header.modules.map (·.module)).push sourceEnv.mainModule
  let mut outside : Array Lean.Name := #[]
  for root in roots do
    let dir := System.mkFilePath (root.components.map toString)
    for file in ← liftIO (System.FilePath.walkDir dir) do
      let mod := (file.withExtension "").components.foldl .mkStr .anonymous
      if file.extension == some "lean" && !closure.contains mod then
        outside := outside.push mod
  unless outside.isEmpty do
    throwError m!"coverage: pure or proof modules outside the import closure of Theorems.Coverage: \
      {outside.qsort (·.toString < ·.toString)}"
  -- Native evaluation (`native_decide`, `decide +native`, `bv_decide`) adds an axiom too.
  let axioms :=
    (moduleConsts env fun mod => roots.any (·.isPrefixOf mod)).filterMap fun (name, ci) =>
      if ci.isAxiom then some name else none
  unless axioms.isEmpty do
    throwError m!"coverage: axioms in pure or proof modules: {axioms}"
  let pureConsts :=
    (moduleConsts env
          (fun mod => [`Linger.Core, `Linger.Tools].any (·.isPrefixOf mod))).toList.filterMap
      fun (n, ci) => if !ci.isTheorem then some (privateToUserName n, n) else none
  let theoremConsts :=
    (moduleConsts env ((`Theorems : Lean.Name).isPrefixOf ·)).foldl
      (fun acc (n, ci) =>
        if
            ci.isTheorem &&
              (declRangeExt.find? (level := .exported) env n <|>
                  declRangeExt.find? (level := .server) env n).isSome then
          ci.type.foldConsts acc fun name seen => seen.insert name
        else acc)
      NameHashSet.empty
  let mut resolved : Array (Lean.Name × Lean.Name) := #[]
  for n in logical do
    let candidates :=
      pureConsts.filterMap fun (logical, actual) => if logical == n then some actual else none
    let [actual] := candidates
      | throwError m!"coverage: `{n}` resolved to {candidates.length} constants: {candidates}"
    resolved := resolved.push (n, actual)
  let unclaimed := resolved.filter fun (_, actual) => !theoremConsts.contains actual
  unless unclaimed.isEmpty do
    throwError m!"coverage: pure definitions absent from every written theorem type: \
      {unclaimed.map (·.1)}"
  return logical

-- These fixed fixtures run when the checker or its imports are rebuilt.
-- The standalone E2E check calls checkPureCoverage again for fresh source files.
run_cmd
  let env ← getEnv
  let defs ← checkPureCoverage
  -- This exact fixture must compile before its two inventories can pass.
  let fixture :=
    r#"module
public import Lean.Elab.Command
public import Linger.Runtime.CoverageShadow
public import Linger.Core.Render
public section
namespace Probe
  def indented : Nat := 0
  abbrev shorthand : Nat := 0
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
private def canonical := Linger.Core.Render.titleAnsi
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
    #[`Probe.indented, `Probe.shorthand, `Probe.splitName, `Probe.Inner.matches, `rootAfter,
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

end Theorems.Coverage
