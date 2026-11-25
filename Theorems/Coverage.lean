module

import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Wire
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.History
import all Terminal.Proofs.Mediation
import all Terminal.Proofs.Title
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Driver
import all Linger.Target.Proofs.Name
import all Linger.Session.Proofs.Checkpoint
import all Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Names
import all Linger.Display.Proofs.Listing
import all Terminal.Proofs.Render
import all Terminal.Proofs.Replay
import all Linger.Session.Proofs.Resume
import all Linger.Session.Proofs.Record
import all Linger.Session.Proofs.Start
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.Title
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import all Fuzzy.Proofs
import all Fuzzy.Solution
import all Linger.Selector.Proofs.Picker
import all Input.Proofs
import all Input.Solution
import all Terminal.Solution
import all Os.Solution
import all Linger.Selector.Proofs.Key
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Kill
import all Linger.App.Proofs.Wait
import all Linger.Os.Proofs.Answer
import all Linger.Os.Proofs.Env
import all Os.Proofs.Wait
import all Theorems.Solution
public meta import Lean.Elab.Command
import Lean.Parser.Command
public meta import Lean.Compiler.CSimpAttr
import Lean.Compiler.CSimpAttr

/-! # Pure definitions, their `@[csimp]` replacements and the renderer's emitters

`pureDefNames` reads every explicit `def` or `abbrev` in a pure module (`pureModule`: a
`CoreSpec` or `CoreCode` module) from the sources, and `runtimeEmitters` finds those of the
renderer and the replay that the program references outside their own module, which
`Verify/Coverage.lean` classifies. Pure code
reaches a global `@[csimp]` replacement only through its specification, from definitions
declared after the theorem, which is tagged in the specification's module; `scripts/verify.sh`
checks on the generated C that each replacement, a module-local one included, is still called.
That check reads only this module's import closure, so each pure module must be in it. This
module is under the sanctioned friend region so it can resolve private definitions without
granting that access to suites or runtime code. -/

namespace Theorems.Coverage

open Lean Elab Command

/-- The roles a module's name gives it, as linger lays its modules out: the first component of
its name that is one of these is its role. -/
public meta def roles : List Lean.Name := [`CoreSpec, `CoreCode, `WorldSpec, `WorldCode]

/-- A module of pure code: one whose role, the first component of its name in `roles`, is
`CoreSpec` or `CoreCode`, linger's or a package's. -/
public meta def pureModule (mod : Lean.Name) : Bool :=
  match mod.components.find? roles.contains with
  | some role => role == `CoreSpec || role == `CoreCode
  | none => false

/-- The source files under `Linger/`, `Theorems/` and each package's directory whose module
`keep` selects, read from the tree so that a module nothing imports still counts. A package's
modules are named from its own directory. -/
public meta def sourceModules (keep : Lean.Name → Bool) :
    IO (Array (System.FilePath × Lean.Name)) := do
  let mut found := #[]
  let mut roots : Array (List String × System.FilePath) := #[([], "Linger"), ([], "Theorems")]
  if ← System.FilePath.pathExists "packages" then
    for entry in ← System.FilePath.readDir "packages" do
      if ← entry.path.isDir then
        roots := roots.push (["packages", entry.fileName], entry.path)
  for (base, dir) in roots do
    unless ← System.FilePath.pathExists dir do
      continue
    for file in ← System.FilePath.walkDir dir do
      if file.extension == some "lean" then
        let mod := ((file.withExtension "").components.drop base.length).foldl .mkStr .anonymous
        if keep mod then
          found := found.push (file, mod)
  return found.qsort (·.2.toString < ·.2.toString)

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
        (node.getArg 1).getId.components.foldl (fun scopes part => (scopes.head! ++ part) :: scopes)
          scopes
      set (scopes, names)
    else if node.isOfKind ``Parser.Command.section then
      set (List.replicate (max 1 ((node.getArg 2).getArg 0).getId.getNumParts) ns ++ scopes, names)
    else if node.isOfKind ``Parser.Command.end then
      let count := max 1 ((node.getArg 1).getArg 0).getId.getNumParts
      if count ≥ scopes.length then
        throw "unmatched end in the definition inventory"
      set (scopes.drop count, names)
    else if node.isOfKind ``Parser.Command.withWeakNamespace then
      throw "with_weak_namespace needs an explicit inventory scope rule"
    else if node.isOfKind ``Parser.Command.declaration then
      let decl := node.getArg 1
      if decl.isOfKind ``Parser.Command.definition || decl.isOfKind ``Parser.Command.abbrev then
        let id := ((decl.getArg 1).getArg 0).getId
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
  let files := (← sourceModules pureModule).map (·.1)
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

/-- Resolved renderer/replay references in the built program's module closure: `main`'s and
those of every program module, linger's and the terminal package's, whose emitters linger's
binary runs.

Reading implementation metadata stays in the friend region; callers receive
names only. Run after building the program. Alternate artifacts let the regression
check inspect a separately compiled fixture without changing the search path. -/
public meta def runtimeEmitters (defs : Array Lean.Name)
    (main : Lean.Name := `Linger.App.WorldCode.Main) (arts : NameMap ImportArtifacts := {}) :
    IO (Array String) := do
  let env ← importModules #[{ module := main }] {} (arts := arts)
  let mut refs : NameHashSet := {}
  let program (mod : Lean.Name) :=
    mod == main || (`Linger).isPrefixOf mod || (`Terminal).isPrefixOf mod
  for (name, ci) in moduleConsts env program do
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
            [(`Terminal.Render, `Terminal.CoreCode.Render),
                  (`Terminal.Replay, `Terminal.CoreCode.Replay)].any
              (fun (family, module) =>
                family.isPrefixOf logical && module.isPrefixOf targetMod) then
        refs := refs.insert logical
  return (refs.toList.map (fun n => (n.replacePrefix `Terminal .anonymous).toString)).toArray.qsort
      (· < ·)

/-- Read the explicit definitions of the pure sources, require every pure module in the import
closure and check that pure code reaches each `@[csimp]` replacement only through its
specification, from definitions declared after the theorem.

Load private metadata inside this friend module, keeping the caller's imports sealed. Return
the definitions read so that `runtimeEmitters` uses the same inventory. -/
public meta def checkPureCode : CommandElabM (Array Lean.Name) := do
  let sourceEnv ← getEnv
  let logical ← liftIO (pureDefNames sourceEnv)
  let env ← liftIO (importModules sourceEnv.header.imports {})
  -- The `@[csimp]` check reads only this import closure, so it must hold every pure module.
  let closure := (env.header.modules.map (·.module)).push sourceEnv.mainModule
  let outside :=
    (← liftIO (sourceModules pureModule)).filterMap fun (_, mod) =>
      if closure.contains mod then none else some mod
  unless outside.isEmpty do
    throwError m!"coverage: pure modules outside the import closure of Theorems.Coverage: \
      {outside}"
  -- Compiled code reaches a `@[csimp]` replacement only through its specification, and the
  -- compiler replaces a specification only in definitions declared after the theorem. A
  -- constant without a range, such as a recursive definition's `_unary`, takes its owner's.
  let line (n : Lean.Name) :=
    (List.range n.getNumParts).findSome? fun up =>
      let owner := Nat.repeat Lean.Name.getPrefix up n
      (declRangeExt.find? (level := .exported) env owner <|>
            declRangeExt.find? (level := .server) env owner).map
        (·.range.pos.line)
  let code := moduleConsts env pureModule
  -- Read the global theorems from each module's entries: this environment loads no extension
  -- state, and `Verify/Coverage.lean` elaborates in one that lacks Linger's.
  let csimps :=
    (List.range env.header.modules.size).foldl
      (fun acc idx =>
        acc ++
          (Compiler.CSimp.ext.ext.getModuleEntries env idx).toList.filterMap fun
            | .global e => some (idx, e)
            | .scoped .. => none)
      []
  for (idx, e) in csimps do
    unless (`Linger).isPrefixOf e.toDeclName do
      continue
    -- Recorded in the specification's module, a replacement reaches every importer, and lines
    -- order the theorem against that module's own callers.
    unless env.getModuleIdxFor? e.fromDeclName == some idx do
      throwError m!"coverage: `{e.thmName}` replaces `{e.fromDeclName}` outside its module, \
        so callers there run the specification"
    for (n, ci) in code do
      let some v := ci.value? (allowOpaque := true) | continue
      if ci.isTheorem || e.toDeclName.isPrefixOf n || e.fromDeclName.isPrefixOf n then
        continue
      let used := v.getUsedConstants
      if used.contains e.toDeclName then
        throwError m!"coverage: `{n}` names the csimp replacement `{e.toDeclName}`"
      if
          used.contains e.fromDeclName &&
            env.getModuleIdxFor? n == env.getModuleIdxFor? e.fromDeclName &&
            (line n).any (· < (line e.thmName).getD 0) then
        throwError m!"coverage: `{n}` precedes `{e.thmName}`, so it runs `{e.fromDeclName}`"
  return logical

-- These fixed fixtures run when the checker or its imports are rebuilt.
-- The standalone check in `Verify.Coverage` calls checkPureCode again for fresh source files.
run_cmd
  let env ← getEnv
  let defs ← checkPureCode
  -- This exact fixture must compile before its two inventories can pass.
  let fixture :=
    r#"module
public import Lean.Elab.Command
public import Linger.Probe.CoverageShadow
public import Terminal.CoreCode.Render
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
private def canonical := Terminal.Render.titleAnsi
def relative := Terminal.Render.scrollbackAnsi
def rooted := _root_.Terminal.Render.restore
open Terminal
def short := Render.modesAnsi
open Terminal.Render (digits)
def unqualified := digits
open Terminal.Render renaming dropTrailingBlanks → trimmed
def renamed := trimmed
def field := Render.leaveAnsi.toArray
def localShadow (digits : Nat) := digits
def stringDecoy : String := "Terminal.Render.safeChar"
def quotedRef : Lean.MacroM (Lean.TSyntax `term) := `(term| Terminal.Render.colorCodes)
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
namespace Terminal.Render
private def safeChar : List UInt8 := [65]
end Terminal.Render
namespace Linger.ReferenceProbe
def privateShadow : List UInt8 := Terminal.Render.safeChar
end Linger.ReferenceProbe
"#
        let mut arts : NameMap ImportArtifacts := {}
        for (mod, content) in
          #[(`Linger.Probe.CoverageShadow, shadow), (`CoverageFixture, fixture)] do
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
            #["Render.digits", "Render.dropTrailingBlanks", "Render.leaveAnsi", "Render.modesAnsi",
              "Render.restore", "Render.scrollbackAnsi", "Render.titleAnsi"] do
          throw (IO.userError s!"resolved reference inventory mismatch: {found}")
  let parsed ← liftIO (Parser.testParseModule env "coverage fixture" fixture)
  let .ok names := sourceDefNames parsed
    | throwError "the definition inventory rejected the regression fixture"
  unless names == expected do
    throwError m!"definition inventory mismatch: {names}"

end Theorems.Coverage
