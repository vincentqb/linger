module

import all Theorems.Buf
import all Theorems.Wire
import all Theorems.Vt
import all Theorems.Terminal
import all Theorems.Session
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
import all Theorems.Entry
public meta import Lean.Elab.Command

/-! # Semantic coverage gate

Every explicit `def` under `Linger/Core` or `Tools` must occur as
its exact environment constant in a theorem type from `Theorems`. This module
is under the sanctioned friend region so it can resolve private definitions and
theorem declarations without granting that access to E2E or runtime code. -/

namespace Theorems.Coverage

open Lean Elab Command

public meta partial def leanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut acc := #[]
  for entry in ← root.readDir do
    if ← entry.path.isDir then
      acc := acc ++ (← leanFiles entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push entry.path
  return acc

/-- Parse the program's standard Lean syntax; unrecognized syntax is an error. -/
public meta def sourceSyntax (env : Environment) (file : System.FilePath) : IO Syntax :=
  Parser.testParseFile env file

/-- Explicit definition names, with nested namespace and section scopes. -/
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
      if decl.isOfKind ``Parser.Command.definition then
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

Lean's parser handles layout, escaped identifiers, strings and nested comments;
the semantic check below resolves each name against the compiled environment. -/
public meta def pureDefNames (env : Environment) : IO (Array Lean.Name) := do
  let mut names : Array Lean.Name := #[]
  let files :=
    (← leanFiles (System.FilePath.mk "Linger/Core")) ++ (← leanFiles (System.FilePath.mk "Tools"))
  for f in files do
    let found ←
      match sourceDefNames (← sourceSyntax env f) with
      | .ok found =>
        pure found
      | .error why =>
        throw (IO.userError s!"{f}: {why}")
    for name in found do
      if !names.contains name then
        names := names.push name
  return names.qsort (·.toString < ·.toString)

meta def moduleUnder (env : Environment) (root decl : Lean.Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | none => false
  | some idx => root.isPrefixOf env.header.moduleNames[idx.toNat]!

/-- Resolved renderer/replay references in the built program's module closure.

Reading implementation metadata stays in the friend region; callers receive
names only. Run after building the program. Alternate artifacts let the regression
check inspect a separately compiled fixture without changing the search path. -/
public meta def runtimeEmitters (defs : Array Lean.Name) (main : Lean.Name := `Main)
    (arts : NameMap ImportArtifacts := {}) : IO (Array String) := do
  let env ← importModules #[{ module := main }] {} (arts := arts)
  let mut refs : NameHashSet := {}
  for (name, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? name | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mod == main || [`Linger, `Tools, `Manager].any (·.isPrefixOf mod) do
      continue
    if ci.isTheorem then
      continue
    let some value := ci.value? (allowOpaque := true) | continue
    for target in value.getUsedConstants do
      let some targetIdx := env.getModuleIdxFor? target | continue
      let targetMod := env.header.moduleNames[targetIdx.toNat]!
      let logical := privateToUserName target
      if
          defs.contains logical && mod != targetMod &&
            [`Linger.Core.Render, `Linger.Core.Replay].any
              (fun family => family.isPrefixOf logical && family.isPrefixOf targetMod) then
        refs := refs.insert logical
  return (refs.toList.map
          (fun n => (n.replacePrefix `Linger.Core .anonymous).toString)).toArray.qsort
      (· < ·)

run_cmd
  let env ← getEnv
  let logical ← liftIO (pureDefNames env)
  let constants := env.constants.toList
  let pureConsts :=
    constants.filterMap fun (n, ci) =>
      if !ci.isTheorem && (moduleUnder env `Linger.Core n || moduleUnder env `Tools n) then
        some (privateToUserName n, n)
      else none
  let theoremConsts :=
    constants.foldl
      (fun acc (n, ci) =>
        if ci.isTheorem && moduleUnder env `Theorems n then
          ci.type.foldConsts acc fun name seen => seen.insert name
        else acc)
      NameHashSet.empty
  let mut resolved : Array (Lean.Name × Lean.Name) := #[]
  for n in logical do
    let candidates :=
      pureConsts.filterMap fun (logical, actual) => if logical == n then some actual else none
    unless candidates.length == 1 do
      throwError m!"coverage: `{n}` resolved to {candidates.length} constants: {candidates}"
    resolved := resolved.push (n, candidates[0]!)
  let unclaimed := resolved.filter fun (_, actual) => !theoremConsts.contains actual
  unless unclaimed.isEmpty do
    throwError m!"coverage: pure definitions absent from every theorem type: \
      {unclaimed.map (·.1)}"

end Theorems.Coverage
