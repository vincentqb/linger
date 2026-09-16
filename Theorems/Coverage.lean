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
import all Theorems.Resume
import all Theorems.Status
public meta import Lean.Elab.Command

/-! # Semantic coverage gate

Every explicit `def` under `Linger/Core` must occur as its exact environment
constant in a theorem type from `Theorems`. This module is under the sanctioned
friend region so it can resolve private definitions and theorem declarations
without granting that access to E2E or runtime code. -/

namespace Theorems.Coverage

open Lean Elab Command

public def identChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '\''

/-- Source with block and line comments removed. -/
public partial def stripComments (s : String) : String :=
  let rec block (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '/' :: '-' :: t =>
      let rec close (r : List Char) : List Char :=
        match r with
        | [] => []
        | '-' :: '/' :: t' => t'
        | _ :: t' => close t'
      block (close t) (' ' :: acc)
    | '-' :: '-' :: t =>
      let rec eol (r : List Char) : List Char :=
        match r with
        | [] => []
        | '\n' :: t' => '\n' :: t'
        | _ :: t' => eol t'
      block (eol t) (' ' :: acc)
    | c :: t => block t (c :: acc)
  String.ofList (block s.toList [])

public partial def leanFiles (root : System.FilePath) : IO (Array System.FilePath) := do
  let mut acc := #[]
  for entry in ← root.readDir do
    if ← entry.path.isDir then
      acc := acc ++ (← leanFiles entry.path)
    else if entry.path.extension == some "lean" then
      acc := acc.push entry.path
  return acc

public def dropModifiers (line : String) : String :=
  let l :=
    if line.startsWith "@[" then
      match (line.splitOn "]").tail? with
      | some (rest :: _) => rest.trimAsciiStart.toString
      | _ => line
    else line
  if l.startsWith "private " then (l.drop 8).toString
  else if l.startsWith "public " then (l.drop 7).toString else l

public def declChar (c : Char) : Bool := identChar c || c == '.' || c == '?' || c == '!'

public def declToken (afterKeyword : String) : String :=
  ((afterKeyword.dropWhile (· == ' ')).toString.takeWhile declChar).toString

public def declName (afterKeyword : String) : String :=
  (declToken afterKeyword |>.splitOn ".").getLast!

/-- Logical fully qualified names of explicit pure-core definitions.

Every current core file has one top-level namespace. A layout change makes names
fail to resolve below, so the census fails closed. -/
public def coreDefNames : IO (Array Lean.Name) := do
  let mut names : Array Lean.Name := #[]
  for f in ← leanFiles (System.FilePath.mk "Linger/Core") do
    let src := stripComments (← IO.FS.readFile f)
    let some nsLine := src.splitOn "\n" |>.find? (·.startsWith "namespace ")
      | throw (IO.userError s!"{f}: no top-level namespace")
    let ns := (nsLine.drop 10).toString.trimAscii.toString
    for line in src.splitOn "\n" do
      let l := dropModifiers line
      if l.startsWith "def " then
        let token := declToken (l.drop 4).toString
        let n := s!"{ns}.{token}".toName
        if !token.isEmpty && !names.contains n then
          names := names.push n
  return names.qsort (·.toString < ·.toString)

meta def moduleUnder (env : Environment) (root decl : Lean.Name) : Bool :=
  match env.getModuleIdxFor? decl with
  | none => false
  | some idx => root.isPrefixOf env.header.moduleNames[idx.toNat]!

meta def coreCandidates (env : Environment) (logical : Lean.Name) : Array Lean.Name :=
  match env.find? logical with
  | some ci => if ci.isTheorem then #[] else #[logical]
  | none =>
    env.constants.toList.filterMap
        (fun (n, ci) =>
          if
              !ci.isTheorem && moduleUnder env `Linger.Core n &&
                n.toString.endsWith logical.toString then
            some n
          else none) |>.toArray

meta def exprConsts (acc : NameHashSet) : Expr → NameHashSet
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .lit _ => acc
  | .const n _ => acc.insert n
  | .app f a => exprConsts (exprConsts acc f) a
  | .lam _ type body _ | .forallE _ type body _ => exprConsts (exprConsts acc type) body
  | .letE _ type value body _ => exprConsts (exprConsts (exprConsts acc type) value) body
  | .mdata _ body => exprConsts acc body
  | .proj _ _ body => exprConsts acc body

run_cmd
  let logical ← liftIO coreDefNames
  let env ← getEnv
  let theoremConsts :=
    env.constants.toList.foldl
      (fun acc (n, ci) =>
        if ci.isTheorem && moduleUnder env `Theorems n then exprConsts acc ci.type else acc)
      NameHashSet.empty
  let mut resolved : Array (Lean.Name × Lean.Name) := #[]
  for n in logical do
    let candidates := coreCandidates env n
    unless candidates.size == 1 do
      throwError m!"coverage: `{n}` resolved to {candidates.size} constants: {candidates}"
    resolved := resolved.push (n, candidates[0]!)
  let unclaimed := resolved.filter fun (_, actual) => !theoremConsts.contains actual
  unless unclaimed.isEmpty do
    throwError m!"coverage: pure-core definitions absent from every theorem type: \
      {unclaimed.map (·.1)}"

end Theorems.Coverage
