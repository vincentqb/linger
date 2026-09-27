module

public import Linger.Core.Name

public section

/-! Pure tmux-resurrect pane import and planning.

Only pane records matter. The caller must preflight every saved directory before
performing effects. Planning uses an explicit snapshot of existing names; it does
not claim atomic creation or protection from concurrent same-name creators.
-/

namespace Tools.Resurrect

/-- Replace terminal controls only when displaying an error, preserving its other text. -/
def diagnostic (message : String) : String :=
  message.map fun c => if 32 ≤ c.toNat && (c.toNat < 127 || 160 ≤ c.toNat) then c else '?'

structure Pane where
  name : String
  dir : String
  line : Nat
  deriving BEq, Repr

/-- Parse one tab-split row, validating and discarding its saved command. -/
private def parseRow (home : String) (line : Nat) (fields : List String) :
    Except String (Option Pane) :=
  if fields.head? != some "pane" then .ok none
  else
    match fields with
    | [_, session, window, _, _, pane, _, cwd, _, _, savedCommand] =>
      if
          session.isEmpty || window.isEmpty || pane.isEmpty || !cwd.startsWith ":" ||
            !savedCommand.startsWith ":" then
        .error s!"malformed pane record at line {line}"
      else
        let name := session ++ "-w" ++ window ++ "-p" ++ pane
        let decoded := (cwd.drop 1).toString.replace "\\ " " "
        let dir :=
          if decoded == "~" then home
          else if decoded.startsWith "~/" then home ++ (decoded.drop 1).toString else decoded
        if dir.contains '\x00' || savedCommand.contains '\x00' then
          .error s!"malformed pane record at line {line}"
        else
          if Linger.Core.Name.sanitize name != name then
            .error s!"projected session is not a valid linger name at line {line}: {name}"
          else .ok (some { name, dir, line })
    | _ => .error s!"malformed pane record at line {line}"

/-- Validate left to right so a duplicate reports its second occurrence. -/
private def parseRows (home : String) (line : Nat) (seen : List String) (rows : List String) :
    Except String (List Pane) :=
  match rows with
  | [] => .ok []
  | row :: rows =>
    match parseRow home line (row.splitOn "\t") with
    | .error error => .error error
    | .ok none => parseRows home (line + 1) seen rows
    | .ok (some pane) =>
      if seen.contains pane.name then
        .error s!"duplicate projected session at line {line}: {pane.name}"
      else (parseRows home (line + 1) (pane.name :: seen) rows).map (pane :: ·)

/-- All rows must validate, and at least one pane must be present. -/
def parseSave (home content : String) : Except String (List Pane) :=
  match parseRows home 1 [] (content.splitOn "\n") with
  | .error error => .error error
  | .ok [] => .error "no pane records in save"
  | .ok (pane :: panes) => .ok (pane :: panes)

/-- Skip existing names, preserving whole records and their order. -/
def plan (existing : List String) (panes : List Pane) : List Pane :=
  panes.filter (fun pane => !existing.contains pane.name)

end Tools.Resurrect
