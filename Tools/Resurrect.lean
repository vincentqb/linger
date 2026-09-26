module

public import Linger.Core.Name

public section

/-! Pure tmux-resurrect pane import and planning.

Only pane records matter. The caller must preflight every saved directory before
performing effects. Planning uses an explicit snapshot of existing names; it does
not claim atomic creation or protection from concurrent same-name creators.
-/

namespace Tools.Resurrect

structure Pane where
  name : String
  dir : String
  command : String
  line : Nat
  deriving BEq, Repr

structure PlannedPane where
  pane : Pane
  command : Option String
  deriving BEq, Repr

/-- Parse one tab-split row, retaining the full command after its format sentinel. -/
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
        let command := (savedCommand.drop 1).toString
        if dir.contains '\x00' || command.contains '\x00' then
          .error s!"malformed pane record at line {line}"
        else
          if Linger.Core.Name.sanitize name != name then
            .error s!"projected session is not a valid linger name at line {line}: {name}"
          else .ok (some { name, dir, command, line })
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

/-- Fixed first-word process policy, shared by planning and the caller's presentation. -/
def allowed : List String :=
  ["vi", "vim", "view", "nvim", "emacs", "man", "less", "more", "tail", "top", "htop", "irssi",
    "weechat", "mutt"]

/-- Split only on ASCII spaces and discard empty words, as in the fish recipe. -/
def firstWord (command : String) : String := ((command.splitOn " ").find? (· != "")).getD ""

/-- Opt-in permits the original whole command; it does not interpret shell syntax. -/
def restoreCommand (restore : Bool) (pane : Pane) : Option String :=
  if restore && allowed.contains (firstWord pane.command) then some pane.command else none

/-- Filter whole records before assigning commands, preserving alignment and order. -/
def plan (restore : Bool) (existing : List String) (panes : List Pane) : List PlannedPane :=
  (panes.filter (fun pane => !existing.contains pane.name)).map
    (fun pane => { pane, command := restoreCommand restore pane })

end Tools.Resurrect
