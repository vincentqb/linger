module

import Linger.Core.Name
import Linger.Core.Status

public section

/-! Pure tmux-resurrect interchange and import planning.

Pane records supply session identity and directory. Window names are used only
for browsing; unused metadata is discarded. The caller must preflight every
directory it will import before performing effects.
Planning uses an explicit snapshot of existing names; it does not claim atomic
creation or protection from concurrent same-name creators.
-/

namespace Linger.Tools.Resurrect

/-- Replace terminal controls only when displaying an error, preserving its other text. -/
def diagnostic (message : String) : String :=
  message.map fun c => if 32 ≤ c.toNat && (c.toNat < 127 || 160 ≤ c.toNat) then c else '?'

structure Pane where
  name : String
  dir : String
  line : Nat
  deriving BEq, Repr

/-- Session identity and directory, independent of the source line. -/
def common (panes : List Pane) : List (String × String) :=
  panes.map fun pane => (pane.name, pane.dir)

/-- Reserve an identity namespace whose dots survive tmux session naming. -/
def encodeName (name : String) : String :=
  "linger=" ++ name.map (fun c => if c == '.' then '~' else c)

private def projectName (session window pane : String) : Option String :=
  if session.startsWith "linger=" then
    let name := (session.drop 7).toString.map (fun c => if c == '~' then '.' else c)
    if
        window == "0" && pane == "0" && Linger.Core.Name.sanitize name == name &&
          encodeName name == session then
      some name
    else none
  else some (session ++ "-w" ++ window ++ "-p" ++ pane)

/-- Parse one tab-split row, validating the command and discarding unused metadata. -/
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
        match projectName session window pane with
        | none => .error s!"malformed native session at line {line}: {session}"
        | some name =>
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

/-- One ordered catalog for human listing and the selector. Display context is
printable; the directory remains exact until the `IO` boundary encodes it.
Window metadata can describe a pane but cannot change its identity or cwd. -/
def catalogRows (content : String) (panes : List Pane) : List (List (String × String)) :=
  let rows := (content.splitOn "\n").map (·.splitOn "\t")
  panes.map fun pane =>
    let fields := rows[pane.line - 1]?.getD []
    let session := fields[1]?.getD ""
    let window := fields[2]?.getD ""
    let record :=
      rows.find? fun fields =>
        fields[0]? == some "window" && fields[1]? == some session && fields[2]? == some window
    let rawTitle := (record.getD [])[3]?.getD ""
    let title := (rawTitle.dropPrefix ":").toString
    let context := if title.isEmpty then s!"{session}:{window}" else s!"{session}:{window} {title}"
    [("name", pane.name), ("status", Linger.Core.Status.name .resumable),
      ("cmd", diagnostic s!"{context}  ·  {pane.dir}"), ("directory", pane.dir),
      ("line", toString pane.line)]

/-- Revalidate the exact displayed action data after transport. Never normalize a
target or execute a command from a save; absent or hostile identities fail closed. -/
def selectedPane (name dir : String) (line : Nat) : Option Pane :=
  if Linger.Core.Name.sanitize name == name && !dir.contains '\x00' then some { name, dir, line }
  else none

/-- Literal absolute directories that survive save/restore field handling. -/
private def representableDir (dir : String) : Bool :=
  dir.startsWith "/" && !dir.endsWith " " && !dir.contains "  " &&
    !dir.toList.any (fun c => ['\\', '\x00', '\t', '\n', '\r', '*', '?', '[', '#'].contains c)

/-- Generate one window and pane per native session. Reparse the actual text
before returning it; a NUL home also excludes any dependence on home expansion. -/
def renderSave (fields : List (String × String)) : Except String String :=
  match fields.find? (fun field => !representableDir field.2) with
  | some (_, dir) => .error s!"unrepresentable cwd in tmux save: {dir}"
  | none =>
    let content :=
      String.join
          (fields.map fun (name, dir) =>
            let session := encodeName name
            s!"pane\t{session}\t0\t1\t:*\t0\t{name}\t:{dir}\t1\tsh\t:\n" ++
              s!"window\t{session}\t0\t:{name}\t1\t:*\teven-horizontal\toff\n") ++
        match fields.head? with
        | none => ""
        | some (name, _) => s!"state\t{encodeName name}\t{encodeName name}\n"
    match parseSave "\x00" content with
    | .error error => .error error
    | .ok panes =>
      if common panes == fields then .ok content
      else .error "generated tmux save changed session identity or cwd"

/-- Skip existing names, preserving whole records and their order. -/
def plan (existing : List String) (panes : List Pane) : List Pane :=
  panes.filter (fun pane => !existing.contains pane.name)

end Linger.Tools.Resurrect
