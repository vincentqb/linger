module

import Linger.Core.Name
import Linger.Core.Status
public import Linger.Core.Checkpoint

public section

/-! Pure tmux-resurrect interchange and import planning.

Pane records supply identity, directory, title and command information. Captured
contents seed a checkpoint; commands remain labels, never executable arguments.
The caller must preflight every directory it will import before performing effects.
Planning uses an explicit snapshot of existing names; it does not claim atomic
creation or protection from concurrent same-name creators.
-/

namespace Linger.Tools.Resurrect

/-- Replace terminal controls only when displaying an error, preserving its other text. -/
def diagnostic (message : String) : String :=
  message.map fun c => if 32 ≤ c.toNat && (c.toNat < 127 || 160 ≤ c.toNat) then c else '?'

/-- Information about the original tmux pane, retained independently of the fresh shell. -/
structure Details where
  /-- Original tmux session name. -/
  session : String := ""
  /-- Original tmux window index. -/
  window : String := ""
  /-- Original tmux pane index, distinct from tmux's internal pane ID. -/
  index : String := ""
  /-- Saved pane title. -/
  title : String := ""
  /-- Foreground command name at save time, not the last completed shell command. -/
  command : String := ""
  /-- Saved foreground command line, without the file format's colon sentinel. -/
  savedCommand : String := ""
  /-- Saved window title. -/
  windowTitle : String := ""
  /-- Saved layout width; 80 when the layout cannot be resolved. -/
  cols : Nat := 80
  /-- Saved layout height; 24 when the layout cannot be resolved. -/
  rows : Nat := 24
  deriving BEq, Repr

/-- One saved pane and its independent linger session. -/
structure Pane where
  /-- The projected linger session name; parsing accepts only canonical names. -/
  name : String
  /-- The decoded working directory; parsing expands `~` and a `~/` prefix to the home
  directory and rejects NUL. -/
  dir : String
  /-- The 1-based line of the pane record in the save, for diagnostics and catalog rows. -/
  line : Nat
  /-- Original pane metadata; never used to launch a saved command. -/
  details : Details := {}
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

/-- Parse one tab-split row, retaining title and command information as data. -/
private def parseRow (home : String) (line : Nat) (fields : List String) :
    Except String (Option Pane) :=
  if fields.head? != some "pane" then .ok none
  else
    match fields with
    | [_, session, window, _, _, pane, title, cwd, _, command, savedCommand] =>
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
            else
              .ok
                (some
                  { name, dir, line,
                    details :=
                      { session, window, index := pane, title, command,
                        savedCommand := (savedCommand.drop 1).toString } })
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

/-- Leaf dimensions from the ordinary tmux layout grammar, in layout order.
Container nodes have no numeric pane ID; their first child begins with a size. -/
private def layoutLeaves : List String → List (Nat × Nat)
  | [] => []
  | size :: rest =>
    let later := layoutLeaves rest
    match size.splitOn "x", rest with
    | [cols, rows], x :: y :: id :: _ =>
      match cols.toNat?, rows.toNat?, x.toNat?, y.toNat?, id.toNat? with
      | some cols, some rows, some _, some _, some _ => (cols, rows) :: later
      | _, _, _, _, _ => later
    | _, _ => later

/-- Read tmux's leaf sizes without interpreting its layout checksum or pane IDs. -/
def layoutSizes (layout : String) : List (Nat × Nat) :=
  layoutLeaves
    ((layout.map fun c => if ['{', '}', '[', ']'].contains c then ',' else c).splitOn ",")

/-- Enrich a pane from its window record. Numeric pane indices enumerate tmux's
layout leaves; unsupported layouts or a mismatched leaf count use 80×24. -/
def preparePane (content : String) (panes : List Pane) (pane : Pane) : Pane :=
  let record :=
    ((content.splitOn "\n").map (·.splitOn "\t")).find? fun fields =>
      fields[0]? == some "window" && fields[1]? == some pane.details.session &&
        fields[2]? == some pane.details.window
  let fields := record.getD []
  let sizes := layoutSizes (fields[6]?.getD "")
  let siblings :=
    (panes.filter fun p =>
        p.details.session == pane.details.session &&
          p.details.window == pane.details.window).toArray
  let ordered :=
    siblings.qsort (fun a b => a.details.index.toNat?.getD 0 < b.details.index.toNat?.getD 0)
  let rank := ordered.toList.findIdx? (fun p => p.name == pane.name)
  let size :=
    if sizes.length == siblings.size && siblings.all (·.details.index.toNat?.isSome) then
      rank.bind (sizes[·]?)
    else none
  { pane with
    details :=
      { pane.details with
        windowTitle := ((fields[3]?.getD "").dropPrefix ":").toString,
        cols := size.map Prod.fst |>.getD 80, rows := size.map Prod.snd |>.getD 24 } }

/-- The exact archive member for a validated source identity. No path rewriting. -/
def contentMember (pane : Pane) : Option String :=
  if
      Linger.Core.Name.sanitize pane.name == pane.name &&
        projectName pane.details.session pane.details.window pane.details.index ==
          some pane.name then
    some s!"./pane_contents/pane-{pane.details.session}:{pane.details.window}.{pane.details.index}"
  else none

/-- Maximum retained capture bytes per pane; oversize input is refused at the `IO` boundary. -/
def captureLimit : Nat := 8 * 1024 * 1024

/-- Turn captured lines into terminal input. The archive's final newline is framing;
other newlines start at column zero. The pure adapter also bounds its input. -/
def captureBytes (contents : String) : List UInt8 :=
  let bytes := contents.toUTF8.toList.take captureLimit
  let bytes := if bytes.getLast? == some 10 then bytes.dropLast else bytes
  bytes.flatMap fun b => if b == 10 then [13, 10] else [b]

/-- Seed screen and scrollback through the terminal's public parser, and retain
saved commands and source identity only in checkpoint labels. -/
def checkpoint (pane : Pane) (contents : Option String) : Linger.Core.Checkpoint.Ckpt :=
  {
    vt :=
      ((Linger.Core.Vt.Vt.init pane.details.cols pane.details.rows).feed
          (captureBytes (contents.getD ""))).quiesce,
    cwd := pane.dir,
    labels :=
      [("tmux.session", pane.details.session), ("tmux.window", pane.details.window),
        ("tmux.pane", pane.details.index), ("tmux.title", pane.details.title),
        ("tmux.command", pane.details.command), ("tmux.saved-command", pane.details.savedCommand),
        ("tmux.window-title", pane.details.windowTitle),
        ("tmux.capture", if contents.isSome then "saved" else "none")] }

/-- One ordered catalog for human listing and the selector. Display context is
printable; the directory remains exact until the `IO` boundary encodes it.
Window metadata can describe a pane but cannot change its identity or cwd. -/
def catalogRows (content : String) (panes : List Pane) : List (List (String × String)) :=
  let rows := (content.splitOn "\n").map (·.splitOn "\t")
  panes.map fun pane =>
    let details := (preparePane content panes pane).details
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
      ("line", toString pane.line), ("session", details.session), ("window", details.window),
      ("pane", details.index), ("title", details.title), ("command", details.command),
      ("saved-command", details.savedCommand), ("window-title", details.windowTitle),
      ("cols", toString details.cols), ("rows", toString details.rows)]

/-- Revalidate the exact displayed action data after transport. Never normalize a
target or execute a command from a save; absent or hostile identities fail closed. -/
def selectedPane (name dir : String) (line : Nat) (details : Details := {}) : Option Pane :=
  if Linger.Core.Name.sanitize name == name && !dir.contains '\x00' then
    some { name, dir, line, details }
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
