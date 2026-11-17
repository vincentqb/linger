module

public import Linger.Display.CoreSpec
import Linger.Display.CoreCode.Status
import Terminal.CoreCode.Render
import Terminal.CoreCode.Vt

public section

/-! # Linger.Display.Listing — a `list` row's identity

The headline `rowFields_name` (`Challenge.lean`, part 2): a listed session's *identity* is
a function of its socket filename alone, never of the `info` reply the daemon returns. A
daemon too busy to answer within the poll window still lists under its
real name; and — because that same row set is the porcelain a remote
`-r` parses — a peer cannot rename or blank another session's row by
crafting a reply. `Inventory.localRows` builds every local row through
`rowFields`, so the property is *proved* (Linger/Display/Proofs/Listing.lean) rather
than asserted at the call site.
-/

namespace Linger.Display.Listing

/-- A session's listing fields, from its socket filename and the
key/values it reported. The leading `name` is always the socket filename,
which the caller has already validated; any `name` the reply tried to set
is dropped, so the row's identity is independent of the reply. -/
def rowFields (socketName : String) (info : List (String × String)) : List (String × String) :=
  ("name", socketName) :: info.filter (·.1 != "name")

/-! ## The row's status

`Status.classify` needs observations from two sources: the daemon reports
`unseen`/`fresh`/`exit` in its `info` reply, and the caller supplies what only
it can know, as the `Row` it passes — whether a socket accepted the connection and, for a
session without one, what its name's end record says. Splitting it this way is what makes
row identity extend to the status column: an absent or partial reply cannot make a
row look healthier than it is, because `daemonUp` comes from the caller and
`known` requires the `pid` or `cmd` field every real reply carries.
-/

open Linger.Display.Status (Status classify ofName)

/-- One boolean from the reply, defaulting to `false` when absent or
malformed — a reply cannot make a row *more* alive by omission. -/
private def flag (info : List (String × String)) (key : String) : Bool :=
  info.lookup key == some "true"

/-- Did the daemon actually answer? A connection can succeed while the daemon
is too busy to fill in the reply within the window, and the row must not then
be reported as a healthy idle session. `pid`/`cmd` are the fields a real reply
always carries, so their absence is the signal. -/
private def answered (info : List (String × String)) : Bool :=
  info.any (fun kv => (kv.1 == "pid" || kv.1 == "cmd") && kv.2 != "")

/-- The status a row displays. Only a live row consults the daemon's reply, and a remote row
shows its peer's status while the peer reports it live, or once the peer says its program
ended. -/
def rowStatus : Row → Status
  | .live info =>
    classify
      { known := answered info, daemonUp := true,
        -- a reply's exit status is read only here, for a live row: a socket-less row's
        -- comes from its end record (`ended`), so a reply can never make one look like a
        -- completed run
        exit := (info.lookup "exit").bind String.toNat?, fresh := flag info "fresh",
        unseen := flag info "unseen", asks := flag info "asks" }
  | .stale => .resumable
  | .ended status => classify { daemonUp := false, exit := some status }
  | .broken => .unknown
  | .remote live peerStatus =>
    -- a session the peer lists as saved shows how its program ended, and never what only a
    -- running session can show
    let status := ofName peerStatus
    if live || status == .exitedOk || status == .exitedBad then status else .resumable
  | .published fresh unseen asks => classify { fresh, unseen, asks }

/-! ## Rendering the human-readable listing

The daemon's info reply is framed by `infoText` (`infoText_records`); the CLI prints porcelain
from those parsed records. The *human* listing is different: it is printed straight to a
terminal, so a control byte in a `cmd`, a description, a checkpoint filename or a `-r` host
would execute as an escape sequence. Rather than scrub at the call site — an audit that has to
be redone whenever a new field is displayed — the row is rendered here, in the core, through
`Render.utf8s` (which maps every C0/DEL codepoint to U+FFFD), and `Linger/Display/Proofs/Listing.lean` proves
the result carries no control byte for *any* `info`. That is the same move `infoText` makes for
the daemon's reply, one layer out.

Rendering here also lets the column alignment be a property of the whole row *set* (the name
column is as wide as the widest name), which a per-`IO.println` call site cannot express. -/

open Terminal.Render (utf8s dropTrailingBlanks textChar)

/-- Text and optional badge style stay separate until a terminal renderer has
clipped the text, and the name span lets a selector emphasize the name without
parsing rendered text. -/
structure RowPiece where
  /-- The characters to display, already printable. -/
  text : List Char
  /-- The status whose style the piece takes; names and detail text never carry one. -/
  status : Option Status := none
  /-- The session name's offset and length within `text`, in Unicode scalars. -/
  nameSpan : Option (Nat × Nat) := none
  deriving BEq, Repr

/-! ## What a row shows

A row shows the session's present after its status and name, each field from its one source
(`sources`): the user's description, else the program's own title (`caption`); while the session
asks (`⚑`), the text of its program's last notification since the session was last looked at
(`notice`); how the last command that finished since then ended, as its shell's marks reported it
(`lastText`); the program in the terminal's foreground, unless it is the session's login shell at
its prompt (`program`); that program's directory; how long ago the session last printed; and its
watchers. A field appears only when it adds something: the program when the caption does not
already name it, the directory when the caption does not already hold it, and no text twice. The
user's words outrank the program's, which outrank the operating system's. -/

/-- A field of a record, `""` when the record lacks it. -/
def look (info : List (String × String)) (key : String) : String := (info.lookup key).getD ""

/-- The row's words: the title the program gave its window, else the status text it last gave
through `sd_notify`, else a description an older linger saved, which shows where the program's
words would while it gives none. The program's own words come first, its window's name before
its status, and what linger kept last. -/
def caption (info : List (String × String)) : String :=
  if (look info "title").isEmpty then
    if (look info "status_text").isEmpty then look info "description" else look info "status_text"
  else look info "title"

/-- The text of the program's last notification since the session was last looked at, while the
session asks; nothing for any other status. -/
def notice (info : List (String × String)) : String :=
  if Status.ofName (look info "status") == .asks then look info "notice" else ""

/-- How the last command that finished since the session was last looked at ended, as its
shell's marks reported it: its command line and `exit` with its status, as `make test: exit 2`,
or `ended` when its shell gave no status; the status alone when no command line reads; nothing
when no command finished unseen. -/
def lastText (info : List (String × String)) : String :=
  match info.lookup "lastcmd", info.lookup "lastexit" with
  | some line, some code => s!"{line}: exit {code}"
  | some line, none => s!"{line}: ended"
  | none, some code => s!"exit {code}"
  | none, none => ""

/-- The foreground program's command line, from the operating system's report: nothing while
that is the session's login shell itself, as at its prompt. A row whose daemon reports no
foreground but which has no `pid`, as a peer's, has its command. -/
def foregroundText (info : List (String × String)) : String :=
  if (info.lookup "fg").isSome then
    if look info "login" == "true" && look info "fgpid" == look info "pid" then ""
    else look info "fg"
  else if (look info "pid").isEmpty then look info "cmd" else ""

/-- The program in the terminal's foreground, as its command line: nothing while that is the
session's login shell itself, as at its prompt, or when the caption already names it. A row
whose daemon reports no foreground but which has no `pid`, as a peer's, shows its command. -/
def program (info : List (String × String)) : String :=
  if decide ((command (foregroundText info)).toList <:+: (caption info).toList) then ""
  else foregroundText info

/-- A count of seconds, in its largest whole unit: `42s`, `5m`, `3h` or `2d`. -/
def ago (seconds : Nat) : String :=
  if seconds < 60 then s!"{seconds}s"
  else
    if seconds < 3600 then s!"{seconds / 60}m"
    else if seconds < 86400 then s!"{seconds / 3600}h" else s!"{seconds / 86400}d"

/-- How a saved row's program ended, in the words a client prints when a session ends, from the
`exit`, `signal` and `outcome` fields `Session.outcomeFields` writes: `none` for a row that
carries none of them. -/
def endingText (info : List (String × String)) : Option String :=
  match info.lookup "signal", info.lookup "outcome", info.lookup "exit" with
  | some signal, _, _ => some s!"killed by signal {signal}"
  | none, some "unknown", _ => some "outcome unknown"
  | none, _, some code => some s!"status {code}"
  | none, _, none => none

/-- What a row says of a session that is not running: that it ended, and how, or that it is
resumable, and which signal stopped its daemon when one saved it (the `saved` field
`Session.endingFields` writes), or, for a row of a source linger only reads, which source saved
it, as `(saved by tmux)`; `(busy)` for a local daemon that did not answer, which carries no `pid`
and no `cmd`; and nothing for a running session. -/
def stateText (info : List (String × String)) : String :=
  let st := Status.ofName (look info "status")
  if look info "state" == "resumable" then
    if st == .exitedOk || st == .exitedBad then
      "ended" ++ ((endingText info).map (s!" ({·})")).getD ""
    else
      match info.lookup "saved", info.lookup "source" with
      | some signal, _ => s!"(resumable, saved by signal {signal})"
      | none, some source => s!"(saved by {source})"
      | none, none => "(resumable)"
  else
    if st == .unknown && (look info "pid").isEmpty && (look info "cmd").isEmpty then "(busy)"
    else ""

/-- The fields of `info` that `keys` names, in their order: a cell built from them cannot read any
other field. -/
def only (keys : List String) (info : List (String × String)) : List (String × String) :=
  keys.filterMap fun key => (info.lookup key).map ((key, ·))

/-- The caption cell: how a session that is not running stands, the caption, the text of a
notification while the session asks and how the last command that finished unseen ended, two
spaces apart. -/
def captionCell (info : List (String × String)) : String :=
  String.intercalate "  "
    ([stateText info, caption info, notice info, lastText info].filter (!·.isEmpty))

/-- The directory cell: the foreground program's directory, unless the caption holds it. -/
def dirCell (info : List (String × String)) : String :=
  if decide ((look info "fgdir").toList <:+: (caption info).toList) then "" else look info "fgdir"

/-- The age cell: how long ago the session last printed, unless it prints now. -/
def ageCell (info : List (String × String)) : String :=
  if Status.ofName (look info "status") == .working then ""
  else ((look info "idle").toNat?.map ago).getD ""

/-- The watchers cell: `+N` watchers, or nothing for none. -/
def watchCell (info : List (String × String)) : String :=
  if (look info "clients").isEmpty || look info "clients" == "0" then ""
  else s!"+{look info "clients"}"

/-- The cells after the name, in order, each from its own fields (`cellSources`): the caption,
the program, its directory, the age and the watchers. -/
def cells (info : List (String × String)) : List String :=
  [captionCell (only (cellSources.getD 0 []) info), program (only (cellSources.getD 1 []) info),
    dirCell (only (cellSources.getD 2 []) info), ageCell (only (cellSources.getD 3 []) info),
    watchCell (only (cellSources.getD 4 []) info)]

/-- The record a row reads: the `sources` fields of `info`, in their order. A row built from it
cannot show any other field. -/
def project (info : List (String × String)) : List (String × String) := only sources info

/-- The display columns `cs` takes on a terminal: a wide character two, a combining mark none. -/
def cols (cs : List Char) : Nat := (cs.map Terminal.Vt.charWidth).sum

/-- The longest start of `cs` that fits `room` display columns. -/
def takeCols : Nat → List Char → List Char
  | _, [] => []
  | room, c :: cs =>
    if Terminal.Vt.charWidth c ≤ room then c :: takeCols (room - Terminal.Vt.charWidth c) cs else []

/-- Cut `cs` to `room` display columns from the right: whole when it fits, else what fits before
an ellipsis, its trailing blanks dropped. -/
def cut (room : Nat) (cs : List Char) : List Char :=
  if cols cs ≤ room then cs
  else if room = 0 then [] else dropTrailingBlanks (takeCols (room - 1) cs) ++ ['…']

/-- `cs` padded with blanks to `width` display columns. -/
def pad (width : Nat) (cs : List Char) : List Char := cs ++ List.replicate (width - cols cs) ' '

/-- The parts of a row after its name, from the fields `rest`: each cell, cut to its column's
width and padded to it, between two spaces, so cells stand two spaces apart and the first one
space after the name, and nothing for a column of width zero. -/
def segments (layout : Layout) (rest : List (String × String)) : List (List Char) :=
  layout.widths.zipIdx.map fun (w, i) =>
    if w = 0 then [] else ' ' :: pad w (cut w ((cells rest).getD i "").toList) ++ [' ']

/-- A row's parts, one to a column, as a terminal shows them: the glyph and a space, the name
padded to the name column, then the cells (`segments`). Each part takes the display columns
`Layout.spans` gives it while the name fits its column (`columns_aligned`). -/
def columns (layout : Layout) (info : List (String × String)) : List (List Char) :=
  [[Status.icon (Status.ofName (look info "status")), ' '],
      (pad layout.nameCol (look info "name").toList).map textChar] ++
    (segments layout (project info)).map (·.map textChar)

/-- A row's pieces within `width` display columns, if any: the status badge, then the name and
what `after` shows after it, already printable. The badge and the name are never cut; what follows
shrinks from the right to fit. Every untrusted value is made printable before a renderer sees it,
including C1 controls that can otherwise be interpreted as terminal commands. -/
def piecesOf (width : Option Nat) (name status : String) (after : List Char) : List RowPiece :=
  let st := Status.ofName status
  let name := name.toList
  let tail := dropTrailingBlanks after
  let tail :=
    match width with
    | some w => cut (w - 2 - cols name) tail
    | none => tail
  [{ text := [Status.icon st], status := some st },
    { text := (' ' :: name).map textChar ++ tail, nameSpan := some (1, name.length) }]

/-- A row's pieces within `width` display columns, if any, from the fields `sources` names: the
badge, then its parts one to a column (`columns`), the name's padding and each cell in its column,
from the fields `sources` names. -/
def rowPiecesIn (width : Option Nat) (layout : Layout) (info : List (String × String)) :
    List RowPiece :=
  piecesOf width (look info "name") (look info "status")
    (((columns layout info).drop 1).flatten.drop (look info "name").length)

/-- One shared row of any width: status badge, aligned name and the session's present. -/
def rowPieces (layout : Layout) (info : List (String × String)) : List RowPiece :=
  rowPiecesIn none layout info

/-- A row's characters within `width`, if any: what a terminal shows of it. -/
def rowText (width : Option Nat) (layout : Layout) (info : List (String × String)) : List Char :=
  (rowPiecesIn width layout info).flatMap (·.text)

/-- The widest a column after the name grows, in display columns: the caption's, the program's,
the directory's, the age's and the watchers'. A longer value is cut with `…`. -/
def caps : List Nat := [48, 24, 32, 4, 5]

/-- The layout of a view of `rows`: the name column as wide as the widest name, and each later
column as wide as its widest cell, up to its cap when `capped`. -/
def layoutOf (rows : List (List (String × String))) (capped : Bool := true) : Layout where
  nameCol := rows.foldl (fun m r => max m (cols (look r "name").toList)) 0
  widths :=
    caps.zipIdx.map fun (cap, i) =>
      let widest := rows.foldl (fun m r => max m (cols ((cells (project r)).getD i "").toList)) 0
      if capped then min cap widest else widest

/-- A home directory's place in a directory: `~` for the home itself and `~/…` below it. -/
def tilde (home dir : String) : String :=
  if home.isEmpty || home == "/" then dir
  else
    if dir == home then "~"
    else if dir.startsWith (home ++ "/") then "~" ++ (dir.drop home.length).toString else dir

/-- A row with its foreground directory shortened with `~` under `home`, for a human reader. -/
def atHome (home : String) (info : List (String × String)) : List (String × String) :=
  info.map fun (k, v) => if k == "fgdir" then (k, tilde home v) else (k, v)

/-- Plain bytes, including when redirected: styles are deliberately absent. -/
def humanRow (layout : Layout) (info : List (String × String)) : List UInt8 :=
  utf8s ((rowPieces layout info).flatMap (·.text))

/-- `CSI <params> m`, select graphic rendition: the sequence that sets a style, its parameters
in decimal separated by `;`. -/
def sgr (params : List Nat) : List UInt8 :=
  Terminal.Render.csiB ++ ((params.map Terminal.Render.digits).intersperse [0x3B]).flatten ++ [0x6D]

/-- Render already-separated row pieces. Styling surrounds only the badge and
resets immediately, so names and details retain the default foreground. -/
private def renderPieces (withColor : Bool) (pieces : List RowPiece) : List UInt8 :=
  pieces.flatMap fun piece =>
    let text := utf8s piece.text
    match piece.status with
    | some status => if withColor then sgr (Status.style status) ++ text ++ sgr [0] else text
    | none => text

/-- The whole human-readable listing, one LF-terminated row per session (or the
empty-state line), with the same row pieces as the picker, each within `width` display columns
when it is given. The columns are the set's (`layoutOf`), so each field starts at one column in
every row; the columns' caps apply only within a width, so a listing written elsewhere than a
terminal, or a saved catalog's, which `tmux ls` writes, cuts no value. Callers choose whether color is enabled with `Linger.Os.Env.withColor`. -/
def terminalListing (withColor : Bool) (width : Option Nat) (rows : List (List (String × String))) :
    List UInt8 :=
  if rows.isEmpty then utf8s "no sessions".toList ++ [0x0A]
  else
    rows.flatMap fun r =>
      (if withColor then renderPieces true (rowPiecesIn width (layoutOf rows width.isSome) r)
        else utf8s (rowText width (layoutOf rows width.isSome) r)) ++
        [0x0A]

end Linger.Display.Listing
