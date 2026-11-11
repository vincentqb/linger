module

public import Linger.Display.Spec
import Linger.Display.Status
import Terminal.Render

public section

/-! # Linger.Display.Listing — a `list` row's identity

§Row (THEOREMS.md): a listed session's *identity* is a function of its
socket filename alone, never of the `info` reply the daemon returns. A
daemon too busy to answer within the poll window still lists under its
real name; and — because that same row set is the porcelain a remote
`-r` parses — a peer cannot rename or blank another session's row by
crafting a reply. `Cli.cmdList` builds every local row through
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
it can know — whether a socket is there, whether the daemon answered, and
whether a checkpoint loads. Splitting it this way is what makes the §Row
property extend to the status column: an absent or partial reply cannot make a
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
        unseen := flag info "unseen" }
  | .stale => .resumable
  | .ended status => classify { daemonUp := false, exit := some status }
  | .broken => .unknown
  | .remote live peerStatus =>
    -- a session the peer lists as saved shows how its program ended, and never what only a
    -- running session can show
    let status := ofName peerStatus
    if live || status == .exitedOk || status == .exitedBad then status else .resumable
  | .published fresh unseen => classify { fresh, unseen }

/-! ## Rendering the human-readable listing

The daemon's info reply is framed by `infoText` (`infoText_records`); the CLI prints porcelain
from those parsed records. The *human* listing is different: it is printed straight to a
terminal, so a control byte in a `cmd`, a label value, a checkpoint filename or a `-r` host
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

/-- How a saved row's program ended, in the words a client prints when a session ends, from the
`exit`, `signal` and `outcome` fields `Session.outcomeFields` writes: `none` for a row that
carries none of them. -/
def endingText (info : List (String × String)) : Option String :=
  match info.lookup "signal", info.lookup "outcome", info.lookup "exit" with
  | some signal, _, _ => some s!"killed by signal {signal}"
  | none, some "unknown", _ => some "outcome unknown"
  | none, _, some code => some s!"status {code}"
  | none, _, none => none

/-- One shared row: status badge, aligned name, command/pid, labels and watchers.
Every untrusted value is made printable before a renderer sees it, including C1
controls that can otherwise be interpreted as terminal commands. A saved row whose program
ended says how, where another saved row says it is resumable. -/
def rowPieces (nameCol : Nat) (info : List (String × String)) : List RowPiece :=
  let f := fun k => (info.lookup k).getD ""
  let st := Status.ofName (f "status")
  let labels :=
    info.filterMap
      (fun (k, v) => if k.startsWith "label." then some s!"{(k.drop 6).toString}={v}" else none)
  let labelStr := if labels.isEmpty then "" else "  [" ++ String.intercalate " " labels ++ "]"
  -- `(busy)` is only for a *local* daemon that did not answer (status unknown,
  -- no pid/cmd); a live remote row carries no pid but is not busy.
  let detail :=
    if f "state" == "resumable" then
      if st == .exitedOk || st == .exitedBad then
        "ended" ++ ((endingText info).map (s!" ({·})")).getD ""
      else "(resumable)"
    else
      if st == .unknown && (f "pid").isEmpty && (f "cmd").isEmpty then "(busy)"
      else if (f "pid").isEmpty then f "cmd" else s!"pid {f "pid"}  {f "cmd"}"
  let watch := if (f "clients").isEmpty || f "clients" == "0" then "" else s!"  +{f "clients"}"
  let name := (f "name").toList
  let text :=
    (dropTrailingBlanks
          ([' '] ++ name ++ List.replicate (nameCol - name.length) ' ' ++ [' '] ++
            (detail ++ labelStr ++ watch).toList)).map
      textChar
  [{ text := [Status.icon st], status := some st }, { text, nameSpan := some (1, name.length) }]

/-- Plain bytes, including when redirected: styles are deliberately absent. -/
def humanRow (nameCol : Nat) (info : List (String × String)) : List UInt8 :=
  utf8s ((rowPieces nameCol info).flatMap (·.text))

/-- Shared name column width over the complete listing snapshot. -/
def nameWidth (rows : List (List (String × String))) : Nat :=
  rows.foldl (fun m r => max m ((r.lookup "name").getD "").toList.length) 0

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
empty-state line), with the same row pieces as the picker. The name column is as
wide as the widest name in the set, so the detail columns align. Callers choose
whether color is enabled from terminal detection and `NO_COLOR`. -/
def terminalListing (withColor : Bool) (rows : List (List (String × String))) : List UInt8 :=
  if rows.isEmpty then utf8s "no sessions".toList ++ [0x0A]
  else rows.flatMap (fun r => renderPieces withColor (rowPieces (nameWidth rows) r) ++ [0x0A])

end Linger.Display.Listing
