module

public import Linger.Core.Name
public import Linger.Core.Status
public import Linger.Core.Render

public section

/-! # Linger.Core.Listing — a `list` row's identity

§Row (THEOREMS.md): a listed session's *identity* is a function of its
socket filename alone, never of the `info` reply the daemon returns. A
daemon too busy to answer within the poll window still lists under its
real name; and — because that same row set is the porcelain a remote
`-r` parses — a peer cannot rename or blank another session's row by
crafting a reply. `Cli.cmdList` builds every local row through
`rowFields`, so the property is *proved* (Theorems/Listing.lean) rather
than asserted at the call site.
-/

namespace Linger.Core.Listing

open Linger.Core.Name (sanitize)

/-- A session's listing fields, from its socket filename and the
key/values it reported. The leading `name` is always the sanitized
socket filename; any `name` the reply tried to set is dropped, so the
row's identity is independent of the reply. -/
def rowFields (socketName : String) (info : List (String × String)) : List (String × String) :=
  ("name", sanitize socketName) :: info.filter (·.1 != "name")

/-! ## The row's status

`Status.classify` needs observations from two sources: the daemon reports
`unseen`/`fresh`/`exit` in its `info` reply, and the caller supplies what only
it can know — whether a socket is there, whether the daemon answered, and
whether a checkpoint loads. Splitting it this way is what makes the §Row
property extend to the status column: an absent or hostile reply cannot make a
row look healthier than it is, because `known` and `daemonUp` are not taken
from the reply.
-/

open Linger.Core.Status (Status Obs classify ofName)

/-- One boolean from the reply, defaulting to `false` when absent or
malformed — a reply cannot make a row *more* alive by omission. -/
def flag (info : List (String × String)) (key : String) : Bool :=
  (info.find? (·.1 == key)).any (·.2 == "true")

/-- Did the daemon actually answer? A connection can succeed while the daemon
is too busy to fill in the reply within the window, and the row must not then
be reported as a healthy idle session. `pid`/`cmd` are the fields a real reply
always carries, so their absence is the signal. -/
def answered (info : List (String × String)) : Bool :=
  info.any (fun kv => (kv.1 == "pid" || kv.1 == "cmd") && kv.2 != "")

/-- Where a listing row came from. **A sum type rather than a handful of
`Bool`s on purpose.** The previous signature took `socketPresent`,
`answered` and `ckptLoadable` separately, and a caller passed a literal
`true` for `answered` — so "the daemon did not answer" became unreachable and
a busy session listed as a healthy idle one, even though the theorem about it
was correct. Booleans a caller has to get right are the hazard; each
constructor here carries exactly the facts its case has, so there is no
argument left to pass wrongly. -/
inductive Row where
  /-- A socket accepted the connection; `info` is whatever it replied (possibly
  nothing, if it was too busy). -/
  | live (info : List (String × String))
  /-- No socket, but a checkpoint file is there. -/
  | stale
  /-- No socket, and the checkpoint will not load. Not produced by `Cli` yet —
  it lists checkpoint *names* without probing them — and that gap is visible
  here as an unused constructor rather than hidden in a `true`. -/
  | broken
  /-- From a peer's porcelain over ssh. A peer forwards liveness but not
  activity, so `⣀` on a remote row means "alive, activity unknown"; forwarding
  the peer's own `status` field is the improvement that would fix it. -/
  | remote (live : Bool) (peerStatus : String)
  deriving Repr

def rowStatus : Row → Status
  | .live info =>
    classify
      { known := answered info, daemonUp := true,
        -- an exit status can only come from a live daemon, so it is read only
        -- here: a reply-supplied "exit" must never make a socket-less row look
        -- like a completed run
        exit := (info.find? (·.1 == "exit")).bind (fun kv => kv.2.toNat?),
        fresh := flag info "fresh", unseen := flag info "unseen" }
  | .stale => .resumable
  | .broken => .unknown
  | .remote live peerStatus => if live then ofName peerStatus else .resumable

/-! ## Rendering the human-readable listing

The `--porcelain` output is `k\tv\n` records, parsed by a peer and proved framing-safe by
`Session.infoText_records`. The *human* listing is different: it is printed straight to a
terminal, so a control byte in a `cmd`, a label value, a checkpoint filename or a `-r` host
would execute as an escape sequence. Rather than scrub at the call site — an audit that has to
be redone whenever a new field is displayed — the row is rendered here, in the core, through
`Render.utf8s` (which maps every C0/DEL codepoint to U+FFFD), and `Theorems/Listing.lean` proves
the result carries no control byte for *any* `info`. That is the same move `infoText` makes for
the daemon's reply, one layer out.

Rendering here also lets the column alignment be a property of the whole row *set* (the name
column is as wide as the widest name), which a per-`IO.println` call site cannot express. -/

open Linger.Core.Render (utf8s dropTrailingBlanks safeChar)

/-- Text and optional badge style stay separate until a terminal renderer has
clipped the text. Names and detail text never carry a status style. -/
structure RowPiece where
  text : List Char
  status : Option Status := none
  deriving BEq, Repr

/-- One shared row: status badge, aligned name, command/pid, labels and watchers.
Every untrusted value is made printable before a renderer sees it, including C1
controls that can otherwise be interpreted as terminal commands. -/
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
    if f "state" == "resumable" then "(resumable)"
    else
      if st == .unknown && (f "pid").isEmpty && (f "cmd").isEmpty then "(busy)"
      else if (f "pid").isEmpty then f "cmd" else s!"pid {f "pid"}  {f "cmd"}"
  let watch := if (f "clients").isEmpty || f "clients" == "0" then "" else s!"  +{f "clients"}"
  let name := (f "name").toList
  let text :=
    (dropTrailingBlanks
          ([' '] ++ name ++ List.replicate (nameCol - name.length) ' ' ++ [' '] ++
            (detail ++ labelStr ++ watch).toList)).map
      fun c => if c.toNat ≥ 0x7F && c.toNat < 0xA0 then '�' else safeChar c
  [{ text := [Status.icon st], status := some st }, { text }]

/-- Plain bytes, including when redirected: styles are deliberately absent. -/
def humanRow (nameCol : Nat) (info : List (String × String)) : List UInt8 :=
  utf8s ((rowPieces nameCol info).flatMap (·.text))

/-- Shared name column width over the complete listing snapshot. -/
def nameWidth (rows : List (List (String × String))) : Nat :=
  rows.foldl (fun m r => max m ((r.lookup "name").getD "").toList.length) 0

/-- Render already-separated row pieces. Styling surrounds only the badge and
resets immediately, so names and details retain the default foreground. -/
def renderPieces (withColor : Bool) (pieces : List RowPiece) : List UInt8 :=
  pieces.flatMap fun piece =>
    let text := utf8s piece.text
    match piece.status with
    | some status =>
      if withColor then (Status.style status).toUTF8.toList ++ text ++ "\x1b[0m".toUTF8.toList
      else text
    | none => text

/-- The whole human-readable listing, one LF-terminated row per session (or the
empty-state line). The name column is as wide as the widest name in the set, so
the detail columns align. -/
def humanListing (rows : List (List (String × String))) : List UInt8 :=
  if rows.isEmpty then utf8s "no sessions".toList ++ [0x0A]
  else rows.flatMap (fun r => humanRow (nameWidth rows) r ++ [0x0A])

/-- Terminal listing with the same row pieces as the picker. Callers choose
whether color is enabled from terminal detection and `NO_COLOR`. -/
def terminalListing (withColor : Bool) (rows : List (List (String × String))) : List UInt8 :=
  if rows.isEmpty then utf8s "no sessions".toList ++ [0x0A]
  else rows.flatMap (fun r => renderPieces withColor (rowPieces (nameWidth rows) r) ++ [0x0A])

end Linger.Core.Listing
