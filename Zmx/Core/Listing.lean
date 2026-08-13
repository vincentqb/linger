import Zmx.Core.Name
import Zmx.Core.Status
/-! # Zmx.Core.Listing — a `list` row's identity

§Row (THEOREMS.md): a listed session's *identity* is a function of its
socket filename alone, never of the `info` reply the daemon returns. A
daemon too busy to answer within the poll window still lists under its
real name; and — because that same row set is the porcelain a remote
`-r` parses — a peer cannot rename or blank another session's row by
crafting a reply. `Cli.cmdList` builds every local row through
`rowFields`, so the property is *proved* (Theorems/Listing.lean) rather
than asserted at the call site.
-/

namespace Zmx.Core.Listing

open Zmx.Core.Name (sanitize)

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

open Zmx.Core.Status (Status Obs classify)

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
  | remote (live : Bool)
  deriving Repr

def rowStatus : Row → Status
  | .live info =>
    classify {
      known := answered info,
      daemonUp := true,
      -- an exit status can only come from a live daemon, so it is read only
      -- here: a reply-supplied "exit" must never make a socket-less row look
      -- like a completed run
      exit := (info.find? (·.1 == "exit")).bind (fun kv => kv.2.toNat?),
      fresh := flag info "fresh",
      unseen := flag info "unseen" }
  | .stale => .resumable
  | .broken => .unknown
  | .remote live => if live then .idle else .resumable

end Zmx.Core.Listing
