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

def rowStatus (socketPresent answered ckptLoadable : Bool)
    (info : List (String × String)) : Status :=
  classify {
    known := if socketPresent then answered else ckptLoadable,
    daemonUp := socketPresent,
    -- an exit status can only come from a live daemon: without one there is
    -- nobody to have observed the child, so a reply-supplied "exit" must not
    -- make a socket-less row look like a completed run
    exit := if socketPresent then (info.find? (·.1 == "exit")).bind (fun kv => kv.2.toNat?)
            else none,
    fresh := flag info "fresh",
    unseen := flag info "unseen" }

end Zmx.Core.Listing
