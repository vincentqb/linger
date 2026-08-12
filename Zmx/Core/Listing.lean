import Zmx.Core.Name
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

end Zmx.Core.Listing
