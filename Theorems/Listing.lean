import Zmx.Core.Listing
/-! # §Row — a list row's identity is its socket filename, not the reply

The tension: the `info` reply is data from another process (a local
daemon, or — via porcelain — a remote host's `linger`), so it is not
trusted to name itself. `rowFields` derives the row's `name` from the
socket filename alone; these two theorems say the reply can neither
change it (`rowFields_name`) nor smuggle a second one in
(`rowFields_reply_excluded`).
-/

namespace Zmx.Core.Listing

open Zmx.Core.Name (sanitize)

/-- The row's `name` is the sanitized socket filename for ANY reply, so
a peer's reply can never spoof another session's identity. -/
theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (rowFields socketName info).lookup "name" = some (sanitize socketName) := by
  simp [rowFields]

/-- Nothing after the leading name — everything the reply contributed —
carries the "name" key: the reply's own name (if any) is physically
dropped, not merely shadowed. -/
theorem rowFields_reply_excluded (socketName v : String)
    (info : List (String × String)) :
    (⟨"name", v⟩ : String × String) ∉ (rowFields socketName info).tail := by
  simp [rowFields, List.mem_filter]

end Zmx.Core.Listing
