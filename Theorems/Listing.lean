import Theorems.Status
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

/-! ## §Row extends to the status column

The identity half of §Row says a reply cannot rename a row. These say it
cannot lie about the row's *health* either: the two facts that decide whether
a row is trustworthy at all come from the caller, never from the reply.
-/

open Zmx.Core.Status (Status)

/-- A live socket that did not answer is `unknown`, whatever the reply
contained — so a daemon too busy to answer cannot be reported as idle, and a
crafted reply cannot claim otherwise. -/
theorem rowStatus_unanswered (info : List (String × String))
    (h : answered info = false) : rowStatus (.live info) = Status.unknown := by
  simp [rowStatus, Zmx.Core.Status.classify, h]

/-- No socket but a loadable checkpoint is `resumable`, whatever the reply
contained (there is no daemon to have sent one). -/
theorem rowStatus_resumable : rowStatus .stale = Status.resumable := rfl

/-- No socket and no loadable checkpoint is `unknown`. -/
theorem rowStatus_gone : rowStatus .broken = Status.unknown := rfl

/-- An empty reply is not an answer, so a busy daemon lists as `unknown`
rather than as a healthy idle session. This is the §Row property applied to
health: the row still carries its real name, and is honestly marked as one we
could not read. -/
theorem answered_nil : answered [] = false := rfl

theorem rowStatus_empty_reply : rowStatus (.live []) = Status.unknown := rfl

/-- A peer cannot claim a state we could not read: an absent or unrecognised
`status` reports `unknown`, not `idle`. This is what keeps a remote glyph an
honest statement rather than an inference from liveness alone. -/
theorem rowStatus_remote_unreadable (junk : String)
    (h : Zmx.Core.Status.ofName junk = Status.unknown) :
    rowStatus (.remote true junk) = Status.unknown := by
  simp [rowStatus, h]

theorem rowStatus_remote_absent : rowStatus (.remote true "") = Status.unknown := rfl

/-- …and a peer that does report one is taken at its word, since it is the
authority on its own session. Round-trips through the porcelain name by
`ofName_name`. -/
theorem rowStatus_remote_reported (st : Status) :
    rowStatus (.remote true (Zmx.Core.Status.name st)) = st := by
  simp [rowStatus, Zmx.Core.Status.ofName_name]

/-- A missing or malformed flag reads as `false`, so an omission cannot make
a row look busier or fresher than it is. -/
theorem flag_absent (info : List (String × String)) (k : String)
    (h : info.find? (·.1 == k) = none) : flag info k = false := by
  simp [flag, h]

end Zmx.Core.Listing
