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
theorem rowStatus_unanswered (ckpt : Bool) (info : List (String × String)) :
    rowStatus true false ckpt info = Status.unknown := rfl

/-- No socket but a loadable checkpoint is `resumable`, whatever the reply
contained (there is no daemon to have sent one). -/
theorem rowStatus_resumable (answered : Bool) (info : List (String × String)) :
    rowStatus false answered true info = Status.resumable := rfl

/-- No socket and no loadable checkpoint is `unknown`. -/
theorem rowStatus_gone (answered : Bool) (info : List (String × String)) :
    rowStatus false answered false info = Status.unknown := rfl

/-- An empty reply is not an answer, so a busy daemon lists as `unknown`
rather than as a healthy idle session. This is the §Row property applied to
health: the row still carries its real name, and is honestly marked as one we
could not read. -/
theorem answered_nil : answered [] = false := rfl

theorem rowStatus_empty_reply : rowStatus true (answered []) true [] = Status.unknown :=
  rfl

/-- A missing or malformed flag reads as `false`, so an omission cannot make
a row look busier or fresher than it is. -/
theorem flag_absent (info : List (String × String)) (k : String)
    (h : info.find? (·.1 == k) = none) : flag info k = false := by
  simp [flag, h]

end Zmx.Core.Listing
