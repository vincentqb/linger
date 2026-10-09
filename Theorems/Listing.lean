module

public import Theorems.Status
public import Theorems.Render
public import Linger.Core.Listing
import all Linger.Core.Listing
import all Linger.Core.Status
-- Converted from legacy by the `Vt` seal (`specs/archive/vt-toolkit.md` Step 1): the proof
-- layer is module-private now, so `utf8s_no_ctl` arrives via `import all`.
import all Theorems.Render
import all Theorems.Status

/-! # §Row — a list row's identity is its socket filename, not the reply

The tension: the `info` reply is data from another process (a local
daemon, or — via porcelain — a remote host's `linger`), so it is not
trusted to name itself. `rowFields` derives the row's `name` from the
socket filename alone; these two theorems say the reply can neither
change it (`rowFields_name`) nor smuggle a second one in
(`rowFields_reply_excluded`).
-/

namespace Linger.Core.Listing

/-- The row's `name` is the socket filename for ANY reply, so a peer's
reply can never spoof another session's identity. -/
theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (rowFields socketName info).lookup "name" = some socketName := by simp [rowFields]

/-- Nothing after the leading name — everything the reply contributed —
carries the "name" key: the reply's own name (if any) is physically
dropped, not merely shadowed. -/
theorem rowFields_reply_excluded (socketName v : String) (info : List (String × String)) :
    (⟨"name", v⟩ : String × String) ∉ (rowFields socketName info).tail := by
  simp [rowFields, List.mem_filter]

/-! ## §Row extends to the status column

The identity half of §Row says a reply cannot rename a row. These say it
cannot lie about the row's *health* either: the two facts that decide whether
a row is trustworthy at all come from the caller, never from the reply.
-/

open Linger.Core.Status (Status)

/-- A live socket that did not answer is `unknown`, whatever the reply
contained — so a daemon too busy to answer cannot be reported as idle, and a
crafted reply cannot claim otherwise. -/
theorem rowStatus_unanswered (info : List (String × String)) (h : answered info = false) :
    rowStatus (.live info) = Status.unknown := by simp [rowStatus, Linger.Core.Status.classify, h]

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

/-- A peer cannot claim a state we could not read: an absent or unrecognised
`status` reports `unknown`, not `idle`. This is what keeps a remote glyph an
honest statement rather than an inference from liveness alone. -/
theorem rowStatus_remote_unreadable (junk : String)
    (h : Linger.Core.Status.ofName junk = Status.unknown) :
    rowStatus (.remote true junk) = Status.unknown := by simp [rowStatus, h]

/-- …and a peer that does report one is taken at its word, since it is the
authority on its own session. Round-trips through the porcelain name by
`ofName_name`. -/
theorem rowStatus_remote_reported (st : Status) :
    rowStatus (.remote true (Linger.Core.Status.name st)) = st := by
  simp [rowStatus, Linger.Core.Status.ofName_name]

/-- A missing or malformed flag reads as `false`, so an omission cannot make
a row look busier or fresher than it is. -/
theorem flag_absent (info : List (String × String)) (k : String) (h : info.lookup k = none) :
    flag info k = false := by simp [flag, h]

/-! ## The human-readable listing is safe to print

The listing goes straight to a terminal, so a control byte in any displayed value — a `cmd`, a
label, a checkpoint filename, a `-r` host — would run as an escape sequence. These say it
cannot, for ANY `info` a reply could carry: the row is rendered through `Render.utf8s`, which
maps every C0/DEL codepoint to U+FFFD, so the guarantee needs no hypothesis about the source.
The `infoText` argument (`Session.infoText_framing`), applied one layer out at the display. -/

open Linger.Core.Render (utf8s_no_ctl)

/-- **Every byte of a printed row is printable content** — no C0 control, no DEL — whatever the
reply contained. `humanRow` ends in `utf8s`, so this is `utf8s`'s own guarantee. -/
theorem humanRow_printable (nameCol : Nat) (info : List (String × String)) :
    ∀ b ∈ humanRow nameCol info, 0x20 ≤ b ∧ b ≠ 0x7F := utf8s_no_ctl _

/-- A row carries no newline, so a `cmd` or label value cannot forge a listing row. -/
theorem humanRow_no_lf (nameCol : Nat) (info : List (String × String)) :
    ∀ b ∈ humanRow nameCol info, b ≠ 0x0A := by
  intro b hb he
  have := (humanRow_printable nameCol info b hb).1
  rw [he] at this; exact absurd this (by decide)

/-- **Every byte of the whole listing is printable content or a row-terminating newline** — the
only bytes are what the rows render (safe by `humanRow_printable`) and the `0x0A` separators. -/
theorem humanListing_printable (rows : List (List (String × String))) :
    ∀ b ∈ humanListing rows, (0x20 ≤ b ∧ b ≠ 0x7F) ∨ b = 0x0A := by
  intro b hb
  unfold humanListing at hb
  by_cases hz : rows.isEmpty
  · rw [ite_eq_left hz] at hb
    rcases List.mem_append.mp hb with h | h
    · exact Or.inl (utf8s_no_ctl _ b h)
    · exact Or.inr (by simpa using h)
  · rw [ite_eq_right hz] at hb
    rw [List.mem_flatMap] at hb
    obtain ⟨r, -, hbr⟩ := hb
    rcases List.mem_append.mp hbr with h | h
    · exact Or.inl (humanRow_printable _ r b h)
    · exact Or.inr (by simpa using h)

/-- Pieces remove controls before width calculation or styling. A terminal
renderer therefore never clips inside an untrusted escape sequence. -/
theorem rowPieces_printable (nameCol : Nat) (info : List (String × String)) :
    ∀ piece ∈ Linger.Core.Listing.rowPieces nameCol info,
      ∀ c ∈ piece.text, 32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) := by
  intro piece hp c hc
  simp only [rowPieces, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · simp only [List.mem_singleton] at hc
    subst c
    cases Status.ofName ((info.lookup "status").getD "") <;> decide
  · obtain ⟨raw, _, rfl⟩ := List.mem_map.mp hc
    split
    · decide
    · unfold Linger.Core.Render.safeChar
      split
      · decide
      · simp_all <;> omega

/-- Exactly the badge is styled; the name, details, labels and watchers are plain. -/
theorem rowPieces_styles (nameCol : Nat) (info : List (String × String)) :
    (Linger.Core.Listing.rowPieces nameCol info).map (·.status) =
      [some (Status.ofName ((info.lookup "status").getD "")), none] := rfl

/-- Query emphasis addresses only the name after the body's leading space.
Its length comes from the actual name, independently of padding or metadata. -/
theorem rowPieces_nameSpan (nameCol : Nat) (info : List (String × String)) :
    (Linger.Core.Listing.rowPieces nameCol info).map (·.nameSpan) =
      [none, some (1, ((info.lookup "name").getD "").toList.length)] := rfl

theorem nameWidth_empty : Linger.Core.Listing.nameWidth [] = 0 := rfl

/-- A width fits the complete snapshot exactly when it fits every name.
The computed column is therefore the least sufficient width. -/
theorem nameWidth_le_iff (rows : List (List (String × String))) (width : Nat) :
    Linger.Core.Listing.nameWidth rows ≤ width ↔
      ∀ row ∈ rows, ((row.lookup "name").getD "").toList.length ≤ width := by
  have fold_le (rs : List (List (String × String))) (n : Nat) :
    rs.foldl (fun m r => max m ((r.lookup "name").getD "").toList.length) n ≤ width ↔
      n ≤ width ∧ ∀ row ∈ rs, ((row.lookup "name").getD "").toList.length ≤ width := by
    induction rs generalizing n with
    | nil => simp
    | cons r rs ih => simp [List.foldl_cons, ih, Nat.max_le, and_assoc]
  simpa [nameWidth] using fold_le rows 0

/-- Every row's name fits the column calculated for the entire snapshot. -/
theorem nameWidth_covers (rows : List (List (String × String))) (row : List (String × String))
    (h : row ∈ rows) :
    ((row.lookup "name").getD "").toList.length ≤ Linger.Core.Listing.nameWidth rows :=
  (nameWidth_le_iff rows _).mp (Nat.le_refl _) row h

/-- Removing style produces exactly the bytes of the same plain row pieces. -/
theorem renderPieces_plain (pieces : List RowPiece) :
    Linger.Core.Listing.renderPieces false pieces =
      Linger.Core.Render.utf8s (pieces.flatMap (·.text)) := by
  induction pieces with
  | nil => rfl
  | cons piece pieces ih =>
    cases hs : piece.status <;>
      simp_all [renderPieces, Linger.Core.Render.utf8s, List.flatMap_append]

/-- Plain terminal output and the human API coincide for all metadata. -/
theorem terminalListing_plain (rows : List (List (String × String))) :
    Linger.Core.Listing.terminalListing false rows = Linger.Core.Listing.humanListing rows := by
  simp [terminalListing, humanListing, renderPieces_plain, humanRow]

end Linger.Core.Listing
