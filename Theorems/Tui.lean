import Zmx.Core.Tui
import Theorems.Name
import Theorems.Remote
/-! # §Bound(tui) — the picker cannot escape its own list

Small but load-bearing: the selection index stays inside the filtered
match list (or 0 when it's empty) after ANY event, and the query never
grows past `maxQuery`. The renderer indexes with `[·]?` everywhere, so
these bounds are about correct behavior (highlight follows a real row),
not crash-safety — §Total is by construction here.
-/

namespace Zmx.Core.Tui

/-- The invariant: selection is clamped to the matches, query capped. -/
structure Ok (st : State) : Prop where
  selLt : st.sel = 0 ∨ st.sel < st.matches.length
  queryLe : st.query.length ≤ maxQuery

theorem ok_init : Ok ({} : State) := ⟨Or.inl rfl, by simp [maxQuery]⟩

theorem clampSel_ok (st : State) (hq : st.query.length ≤ maxQuery) :
    Ok st.clampSel := by
  constructor
  · show st.clampSel.sel = 0 ∨ st.clampSel.sel < st.clampSel.matches.length
    have hm : st.clampSel.matches = st.matches := rfl
    rw [hm]
    unfold State.clampSel
    dsimp only
    by_cases h : st.matches.length == 0
    · left
      simp [h]
    · right
      have hne : st.matches.length ≠ 0 := by simpa using h
      simp only [h, Bool.false_eq_true, if_false]
      omega
  · exact hq

/-- §Bound(tui): every event lands in an Ok state. (The `matches` list
is recomputed from rows+query, so `sel`'s bound is against the *new*
matches — the subtle case is rows/query changing under a high sel,
which `clampSel` re-establishes.) -/
theorem step_ok (st : State) (ev : Event) (h : Ok st) : Ok (step st ev).1 := by
  obtain ⟨hsel, hq⟩ := h
  unfold step
  match ev with
  | .rowsUpdated rows =>
    dsimp only
    exact clampSel_ok _ hq
  | .previewUpdated name host lines =>
    dsimp only
    split
    · exact ⟨hsel, hq⟩
    · exact ⟨hsel, hq⟩
  | .resized c r => exact ⟨hsel, hq⟩
  | .key k =>
    dsimp only
    match k with
    | .esc | .ctrlC | .ctrlQ => exact ⟨hsel, hq⟩
    | .up | .ctrlP | .ctrlK => exact clampSel_ok _ hq
    | .down | .ctrlN | .ctrlJ => exact clampSel_ok _ hq
    | .char c =>
      dsimp only
      split
      · exact ⟨hsel, hq⟩
      · refine clampSel_ok _ ?_
        rename_i hlt
        simp only [String.length_push]
        omega
    | .backspace =>
      refine clampSel_ok _ ?_
      simp only [String.length_ofList, List.length_dropLast, String.length_toList]
      omega
    | .enter =>
      dsimp only
      split
      · exact ⟨hsel, hq⟩
      · split
        · exact ⟨hsel, hq⟩
        · exact ⟨hsel, hq⟩
    | .ctrlX =>
      dsimp only
      split
      · exact ⟨hsel, hq⟩
      · split
        · exact ⟨hsel, hq⟩
        · exact ⟨hsel, hq⟩
    | .ctrlR => exact ⟨hsel, hq⟩
    | .other => exact ⟨hsel, hq⟩

end Zmx.Core.Tui


namespace Zmx.Core.Tui
/-! ## §Row — a row's identity comes from the socket, not from the peer

A session's row is built from two sources: its socket filename (which
the local filesystem guarantees) and its `info` reply (which the daemon
supplies, and may be late, truncated, or nonsense — a daemon busy with
a burst of pty output can miss the reply window entirely).

§Row: the name is a function of the filename **alone**. Consequences:
a busy daemon still lists under its real name rather than as a blank
row; a confused or hostile daemon cannot rename itself, blank itself,
or claim another session's identity; and since this row set is also
what `list --porcelain` prints for remote machines to parse, identity
never becomes peer-supplied data downstream.
-/

open Zmx.Core.Name (Valid sanitize sanitize_valid)

/-- The reply cannot influence the name: any two replies give the same
identity for the same socket. -/
theorem rowOfInfo_name_independent (n : String) (kvs kvs' : List (String × String))
    (h h' : Host) : (rowOfInfo n kvs h).name = (rowOfInfo n kvs' h').name := rfl

/-- The name is exactly the sanitized socket name. -/
theorem rowOfInfo_name (n : String) (kvs : List (String × String)) (h : Host) :
    (rowOfInfo n kvs h).name = sanitize n := rfl

/-- So it is always §Name-valid: nonempty, bounded, no separators — in
particular a silent daemon can never produce an empty row. -/
theorem rowOfInfo_name_valid (n : String) (kvs : List (String × String)) (h : Host) :
    Valid (rowOfInfo n kvs h).name := by
  rw [rowOfInfo_name]
  exact sanitize_valid n

/-- Display fields taken from the reply are scrubbed of control bytes,
so a reply cannot inject escape sequences into the rendered frame
(the local mirror of §Remote's guarantee). -/
theorem rowOfInfo_cmd_scrubbed (n : String) (kvs : List (String × String)) (h : Host) :
    ∀ c ∈ (rowOfInfo n kvs h).cmd.toList, c.toNat ≥ 0x20 ∧ c.toNat ≠ 0x7F :=
  Zmx.Core.Remote.scrub_no_ctl _

theorem rowOfInfo_pid_scrubbed (n : String) (kvs : List (String × String)) (h : Host) :
    ∀ c ∈ (rowOfInfo n kvs h).pid.toList, c.toNat ≥ 0x20 ∧ c.toNat ≠ 0x7F :=
  Zmx.Core.Remote.scrub_no_ctl _

end Zmx.Core.Tui
