import Theorems.Render.Sticky
/-! # §Row integrity for `linger history` — a cell cannot inject a line break

`history`'s framing: every byte is a line terminator or printable content, and the
newline count is the row count, so a cell's contents cannot forge a line. Split out
of `Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## §Row integrity for `linger history` — a cell cannot inject a line break

The last of the runtime's byte streams to acquire a theorem, and the reason it was last
is recorded in `tests/coverage.py`: `history` was assembled through `String`, and a
`String` does not reduce in the kernel, so nothing could be said about the bytes it
writes to a terminal. `rowText` now builds `List UInt8` (the same restructure
`Session.infoText` needed), which makes both claims below available.

They matter for the same reason `infoText`'s do. `linger history` is line-oriented
output that a caller may parse, and a *cell* is attacker-influenced — a program running
in the session writes whatever it likes into the grid. `Render.safeChar` maps a C0
control to U+FFFD on the way out, so a cell holding a newline cannot forge a line, and
the line count is exactly the row count. -/

/-- The scrubbing happens at the **fold**, not only at the encoder. Worth proving
separately: `rowText_scrubbed` below is true even without this, because `utf8s` scrubs
again on the way out — so without it the claim would rest on a single guard, and this
says the grid never hands a control codepoint to the encoder in the first place. -/
theorem rowChars_scrubbed (row : Row) :
    ∀ c ∈ rowChars row, 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F := by
  unfold rowChars
  rw [← Array.foldl_toList]
  refine invariant_foldl
    (fun acc : List Char => ∀ c ∈ acc, 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F) _ ?_
    row.toList [] (by intro c hc; simp at hc)
  intro acc cell hacc
  split
  · exact hacc
  · intro c hc
    rcases List.mem_append.mp hc with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact hacc c h'
      · simp only [List.mem_singleton] at h'
        subst h'
        exact safeChar_ge cell.base
    · obtain ⟨m, -, hm⟩ := List.mem_map.mp h
      subst hm
      exact safeChar_ge m

/-- Trimming only drops, so it cannot introduce a character the fold excluded. -/
theorem dropTrailingBlanks_subset (cs : List Char) :
    ∀ c ∈ dropTrailingBlanks cs, c ∈ cs := by
  intro c hc
  unfold dropTrailingBlanks at hc
  rw [List.mem_reverse] at hc
  exact List.mem_reverse.mp ((List.dropWhile_sublist _).mem hc)

theorem rowText_scrubbed (row : Row) : ∀ b ∈ rowText row, 0x20 ≤ b ∧ b ≠ 0x7F :=
  utf8s_no_ctl _

theorem rowText_no_lf (row : Row) : ∀ b ∈ rowText row, b ≠ 0x0A := by
  intro b hb
  obtain ⟨hge, -⟩ := rowText_scrubbed row b hb
  intro he
  rw [he] at hge
  exact absurd hge (by decide)

/-- **Every byte is a line terminator or printable content.** -/
theorem history_framing (v : Vt) :
    ∀ b ∈ history v false, b = 0x0A ∨ (0x20 ≤ b ∧ b ≠ 0x7F) := by
  intro b hb
  unfold history at hb
  rw [if_neg (by decide)] at hb
  simp only [List.mem_flatMap] at hb
  obtain ⟨row, -, hmem⟩ := hb
  rcases List.mem_append.mp hmem with h | h
  · exact Or.inr (rowText_scrubbed row b h)
  · simp only [List.mem_singleton] at h
    exact Or.inl h

private theorem count_rows : ∀ (rows : List Row),
    (rows.flatMap (fun row => rowText row ++ [0x0A])).count 0x0A = rows.length
  | [] => rfl
  | row :: t => by
    rw [List.flatMap_cons, List.count_append, count_rows t, List.count_append,
      List.count_eq_zero.mpr (fun hmem => rowText_no_lf row 0x0A hmem rfl)]
    simp
    omega

/-- **One line per row, structurally.** A cell cannot forge a line: the newline count is
the row count, whatever the session's program wrote into the grid. -/
theorem history_lines (v : Vt) :
    (history v false).count 0x0A = (v.sb.toList ++ v.grid.toList).length := by
  unfold history
  rw [if_neg (by decide)]
  exact count_rows _


/-- `safeChar` is the identity on a character a cell is allowed to hold. The emit-side
guard and the store-side one agree, which is what lets a repaint reproduce a stored
cell — `printableChar` on store, `safeChar` on emit, both `Emittable`'s range. -/
theorem safeChar_of_emittable {c : Char} (h : Emittable c) : safeChar c = c := by
  unfold safeChar
  rw [if_neg (by
    simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
    obtain ⟨h20, h7⟩ := h
    omega)]


end Linger.Core.Render
