module

public import Theorems.Render.Sticky
import all Linger.Core.Render
import all Linger.Core.Vt
import all Theorems.Render.Sticky

-- No `public section`: a **public** declaration's type may not mention a private
-- field, and `Vt`'s are private now (the seal, `specs/archive/vt-toolkit.md` Step 1).
-- Module-private is the default, so consumers reach in with `import all`. See the
-- longer note in `Theorems/Vt.lean`.

/-! # §Row integrity for `linger history` — a cell cannot inject a line break

`history`'s framing: every byte is a line terminator or printable content, and the
newline count is the row count, so a cell's contents cannot forge a line. Split out
of `Theorems/Render.lean`. -/

namespace Linger.Core.Render

open Linger.Core.Vt

/-! ## §Row integrity for `linger history` — a cell cannot inject a line break

The last of the runtime's byte streams to acquire a theorem, and the reason it was last
is recorded in `E2E/Coverage.lean` (ported from the retired `tests/coverage.py`): `history` was assembled through `String`, and a
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
theorem rowChars_scrubbed (row : Row) : ∀ c ∈ rowChars row, 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F := by
  unfold rowChars
  rw [← Array.foldl_toList]
  refine
    invariant_foldl (fun acc : List Char => ∀ c ∈ acc, 0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F) _ ?_
      row.toList []
      (by
        intro c hc; simp at hc)
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
theorem dropTrailingBlanks_subset (cs : List Char) : ∀ c ∈ dropTrailingBlanks cs, c ∈ cs := by
  intro c hc
  unfold dropTrailingBlanks at hc
  rw [List.mem_reverse] at hc
  exact List.mem_reverse.mp ((List.dropWhile_sublist _).mem hc)

theorem rowText_scrubbed (row : Row) : ∀ b ∈ rowText row, 0x20 ≤ b ∧ b ≠ 0x7F := utf8s_no_ctl _

theorem rowText_no_lf (row : Row) : ∀ b ∈ rowText row, b ≠ 0x0A := by
  intro b hb
  obtain ⟨hge, -⟩ := rowText_scrubbed row b hb
  intro he
  rw [he] at hge
  exact absurd hge (by decide)

/-- **Every byte is a line terminator or printable content.** -/
theorem history_framing (v : Vt) : ∀ b ∈ history v, b = 0x0A ∨ (0x20 ≤ b ∧ b ≠ 0x7F) := by
  intro b hb
  unfold history at hb
  simp only [List.mem_flatMap] at hb
  obtain ⟨row, -, hmem⟩ := hb
  rcases List.mem_append.mp hmem with h | h
  · exact Or.inr (rowText_scrubbed row b h)
  · simp only [List.mem_singleton] at h
    exact Or.inl h

private theorem count_rows :
    ∀ (rows : List Row), (rows.flatMap (fun row => rowText row ++ [0x0A])).count 0x0A = rows.length
  | [] => rfl
  | row :: t => by
    rw [List.flatMap_cons, List.count_append, count_rows t, List.count_append,
      List.count_eq_zero.mpr (fun hmem => rowText_no_lf row 0x0A hmem rfl)]
    simp
    omega

/-- **One line per row, structurally.** A cell cannot forge a line: the newline count is
the row count, whatever the session's program wrote into the grid. -/
theorem history_lines (v : Vt) :
    (history v).count 0x0A = (v.sb.toList ++ v.grid.toList).length := by
  unfold history
  exact count_rows _

/-! ## The same two claims for `screenText` (`linger capture`)

Same emitter shape as `history`'s plain branch — `rowText`-per-row over the
grid alone — so the anti-forgery pair transfers verbatim. `screenText_lines` is
what makes a capture *positionally* parseable by an agent that read `rows` from
`info`: exactly one line per grid row, so line k of the capture IS row k of the
screen, whatever the session's program printed. -/

/-- **Every byte is a line terminator or printable content.** -/
theorem screenText_framing (v : Vt) : ∀ b ∈ screenText v, b = 0x0A ∨ (0x20 ≤ b ∧ b ≠ 0x7F) := by
  intro b hb
  unfold screenText at hb
  simp only [List.mem_flatMap] at hb
  obtain ⟨row, -, hmem⟩ := hb
  rcases List.mem_append.mp hmem with h | h
  · exact Or.inr (rowText_scrubbed row b h)
  · simp only [List.mem_singleton] at h
    exact Or.inl h

/-- **One line per grid row, and only the grid** — the scrollback ring
contributes nothing, which is the whole difference from `history`. -/
theorem screenText_lines (v : Vt) : (screenText v).count 0x0A = v.grid.toList.length := by
  unfold screenText
  exact count_rows _

/-! ## The parse contract — line k IS row k

`screenText_framing` + `screenText_lines` say the right *number* of clean
lines; neither says which bytes land on which line. `linesLF` is the
consumer's splitter as a specification, and these say splitting the stream
gives back exactly the rows' texts, in order — the claim an agent's positional
parser actually relies on. (A reversed-row emitter passes both count and
framing; only this catches it.) -/

/-- One LF-terminated record peels off `linesLF` whole, whatever follows —
provided the record itself is LF-free, which `rowText_no_lf` supplies for
every row. -/
theorem linesLF_record (x rest : Bytes) (hx : ∀ b ∈ x, b ≠ 0x0A) :
    linesLF (x ++ 0x0A :: rest) = x :: linesLF rest := by
  induction x with
  | nil => simp [linesLF]
  | cons b x
    ih =>
    have hb : (b == 0x0A) = false := beq_eq_false_iff_ne.mpr (hx b (List.mem_cons_self ..))
    rw [List.cons_append, linesLF, ite_eq_right (by simp [hb]),
      ih (fun b' hb' => hx b' (List.mem_cons_of_mem _ hb'))]

private theorem linesLF_rows (rows : List Row) :
    linesLF (rows.flatMap (fun row => rowText row ++ [0x0A])) = rows.map rowText := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons, List.map_cons, List.append_assoc, List.singleton_append,
      linesLF_record _ _ (fun b hb => rowText_no_lf r b hb), ih]

/-- **The capture parse contract.** Splitting a capture on `0x0A` yields the
grid, row for row: line k IS `rowText` of row k. This is what licenses an
agent to parse a capture positionally with `rows` from `info`. -/
theorem screenText_records (v : Vt) :
    linesLF (screenText v) = v.grid.toList.map rowText := linesLF_rows _

/-- The same contract for `history`: the transcript parses as scrollback rows
then screen rows, in order. -/
theorem history_records (v : Vt) :
    linesLF (history v) = (v.sb.toList ++ v.grid.toList).map rowText := by
  unfold history
  exact linesLF_rows _

/-- And the two streams agree byte-for-byte on the part they share: a capture
is exactly the tail of the transcript — same renderer, same trimming, same
framing — so an agent may mix the two verbs without normalizing anything. -/
theorem history_screenText_suffix (v : Vt) :
    history v = v.sb.toList.flatMap (fun row => rowText row ++ [0x0A]) ++ screenText v := by
  unfold history screenText
  rw [List.flatMap_append]

/-- `safeChar` is the identity on a character a cell is allowed to hold. The emit-side
guard and the store-side one agree, which is what lets a repaint reproduce a stored
cell — `printableChar` on store, `safeChar` on emit, both `Emittable`'s range. -/
theorem safeChar_of_emittable {c : Char} (h : Emittable c) : safeChar c = c := by
  unfold safeChar
  rw [ite_eq_right
      (by
        simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq]
        obtain ⟨h20, h7⟩ := h
        omega)]

end Linger.Core.Render
