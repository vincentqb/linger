module

public import Linger.Selector.CoreCode.Picker
public import Linger.Display.CoreSpec
public import Terminal.CoreSpec
public import Terminal.CoreCode.Render
import all Linger.Selector.Proofs.Picker
import all Linger.Selector.CoreCode.Picker
import Linger.Display.Proofs.Clean
import Input.Proofs
import all Terminal.CoreCode.Render
import all Terminal.CoreCode.Vt
-- The proof layer is module-private, so `safeChar_eq_self` arrives through `import all`.
import all Terminal.Proofs.Render

public section

/-! # The selector's frame is clean

What the selector writes is made of the pieces `Display.Clean` lists: its frame (an SGR reset,
the cursor home, then rows of printable characters in SGR pens joined by CR LF), each row's own
paint, an update (cursor moves and rows' paints) and the sequences that take and give back the
terminal. A row is the cells `lineCells` builds from a frame line, each `Fit`: a printable base
and marks, its width the base's, and marks only on a narrow cell, so a row's paint never parks
the cursor between a wide glyph and its shadow. The cells also come in whole pairs (`Paired`), a
wide glyph followed by its shadow, which the repaint proofs read (`Linger.Selector.Proofs.Repaint`).
-/

namespace Linger.Selector.Picker

open Linger.Display
open Terminal.Vt (Cell Pen charWidth)

/-- A cell as the picker builds it: a printable base whose width is the cell's unless the cell
is a shadow, at most eight printable marks of width zero, and marks only on a narrow cell. -/
def Fit (c : Cell) : Prop :=
  Printable c.base ∧
    (∀ m ∈ c.marks, Printable m ∧ charWidth m = 0) ∧
    c.marks.length ≤ 8 ∧ (c.width ≠ 0 → charWidth c.base = c.width) ∧ (c.width ≠ 1 → c.marks = [])

/-- Cells in whole pairs: each narrow, or wide and followed by its shadow, a blank in its pen. -/
inductive Paired : List Cell → Prop where
  /-- No cells. -/
  | nil : Paired []
  /-- A narrow cell, then paired cells. -/
  | narrow {c : Cell} {l : List Cell} (h : c.width = 1) (rest : Paired l) : Paired (c :: l)
  /-- A wide cell and its shadow, then paired cells. -/
  |
  wide {c : Cell} {l : List Cell} (h : c.width = 2) (rest : Paired l) :
    Paired (c :: { base := ' ', marks := [], width := 0, pen := c.pen } :: l)

/-- Cells in whole pairs, last first, as `lineCells` holds them. -/
private inductive RPaired : List Cell → Prop where
  | nil : RPaired []
  | narrow {c : Cell} {l : List Cell} (h : c.width = 1) (rest : RPaired l) : RPaired (c :: l)
  |
  wide {c : Cell} {l : List Cell} (h : c.width = 2) (rest : RPaired l) :
    RPaired ({ base := ' ', marks := [], width := 0, pen := c.pen } :: c :: l)

private theorem rPaired_reverse {r : List Cell} (h : RPaired r) :
    ∀ {l : List Cell}, Paired l → Paired (r.reverse ++ l) := by
  induction h with
  | nil =>
    intro l hl; simpa using hl
  | narrow hw _ ih =>
    intro l hl
    simpa using ih (Paired.narrow hw hl)
  | wide hw _ ih =>
    intro l hl
    simpa using ih (Paired.wide hw hl)

private theorem frameChar_printable (raw : Char) : Printable (frameChar raw) := by
  unfold frameChar
  split
  · exact printable_of_bounds ((Input.printable_iff raw).mp ‹_›)
  · simp only [Printable]
    decide

private theorem charWidth_cases (c : Char) :
    charWidth c = 0 ∨ charWidth c = 1 ∨ charWidth c = 2 := by
  unfold charWidth
  split
  · exact .inl rfl
  · split
    · exact .inr (.inr rfl)
    · exact .inr (.inl rfl)

private theorem fit_blank : Fit ({} : Cell) :=
  ⟨by
    simp only [Printable]; decide, by simp, by simp, fun _ => by decide, fun h => absurd rfl h⟩

/-- What `lineCells` keeps: cells last first, in whole pairs, each `Fit`, as many as the
columns used, which stay within the width. -/
private structure Built (width used : Nat) (cells : List Cell) : Prop where
  paired : RPaired cells
  fit : ∀ c ∈ cells, Fit c
  length : cells.length = used
  within : used ≤ width

private theorem lineCells_built (width : Nat) :
    ∀ (input : List (Char × Pen)) (used : Nat) (cells : List Cell),
      Built width used cells → ∃ n, Built width n (lineCells width used cells input) := by
  intro input
  induction input with
  | nil =>
    intro used cells h; exact ⟨used, by simpa [lineCells] using h⟩
  | cons head rest ih =>
    obtain ⟨raw, pen⟩ := head
    intro used cells h
    unfold lineCells
    have hp := frameChar_printable raw
    by_cases h0 : charWidth (frameChar raw) = 0
    · rw [ite_eq_left (by simpa using h0)]
      split
      · rename_i last before
        split
        · rename_i hcond
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
          apply ih used
          obtain ⟨paired, fit, length, within⟩ := h
          refine ⟨?_, ?_, by simpa using length, within⟩
          · cases paired with
            | narrow hw rest => exact RPaired.narrow hw rest
            | wide hw rest => simp at hcond
          · intro c hc
            simp only [List.mem_cons] at hc
            rcases hc with rfl | hc
            · obtain ⟨b, m, l, w, n⟩ := fit last (by simp)
              refine
                ⟨b, fun x hx => ?_, by
                  simp; omega, w, fun hne => absurd hcond.1 hne⟩
              simp only [List.mem_append, List.mem_singleton] at hx
              rcases hx with hx | rfl
              · exact m x hx
              · exact ⟨hp, h0⟩
            · exact fit c (by simp [hc])
        · exact ih used _ h
      · exact ih used _ h
    · rw [ite_eq_right (by simpa using h0)]
      split
      · exact ⟨used, h⟩
      · rename_i hfit
        simp only [gt_iff_lt, Nat.not_lt] at hfit
        split
        · rename_i h2
          have h2 : charWidth (frameChar raw) = 2 := by simpa using h2
          apply ih (used + 2)
          obtain ⟨paired, fit, length, within⟩ := h
          refine
            ⟨RPaired.wide (c := { base := frameChar raw, width := 2, pen }) rfl paired, ?_, by
              simp [length], by omega⟩
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | rfl | hc
          · exact
              ⟨by
                simp only [Printable]; decide, by simp, by simp, fun h => absurd rfl h, fun _ =>
                rfl⟩
          · exact ⟨hp, by simp, by simp, fun _ => h2, fun _ => rfl⟩
          · exact fit c hc
        · rename_i h2
          have h1 : charWidth (frameChar raw) = 1 := by
            rcases charWidth_cases (frameChar raw) with h | h | h
            · exact absurd h h0
            · exact h
            · simp [h] at h2
          apply ih (used + 1)
          obtain ⟨paired, fit, length, within⟩ := h
          refine
            ⟨RPaired.narrow (c := { base := frameChar raw, pen }) rfl paired, ?_, by simp [length],
              by omega⟩
          intro c hc
          simp only [List.mem_cons] at hc
          rcases hc with rfl | hc
          · exact ⟨hp, by simp, by simp, fun _ => h1, fun h => absurd rfl h⟩
          · exact fit c hc

/-- A frame line's row: as wide as the terminal, its cells in whole pairs, each `Fit`. -/
private theorem lineRow_ok (cols : Nat) (line : List (String × List (List Nat))) :
    (lineRow cols line).size = cols ∧
      Paired (lineRow cols line).toList ∧ ∀ c ∈ (lineRow cols line).toList, Fit c := by
  obtain ⟨n, ⟨paired, fit, length, within⟩⟩ :=
    lineCells_built (cols - 1)
      (line.flatMap fun run => run.1.toList.map fun char => (char, stylePen run.2)) 0 []
      ⟨RPaired.nil, by simp, rfl, Nat.zero_le _⟩
  have blanks : ∀ k, Paired (List.replicate k ({} : Cell)) := by
    intro k
    induction k with
    | zero => exact Paired.nil
    | succ k ih => exact Paired.narrow rfl ih
  simp only [lineRow, List.size_toArray, List.length_append, List.length_reverse,
    List.length_replicate, List.toList_toArray]
  refine ⟨by omega, rPaired_reverse paired (blanks _), fun c hc => ?_⟩
  simp only [List.mem_append, List.mem_reverse, List.mem_replicate] at hc
  rcases hc with hc | ⟨_, rfl⟩
  · exact fit c hc
  · exact fit_blank

/-- A frame shows one row for each of the terminal's, at least one. -/
private theorem picture_length (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) :
    (picture state snapshot statusOf loaded withColor savedTmux remoteAge cols rows).length =
      max 1 rows := by
  have := frameLines_length state snapshot statusOf loaded withColor savedTmux remoteAge rows
  simp only [picture, List.length_map, List.length_append, List.length_replicate]
  omega

private theorem fit_printable {c : Cell} (h : Fit c) : Printable c.base := h.1

private theorem safe_printable {c : Char} (h : Printable c) : Terminal.Render.safeChar c = c := by
  simp only [Printable] at h
  exact Terminal.Render.safeChar_eq_self (by omega) (by omega)

private theorem clean_utf8 {c : Char} (h : Printable c) :
    Clean (Terminal.Render.utf8 (Terminal.Render.safeChar c)) := by
  rw [safe_printable h, Terminal.Render.utf8_eq_utf8EncodeChar]
  exact clean_piece (p := .text c) h

private theorem joinSemi_eq :
    ∀ codes : List Nat,
      Terminal.Render.joinSemi codes = ((codes.map digits).intersperse [0x3B]).flatten
  | [] => rfl
  | [n] => by simp [Terminal.Render.joinSemi, render_digits]
  | n :: m :: rest => by
    rw [Terminal.Render.joinSemi.eq_3 n (m :: rest) (by simp), joinSemi_eq (m :: rest)]
    simp [render_digits, List.intersperse_cons_cons]

private theorem clean_sgrOf (codes : List Nat) : Clean (Terminal.Render.sgrOf codes) := by
  have : Terminal.Render.sgrOf codes = (Piece.csi false codes 0x6D).bytes := by
    simp [Terminal.Render.sgrOf, Terminal.Render.csiB, Piece.bytes, joinSemi_eq]
  rw [this]
  exact clean_piece (by simp [Piece.Ok])

private theorem clean_sgrColorSeq (c : Terminal.Vt.Color) (isFg : Bool) :
    Clean (Terminal.Render.sgrColorSeq c isFg) := by
  unfold Terminal.Render.sgrColorSeq
  split
  · exact clean_nil
  · exact clean_sgrOf _

private theorem clean_penSgr (p : Pen) : Clean (Terminal.Render.penSgr p) :=
  clean_append (clean_append (clean_sgrOf _) (clean_sgrColorSeq _ _)) (clean_sgrColorSeq _ _)

private theorem clean_rowSlot (acc : List UInt8 × Pen × Nat) (c : Cell) (hacc : Clean acc.1)
    (hc : Fit c) : Clean (Terminal.Render.rowSlot acc c).1 := by
  obtain ⟨s, pen, x⟩ := acc
  obtain ⟨hb, hm, -, -, hw⟩ := hc
  have marks : Clean (Terminal.Render.utf8s c.marks) := clean_utf8s fun m h => (hm m h).1
  unfold Terminal.Render.rowSlot
  dsimp only
  split
  · exact clean_append hacc marks
  · rename_i h0
    have body : Clean (Terminal.Render.cellText c) := clean_append (clean_utf8 hb) marks
    refine clean_append ?_ ?_
    · split
      · exact hacc
      · exact clean_append hacc (clean_penSgr _)
    · split
      · rename_i h2
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff] at h2
        exact absurd (hw (by omega)) h2.2
      · exact body

/-- A row's paint is clean when its cells are `Fit`. -/
theorem clean_rowAnsi (row : Terminal.Vt.Row) (pen : Pen) (h : ∀ c ∈ row.toList, Fit c) :
    Clean (Terminal.Render.rowAnsi row pen).1 := by
  have key :
    ∀ (cells : List Cell) (acc : List UInt8 × Pen × Nat),
      Clean acc.1 → (∀ c ∈ cells, Fit c) → Clean (cells.foldl Terminal.Render.rowSlot acc).1 := by
    intro cells
    induction cells with
    | nil =>
      intro acc hacc _; exact hacc
    | cons c rest ih =>
      intro acc hacc hcells
      exact ih _ (clean_rowSlot acc c hacc (hcells c (by simp))) fun d hd => hcells d (by simp [hd])
  simp only [Terminal.Render.rowAnsi, ← Array.foldl_toList]
  exact key row.toList _ clean_nil h

private theorem threadRows_mem :
    ∀ (rows : List Terminal.Vt.Row) (pen : Pen),
      ∀ x ∈ threadRows rows pen, ∃ row ∈ rows, ∃ q, x = (Terminal.Render.rowAnsi row q).1
  | [], _, x, hx => by simp [threadRows] at hx
  | row :: rest, pen, x, hx => by
    simp only [threadRows, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨row, by simp, pen, rfl⟩
    · obtain ⟨r, hr, q, rfl⟩ := threadRows_mem rest _ x hx
      exact ⟨r, by simp [hr], q, rfl⟩

private theorem picture_fit (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) :
    ∀ row ∈ picture state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
      ∀ c ∈ row.toList, Fit c := by
  intro row hrow
  simp only [picture, List.mem_map] at hrow
  obtain ⟨line, -, rfl⟩ := hrow
  exact (lineRow_ok cols line).2.2

/-- The selector's frame is clean, whatever it shows. -/
theorem frame_clean (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) :
    Clean (frame state snapshot statusOf loaded withColor savedTmux remoteAge cols rows) := by
  unfold frame
  rw [csiPlain_bytes, csiNum_bytes]
  refine
    clean_append
      (clean_append (clean_piece (by simp [Piece.Ok])) (clean_piece (by simp [Piece.Ok])))
      (clean_intersperse clean_crlf fun bytes hbytes => ?_)
  obtain ⟨row, hrow, q, rfl⟩ := threadRows_mem _ _ bytes hbytes
  exact
    clean_rowAnsi row q
      (picture_fit state snapshot statusOf loaded withColor savedTmux remoteAge cols rows row hrow)

/-- Each row of the selector's frame, painted on its own, is clean. -/
theorem frameRows_clean (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (remoteAge : Option Nat) (cols rows : Nat) :
    ∀ row ∈ frameRows state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
      Clean row := by
  intro bytes hbytes
  simp only [frameRows, List.mem_map] at hbytes
  obtain ⟨row, hrow, rfl⟩ := hbytes
  rw [csiNum_bytes]
  exact
    clean_append (clean_piece (by simp [Piece.Ok]))
      (clean_rowAnsi row {}
        (picture_fit state snapshot statusOf loaded withColor savedTmux remoteAge cols rows row
          hrow))

/-- `CSI row ; col H`, as the renderer writes it, is the spec's piece. -/
theorem csiNum2_bytes (a b : Nat) (final : UInt8) :
    Terminal.Render.csiNum2 a b final = (Piece.csi false [a, b] final).bytes := by
  simp [Terminal.Render.csiNum2, Terminal.Render.csiB, Piece.bytes, render_digits]

/-- An update between frames whose rows are clean is clean: cursor moves and those rows. -/
theorem update_clean (before after : List (List UInt8)) (h : ∀ row ∈ after, Clean row) :
    Clean (update before after) := by
  suffices
    ∀ (after : List (List UInt8)) (y : Nat) (before : List (List UInt8)),
      (∀ row ∈ after, Clean row) → Clean (updateFrom y before after)
    from this after 0 before h
  intro after
  induction after with
  | nil =>
    intro y before _; exact clean_nil
  | cons row rest ih =>
    intro y before hrows
    simp only [updateFrom]
    refine clean_append ?_ (ih _ _ fun r hr => hrows r (by simp [hr]))
    split
    · exact clean_nil
    · rw [csiNum2_bytes]
      exact clean_append (clean_piece (by simp [Piece.Ok])) (hrows row (by simp))

/-- What the selector writes when it takes the terminal is clean. -/
theorem enterAnsi_clean : Clean enterAnsi := by
  unfold enterAnsi
  exact
    clean_append (clean_append (clean_modeSet _ _ (by decide)) (clean_modeSet _ _ (by decide)))
      (clean_modeSet _ _ (by decide))

/-- What the selector writes when it gives the terminal back is clean. -/
theorem exitAnsi_clean : Clean exitAnsi := by
  unfold exitAnsi
  exact
    clean_append
      (clean_append (clean_append (clean_sgr _) (clean_modeSet _ _ (by decide)))
        (clean_modeSet _ _ (by decide)))
      (clean_modeSet _ _ (by decide))

end Linger.Selector.Picker
