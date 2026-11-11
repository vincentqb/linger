module

public import Linger.Display.Spec
public import Linger.Display.Listing
public import Terminal.Render
public import Terminal.Title
import all Linger.Display.Listing
import all Terminal.Title
-- The proof layer is module-private, so `utf8_eq_utf8EncodeChar` arrives through `import all`.
import all Terminal.Proofs.Render
import Terminal.Proofs.Title
import all Linger.Display.Proofs.Listing
import Terminal.Solution

public section

/-! # Clean terminal: what linger writes on its own account

`Clean` bytes are pieces linger may write (`Linger.Display.Spec`): printable text, line breaks,
tabs, and a short list of control sequences. Clean bytes join into clean bytes; the renderer's
sequences are pieces; the listing, the window titles, the capture text and the handback are
clean. -/

namespace Linger.Display

theorem clean_nil : Clean [] := ⟨[], by simp, rfl⟩

theorem clean_append {a b : List UInt8} (ha : Clean a) (hb : Clean b) : Clean (a ++ b) := by
  obtain ⟨ps, hps, rfl⟩ := ha
  obtain ⟨qs, hqs, rfl⟩ := hb
  refine ⟨ps ++ qs, fun p hp => ?_, by simp⟩
  rcases List.mem_append.mp hp with h | h
  · exact hps p h
  · exact hqs p h

theorem clean_flatten {xs : List (List UInt8)} (h : ∀ x ∈ xs, Clean x) : Clean xs.flatten := by
  induction xs with
  | nil => exact clean_nil
  | cons x xs ih =>
    rw [List.flatten_cons]
    exact clean_append (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem clean_flatMap {α : Type} {xs : List α} {f : α → List UInt8} (h : ∀ x ∈ xs, Clean (f x)) :
    Clean (xs.flatMap f) := by
  induction xs with
  | nil => exact clean_nil
  | cons x xs ih =>
    rw [List.flatMap_cons]
    exact clean_append (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- Lines joined by a clean separator are clean. -/
theorem clean_intersperse {sep : List UInt8} {xs : List (List UInt8)} (hs : Clean sep)
    (h : ∀ x ∈ xs, Clean x) : Clean (xs.intersperse sep).flatten := by
  induction xs with
  | nil => exact clean_nil
  | cons x xs ih =>
    cases xs with
    | nil => simpa using h x (by simp)
    | cons y ys =>
      rw [List.intersperse_cons_cons, List.flatten_cons, List.flatten_cons]
      refine clean_append (h x (by simp)) (clean_append hs ?_)
      exact ih fun z hz => h z (by simp_all)

theorem clean_piece {p : Piece} (h : p.Ok) : Clean p.bytes := ⟨[p], by simpa using h, by simp⟩

/-- The renderer's decimal digits are the spec's. -/
theorem render_digits (n : Nat) : Terminal.Render.digits n = digits n := by
  suffices ∀ k, ∀ n < k, Terminal.Render.digits n = digits n from this (n + 1) n (by omega)
  intro k
  induction k with
  | zero =>
    intro n h
    omega
  | succ k ih =>
    intro n hn
    rw [Terminal.Render.digits, digits]
    split
    · rfl
    · rw [ih (n / 10) (by omega)]

/-- A style's sequence is the spec's SGR piece. -/
theorem sgr_bytes (params : List Nat) :
    Listing.sgr params = (Piece.csi false params 0x6D).bytes := by
  simp [Listing.sgr, Piece.bytes, Terminal.Render.csiB, funext render_digits]

/-- `CSI n final`, as the renderer writes it, is the spec's piece. -/
theorem csiNum_bytes (n : Nat) (final : UInt8) :
    Terminal.Render.csiNum n final = (Piece.csi false [n] final).bytes := by
  simp [Terminal.Render.csiNum, Terminal.Render.csiB, Piece.bytes, render_digits]

/-- `CSI final`, as the renderer writes it, is the spec's piece. -/
theorem csiPlain_bytes (final : UInt8) :
    Terminal.Render.csiPlain final = (Piece.csi false [] final).bytes := by
  simp [Terminal.Render.csiPlain, Terminal.Render.csiB, Piece.bytes]

/-- A DEC private mode set or reset, as the renderer writes it, is the spec's piece. -/
theorem modeSet_bytes (n : Nat) (on : Bool) :
    Terminal.Render.modeSet n on = (Piece.csi true [n] (if on then 0x68 else 0x6C)).bytes := by
  simp [Terminal.Render.modeSet, Terminal.Render.csiPriv, Terminal.Render.csiB, Piece.bytes,
    render_digits]

theorem clean_sgr (params : List Nat) : Clean (Listing.sgr params) := by
  rw [sgr_bytes]
  exact clean_piece (by simp [Piece.Ok])

/-- Resetting any DEC private mode is clean, and so is setting mode 7, 25, 1049 or 2004. -/
theorem clean_modeSet (n : Nat) (on : Bool) (h : on = true → n ∈ [7, 25, 1049, 2004]) :
    Clean (Terminal.Render.modeSet n on) := by
  rw [modeSet_bytes]
  refine clean_piece ?_
  cases on
  · simp [Piece.Ok]
  · simpa [Piece.Ok] using h rfl

theorem clean_crlf : Clean Terminal.Render.crlfB := ⟨[.cr, .lf], by simp [Piece.Ok], rfl⟩

/-- Text of printable characters, line feeds and tabs is clean. -/
theorem clean_text {cs : List Char} (h : ∀ c ∈ cs, Printable c ∨ c = '\n' ∨ c = '\t') :
    Clean (cs.flatMap String.utf8EncodeChar) := by
  refine clean_flatMap fun c hc => ?_
  rcases h c hc with printable | rfl | rfl
  · exact clean_piece (p := .text c) printable
  · exact ⟨[.lf], by simp [Piece.Ok], by decide⟩
  · exact ⟨[.tab], by simp [Piece.Ok], by decide⟩

theorem printable_of_bounds {c : Char} (h : 32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat)) :
    Printable c := by
  simp only [Printable]
  omega

/-- The renderer's text encoding of printable characters is their UTF-8. -/
theorem utf8s_printable {cs : List Char} (h : ∀ c ∈ cs, Printable c) :
    Terminal.Render.utf8s cs = cs.flatMap String.utf8EncodeChar := by
  rw [Terminal.Render.utf8s_eq_flatMap]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have p := h c (by simp)
    simp only [Printable] at p
    simp only [List.map_cons, List.flatMap_cons]
    rw [Terminal.Render.safeChar_eq_self (by omega) (by omega),
      Terminal.Render.utf8_eq_utf8EncodeChar, ih fun d hd => h d (by simp [hd])]

theorem clean_utf8s {cs : List Char} (h : ∀ c ∈ cs, Printable c) :
    Clean (Terminal.Render.utf8s cs) := by
  rw [utf8s_printable h]
  exact clean_text fun c hc => .inl (h c hc)

/-- `ls` prints clean bytes: each row's pieces are printable text, its badge in a status
style followed by an SGR reset, and each row ends with a line feed. -/
theorem terminalListing_clean (withColor : Bool) (rows : List (List (String × String))) :
    Clean (Listing.terminalListing withColor rows) := by
  unfold Listing.terminalListing
  split
  · have empty : ∀ c ∈ "no sessions".toList, Printable c := by
      simp only [Printable]
      decide
    exact clean_append (clean_utf8s empty) (clean_piece (p := .lf) trivial)
  · refine clean_flatMap fun row _ => clean_append ?_ (clean_piece (p := .lf) trivial)
    unfold Listing.renderPieces
    refine clean_flatMap fun piece hpiece => ?_
    have text : Clean (Terminal.Render.utf8s piece.text) :=
      clean_utf8s fun c hc =>
        printable_of_bounds (Listing.rowPieces_printable _ row piece hpiece c hc)
    split
    · split
      · exact clean_append (clean_append (clean_sgr _) text) (clean_sgr _)
      · exact text
    · exact text

/-- A window title linger sets is clean: one OSC 2 whose payload is printable. -/
theorem title_ansi_clean (title : String) : Clean (Terminal.Title.ansi title) := by
  have printable : ∀ c ∈ Terminal.Title.payload title, Printable c := fun c hc =>
    Terminal.Title.payload_safe title c hc
  refine ⟨[.title (Terminal.Title.payload title)], by simpa [Piece.Ok] using printable, ?_⟩
  simp [Terminal.Title.ansi, Piece.bytes, (utf8s_printable printable).symm]

theorem title_update_clean (v : Terminal.Vt.Vt) (title : String) :
    Clean (Terminal.Title.update v title) := by
  unfold Terminal.Title.update
  split
  · exact title_ansi_clean title
  · exact clean_nil

/-- The handback is clean: the pieces that reset what an application may have left on, then
an empty title. -/
theorem leaveAnsi_clean : Clean Terminal.Render.leaveAnsi := by
  refine
    ⟨[.esc 0x5C, .csi true [1049] 0x6C, .csi false [4] 0x6C, .csi true [25] 0x68,
        .csi true [2004] 0x6C, .csi true [1000] 0x6C, .csi true [1002] 0x6C, .csi true [1003] 0x6C,
        .csi true [1006] 0x6C, .csi true [1004] 0x6C, .csi true [1] 0x6C, .esc 0x3E,
        .csi true [6] 0x6C, .csi true [7] 0x68, .csi false [] 0x72, .ascii false, .ascii true,
        .shiftIn, .csi false [999, 1] 0x48, .csi false [0] 0x6D, .title []],
      by simp [Piece.Ok], ?_⟩
  simp only [Terminal.Render.leaveAnsi, Terminal.Render.modeSet, Terminal.Render.csiPriv,
    Terminal.Render.csiNum, Terminal.Render.csiNum2, Terminal.Render.csiPlain,
    Terminal.Render.escSeq, Terminal.Render.escCharset, Terminal.Render.csiB, Terminal.Render.escB,
    Terminal.Render.defaultTitleAnsi, render_digits]
  simp [Piece.bytes, digits]

/-- The screen `capture` prints is clean: printable characters and line feeds. -/
theorem screenText_clean (v : Terminal.Vt.Vt) : Clean (Terminal.Render.screenText v) := by
  obtain ⟨cs, text, safe⟩ := Terminal.screenText_text v
  rw [text]
  exact clean_text fun c hc => (safe c hc).elim (fun h => .inr (.inl h)) .inl

/-- The history `capture --history` prints is clean: printable characters and line feeds. -/
theorem history_clean (v : Terminal.Vt.Vt) : Clean (Terminal.Render.history v) := by
  obtain ⟨cs, text, safe⟩ := Terminal.history_text v
  rw [text]
  exact clean_text fun c hc => (safe c hc).elim (fun h => .inr (.inl h)) .inl

/-- `ESC c`, which resets a terminal, is not clean: no piece starts with it. -/
theorem not_clean_reset : ¬Clean [0x1B, 0x63] := by
  rintro ⟨pieces, ok, eq⟩
  cases pieces with
  | nil => cases eq
  | cons p rest =>
    have first := ok p (by simp)
    cases p with
    | text c =>
      have printable : ∀ c' ∈ [c], Printable c' := by simpa [Piece.Ok] using first
      have noEsc := Terminal.Render.utf8s_no_esc [c]
      rw [utf8s_printable printable] at noEsc
      simp only [List.flatMap_cons, Piece.bytes, List.flatMap_nil, List.append_nil] at eq noEsc
      cases h : String.utf8EncodeChar c with
      | nil => exact absurd h (by simp)
      | cons b bs =>
        rw [h] at eq noEsc
        have : b = 0x1B := by simpa using congrArg List.head? eq
        exact noEsc b (by simp) this
    | lf => simp [Piece.bytes] at eq
    | cr => simp [Piece.bytes] at eq
    | tab => simp [Piece.bytes] at eq
    | csi priv params final => simp [Piece.bytes] at eq
    | title cs => simp [Piece.bytes] at eq
    | esc final =>
      simp only [Piece.Ok] at first
      simp only [List.flatMap_cons, Piece.bytes, List.cons_append, List.nil_append,
        List.cons.injEq] at eq
      rcases first with rfl | rfl <;> simp at eq
    | ascii g1 => cases g1 <;> simp [Piece.bytes] at eq
    | shiftIn => simp [Piece.bytes] at eq

end Linger.Display
