module

public import Linger.Tools.Input
import all Linger.Tools.Input

public section

/-! Decoder contracts for arbitrary states and input bytes.

The state has finite control tags and at most three stored byte fields. Lean's
UTF-8 validator interprets a completed prefix of at most four bytes; the
theorems characterize that boundary and prove the subsequent control filter.
No claim is made about terminal IO, poll timing or a pasted end marker's origin.
-/

namespace Linger.Tools.Input

private theorem stored_bound (mode : Mode) : (stored mode).size ≤ 3 := by
  cases mode <;> simp [stored]

/-- The actual buffer passed to UTF-8 conversion is bounded independently of
how many bytes have already arrived. CSI never stores parameter text. -/
private theorem completed_bound (mode : Mode) (byte : UInt8) :
    ((stored mode).push byte).size ≤ 4 := by
  have := stored_bound mode
  simp only [Array.size_push]
  omega

theorem pending_iff (state : State) : pending state = false ↔ state.mode = .idle := by
  cases state with
  | mk paste mode => cases mode <;> simp [pending]

theorem init_idle : pending init = false ∧ init.paste = false := by simp [pending, init]

private theorem advance_other (byte : UInt8) : advance .other byte = .other := by simp [advance]

/-- A paste marker's parameter cannot be recognized as a subsequence of a
longer, malformed or overflowing parameter. -/
private theorem advance_pasteStart (parameter : Parameter) (byte : UInt8) :
    advance parameter byte = .pasteStart ↔ parameter = .twenty ∧ byte = 0x30 := by
  cases parameter <;> unfold advance <;> split <;> simp_all

private theorem advance_pasteEnd (parameter : Parameter) (byte : UInt8) :
    advance parameter byte = .pasteEnd ↔ parameter = .twenty ∧ byte = 0x31 := by
  cases parameter <;> unfold advance <;> split <;> simp_all

private theorem cursor_exact (byte : UInt8) (key : Key) :
    cursor byte = some key ↔
      (byte = 0x41 ∧ key = .up) ∨
        (byte = 0x42 ∧ key = .down) ∨ (byte = 0x48 ∧ key = .home) ∨ (byte = 0x46 ∧ key = .end) := by
  unfold cursor
  split <;> simp_all [eq_comm]

private theorem decode_validated (bytes : Array UInt8) (char : Char)
    (h : decode bytes = some char) :
    ∃ text, String.fromUTF8? (ByteArray.mk bytes) = some text ∧ text.toList = [char] := by
  unfold decode at h
  split at h
  · rename_i text htext
    split at h
    · rename_i actual hchars
      cases h
      exact ⟨text, htext, hchars⟩
    · cases h
  · cases h

private theorem idle_paste (paste : Bool) (byte : UInt8) : (idle paste byte).1.paste = paste := by
  unfold idle
  repeat'
    (first
      | rfl
      | split)

private theorem idle_ascii (paste : Bool) (byte : UInt8) (h : 32 ≤ byte ∧ byte < 127) :
    idle paste byte = ({ paste }, some (.text (Char.ofUInt8 byte))) := by
  unfold idle
  repeat'
    (first
      | rfl
      | split)
  all_goals simp_all [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt]
  all_goals omega

private theorem utf8Step_paste (state : State) (byte : UInt8) :
    (utf8Step state byte).1.paste = state.paste := by
  unfold utf8Step
  split
  · cases state.mode <;> rfl
  · exact idle_paste _ _

/-- Completing a scalar invokes the validator with exactly the retained bytes
and the new continuation; the scalar is never assembled by unchecked casts. -/
private theorem utf8Step_completed (paste : Bool) (mode : Mode) (byte : UInt8)
    (hbyte : 0x80 ≤ byte ∧ byte ≤ 0xbf)
    (hmode :
      (∃ a, mode = .utf2 a) ∨ (∃ a b, mode = .utf3Last a b) ∨ (∃ a b c, mode = .utf4Last a b c)) :
    utf8Step { paste, mode } byte = ({ paste }, (decode ((stored mode).push byte)).map .text) := by
  rcases hmode with ⟨a, rfl⟩ | ⟨a, b, rfl⟩ | ⟨a, b, c, rfl⟩ <;> simp [utf8Step, hbyte]

/-- Only the final byte of a recognized bracket marker changes paste mode. -/
private theorem step_paste (state : State) (byte : UInt8) :
    (step state byte).1.paste =
      if state.mode = .csi .pasteEnd ∧ byte = 0x7e then false
      else if state.mode = .csi .pasteStart ∧ byte = 0x7e then true else state.paste := by
  cases state with
  | mk paste
    mode =>
    cases mode <;> simp only [step, idle_paste, utf8Step_paste, init, Mode.csi.injEq]
    all_goals repeat' (split <;> simp_all)
    all_goals
      rename_i parameter _
      cases parameter <;> repeat' (split <;> simp_all)
    all_goals by_cases final : byte = 0x7e <;> simp_all

/-- Delivery preserves the decoded key exactly and drops precisely the forbidden
events. Printable text remains available in either paste mode. -/
private theorem deliver_mem (paste : Bool) (event : Option Key) (key : Key) :
    key ∈ deliver paste event ↔
      event = some key ∧
        match key with
        | .text char => 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)
        | _ => paste = false := by
  cases key <;> simp [deliver]

private theorem deliver_length (paste : Bool) (event : Option Key) :
    (deliver paste event).length ≤ 1 := Option.length_toList_le

private theorem deliver_text (paste : Bool) (event : Option Key) (char : Char)
    (h : .text char ∈ deliver paste event) :
    32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat) :=
  ((deliver_mem paste event (.text char)).mp h).2

private theorem deliver_paste (event : Option Key) (key : Key) (h : key ∈ deliver true event) :
    ∃ char, key = .text char := by
  have allowed := ((deliver_mem true event key).mp h).2
  cases key <;> simp_all

/-- At most one key is emitted per byte, including malformed input. -/
theorem feed_length (state : State) (byte : UInt8) : (feed state byte).2.length ≤ 1 := by
  unfold feed
  exact deliver_length _ _

private theorem feed_storage_bound (state : State) (byte : UInt8) :
    (stored (feed state byte).1.mode).size ≤ 3 := stored_bound _

/-- Text crossing the decoder boundary cannot contain C0, DEL or C1 controls. -/
theorem feed_text_valid (state : State) (byte : UInt8) (char : Char)
    (h : .text char ∈ (feed state byte).2) :
    32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat) := by
  unfold feed at h
  exact deliver_text _ _ _ h

/-- The filter consults the state before the byte, so a pasted control key is
suppressed even on a byte that finishes a control sequence. -/
theorem feed_paste_only_text (state : State) (byte : UInt8) (key : Key)
    (hpaste : state.paste = true) (h : key ∈ (feed state byte).2) : ∃ char, key = .text char := by
  unfold feed at h
  rw [hpaste] at h
  exact deliver_paste _ _ h

theorem feed_paste_no_controls (state : State) (byte : UInt8) (hpaste : state.paste = true) :
    .enter ∉ (feed state byte).2 ∧
      .escape ∉ (feed state byte).2 ∧
      .up ∉ (feed state byte).2 ∧
      .down ∉ (feed state byte).2 ∧
      .home ∉ (feed state byte).2 ∧
      .end ∉ (feed state byte).2 ∧
      .backspace ∉ (feed state byte).2 ∧
      .tab ∉ (feed state byte).2 ∧ (∀ control, .control control ∉ (feed state byte).2) := by
  have h := feed_paste_only_text state byte
  repeat' constructor
  all_goals
    repeat' intro
    rename_i member
    obtain ⟨char, impossible⟩ := h _ hpaste member
    cases impossible

theorem feed_paste_sticky (state : State) (byte : UInt8) (hpaste : state.paste = true)
    (hmarker : ¬(state.mode = .csi .pasteEnd ∧ byte = 0x7e)) :
    (feed state byte).1.paste = true := by
  change (step state byte).1.paste = true
  rw [step_paste]
  simp [hmarker, hpaste]

theorem feed_paste_end (paste : Bool) :
    feed { paste, mode := .csi .pasteEnd } 0x7e = (init, []) := by simp [feed, step, deliver]

theorem feed_paste_start (paste : Bool) :
    feed { paste, mode := .csi .pasteStart } 0x7e = ({ paste := true }, []) := by
  simp [feed, step, deliver]

/-- Dedicated ASCII keys retain their physical meanings, without application
commands. Escape waits for a continuation or an explicit flush. -/
theorem feed_special (byte : UInt8) (key : Key)
    (h :
      (byte, key) ∈ [(8, .backspace), (127, .backspace), (9, .tab), (13, .enter), (10, .enter)]) :
    feed init byte = (init, [key]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- Every other C0 byte is reported unchanged, including unbound controls.
Paste suppresses these events without changing decoder state. -/
theorem feed_control (paste : Bool) (byte : UInt8) (hbyte : byte < 32)
    (hspecial : byte ≠ 8 ∧ byte ≠ 9 ∧ byte ≠ 10 ∧ byte ≠ 13 ∧ byte ≠ 27) :
    feed { paste } byte = ({ paste }, if paste then [] else [.control byte]) := by
  rcases hspecial with ⟨h8, h9, h10, h13, h27⟩
  have hi : byte < 128 := by
    simp [UInt8.lt_iff_toNat_lt] at *
    omega
  have hlo : ¬32 ≤ byte := by
    simp [UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt] at *
    omega
  have hdel : byte ≠ 127 := by
    intro h
    simp [h, UInt8.lt_iff_toNat_lt] at hbyte
  cases paste <;> simp [feed, step, idle, deliver, h27, hi, hlo]

theorem feed_escape (paste : Bool) : feed { paste } 27 = ({ paste, mode := .escape }, []) := by
  simp [feed, step, idle, deliver]

theorem feed_ascii (paste : Bool) (byte : UInt8) (h : 32 ≤ byte ∧ byte < 127) :
    feed { paste } byte = ({ paste }, [.text (Char.ofUInt8 byte)]) := by
  have lo : 32 ≤ byte.toNat := by simpa [UInt8.le_iff_toNat_le] using h.1
  have hi : byte.toNat < 127 := by simpa [UInt8.lt_iff_toNat_lt] using h.2
  simp [feed, step, idle_ascii paste byte h, deliver, Char.ofUInt8, lo, hi]

/-- Completing any UTF-8 prefix validates at most four bytes and returns to idle.
A character is emitted exactly when those bytes validate as that single scalar
and it passes the printable-text filter. This holds in either paste mode. -/
theorem feed_utf8_complete (paste : Bool) (mode : Mode) (bytes : Array UInt8) (byte : UInt8)
    (hmode :
      (∃ a, mode = .utf2 a ∧ bytes = #[a]) ∨
        (∃ a b, mode = .utf3Last a b ∧ bytes = #[a, b]) ∨
        (∃ a b c, mode = .utf4Last a b c ∧ bytes = #[a, b, c]))
    (hbyte : 0x80 ≤ byte ∧ byte ≤ 0xbf) :
    (bytes.push byte).size ≤ 4 ∧
      (feed { paste, mode } byte).1 = { paste } ∧
      (∀ char,
        .text char ∈ (feed { paste, mode } byte).2 ↔
          (∃ text,
              String.fromUTF8? (ByteArray.mk (bytes.push byte)) = some text ∧
                text.toList = [char]) ∧
            32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) := by
  have hstored : stored mode = bytes := by
    rcases hmode with ⟨a, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ | ⟨a, b, c, rfl, rfl⟩ <;> rfl
  have hstep : step { paste, mode } byte = ({ paste }, (decode (bytes.push byte)).map .text) := by
    rcases hmode with ⟨a, rfl, rfl⟩ | ⟨a, b, rfl, rfl⟩ | ⟨a, b, c, rfl, rfl⟩
    all_goals simp [step, utf8Step, stored, hbyte]
  refine ⟨?_, ?_, ?_⟩
  · rw [← hstored]
    exact completed_bound mode byte
  · simp [feed, hstep]
  · intro char
    have validated :
      decode (bytes.push byte) = some char ↔
        ∃ text,
          String.fromUTF8? (ByteArray.mk (bytes.push byte)) = some text ∧ text.toList = [char] := by
      constructor
      · exact decode_validated _ _
      · rintro ⟨text, htext, hchars⟩
        simp [decode, htext, hchars]
    simp only [feed, hstep, deliver_mem]
    simp [validated]

/-- CSI and SS3 navigation have the same physical meaning. A pasted navigation
sequence completes normally, with its event suppressed. -/
theorem feed_navigation (paste : Bool) (mode : Mode) (byte : UInt8) (key : Key)
    (hmode : mode = .csi .empty ∨ mode = .ss3)
    (hkey : (byte, key) ∈ [(0x41, .up), (0x42, .down), (0x48, .home), (0x46, .end)]) :
    feed { paste, mode } byte = ({ paste }, if paste then [] else [key]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkey
  rcases hmode with rfl | rfl <;> rcases hkey with h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩; cases paste <;> rfl

theorem feed_numeric_navigation (paste : Bool) (parameter : Parameter) (key : Key)
    (hkey : (parameter, key) ∈ [(.one, .home), (.seven, .home), (.four, .end), (.eight, .end)]) :
    feed { paste, mode := .csi parameter } 0x7e = ({ paste }, if paste then [] else [key]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hkey
  rcases hkey with h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩; cases paste <;> rfl

/-- A CSI parameter that has become unsupported stays in discard mode until a
final byte arrives, including when a control byte occurs inside it. -/
theorem feed_csi_discard (paste : Bool) (byte : UInt8) (hescape : byte ≠ 0x1b)
    (hfinal : ¬(0x40 ≤ byte ∧ byte ≤ 0x7e)) :
    feed { paste, mode := .csi .other } byte = ({ paste, mode := .csi .other }, []) := by
  simp [feed, step, advance_other, deliver, hescape, hfinal]

theorem flush_paste (mode : Mode) : flush { paste := true, mode } = ({ paste := true }, []) := by
  simp [flush]

theorem flush_init : flush init = (init, []) := by simp [flush, init]

theorem flush_idle (paste : Bool) : flush { paste } = ({ paste }, []) := by simp [flush]

theorem flush_state (state : State) :
    pending (flush state).1 = false ∧ (flush state).1.paste = state.paste := by
  simp [flush, pending]

/-- A timeout can only report a lone escape outside paste. -/
theorem flush_emits (state : State) (key : Key) (h : key ∈ (flush state).2) :
    key = .escape ∧ state.mode = .escape ∧ state.paste = false := by
  unfold flush at h
  split at h <;> simp_all

theorem flush_escape (state : State) :
    (flush state).2 = [.escape] ↔ state.mode = .escape ∧ state.paste = false := by simp [flush]

theorem flush_no_enter (state : State) : .enter ∉ (flush state).2 := by
  intro h
  have hkey := (flush_emits state .enter h).1
  cases hkey

theorem flush_idempotent (state : State) : flush (flush state).1 = ((flush state).1, []) := by
  simp [flush]

end Linger.Tools.Input
