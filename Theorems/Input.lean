module

public import Tools.Input
import all Tools.Input

public section

/-! Decoder contracts for arbitrary states and input bytes.

The state has finite control tags and at most three stored byte fields. Lean's
UTF-8 validator interprets a completed prefix of at most four bytes; the
theorems characterize that boundary and prove the subsequent control filter.
No claim is made about terminal IO, poll timing or a pasted end marker's origin.
-/

namespace Tools.Input

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
        (byte = 0x42 ∧ key = .down) ∨
        (byte = 0x48 ∧ key = .first) ∨ (byte = 0x46 ∧ key = .last) := by
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

private theorem deliver_length (paste : Bool) (event : Option Key) :
    (deliver paste event).length ≤ 1 := by
  cases event with
  | none => simp [deliver]
  | some key => cases key <;> simp only [deliver] <;> split <;> simp

private theorem deliver_text (paste : Bool) (event : Option Key) (char : Char)
    (h : .text char ∈ deliver paste event) :
    32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat) := by
  cases event with
  | none => simp [deliver] at h
  | some key => cases key <;> simp only [deliver] at h <;> split at h <;> simp_all

private theorem deliver_paste (event : Option Key) (key : Key) (h : key ∈ deliver true event) :
    ∃ char, key = .text char := by
  cases event with
  | none => simp [deliver] at h
  | some value =>
    cases value <;> simp [deliver] at h
    exact ⟨_, h.2⟩

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

theorem feed_paste_no_commands (state : State) (byte : UInt8) (hpaste : state.paste = true) :
    .accept ∉ (feed state byte).2 ∧
      .cancel ∉ (feed state byte).2 ∧
      .up ∉ (feed state byte).2 ∧
      .down ∉ (feed state byte).2 ∧
      .first ∉ (feed state byte).2 ∧
      .last ∉ (feed state byte).2 ∧
      .backspace ∉ (feed state byte).2 ∧ .clear ∉ (feed state byte).2 := by
  have h := feed_paste_only_text state byte
  repeat' constructor
  all_goals intro member; obtain ⟨char, impossible⟩ := h _ hpaste member; cases impossible

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

/-- The ordinary control-byte repertoire is exact, outside paste and sequences. -/
theorem feed_controls (byte : UInt8) (key : Key)
    (h :
      (byte, key) ∈
        [(8, .backspace), (127, .backspace), (21, .clear), (16, .up), (14, .down), (9, .down),
          (13, .accept), (10, .accept), (3, .cancel), (4, .cancel)]) :
    feed init byte = (init, [key]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- Automatic listing refresh has no keyboard event or manual refresh shortcut. -/
theorem feed_ctrl_r : feed init 18 = (init, []) := by rfl

theorem feed_ascii (paste : Bool) (byte : UInt8) (h : 32 ≤ byte ∧ byte < 127) :
    feed { paste } byte = ({ paste }, [.text (Char.ofUInt8 byte)]) := by
  have lo : 32 ≤ byte.toNat := by simpa [UInt8.le_iff_toNat_le] using h.1
  have hi : byte.toNat < 127 := by simpa [UInt8.lt_iff_toNat_lt] using h.2
  simp [feed, step, idle_ascii paste byte h, deliver, Char.ofUInt8, Char.toNat, lo, hi]

/-- A CSI parameter that has become unsupported stays in discard mode until a
final byte arrives, including when a command byte occurs inside it. -/
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

/-- A timeout can only cancel a lone escape outside paste; it cannot accept. -/
theorem flush_emits (state : State) (key : Key) (h : key ∈ (flush state).2) :
    key = .cancel ∧ state.mode = .escape ∧ state.paste = false := by
  unfold flush at h
  split at h <;> simp_all

theorem flush_no_accept (state : State) : .accept ∉ (flush state).2 := by
  intro h
  have hkey := (flush_emits state .accept h).1
  cases hkey

theorem flush_idempotent (state : State) : flush (flush state).1 = ((flush state).1, []) := by
  simp [flush]

end Tools.Input
