module

import all Linger.Tools.Key
import all Linger.Tools.Input
import Theorems.Input

/-! The selector's bindings are checked against concrete byte defaults.
The generic decoder owns recognition and paste suppression; this adapter owns
actions. These contracts do not claim to verify terminal polling or IO. -/

namespace Linger.Tools.Key

theorem ofInput_text (char : Char) : ofInput (.text char) = some (.text char) := by rfl

/-- The control bindings are exact even for a constructed event carrying an
arbitrary byte. Controls not listed here cannot request a selector action. -/
theorem ofInput_control_iff (byte : UInt8) (key : Linger.Tools.Key) :
    ofInput (.control byte) = some key ↔
      (byte = 21 ∧ key = .clear) ∨
        (byte = 16 ∧ key = .up) ∨
        (byte = 14 ∧ key = .down) ∨ (byte = 3 ∧ key = .cancel) ∨ (byte = 4 ∧ key = .cancel) := by
  simp only [ofInput]
  split <;> simp_all [eq_comm]

theorem ofInput_control_none_iff (byte : UInt8) :
    ofInput (.control byte) = none ↔ byte ≠ 21 ∧ byte ≠ 16 ∧ byte ≠ 14 ∧ byte ≠ 3 ∧ byte ≠ 4 := by
  simp only [ofInput]
  split <;> simp_all

theorem ofInput_special (event : Input.Key) (key : Linger.Tools.Key)
    (h :
      (event, key) ∈
        [(.backspace, .backspace), (.tab, .down), (.enter, .accept), (.escape, .cancel), (.up, .up),
          (.down, .down), (.home, .first), (.end, .last)]) :
    ofInput event = some key := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- Binding never manufactures text from a non-text event. -/
theorem ofInput_text_iff (event : Input.Key) (char : Char) :
    ofInput event = some (.text char) ↔ event = .text char := by
  cases event <;> simp only [ofInput]
  all_goals
    repeat'
      (first
        | split
        | simp_all)

/-- All 256 possible bytes have their original selector meaning at idle.
This statement fixes the defaults independently of the adapter's body. -/
theorem feed_byte_bindings (byte : UInt8) :
    (Input.feed Input.init byte).2.filterMap ofInput =
      match byte with
      | 8 | 127 => [.backspace]
      | 21 => [.clear]
      | 16 => [.up]
      | 14 | 9 => [.down]
      | 13 | 10 => [.accept]
      | 3 | 4 => [.cancel]
      | _ => if 32 ≤ byte ∧ byte < 127 then [.text (Char.ofUInt8 byte)] else [] := by
  simp only [Input.feed, Input.init, Input.step, Input.idle]
  repeat'
    (first
      | rfl
      | split)
  all_goals
    simp_all [Input.deliver, Input.printable, ofInput, UInt8.le_iff_toNat_le, UInt8.lt_iff_toNat_lt,
      Char.ofUInt8]
  all_goals try simp_all [Option.filter, ofInput]
  all_goals omega

/-- The original control-byte shortcuts remain selector policy. -/
theorem feed_controls (byte : UInt8) (key : Linger.Tools.Key)
    (h :
      (byte, key) ∈
        [(8, .backspace), (127, .backspace), (21, .clear), (16, .up), (14, .down), (9, .down),
          (13, .accept), (10, .accept), (3, .cancel), (4, .cancel)]) :
    (Input.feed Input.init byte).2.filterMap ofInput = [key] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  all_goals rcases h with ⟨rfl, rfl⟩; rfl

/-- Automatic listing refresh has no manual keyboard action. -/
theorem feed_ctrl_r : (Input.feed Input.init 18).2.filterMap ofInput = [] := by rfl

theorem feed_ascii (paste : Bool) (byte : UInt8) (h : 32 ≤ byte ∧ byte < 127) :
    (Input.feed { paste } byte).2.filterMap ofInput = [.text (Char.ofUInt8 byte)] := by
  simp [Input.feed_ascii paste byte h, ofInput]

/-- Every bound event from paste is the unchanged decoded character. -/
theorem feed_paste_only_text (state : Input.State) (byte : UInt8) (key : Linger.Tools.Key)
    (hpaste : state.paste = true) (h : key ∈ (Input.feed state byte).2.filterMap ofInput) :
    ∃ char, key = .text char ∧ Input.Key.text char ∈ (Input.feed state byte).2 := by
  obtain ⟨event, member, bound⟩ := List.mem_filterMap.mp h
  obtain ⟨char, rfl⟩ := Input.feed_paste_only_text state byte event hpaste member
  exact ⟨char, by simpa [ofInput] using bound.symm, member⟩

theorem feed_paste_no_commands (state : Input.State) (byte : UInt8) (hpaste : state.paste = true) :
    .accept ∉ (Input.feed state byte).2.filterMap ofInput ∧
      .cancel ∉ (Input.feed state byte).2.filterMap ofInput ∧
      .up ∉ (Input.feed state byte).2.filterMap ofInput ∧
      .down ∉ (Input.feed state byte).2.filterMap ofInput ∧
      .first ∉ (Input.feed state byte).2.filterMap ofInput ∧
      .last ∉ (Input.feed state byte).2.filterMap ofInput ∧
      .backspace ∉ (Input.feed state byte).2.filterMap ofInput ∧
      .clear ∉ (Input.feed state byte).2.filterMap ofInput := by
  repeat' constructor
  all_goals
    intro member
    obtain ⟨char, impossible, _⟩ := feed_paste_only_text state byte _ hpaste member
    cases impossible

/-- Only a lone escape outside paste cancels after a timeout. -/
theorem flush_binding (state : Input.State) :
    (Input.flush state).2.filterMap ofInput =
      if state.mode = .escape ∧ state.paste = false then [.cancel] else [] := by
  simp only [Input.flush]
  split <;> simp [ofInput]

theorem flush_emits (state : Input.State) (key : Linger.Tools.Key)
    (h : key ∈ (Input.flush state).2.filterMap ofInput) :
    key = .cancel ∧ state.mode = .escape ∧ state.paste = false := by
  rw [flush_binding] at h
  split at h <;> simp_all

theorem flush_no_accept (state : Input.State) :
    .accept ∉ (Input.flush state).2.filterMap ofInput := by
  intro h
  have hkey := (flush_emits state .accept h).1
  cases hkey

end Linger.Tools.Key
