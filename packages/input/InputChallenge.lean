module

public import Input.Spec

/-! # Headline theorems of the input decoder

What a terminal key decoder must do for the application reading its keys: while a paste is in
progress, deliver only text. The theorem is stated over the decoder, declared below as a hole:
`sorry` here, which the package's code supplies, and `Input.Solution` proves the same statement
of it. -/

public section

/-- Decode one input byte: the decoder's next state, and the keys the byte completes. -/
@[expose]
def Input.feed : Input.State → UInt8 → Input.State × List Input.Key := sorry

namespace Input

/-- While a paste is in progress, the decoder delivers only text: no pasted byte acts as Enter,
Escape, a cursor key, Backspace or a control byte. -/
theorem paste_only_text (state : Input.State) (byte : UInt8) (pasting : state.paste = true) :
    ∀ key ∈ (Input.feed state byte).2, ∃ c, key = .text c := by sorry

/-- `paste_only_text` rejects an input decoder that turns any byte into Enter. -/
theorem paste_only_text_rejects_enter :
    ¬∀ (state : Input.State) (byte : UInt8),
        state.paste = true →
          ∀
            key ∈
              ((fun (state : Input.State) (_ : UInt8) => (state, [Input.Key.enter])) state byte).2,
            ∃ c, key = .text c := by
  sorry

end Input
