module

public import Input
import Input.Proofs

/-! The input decoder's headline theorems, proved of the decoder: `lake comparator` checks that
these are exactly the statements of `InputChallenge.lean`. -/

public section

namespace Input

theorem paste_only_text (state : Input.State) (byte : UInt8) (pasting : state.paste = true) :
    ∀ key ∈ (Input.feed state byte).2, ∃ c, key = .text c := fun key member =>
  Input.feed_paste_only_text state byte key pasting member

theorem paste_only_text_rejects_enter :
    ¬∀ (state : Input.State) (byte : UInt8),
        state.paste = true →
          ∀
            key ∈
              ((fun (state : Input.State) (_ : UInt8) => (state, [Input.Key.enter])) state byte).2,
            ∃ c, key = .text c := by
  intro h
  obtain ⟨c, same⟩ := h { paste := true } 0 rfl .enter (by simp)
  cases same

end Input
