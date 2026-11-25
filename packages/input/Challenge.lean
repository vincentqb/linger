module

public import Input.CoreSpec
meta import SoftwareChallenge

public section

def Input.feed : Input.State → UInt8 → Input.State × List Input.Key := sorry

def Input.flush : Input.State → Input.State × List Input.Key := sorry

namespace Input

theorem paste_only_text (state : Input.State) (byte : UInt8) (pasting : state.paste = true) :
    ∀ key ∈ (Input.feed state byte).2, ∃ c, key = .text c := by sorry

@[kills paste_only_text]
theorem paste_only_text_rejects_enter :
    ¬∀ (state : Input.State) (byte : UInt8),
        state.paste = true →
          ∀
            key ∈
              ((fun (state : Input.State) (_ : UInt8) => (state, [Input.Key.enter])) state byte).2,
            ∃ c, key = .text c := by
  sorry

@[witness paste_only_text]
theorem paste_only_text_applies :
    ∃ (state : Input.State) (byte : UInt8) (_ : state.paste = true) (key : Input.Key),
      key ∈ (Input.feed state byte).2 := by
  sorry

theorem decode_conforms (s : Input.Seq) :
    Input.reads Input.feed Input.flush s = ({ paste := s.pastes }, s.keys) := by sorry

@[kills decode_conforms]
theorem decode_conforms_rejects_ss3 :
    ¬∀ (s : Input.Seq),
        Input.reads (Input.ss3Dropped Input.feed) Input.flush s =
          ({ paste := s.pastes }, s.keys) := by
  sorry

@[kills decode_conforms]
theorem decode_conforms_rejects_delete :
    ¬∀ (s : Input.Seq),
        Input.reads (Input.delDeletes Input.feed) Input.flush s =
          ({ paste := s.pastes }, s.keys) := by
  sorry

end Input
