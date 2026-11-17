module

meta import SoftwareChallenge
public import Input.CoreCode
import all Input.CoreCode
import Input.Proofs

/-! The input decoder's headline theorems, proved of the decoder: `lake comparator` checks that
these are exactly the statements of `Challenge.lean`. -/

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

theorem decode_conforms (s : Input.Seq) :
    Input.reads Input.feed Input.flush s = ({ paste := s.pastes }, s.keys) := by
  cases s with
  | up b
  | down b
  | right b
  | left b
  | enter b
  | backspace b => cases b <;> rfl
  | home f
  | end_ f =>
    rcases f with ⟨f, hf⟩
    match f, hf with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | _ + 4, h => exact absurd h (by omega)
  | ctrl l =>
    rcases l with ⟨l, hl⟩
    match l, hl with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
    | 8, _ => rfl
    | 9, _ => rfl
    | 10, _ => rfl
    | 11, _ => rfl
    | 12, _ => rfl
    | 13, _ => rfl
    | 14, _ => rfl
    | 15, _ => rfl
    | 16, _ => rfl
    | 17, _ => rfl
    | 18, _ => rfl
    | 19, _ => rfl
    | 20, _ => rfl
    | 21, _ => rfl
    | 22, _ => rfl
    | 23, _ => rfl
    | 24, _ => rfl
    | 25, _ => rfl
    | _ + 26, h => exact absurd h (by omega)
  | text i =>
    rcases i with ⟨i, hi⟩
    match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
    | 8, _ => rfl
    | 9, _ => rfl
    | 10, _ => rfl
    | 11, _ => rfl
    | 12, _ => rfl
    | 13, _ => rfl
    | 14, _ => rfl
    | 15, _ => rfl
    | 16, _ => rfl
    | 17, _ => rfl
    | 18, _ => rfl
    | 19, _ => rfl
    | 20, _ => rfl
    | 21, _ => rfl
    | 22, _ => rfl
    | 23, _ => rfl
    | 24, _ => rfl
    | 25, _ => rfl
    | 26, _ => rfl
    | 27, _ => rfl
    | 28, _ => rfl
    | 29, _ => rfl
    | 30, _ => rfl
    | 31, _ => rfl
    | 32, _ => rfl
    | 33, _ => rfl
    | 34, _ => rfl
    | 35, _ => rfl
    | 36, _ => rfl
    | 37, _ => rfl
    | 38, _ => rfl
    | 39, _ => rfl
    | 40, _ => rfl
    | 41, _ => rfl
    | 42, _ => rfl
    | 43, _ => rfl
    | 44, _ => rfl
    | 45, _ => rfl
    | 46, _ => rfl
    | 47, _ => rfl
    | 48, _ => rfl
    | 49, _ => rfl
    | 50, _ => rfl
    | 51, _ => rfl
    | 52, _ => rfl
    | 53, _ => rfl
    | 54, _ => rfl
    | 55, _ => rfl
    | 56, _ => rfl
    | 57, _ => rfl
    | 58, _ => rfl
    | 59, _ => rfl
    | 60, _ => rfl
    | 61, _ => rfl
    | 62, _ => rfl
    | 63, _ => rfl
    | 64, _ => rfl
    | 65, _ => rfl
    | 66, _ => rfl
    | 67, _ => rfl
    | 68, _ => rfl
    | 69, _ => rfl
    | 70, _ => rfl
    | 71, _ => rfl
    | 72, _ => rfl
    | 73, _ => rfl
    | 74, _ => rfl
    | 75, _ => rfl
    | 76, _ => rfl
    | 77, _ => rfl
    | 78, _ => rfl
    | 79, _ => rfl
    | 80, _ => rfl
    | 81, _ => rfl
    | 82, _ => rfl
    | 83, _ => rfl
    | 84, _ => rfl
    | 85, _ => rfl
    | 86, _ => rfl
    | 87, _ => rfl
    | 88, _ => rfl
    | 89, _ => rfl
    | 90, _ => rfl
    | 91, _ => rfl
    | 92, _ => rfl
    | 93, _ => rfl
    | 94, _ => rfl
    | _ + 95, h => exact absurd h (by omega)
  | escape =>
    simp [Input.reads, Input.run, Input.flush, Input.Seq.waits, Input.Seq.bytes, Input.Seq.pasting,
      Input.Seq.keys, Input.Seq.pastes, Input.feed, Input.step, Input.idle, Input.deliver]
  | _ => rfl

theorem decode_conforms_rejects_ss3 :
    ¬∀ (s : Input.Seq),
        Input.reads (Input.ss3Dropped Input.feed) Input.flush s =
          ({ paste := s.pastes }, s.keys) := by
  -- SS3 A is Up in application cursor mode
  intro h
  have := congrArg Prod.snd (h (.up true))
  exact
    absurd this
      (by
        simp [Input.reads, Input.run, Input.ss3Dropped, Input.Seq.bytes, Input.Seq.waits,
          Input.Seq.keys, Input.Seq.pasting, Input.feed, Input.step, Input.idle, Input.deliver])

theorem decode_conforms_rejects_delete :
    ¬∀ (s : Input.Seq),
        Input.reads (Input.delDeletes Input.feed) Input.flush s =
          ({ paste := s.pastes }, s.keys) := by
  -- DEL is what Backspace sends
  intro h
  have := congrArg Prod.snd (h (.backspace false))
  exact
    absurd this
      (by
        simp [Input.reads, Input.run, Input.delDeletes, Input.Seq.bytes, Input.Seq.waits,
          Input.Seq.keys, Input.Seq.pasting])

end Input
