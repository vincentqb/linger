module

public import Input.CoreSpec
meta import SoftwareChallenge

/-! # Headline theorems of the input decoder

What a terminal key decoder must do for the application reading its keys: while a paste is in
progress, deliver only text, and decode each key sequence linger reads as its standard sends it
(`decode_conforms`): the cursor keys in their `CSI` and `SS3` forms, Home and End in all four,
Enter, Backspace as DEL or BS, Tab, the Ctrl-letters, printable ASCII, bracketed paste's start and
end, and ESC alone as Escape once the wait for a sequence ends, each to exactly the key the
reference names and the paste state it leaves, and Left, Right, Page Up and Page Down, which linger
binds none of, to no key. Not claimed: UTF-8 text, modified keys such as `CSI 1 ; 5 A`, function
keys, Alt as an ESC prefix, which the decoder drops, and sequences split by the wait. The theorem is stated over the decoder, declared below as a hole:
`sorry` here, which the package's code supplies, and `Input.Solution` proves the same statement
of it. -/

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
