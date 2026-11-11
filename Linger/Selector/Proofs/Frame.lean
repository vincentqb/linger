module

public import Linger.Selector.Picker
public import Linger.Display.Spec
import all Linger.Selector.Picker
import Linger.Display.Proofs.Clean
import Input.Proofs

public section

/-! # The selector's frame is clean

What the selector writes is made of the pieces `Display.Clean` lists: its frame (an SGR reset,
the cursor home, the screen cleared, then lines of printable characters in SGR styles joined by
CR LF) and the sequences that take and give back the terminal. A style is SGR parameters, so
every style is clean whatever the lines hold. -/

namespace Linger.Selector.Picker

open Linger.Display

private theorem frameChar_printable (raw : Char) : Printable (frameChar raw) := by
  unfold frameChar
  split
  · exact printable_of_bounds ((Input.printable_iff raw).mp ‹_›)
  · simp only [Printable]
    decide

private theorem frameChars_clean (width : Nat) (cs : List Char) :
    ∀ used, Clean (frameChars width used cs).1 := by
  induction cs with
  | nil =>
    intro used
    exact clean_nil
  | cons raw rest ih =>
    intro used
    simp only [frameChars]
    split
    · exact clean_nil
    · exact clean_append (clean_piece (p := .text _) (frameChar_printable raw)) (ih _)

private theorem frameSwitch_clean (active style : List (List Nat)) :
    Clean (frameSwitch active style) := by
  unfold frameSwitch
  split
  · exact clean_flatMap fun params _ => clean_sgr params
  · exact clean_nil

private theorem framePieces_clean (width : Nat) (line : List (String × List (List Nat))) :
    ∀ used active, Clean (framePieces width used active line).1 := by
  induction line with
  | nil =>
    intro used active
    exact clean_nil
  | cons run rest ih =>
    intro used active
    simp only [framePieces]
    split
    · exact clean_append (frameSwitch_clean _ _) (frameChars_clean _ _ _)
    · exact clean_append (clean_append (frameSwitch_clean _ _) (frameChars_clean _ _ _)) (ih _ _)

private theorem frameLine_clean (width : Nat) (line : List (String × List (List Nat))) :
    Clean (frameLine width line) := by
  simp only [frameLine]
  refine clean_append (framePieces_clean width line 0 []) ?_
  split
  · exact clean_nil
  · exact clean_sgr _

/-- The selector's frame is clean, whatever it shows. -/
theorem frame_clean (state : State) (snapshot : Snapshot)
    (statusOf : String → Linger.Display.Status.Status) (loaded withColor savedTmux : Bool)
    (cols rows : Nat) :
    Clean (frame state snapshot statusOf loaded withColor savedTmux cols rows) := by
  unfold frame
  rw [csiPlain_bytes, csiNum_bytes]
  refine
    clean_append
      (clean_append (clean_append (clean_sgr _) (clean_piece (by simp [Piece.Ok])))
        (clean_piece (by simp [Piece.Ok])))
      (clean_intersperse clean_crlf fun bytes hbytes => ?_)
  obtain ⟨line, _, rfl⟩ := List.mem_map.mp hbytes
  exact frameLine_clean _ line

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
