example : (do let x ← some 3; some (x + 1)) = some 4 := by simp?

example (f : Nat → Option Nat) (h : f 3 = some 5) :
    (do let x ← some 3; let y ← f x; some (y + 1)) = some 6 := by
  simp only [Option.bind_some_eq_map]
  sorry
