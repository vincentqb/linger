module

public import Linger.Session
public import Linger.Target.Name
public import Linger.Target.Remote
public import Linger.Target.Spec
public import Linger.Terminal.Render
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Session
import all Linger.Terminal.Proofs.Render.History
import all Linger.Terminal.Proofs.Render.Pen

/-! # Proofs of the headline theorems

`Manifest.lean` states these theorems; each proof here cites the component theorem it
restates. `./lake comparator` checks that the statements match. -/

public section

namespace Linger.Claims

open Linger.Session Linger.Target Linger.Terminal

theorem check_no_alias {a b name : String} (ha : Name.check a = some name)
    (hb : Name.check b = some name) : a = b := Name.check_no_alias ha hb

theorem command_argv (verb : String) (words : List String) :
    Remote.Shell.Words (Remote.command verb words).toList
      (("linger" :: verb :: words).map String.toList) := Remote.command_argv verb words

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) : (run s (chunks.map (Event.bytes id))).1.client? other = s.client? other :=
  Session.run_bytes_isolates s id chunks h

theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Render.screenText_text v
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

end Linger.Claims
