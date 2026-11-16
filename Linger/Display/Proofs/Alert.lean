module

import all Linger.Display.CoreCode.Alert
import all Linger.Display.Proofs.Clean
import all Terminal.Proofs.Title

/-! # Alerts of another session's ask — once per change into asking, never one's own, clean

From one sample to the next, an attached client names exactly the sessions that changed into
asking, other than its own, each once, and none on the first sample; and what it writes for one is
one clean OSC 9. -/

namespace Linger.Display.Alert

open Linger.Display.Status (Status)

/-- The first sample names no session: what asked when the client attached, its title counts. -/
theorem announce_first (current : List (String × Status)) (own : String) :
    announce none current own = [] := rfl

/-- **A change into asking is told, once, and never one's own**: a later sample names a session
exactly when it asks now, did not in the previous sample, and is not the client's own. -/
theorem mem_announce (before current : List (String × Status)) (own name : String) :
    name ∈ announce (some before) current own ↔
      name ≠ own ∧ (name, Status.asks) ∈ current ∧ (name, Status.asks) ∉ before := by
  simp only [announce, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨⟨n, st⟩, ⟨mem, p⟩, rfl⟩
    simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not,
      Bool.not_true] at p
    obtain ⟨⟨rfl, other⟩, fresh⟩ := p
    exact ⟨other, mem, fun h => by simp_all⟩
  · rintro ⟨other, mem, fresh⟩
    exact ⟨(name, .asks), ⟨mem, by simp [other, fresh]⟩, rfl⟩

/-- A sample whose names are distinct names each session at most once. -/
theorem announce_nodup (before current : List (String × Status)) (own : String)
    (distinct : (current.map (·.1)).Nodup) : (announce (some before) current own).Nodup :=
  (List.filter_sublist.map _).nodup distinct

/-- What a client writes for a session's ask is one OSC 9 whose text is printable. -/
theorem notification_clean (name notice : String) : Clean (notification name notice) :=
  clean_piece (fun c hc => Terminal.Title.payload_safe _ c hc)

end Linger.Display.Alert
