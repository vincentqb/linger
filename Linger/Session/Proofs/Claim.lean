module

import Linger.Session.Spec

/-! Ownership of socket and checkpoint resources across arbitrary interleavings, in the
lock-protocol model of `Linger/Session/Spec.lean`. -/

namespace Linger.Session.Claim

/-- `put` changes the map at exactly its key. -/
theorem put_apply {α : Type} (map : Nat → α) (key : Nat) (value : α) (index : Nat) :
    put map key value index = if index = key then value else map index := rfl

/-- At the start no actor has entered a lease. -/
theorem initial_idle (actor : Nat) : initial.active actor = none := rfl

/-- Every active process still holds both resources it claimed. -/
def Protected (s : State) : Prop :=
  ∀ actor lease,
    s.active actor = some lease →
      s.locks lease.socket = some actor ∧ s.locks lease.checkpoint = some actor

theorem protected_step {before after : State} (safe : Protected before) (step : Step before after) :
    Protected after := by cases step <;> simp only [Protected, put] at safe ⊢ <;> grind

/-- Every finite interleaving preserves the lifetime lock invariant. -/
theorem reachable_protected {s : State} (reached : Reachable s) : Protected s := by
  induction reached with
  | initial =>
    intro actor lease active; cases active
  | next _ step ih => exact protected_step ih step

theorem owner_holds_lock {s : State} (reached : Reachable s) {actor resource : Nat} {lease : Lease}
    (active : s.active actor = some lease) (uses : lease.Uses resource) :
    s.locks resource = some actor := by
  obtain ⟨socket, checkpoint⟩ := reachable_protected reached actor lease active
  rcases uses with rfl | rfl
  · exact socket
  · exact checkpoint

/-- Sharing either lock inode excludes simultaneous ownership, even when the
other directory differs. This also excludes offline readers during a live lease. -/
theorem at_most_one_owner {s : State} (reached : Reachable s) {a b resource : Nat}
    {left right : Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b :=
  Option.some.inj
    ((owner_holds_lock reached ha leftUses).symm.trans (owner_holds_lock reached hb rightUses))

/-- A fully free namespace can be acquired and entered, so the protocol does
not obtain exclusivity by refusing every owner. -/
theorem claim_free {s : State} (reached : Reachable s) (actor : Nat) (lease : Lease)
    (idle : s.active actor = none) (socket : s.locks lease.socket = none)
    (checkpoint : s.locks lease.checkpoint = none) (distinct : lease.checkpoint ≠ lease.socket) :
    ∃ after, Reachable after ∧ after.active actor = some lease := by
  let first := { s with locks := put s.locks lease.socket (some actor) }
  have hfirst : Reachable first := reached.next (.acquire s actor lease.socket socket)
  let both := { first with locks := put first.locks lease.checkpoint (some actor) }
  have hboth : Reachable both :=
    hfirst.next (.acquire first actor lease.checkpoint (by simp [first, put, distinct, checkpoint]))
  refine ⟨{ both with active := put both.active actor (some lease) }, ?_, by simp [put]⟩
  exact
    hboth.next
      (.enter both actor lease idle (by simp [both, first, put, Ne.symm distinct])
        (by simp [both, put]))

end Linger.Session.Claim
