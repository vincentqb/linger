module

import Linger.Session.Spec
import all Linger.Session.Claim

/-! Ownership of socket and checkpoint resources across arbitrary interleavings, in the
lock-protocol model of `Linger/Session/Spec.lean`, when the operating system grants only free
locks (`Exclusive`) and each process enters as `enters` decides. -/

namespace Linger.Session.Claim

/-- `put` changes the map at exactly its key. -/
theorem put_apply {α : Type} (map : Nat → α) (key : Nat) (value : α) (index : Nat) :
    put map key value index = if index = key then value else map index := rfl

/-- At the start no actor has entered a lease. -/
theorem initial_idle (actor : Nat) : initial.active actor = none := rfl

/-- A process may act as the session's owner exactly when it holds both of its locks. -/
theorem enters_iff (socket checkpoint : Bool) :
    enters socket checkpoint = true ↔ socket = true ∧ checkpoint = true := by simp [enters]

/-- Every active process still holds both resources it claimed. -/
def Protected (s : State) : Prop :=
  ∀ actor lease,
    s.active actor = some lease →
      s.locks lease.socket = some actor ∧ s.locks lease.checkpoint = some actor

theorem protected_step {grant : State → Nat → Nat → Bool} (exclusive : Exclusive grant)
    {before after : State} (safe : Protected before) (step : Step grant enters before after) :
    Protected after := by
  cases step with
  | acquire actor resource
    granted =>
    have free : before.locks resource = none := exclusive before actor resource granted
    simp only [Protected, put] at safe ⊢
    grind
  | enter actor lease idle
    decided =>
    obtain ⟨socket, checkpoint⟩ := (enters_iff _ _).mp decided
    simp only [beq_iff_eq] at socket checkpoint
    simp only [Protected, put] at safe ⊢
    grind
  | leave actor =>
    simp only [Protected, put] at safe ⊢
    grind
  | release actor resource owned
    idle =>
    simp only [Protected, put] at safe ⊢
    grind
  | unchanged => exact safe

/-- Every finite interleaving preserves the lifetime lock invariant. -/
theorem reachable_protected {grant : State → Nat → Nat → Bool} (exclusive : Exclusive grant)
    {s : State} (reached : Reachable grant enters s) : Protected s := by
  induction reached with
  | initial =>
    intro actor lease active; cases active
  | next _ step ih => exact protected_step exclusive ih step

theorem owner_holds_lock {grant : State → Nat → Nat → Bool} (exclusive : Exclusive grant)
    {s : State} (reached : Reachable grant enters s) {actor resource : Nat} {lease : Lease}
    (active : s.active actor = some lease) (uses : lease.Uses resource) :
    s.locks resource = some actor := by
  obtain ⟨socket, checkpoint⟩ := reachable_protected exclusive reached actor lease active
  rcases uses with rfl | rfl
  · exact socket
  · exact checkpoint

/-- Sharing either lock inode excludes simultaneous ownership, even when the
other directory differs. This also excludes offline readers during a live lease. -/
theorem at_most_one_owner {grant : State → Nat → Nat → Bool} (exclusive : Exclusive grant)
    {s : State} (reached : Reachable grant enters s) {a b resource : Nat} {left right : Lease}
    (ha : s.active a = some left) (hb : s.active b = some right) (leftUses : left.Uses resource)
    (rightUses : right.Uses resource) : a = b :=
  Option.some.inj
    ((owner_holds_lock exclusive reached ha leftUses).symm.trans
      (owner_holds_lock exclusive reached hb rightUses))

/-- A fully free namespace can be acquired and entered when the operating system grants a free
lock, so the protocol does not obtain exclusivity by refusing every owner. -/
theorem claim_free {grant : State → Nat → Nat → Bool}
    (grants : ∀ s actor resource, s.locks resource = none → grant s actor resource = true)
    {s : State} (reached : Reachable grant enters s) (actor : Nat) (lease : Lease)
    (idle : s.active actor = none) (socket : s.locks lease.socket = none)
    (checkpoint : s.locks lease.checkpoint = none) (distinct : lease.checkpoint ≠ lease.socket) :
    ∃ after, Reachable grant enters after ∧ after.active actor = some lease := by
  let first := { s with locks := put s.locks lease.socket (some actor) }
  have hfirst : Reachable grant enters first :=
    reached.next (.acquire s actor lease.socket (grants s actor lease.socket socket))
  let both := { first with locks := put first.locks lease.checkpoint (some actor) }
  have hboth : Reachable grant enters both :=
    hfirst.next
      (.acquire first actor lease.checkpoint
        (grants first actor lease.checkpoint (by simp [first, put, distinct, checkpoint])))
  refine ⟨{ both with active := put both.active actor (some lease) }, ?_, by simp [put]⟩
  exact
    hboth.next (.enter both actor lease idle (by simp [enters, both, first, put, Ne.symm distinct]))

end Linger.Session.Claim
