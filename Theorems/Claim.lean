module

/-! Ownership of socket and checkpoint resources across arbitrary interleavings.

A resource identifies a stable lock inode, not a pathname string. Successful
exclusive acquisition requires that resource to be free. Failed acquisition
leaves the state unchanged, so a starting daemon that retries a held lock for a
short time takes only `unchanged` steps until it acquires. A daemon or offline
reader enters only after holding both resources, and releases them only after
leaving and completing its cleanup.

The model permits acquisition, release and later reuse by different processes.
Its assumptions require cooperating processes, lock files that are never
unlinked or replaced, and a filesystem that implements the locking contract.
The runtime correspondence is tested and source-gated, not proved here.
-/

namespace Linger.Core.Claim

/-- The socket and checkpoint resources a daemon or offline reader claims together. -/
structure Lease where
  socket : Nat
  checkpoint : Nat
  deriving DecidableEq

/-- `resource` is the lease's socket or checkpoint resource. -/
def Lease.Uses (lease : Lease) (resource : Nat) : Prop :=
  resource = lease.socket ∨ resource = lease.checkpoint

/-- `locks` maps each resource to the actor holding its lock; `active` maps each actor to
the lease it has entered. -/
structure State where
  locks : Nat → Option Nat
  active : Nat → Option Lease

/-- No lock is held and no actor has entered. -/
def initial : State := ⟨fun _ => none, fun _ => none⟩

/-- `map` updated at `key` to `value`. -/
def put {α : Type} (map : Nat → α) (key : Nat) (value : α) : Nat → α := fun index =>
  if index = key then value else map index

/-- The OS acquisition contract and the application's lifetime protocol.
`enter` covers both daemon ownership and an offline reader's critical section.
`leave` means all resource access and cleanup have finished. -/
inductive Step : State → State → Prop where
  |
  acquire (s : State) (actor resource : Nat) (free : s.locks resource = none) :
    Step s { s with locks := put s.locks resource (some actor) }
  |
  enter (s : State) (actor : Nat) (lease : Lease) (idle : s.active actor = none)
    (socket : s.locks lease.socket = some actor)
    (checkpoint : s.locks lease.checkpoint = some actor) :
    Step s { s with active := put s.active actor (some lease) }
  | leave (s : State) (actor : Nat) : Step s { s with active := put s.active actor none }
  |
  release (s : State) (actor resource : Nat) (owned : s.locks resource = some actor)
    (idle : s.active actor = none) : Step s { s with locks := put s.locks resource none }
  | unchanged (s : State) : Step s s

/-- The states reached from `initial` by finitely many `Step`s. -/
inductive Reachable : State → Prop where
  | initial : Reachable initial
  | next {before after} (reached : Reachable before) (step : Step before after) : Reachable after

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

end Linger.Core.Claim
