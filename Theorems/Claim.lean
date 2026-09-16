module

public import Linger.Core.Name

public section

/-! # §Claim — mutual exclusion, relative to exactly one assumption

Can an *advisory* lock give us a theorem? Yes, but only a conditional
one — and that is the point rather than a weakness. An OS primitive
cannot be proved in Lean; what can be done is to state its contract as
a hypothesis, prove the protocol correct **given** that hypothesis, and
thereby name precisely what is being trusted. Everything outside the
hypothesis is proved; everything inside it is a one-line claim about
the kernel that a reader can check against `flock(2)`.

The model is a trace of `(agent, action)` events. `Exclusive` is the
kernel's side of the bargain: at most one agent ever completes a
`lock`. That is what `flock(LOCK_EX | LOCK_NB)` buys, and it holds only
while three side conditions hold — all three are code properties, not
kernel ones, so they are reviewable and testable:

1. nobody releases the lock early (we hold the fd for process life),
2. nobody unlinks the lock file (a newcomer would lock a fresh inode
   while the owner still held the old one),
3. the lock file is on a filesystem where `flock` works — false on NFS,
   which is why `Paths.socketDir` defaults to local storage.

`Guarded` is our side: an agent only mutates the shared name — unlink a
stale socket, bind a new one — if it holds the lock. The theorem is
that the two together give at most one owner of a session name.

Scope: this is a model of the claim sequence in `Linger.Runtime.Daemon.serve`,
not an extraction of it. The correspondence is by inspection (four
lines of `serve`), and it is pinned from the outside by
`E2E/Robust.lean` (ported from `tests/robust_test.py`), which races eight daemons over a stale socket
and requires exactly one survivor. §Claim's value is that it makes the
trust boundary explicit and would catch a reordering — not that it
verifies the runtime.
-/

namespace Linger.Core.Claim

/-- What an agent can do to a session name. -/
inductive Act where
  /-- acquired the name lock (`flock(LOCK_EX|LOCK_NB)` succeeded) -/
  | lock
  /-- connected to the socket to see whether a live daemon answers -/
  | probe
  /-- removed a socket believed stale — mutates the shared name -/
  | unlinkStale
  /-- bound the socket: became the owner — mutates the shared name -/
  | bind
  deriving Repr, DecidableEq, Inhabited

abbrev Trace := List (Nat × Act)

/-- The mutating actions: the ones that need the lock. -/
def Act.mutates : Act → Bool
  | .unlinkStale | .bind => true
  | .lock | .probe => false

/-- **Our obligation.** An agent that mutates the shared name appears in
the trace holding the lock. -/
def Guarded (t : Trace) : Prop := ∀ e ∈ t, e.2.mutates = true → (e.1, Act.lock) ∈ t

/-- **The kernel's obligation** (the assumption; see the header). At most
one agent ever completes a lock. -/
def Exclusive (t : Trace) : Prop := ∀ i j, (i, Act.lock) ∈ t → (j, Act.lock) ∈ t → i = j

/-- §Claim: at most one agent binds the socket — so a session name has
at most one owner, and no daemon can be left holding a pty that nobody
can reach by name. -/
theorem at_most_one_owner {t : Trace} (hg : Guarded t) (he : Exclusive t) :
    ∀ i j, (i, Act.bind) ∈ t → (j, Act.bind) ∈ t → i = j := by
  intro i j hi hj
  exact he i j (hg _ hi rfl) (hg _ hj rfl)

/-- The same argument covers unlinking: two agents cannot both decide a
socket is stale and remove it. This is the exact hazard the lock was
added for — one daemon deleting another's live socket. -/
theorem at_most_one_unlinker {t : Trace} (hg : Guarded t) (he : Exclusive t) :
    ∀ i j, (i, Act.unlinkStale) ∈ t → (j, Act.unlinkStale) ∈ t → i = j := by
  intro i j hi hj
  exact he i j (hg _ hi rfl) (hg _ hj rfl)

/-- And the owner is the lock holder, never a bystander. -/
theorem owner_holds_lock {t : Trace} (hg : Guarded t) :
    ∀ i, (i, Act.bind) ∈ t → (i, Act.lock) ∈ t := fun _ hi => hg _ hi rfl

/-! ## Our sequence satisfies the obligation

`serve` runs exactly this, in this order. Both facts below are checked
by `decide`, so reordering the description fails the build; reordering
the *code* is caught by `E2E/Robust.lean` (ported from `tests/robust_test.py`). -/

def ourClaim : List Act := [.lock, .probe, .unlinkStale, .bind]

/-- One agent following `ourClaim` is `Guarded`. -/
theorem ourClaim_guarded (a : Nat) : Guarded (ourClaim.map (fun act => (a, act))) := by
  intro e he hm
  simp only [ourClaim, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at he ⊢
  left
  rcases he with h | h | h | h <;> subst h <;>
    first
    | rfl
    | simp [Act.mutates] at hm

/-- The lock comes *first*: no mutation is even attempted before it, so
a failed lock cannot leave a half-claimed name behind. -/
theorem ourClaim_lock_first :
    (ourClaim.takeWhile (fun a => a.mutates == false)).contains Act.lock = true := by decide

/-- Nothing mutating precedes the lock. -/
theorem ourClaim_no_early_mutation :
    ((ourClaim.takeWhile (· != Act.lock)).all (fun a => a.mutates == false)) = true := by decide

/-! ## What §Claim does not say

* Nothing about *liveness*: a daemon that loses the race exits, and the
  client that spawned it finds the winner's socket by polling. That is
  a runtime property, tested rather than proved.
* Nothing across hosts. `flock` is per-kernel and unix sockets are
  host-local, so a socket directory shared over a network filesystem
  breaks `Exclusive` and this theorem says nothing. Local storage is a
  precondition, documented at `Paths.socketDir`.
* Nothing about non-cooperating processes. The lock is advisory: `rm`
  can still delete a live socket. The guarantee is among `linger`
  daemons, which is the whole population that claims names.
-/

end Linger.Core.Claim
