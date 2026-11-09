module

public section

/-! # What the status headline theorems mean

A session's status says what linger saw of it, in one glyph: the seven statuses, the observation
a listing row is classified from, and the legend line each status stands for, written as
predicates on that observation independently of the classifier that computes them. -/

namespace Linger.Display.Status

/-- Seven mutually exclusive states, in priority order: a row shows the
first one that applies. -/
inductive Status where
  /-- `?` — no answer: the daemon did not answer, or the saved session could not be read. -/
  | unknown
  /-- `!` — the program ended any other way: a nonzero exit, a signal, or an ending linger did
  not see. -/
  | exitedBad
  /-- `✓` — the program exited 0. It did its job. -/
  | exitedOk
  /-- `~` — no daemon, but a checkpoint is on disk whose program was interrupted before it
  ended: attach resumes it. -/
  | resumable
  /-- `⣿` — new output since the session was last looked at, a bell included, then it stopped. -/
  | wantsYou
  /-- `⣷` — output right now. -/
  | working
  /-- `⣀` — nothing new since you last looked. -/
  | idle
  deriving DecidableEq, Repr, Inhabited

/-- What a row is classified from. Booleans the runtime computes, so the
classifier depends on nothing else — no clock, no filesystem. -/
structure Obs where
  /-- We got a trustworthy answer about this row. -/
  known : Bool := true
  /-- The session's socket is live. -/
  daemonUp : Bool := true
  /-- The status a shell reports for how the program ended, once it has: from the daemon while
  it ends, then from the name's end record, which a socket-less row reads. -/
  exit : Option Nat := none
  /-- Output within the "working" window. -/
  fresh : Bool := false
  /-- Output, or a bell, since the session was last looked at (attach, output while
  attached, or capture). -/
  unseen : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The legend, as predicates on an observation: the observation each status's line in
`linger help` describes. -/
@[expose]
def Is : Status → Obs → Prop
  | .unknown, o => o.known = false
  | .exitedOk, o => o.known = true ∧ o.exit = some 0
  | .exitedBad, o => o.known = true ∧ ∃ n, o.exit = some n ∧ n ≠ 0
  | .resumable, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = false
  | .working, o => o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = true
  | .wantsYou, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = false ∧ o.unseen = true
  | .idle, o =>
    o.known = true ∧ o.exit = none ∧ o.daemonUp = true ∧ o.fresh = false ∧ o.unseen = false

end Linger.Display.Status
