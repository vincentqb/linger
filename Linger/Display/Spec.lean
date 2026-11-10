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

namespace Linger.Display.Listing

/-- Where a listing row came from. **A sum type rather than a handful of
`Bool`s on purpose.** The previous signature took `socketPresent`,
`answered` and `ckptLoadable` separately, and a caller passed a literal
`true` for `answered` — so "the daemon did not answer" became unreachable and
a busy session listed as a healthy idle one, even though the theorem about it
was correct. Booleans a caller has to get right are the hazard; each
constructor here carries exactly the facts its case has, so there is no
argument left to pass wrongly. -/
inductive Row where
  /-- A socket accepted the connection; `info` is whatever it replied (possibly
  nothing, if it was too busy). -/
  | live (info : List (String × String))
  /-- No socket, but a checkpoint file is there, and its end record does not say how its
  program ended: the session was interrupted, as by a reboot. -/
  | stale
  /-- No socket, a checkpoint, and an end record saying its program ended with this status, as
  a shell reports it: the session's result, until `kill` discards it. -/
  | ended (status : Nat)
  /-- No socket, and the saved session cannot be read: its end record, which says whether its
  program ended, cannot be read. A checkpoint that will not load would be one too, but the
  listing does not load checkpoints. -/
  | broken
  /-- From a peer's porcelain over ssh: whether the peer lists the session live,
  and the peer's own `status` name, read by `Status.ofName`. -/
  | remote (live : Bool) (peerStatus : String)
  /-- A socket whose daemon holds the name, read from the name's end record instead of asking:
  whether the daemon last saw fresh output, and output since the session was last looked at
  (`Session.Record.published`). -/
  | published (fresh unseen : Bool)
  deriving Repr

end Linger.Display.Listing
