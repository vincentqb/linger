/-! # Session status — what a listing row reports

One glyph per row, and the design constraint that produced this set is
**two states share a glyph only when they call for the same action**. That
rule settled four separate merges: a bell and unread output both mean "go
look"; waiting-at-a-prompt is the same observation as "was working, now
silent" unless the shell emits OSC 133, and even then the response is
identical; a busy daemon and an unloadable checkpoint both mean "we cannot
tell you the truth about this row". What stayed distinct is where the
response differs: a clean exit versus a failed one, idle versus wants-you.

The classifier is a pure function of an observation record, so the states
partition the observation space by construction rather than by convention —
`Theorems/Status.lean` proves the cover, the disjointness, and that every
state is reachable (a state no observation produces would be a lie in the
legend).
-/

namespace Zmx.Core.Status

/-- Seven mutually exclusive states, in priority order: a row shows the
first one that applies. -/
inductive Status where
  /-- `?` — the checkpoint will not load, or the daemon did not answer. -/
  | unknown
  /-- `!` — the program exited nonzero, or was killed by a signal. -/
  | exitedBad
  /-- `✓` — the program exited 0. It did its job. -/
  | exitedOk
  /-- `~` — no daemon, but a checkpoint is on disk: attach restores it. -/
  | resumable
  /-- `⣿` — output or a bell since you last detached, now quiet. -/
  | wantsYou
  /-- `⣷` — output right now. -/
  | working
  /-- `⣀` — nothing since you last looked. -/
  | idle
  deriving DecidableEq, Repr, Inhabited

/-- What a row is classified from. Booleans the runtime computes, so the
classifier depends on nothing else — no clock, no filesystem. -/
structure Obs where
  /-- We got a trustworthy answer about this row. -/
  known : Bool := true
  /-- The session's socket is live. -/
  daemonUp : Bool := true
  /-- The exit status, once the child is gone. Only the daemon can report
  it, so `some _` presupposes `daemonUp`. -/
  exit : Option Nat := none
  /-- Output within the "working" window. -/
  fresh : Bool := false
  /-- Output, or a bell, since this viewer last detached. -/
  unseen : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- The classifier: a priority cascade. -/
def classify (o : Obs) : Status :=
  if !o.known then .unknown
  else match o.exit with
    | some 0 => .exitedOk
    | some _ => .exitedBad
    | none =>
      if !o.daemonUp then .resumable
      else if o.fresh then .working
      else if o.unseen then .wantsYou
      else .idle

/-- The glyph for a state. All seven are single-column *by our own
`charWidth`*; note that table covers East-Asian Wide and Fullwidth but not
Ambiguous, so `✓` may render double-width under a CJK-ambiguous locale. The
cost there is one column of drift in a listing, not corruption. -/
def icon : Status → Char
  | .unknown => '?'
  | .exitedBad => '!'
  | .exitedOk => '✓'
  | .resumable => '~'
  | .wantsYou => '⣿'
  | .working => '⣷'
  | .idle => '⣀'

/-- The machine-readable name, for `--porcelain`. Stable: recipes parse it,
so it is a contract and not a label. -/
def name : Status → String
  | .unknown => "unknown"
  | .exitedBad => "exited-bad"
  | .exitedOk => "exited-ok"
  | .resumable => "resumable"
  | .wantsYou => "wants-you"
  | .working => "working"
  | .idle => "idle"

/-- Back from the porcelain name. Total: an unrecognised name is `unknown`,
which is the safe direction -- a row we cannot interpret is reported as one we
cannot interpret. Left inverse of `name` (`ofName_name`). -/
def ofName : String → Status
  | "exited-bad" => .exitedBad
  | "exited-ok" => .exitedOk
  | "resumable" => .resumable
  | "wants-you" => .wantsYou
  | "working" => .working
  | "idle" => .idle
  | _ => .unknown

end Zmx.Core.Status
