module

public section

/-! # Session status — what a listing row reports

**One glyph, one observation.** Every session has exactly one of seven statuses. Each is
something linger saw directly, shown as one glyph, and says what to do next: leave `⣷`, look at
`⣿`, nothing for `⣀`, read or discard `✓` and `!`, resume `~` when wanted, and check `?`. A new
status belongs here only when these seven cannot say what someone needs. Titles and
`ls --summary` count the three that ask for someone: `⣿`, `!` and `?` (`summary`).

The classifier is a pure function of an observation record, so the states
partition the observation space by construction rather than by convention —
`Linger/Display/Proofs/Status.lean` proves the cover, the disjointness, and that every
state is reachable (a state no observation produces would be a lie in the legend).
-/

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

/-- The classifier: a priority cascade. -/
def classify (o : Obs) : Status :=
  if !o.known then .unknown
  else
    match o.exit with
    | some 0 => .exitedOk
    | some _ => .exitedBad
    | none =>
      if !o.daemonUp then .resumable
      else if o.fresh then .working else if o.unseen then .wantsYou else .idle

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

/-- Foreground styles use the terminal's standard palette. Quiet states dim the
default foreground; no background or selection attribute belongs to a status. -/
def style : Status → String
  | .working => "\x1b[36m"
  | .wantsYou | .unknown => "\x1b[33m"
  | .exitedOk => "\x1b[32m"
  | .exitedBad => "\x1b[31m"
  | .idle | .resumable => "\x1b[2;39m"

/-- The statuses that ask for someone, in display order: titles and `ls --summary` count only
these. Ordinary activity and successful completion do not ask for attention. -/
def attention : List Status := [.wantsYou, .exitedBad, .unknown]

/-- Attention groups in display order, retaining only positive exact counts. -/
private def attentionCounts (statuses : List Status) : List (Status × Nat) :=
  attention.filterMap fun status =>
    let count := statuses.count status
    if count == 0 then none else some (status, count)

/-- Compact plain text for prompts and titles: a decimal count and the canonical
icon for each attention group, separated by one space with no trailing newline. -/
def summary (statuses : List Status) : String :=
  String.intercalate " "
    ((attentionCounts statuses).map fun (status, count) => (toString count).push (icon status))

/-- What linger saw, in the words `linger help` gives each status. -/
def seen : Status → String
  | .working => "output right now"
  | .wantsYou => "new output, then it stopped"
  | .idle => "nothing new since you looked"
  | .exitedOk => "ended with status 0"
  | .exitedBad => "ended with a failure status or a signal"
  | .resumable => "not running, saved: attach resumes it"
  | .unknown => "no answer"

/-- The statuses in the order `linger help` lists them: a running program's, an ended one's,
then a session with no program running. -/
def legendOrder : List Status :=
  [.working, .wantsYou, .idle, .exitedOk, .exitedBad, .resumable, .unknown]

/-- The legend `linger help` prints: one line per status, its glyph and what linger saw. -/
def legend : List String := legendOrder.map fun status => s!"{icon status}  {seen status}"

end Linger.Display.Status
