module

public import Linger.Display.Spec

public section

/-! # Session status — what a listing row reports

**One glyph, one observation.** Every session has exactly one of seven statuses. Each is
something linger saw directly, shown as one glyph, and says what to do next: leave `⣷`, look at
`⣿`, nothing for `⣀`, read or discard `✓` and `!`, resume `~` when wanted, and check `?`. A new
status belongs here only when these seven cannot say what someone needs. Titles and
`ls --summary` count the three that ask for someone: `⣿`, `!` and `?` (`summary`).

The states, the observation record and the legend live in `Linger/Display/Spec.lean`. The
classifier is a pure function of an observation record, so the states
partition the observation space by construction rather than by convention —
`Linger/Display/Proofs/Status.lean` proves the cover, the disjointness, and that every
state is reachable (a state no observation produces would be a lie in the legend).
-/

namespace Linger.Display.Status

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

/-- A status's style, as the parameters of the SGR sequence that selects it. Foreground styles
use the terminal's standard palette. Quiet states dim the default foreground; no background or
selection attribute belongs to a status. -/
def style : Status → List Nat
  | .working => [36]
  | .wantsYou | .unknown => [33]
  | .exitedOk => [32]
  | .exitedBad => [31]
  | .idle | .resumable => [2, 39]

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
