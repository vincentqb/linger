module

public import Linger.Display.CoreSpec

public section

/-! # Session status — what a listing row reports

**One glyph, one observation.** Every session has exactly one of ten statuses. Each is
something linger saw directly, shown as one glyph, and says what to do next: answer `⚑`, see to
the error `!`, leave `⣷` and `⣤`, look at `⣿`, nothing for `⣀`, read or discard `✓` and `✗`,
resume `~` when wanted, and check `?`. A new status belongs here only when these ten cannot say
what someone needs. Titles and `ls --summary` count the five that ask for someone: `⚑`, `⣿`, `✗`,
`!` and `?` (`summary`).

The states, the observation record and the legend live in `Linger/Display/CoreSpec.lean`. The
classifier is a pure function of an observation record, so the states
partition the observation space by construction rather than by convention —
`Linger/Display/Proofs/Status.lean` proves the cover, the disjointness, and that every
state is reachable (a state no observation produces would be a lie in the legend).
-/

namespace Linger.Display.Status

/-- The classifier: a priority cascade. A program that asks for you outranks the progress it
declared, each state its own status, which outranks a command its shell's marks say runs, which
outranks new lines. -/
def classify (o : Obs) : Status :=
  if !o.known then .unknown
  else
    match o.exit with
    | some 0 => .exitedOk
    | some _ => .exitedBad
    | none =>
      if !o.daemonUp then .resumable
      else
        if o.asks then .asks
        else
          match o.progress with
          | some .error => .errored
          | some .paused => .paused
          | some .normal | some .indeterminate => .working
          | none => if o.running then .working else if o.unseen then .wantsYou else .idle

/-- The glyph for a state. All ten are single-column *by our own
`charWidth`*, and East Asian Width neutral or narrow, none an emoji; note that table covers
East-Asian Wide and Fullwidth but not Ambiguous, so `✓` may render double-width under a
CJK-ambiguous locale. The cost there is one column of drift in a listing, not corruption. -/
def icon : Status → Char
  | .unknown => '?'
  | .exitedBad => '✗'
  | .exitedOk => '✓'
  | .resumable => '~'
  | .asks => '⚑'
  | .errored => '!'
  | .paused => '⣤'
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
  | .asks => "asks-you"
  | .errored => "running-error"
  | .paused => "paused"
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
  | "asks-you" => .asks
  | "running-error" => .errored
  | "paused" => .paused
  | "wants-you" => .wantsYou
  | "working" => .working
  | "idle" => .idle
  | _ => .unknown

/-- The name `info` gives a declared progress state, `none` for no progress. -/
def progressName : Option Terminal.Mediation.Progress → String
  | some .normal => "normal"
  | some .error => "error"
  | some .indeterminate => "indeterminate"
  | some .paused => "paused"
  | none => "none"

/-- Back from the name `info` gives a declared progress state: any other name is no progress. -/
def progressOfName : String → Option Terminal.Mediation.Progress
  | "normal" => some .normal
  | "error" => some .error
  | "indeterminate" => some .indeterminate
  | "paused" => some .paused
  | _ => none

/-- A status's style, as the parameters of the SGR sequence that selects it. Foreground styles
use the terminal's standard palette: what asks for someone is yellow, a failure red, success
green and activity cyan. Quiet states dim the default foreground; no background or selection
attribute belongs to a status. -/
def style : Status → List Nat
  | .working => [36]
  | .asks | .wantsYou | .unknown => [33]
  | .exitedOk => [32]
  | .exitedBad | .errored => [31]
  | .idle | .paused | .resumable => [2, 39]

/-- The statuses that ask for someone, in display order: titles and `ls --summary` count only
these. Ordinary activity and successful completion do not ask for attention. -/
def attention : List Status := [.asks, .wantsYou, .exitedBad, .errored, .unknown]

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
  | .asks => "a bell or a notification since you looked"
  | .errored => "says an error stopped it"
  | .working => "says it is working"
  | .paused => "says it is paused"
  | .wantsYou => "new lines since you looked"
  | .idle => "nothing new since you looked"
  | .exitedOk => "ended with status 0"
  | .exitedBad => "ended with a failure status or a signal"
  | .resumable => "not running, saved: attach resumes it"
  | .unknown => "no answer"

/-- The statuses in the order `linger help` lists them: a running program's, the one that asks
for you first, an ended one's, then a session with no program running. -/
def legendOrder : List Status :=
  [.asks, .errored, .working, .paused, .wantsYou, .idle, .exitedOk, .exitedBad, .resumable,
    .unknown]

/-- The legend `linger help` prints: one line per status, its glyph and what linger saw. -/
def legend : List String := legendOrder.map fun status => s!"{icon status}  {seen status}"

end Linger.Display.Status
