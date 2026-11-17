module

public import Linger.Display.CoreSpec

public section

/-! # Session status — what a listing row reports

**Two columns, two facts.** A row shows whether there is something for you since you last
looked, its attention: `⚑` a bell or a notification, `∙` new lines or an ending nobody saw, blank
neither, an ask winning when both hold. Then it shows what the session is, its state: `!` an
error its program declared, `⣷` working, `⣤` paused, `⣀` running with nothing declared, `~`
saved, `✓` and `✗` its endings and `?` no answer. Each column reads its own signals alone
(`attention_independent`, `state_independent`), so a session that rang while it works shows `⚑ ⣷`.
Titles and `ls --summary` count attention alone (`summary`).

The attentions, the states, the observation record and the legend live in
`Linger/Display/CoreSpec.lean`. The classifier is a pure function of an observation record, so the
statuses partition the observation space by construction rather than by convention —
`Linger/Display/Proofs/Status.lean` proves the cover, the disjointness, and that every
status is reachable (a status no observation produces would be a lie in the legend).
-/

namespace Linger.Display.Status

/-- An observation's attention: an ask wins over new lines. -/
def attentionOf (o : Obs) : Attention :=
  if o.asks then .asked else if o.unseen then .unread else .none

/-- An observation's state: a priority cascade. No answer outranks an ending, which outranks a
missing daemon, which outranks the progress the program declared, each state its own, which
outranks a command its shell's marks say runs. -/
def stateOf (o : Obs) : State :=
  if !o.known then .unknown
  else
    match o.exit with
    | some 0 => .exitedOk
    | some _ => .exitedBad
    | none =>
      if !o.daemonUp then .resumable
      else
        match o.progress with
        | some .error => .errored
        | some .paused => .paused
        | some .normal | some .indeterminate => .working
        | none => if o.running then .working else .idle

/-- The classifier: each column from its own sources. -/
def classify (o : Obs) : Status := ⟨attentionOf o, stateOf o⟩

/-- The mark for an attention, blank for none. Both marks are single-column *by our own
`charWidth`*, and East Asian Width neutral, none an emoji: `∙` is U+2219, as `⚑` is U+2691. -/
def mark : Attention → Char
  | .asked => '⚑'
  | .unread => '∙'
  | .none => ' '

/-- The glyph for a state. All eight are single-column *by our own
`charWidth`*, and East Asian Width neutral or narrow, none an emoji; note that table covers
East-Asian Wide and Fullwidth but not Ambiguous, so `✓` may render double-width under a
CJK-ambiguous locale. The cost there is one column of drift in a listing, not corruption. -/
def icon : State → Char
  | .unknown => '?'
  | .exitedBad => '✗'
  | .exitedOk => '✓'
  | .resumable => '~'
  | .errored => '!'
  | .paused => '⣤'
  | .working => '⣷'
  | .idle => '⣀'

/-- A state's machine-readable name, the porcelain's `status`. Stable: recipes parse it,
so it is a contract and not a label. -/
def name : State → String
  | .unknown => "unknown"
  | .exitedBad => "exited-bad"
  | .exitedOk => "exited-ok"
  | .resumable => "resumable"
  | .errored => "running-error"
  | .paused => "paused"
  | .working => "working"
  | .idle => "idle"

/-- Back from the porcelain name. Total: an unrecognised name is `unknown`,
which is the safe direction -- a row we cannot interpret is reported as one we
cannot interpret. Left inverse of `name` (`ofName_name`). -/
def ofName : String → State
  | "exited-bad" => .exitedBad
  | "exited-ok" => .exitedOk
  | "resumable" => .resumable
  | "running-error" => .errored
  | "paused" => .paused
  | "working" => .working
  | "idle" => .idle
  | _ => .unknown

/-- An attention's machine-readable name, the porcelain's `attention`. -/
def attentionName : Attention → String
  | .asked => "asked"
  | .unread => "unread"
  | .none => "none"

/-- Back from the porcelain's `attention`: any other name is none. Left inverse of
`attentionName` (`ofAttentionName_attentionName`). -/
def ofAttentionName : String → Attention
  | "asked" => .asked
  | "unread" => .unread
  | _ => .none

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

/-- A state's style, as the parameters of the SGR sequence that selects it. Foreground styles
use the terminal's standard palette: what linger could not read is yellow, a failure red, success
green and activity cyan. Quiet states dim the default foreground; no background or selection
attribute belongs to a status. -/
def style : State → List Nat
  | .working => [36]
  | .unknown => [33]
  | .exitedOk => [32]
  | .exitedBad | .errored => [31]
  | .idle | .paused | .resumable => [2, 39]

/-- An attention's style: what asks for someone is yellow, and a blank mark has none. -/
def markStyle : Attention → Option (List Nat)
  | .asked | .unread => some [33]
  | .none => none

/-- The attentions titles and `ls --summary` count, in display order: every attention but none. -/
def counted : List Attention := [.asked, .unread]

/-- Attention groups in display order, retaining only positive exact counts. -/
private def attentionCounts (attentions : List Attention) : List (Attention × Nat) :=
  counted.filterMap fun a =>
    let count := attentions.count a
    if count == 0 then none else some (a, count)

/-- Compact plain text for prompts and titles: a decimal count and the canonical mark for each
attention group, separated by one space with no trailing newline. -/
def summary (attentions : List Attention) : String :=
  String.intercalate " "
    ((attentionCounts attentions).map fun (a, count) => (toString count).push (mark a))

/-- What linger heard, in the words `linger help` gives each attention that has a mark. -/
def heard : Attention → String
  | .asked => "a bell or a notification since you looked"
  | .unread => "new lines since you looked, or an ending nobody saw"
  | .none => "nothing since you looked"

/-- What linger saw, in the words `linger help` gives each state. -/
def seen : State → String
  | .errored => "says an error stopped it"
  | .working => "says it is working"
  | .paused => "says it is paused"
  | .idle => "runs and declares nothing"
  | .exitedOk => "ended with status 0"
  | .exitedBad => "ended with a failure status or a signal"
  | .resumable => "not running, saved: attach resumes it"
  | .unknown => "no answer"

/-- The states in the order `linger help` lists them: a running program's, an ended one's, then
a session with no program running. -/
def legendOrder : List State :=
  [.errored, .working, .paused, .idle, .exitedOk, .exitedBad, .resumable, .unknown]

/-- The legend `linger help` prints: an `Attention` block, one line per mark, then a `State`
block, one line per state, each line its glyph and what linger heard or saw. -/
def legend : List String :=
  "Attention" :: counted.map (fun a => s!"{mark a}  {heard a}") ++
    "State" :: legendOrder.map fun st => s!"{icon st}  {seen st}"

end Linger.Display.Status
