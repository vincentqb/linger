module

public import Linger.App.Spec
import Linger.Session

public section

/-! # Linger.App.Wait — what `wait` answers from what it hears

`wait` looks at a name until it can answer (`decide`): how the session ended, from its daemon or,
with no daemon to answer, from the name's end record, which is its program's ending or, for a
session a signal to its daemon saved, `interrupted`; that no session took the name; that its time
limit passed; or that it could not find out. The last only when the name stays
held, with no daemon answering, for `heldNameMs` from the look that first found it so, which
covers a daemon's ending: its drain and its program's stop. -/

namespace Linger.App.Wait

/-- How long `wait` keeps looking at a name another process holds while no daemon answers on
it, from the look that first found it so: past an ending daemon's drain
(`Session.drainTimeoutMs`) and its program's stop, a second for each signal of
`Session.ending`, with three seconds to spare for the end record to reach the disk. -/
def heldNameMs : Nat := Linger.Session.drainTimeoutMs + 5000

/-- What `wait` does after a look that heard `heard` at `now` on the monotonic clock, with an
optional `deadline` on the same clock and `heldSince`, when the looks before this one first found
the name held with no daemon answering. An ending, from the daemon or the end record, is the
answer (`Answer.ofEnding`); so are a refusal and a name no session took. A held name is looked at again until it
has been held for `heldNameMs`, and then `wait` could not find out; silence and a held name end
in `timedOut` once the deadline has passed. -/
def decide (deadline heldSince : Option Nat) (now : Nat) : Heard → Next
  | .ended ending => .answer (Answer.ofEnding ending)
  | .status status => .answer (.program status)
  | .refused => .answer .notDone
  | .recorded none => .answer .notFound
  | .recorded (some ending) => .answer (Answer.ofEnding ending)
  | .silent => if deadline.any (· ≤ now) then .answer .timedOut else .again none
  | .held =>
    let since := heldSince.getD now
    if since + heldNameMs ≤ now then .answer .failed
    else if deadline.any (· ≤ now) then .answer .timedOut else .again (some since)

end Linger.App.Wait
