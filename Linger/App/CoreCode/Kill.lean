module

public import Linger.App.CoreSpec
import Linger.App.CoreCode.Wait

public section

/-! # Linger.App.Kill — what `kill` answers from what it hears

Once the daemon `kill` asked to end a session has taken the request, `kill` looks at the name
until it can answer (`decide`): that it ended the session, once no process holds the name or a
newer session does, which can take it only after the session gave it up; that the session has
not ended, once the daemon it asked still answers as itself; or that it could not find out, once
a process it cannot tell from that daemon holds the name. The last two only once `wait`'s
patience for an ending, `Wait.heldNameMs`, has passed since the daemon took the request, which
covers a daemon's ending: its drain and its program's stop. -/

namespace Linger.App.Kill

/-- What `kill` does after a look that heard `heard` at `now` on the monotonic clock, the daemon
it asked having taken the request at `taken` on the same clock: the session ended when no process
holds the name or a newer session does; while the daemon it asked answers as itself, or a process
it cannot tell from it holds the name, it looks again until `Wait.heldNameMs` has passed since
`taken`, and then answers that the session has not ended, or that it could not find out. -/
def decide (taken now : Nat) : Heard → Next
  | .free | .newer => .answer .done
  | .asked => if taken + Wait.heldNameMs ≤ now then .answer .refused else .again
  | .held => if taken + Wait.heldNameMs ≤ now then .answer .unknown else .again

end Linger.App.Kill
