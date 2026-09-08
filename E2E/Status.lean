module

public import E2E.Harness

public section

/-! # E2E.Status — the status column, the unread mechanism end to end

Ported from `tests/status_test.py`.

`unseen` is a property of the SESSION — output arrived while nobody was watching —
so the two transitions that matter are: attaching marks a session seen, and output
while detached marks it unread again. Both go through the counter pair in
`Session.State` (`outSeq`/`lookSeq`), and this pins them against the rendered
porcelain rather than against the internals.

WHAT THE PORT STRENGTHENS. The Python compared the porcelain column against the
string literals `'wants-you'` and `'idle'`, and the human column against a
hardcoded braille glyph. All three are `Linger.Core.Status`' own output, so
renaming a state would have left the assertions passing against a column that no
longer exists. Here the comparison is against the `Status` constructors (through
`Env.status`, which reads `ofName`) and against `Status.icon` itself, so the same
rename is a compile error. `E2E.Watch` covers the one transition this suite never
exercised: `linger watch` also marks a session seen. -/

namespace E2E.Status

open E2E.Harness
open Linger.Core.Status (Status)

def run : IO UInt32 := do
  let e ← Env.make "status"
  let mut f := 0
  -- a long-lived child, so nothing exits under us and the row stays classifiable
  -- as idle/wants-you rather than exited-ok
  let _ ← e.cli #["run", "st", "sh", "-c", "sleep 60"]
  IO.sleep 1500
  -- 1. a session nobody has watched, that has produced output, is unread
  f := f + (← expect ((← e.status "st") == Status.wantsYou) "unwatched output reads wants-you")
  -- 2. attaching marks it seen: detach with no further output and it is idle.
  let c ← e.spawn #["attach", "st"] 80 24
  IO.sleep 1500
  c.detach
  IO.sleep 800
  c.bye (sendDetach := false)
  f := f + (← expect ((← e.status "st") == Status.idle) "attach marks the session seen")
  -- 3. output while detached makes it unread again
  let _ ← e.cli #["send", "st", "echo", "later"]
  IO.sleep 1200
  f := f + (← expect ((← e.status "st") == Status.wantsYou) "output while away reads wants-you")
  -- `behind` is `toString (Session.behind s)`, a decimal `Nat`, so parse it
  -- rather than compare the string to "0" as the Python did: `!= "0"` also
  -- passes on a field that stopped being a number at all.
  let behind := ((← e.field "st" "behind").getD "0").toNat?.getD 0
  f := f + (← expect (behind > 0) "behind counts unseen output")
  -- 4. the human column renders one glyph for it — `Status.icon`'s own glyph,
  -- which is what `Listing.humanRow` puts at the head of the row.
  let human ← e.out #["ls"]
  f :=
    f +
      (←
        expect (has human (String.singleton (Linger.Core.Status.icon Status.wantsYou)))
            "human listing shows the wants-you glyph")
  e.killAll #["st"]
  verdict f

end E2E.Status
