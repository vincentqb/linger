module

public section

/-! # What the OS boundary's headlines are stated in

How a polling wait runs against the monotonic clock, and what one write attempt reports and what a
full write does after it. Bodies are exposed: each definition here is its own specification. The
world claim the waits rest on, that a sleep lasts at least as long as it was asked to, is
`Os.Wait.Lasts`, beside the foreign declarations in `Os.WorldSpec`; the claims about a session's
processes and descriptors are the session's, in `Linger.Session.WorldSpec`. -/

namespace Os.Wait

/-- A wait from `now` gives up after `looks` looks: it looks, and while `next` asks for a sleep
of `ms`, sleeps until the clock reads `after now ms` and looks again, until `next` reports that
its deadline has passed. -/
inductive Ends (next : Nat → Option Nat) (after : Nat → Nat → Nat) : Nat → Nat → Prop where
  /-- The deadline has passed: this look is the last. -/
  | missed {now : Nat} (h : next now = none) : Ends next after now 1
  /-- A sleep of `ms`, then the looks that follow. -/
  |
  slept {now ms looks : Nat} (h : next now = some ms)
    (rest : Ends next after (after now ms) looks) : Ends next after now (looks + 1)

end Os.Wait

namespace Os.Write

/-- What one write attempt did, as `Os.Shell.write` reports it, one value for each outcome. -/
inductive Result where
  /-- It wrote this many bytes, from where it was asked to begin. -/
  | wrote (n : Nat)
  /-- It wrote nothing: the descriptor is nonblocking and takes no more until its reader reads,
  which the operating system reports as `EAGAIN`. -/
  | full
  /-- It wrote nothing: the reader is gone, which the operating system reports as `EPIPE` or
  `ECONNRESET`, or as `EIO` from a terminal whose other side has closed. -/
  | gone
  deriving Repr, DecidableEq

/-- What a full write does after an attempt. -/
inductive Next where
  /-- Write again, from this offset. -/
  | write (off : Nat)
  /-- Wait until the descriptor can take more, then write again from where the attempt began. -/
  | await
  /-- Stop: every byte is written. -/
  | done
  /-- Stop: the reader is gone, so the bytes not written yet never will be. -/
  | gone
  deriving Repr, DecidableEq

/-- A wrong decision: it takes a full descriptor for a reader that is gone, which stops the write,
and otherwise decides as a full write must. The headline about full writes is shown to reject
it. -/
@[expose]
def fullGone (size off : Nat) : Result → Next
  | .wrote n => if size ≤ off + n then .done else if n = 0 then .gone else .write (off + n)
  | .full | .gone => .gone

end Os.Write
