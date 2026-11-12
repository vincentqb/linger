module

public import Os.Spec

public section

/-! # Os.Write — what a full write does after each attempt

A full write writes its bytes in attempts, each from where the last one stopped, and after each
decides what to do next as `next` says. `Os.Shell.writeAll` runs this decision, waiting for the
descriptor when it says so, and the daemon's flushes of a client's and of the program's queue
run it too, waiting instead for their next poll. `packages/os/Os/Proofs/Write.lean` proves that
each outcome of an attempt has its one reaction: a reader that is gone, and only that, stops a
write early; an attempt that wrote nothing, the descriptor full, waits; and every other one goes
on from where it stopped, so no byte is written twice or skipped. -/

namespace Os.Write

/-- What a full write of `size` bytes does after an attempt from offset `off` did `r`: once every
byte is written it is done; after an attempt that wrote bytes, it writes on from where that one
stopped; after one that wrote nothing, as when the descriptor is full, it waits until the
descriptor can take more; and once the reader is gone it stops. -/
def next (size off : Nat) : Result → Next
  | .wrote n => if size ≤ off + n then .done else if n = 0 then .await else .write (off + n)
  | .full => .await
  | .gone => .gone

end Os.Write
