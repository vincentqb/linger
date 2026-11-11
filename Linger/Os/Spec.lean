module

import SoftwareChallenge.Commands

public section

/-! # Linger.Os.Spec — what the operating system does when linger starts and ends a program

How the operating system answers a request to start a program in a new terminal, and the world
claims the headline theorems rest on about the program it starts and about the signals that end
a session's processes. -/

namespace Linger.Os.Spawn

/-- Why a program could not start in a new terminal, with the operating system's words. -/
inductive Failure where
  /-- Its directory could not be entered. -/
  | directory (why : String)
  /-- No program of its name was found. -/
  | notFound (why : String)
  /-- Its program was found and could not be run. -/
  | notRunnable (why : String)
  deriving Repr, DecidableEq

/-- What a program sees of its start: its words, the directory it runs in, and each environment
variable's value, `none` for a variable that is unset. -/
structure Started where
  /-- Its words, its program's name first. -/
  argv : List String
  /-- The directory it runs in. -/
  dir : String
  /-- Each environment variable's value. -/
  env : String → Option String

/-- The operating system runs what linger asks, and nothing else. A program that `start dir prog
args extra` starts sees the words `prog` and then `args`, runs in `dir`, and reads each variable
as the last pair of `extra` that sets it, or else as `inherited` has it: the environment of the
command that asked for the session, which its daemon runs with. A program that cannot start is
`none`. A started program that sees other words, another directory or another value falsifies
it. -/
WorldClaim Runs (inherited : String → Option String)
  (start : String → String → Array String → List (String × String) → Option Started) :=
  ∀ dir prog args extra started,
    start dir prog args extra = some started →
      started.argv = prog :: args.toList ∧
        started.dir = dir ∧
        ∀ key, started.env key = (extra.reverse.lookup key).orElse fun _ => inherited key

end Linger.Os.Spawn

namespace Linger.Os.Signal

/-- SIGKILL ends every process it reaches within a second. `after sig ms alive` is what still
runs of the processes `alive` once linger sent them signal `sig` and waited `ms` milliseconds:
the processes of the program's terminal session that run as linger's user, which are all a
signal reaches. A signal ends some of them, all or none, and brings none back; SIGKILL ends them
all once linger waited a second. A process that outlives that wait, as one stuck in the kernel
does, falsifies it. A process that left the session with `setsid`, or runs as another user, is
not one of `alive`; on macOS, and on Linux before 5.3, a pid freed and reused between reading
its session and signalling it could receive the signal. -/
WorldClaim Ends (after : UInt32 → Nat → List Nat → List Nat) :=
  (∀ sig ms alive, ∀ p ∈ after sig ms alive, p ∈ alive) ∧
    ∀ ms alive, 1000 ≤ ms → after 9 ms alive = []

end Linger.Os.Signal

namespace Linger.Os.Poll

/-- poll(2) sleeps until an event or its timeout. `returns timeout` is when a poll with that
timeout, whose descriptors stay quiet, returns: after `timeout` milliseconds for a timeout from 0
to the largest `Int32`, and never for -1. A quiet poll that returns early, or that a timeout of
-1 lets return, falsifies it; so would a signal that interrupts it, but the only signal a daemon
handles, SIGCHLD, also makes its child-end descriptor ready. -/
WorldClaim Sleeps (returns : Int32 → Option Nat) :=
  returns (-1) = none ∧ ∀ ms ≤ 2147483647, returns (Int32.ofNat ms) = some ms

end Linger.Os.Poll
