module

import SoftwareChallenge.Commands

public section

/-! # Linger.Os.Spec — what the operating system does when linger starts a program

How the operating system answers a request to start a program in a new terminal, and the world
claim the headline theorems rest on about the program it starts. -/

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
