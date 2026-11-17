module

public import Linger.App.CoreSpec

public section

/-! # Linger.App.Capture — the steps of `capture` of a saved session

A capture of a name no live session holds reads the name's checkpoint as every offline reader
does, holding both of its locks, and writes what it rendered only once it has let them go
(`capture_waits_unlocked`): its write waits for whoever reads it, a pager that is not reading or
a pipe nobody reads, and an attach or a resume that starts the session meanwhile waits for the
locks only as long as a load and a render take. The shell runs the phases `phases` cuts the
steps into, in order, each run of steps between an `acquire` and the next `release` inside one
hold of the locks. -/

namespace Linger.App.Capture

/-- The steps of `capture` of a saved session: take the name's locks, load its checkpoint and
render it, let the locks go, and then write what it rendered. -/
def plan : List Step := [.acquire, .load, .render, .release, .write]

/-- The phases of `steps` once `held`, the steps gathered since an unmatched `acquire`, if any:
the steps from an `acquire` to the next `release`, or to the end, run in one hold of the locks, a
second `acquire` or an unmatched `release` changes nothing, and every other step runs alone,
holding no lock. -/
def phasesFrom : Option (List Step) → List Step → List Phase
  | none, [] => []
  | some inside, [] => [.locked inside]
  | held, step :: rest =>
    match step, held with
    | .acquire, none => phasesFrom (some []) rest
    | .acquire, some inside => phasesFrom (some inside) rest
    | .release, some inside => .locked inside :: phasesFrom none rest
    | .release, none => phasesFrom none rest
    | step, some inside => phasesFrom (some (inside ++ [step])) rest
    | step, none => .unlocked step :: phasesFrom none rest

/-- The phases the shell runs a plan's steps in, holding no lock when it begins
(`capture_waits_unlocked`). -/
def phases (steps : List Step) : List Phase := phasesFrom none steps

end Linger.App.Capture
