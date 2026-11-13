module

public import Linger.App.CoreSpec

public section

/-! # Linger.App.Capture — the steps of `capture` of a saved session

A capture of a name no live session holds reads the name's checkpoint as every offline reader
does, holding both of its locks, and writes what it rendered only once it has let them go
(`capture_waits_unlocked`): its write waits for whoever reads it, a pager that is not reading or
a pipe nobody reads, and an attach or a resume that starts the session meanwhile waits for the
locks only as long as a load and a render take. The shell runs exactly these steps, in order. -/

namespace Linger.App.Capture

/-- The steps of `capture` of a saved session: take the name's locks, load its checkpoint and
render it, let the locks go, and then write what it rendered. -/
def plan : List Step := [.acquire, .load, .render, .release, .write]

end Linger.App.Capture
