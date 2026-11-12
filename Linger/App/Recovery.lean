module

public import Linger.App.Spec
public import Terminal.Vt
import Linger.Session.Checkpoint

public section

/-! # Linger.App.Recovery — what a command does with a saved session

A name no live session holds may have a checkpoint: what a detach, an ended program or the
cadence last saved. A command that may start a session, as `attach` does, starts a new one only
when there is no file; one that may not, as `resume` and the offline readers, answers `notFound`
then. A file whose bytes decode resumes the session they saved. A file whose bytes do not decode
is never taken for no file: the command starts nothing, leaves it as it is and answers `notDone`,
so a torn or emptied file, or one in a newer format, never costs the session itself, and `kill`
discards it (`recovery_exact`). -/

namespace Linger.App.Recovery

/-- What a command does with a name no live session holds, from the bytes of its checkpoint,
`none` when there is no file: start a new session when there is none and `create` allows it,
resume the session the bytes decode to (`Checkpoint.loadBytes`), and otherwise start nothing,
answering `notFound` for no file and `notDone` for bytes that do not decode. -/
def decide (create : Bool) :
    Option ByteArray → Recovery (Linger.Session.Checkpoint.Ckpt Terminal.Vt.Vt)
  | none => if create then .fresh else .refuse .notFound
  | some bytes => ((Linger.Session.Checkpoint.loadBytes bytes).map .resume).getD (.refuse .notDone)

end Linger.App.Recovery
