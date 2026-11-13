module

public import Linger.App.CoreSpec
public import Terminal.CoreCode.Vt
import Linger.Session.CoreCode.Checkpoint
import Linger.Session.CoreCode.Record

public section

/-! # Linger.App.Recovery — what a command does with a saved session

A name no live session holds may have a checkpoint: what a detach, an ended program, a signal
that stopped its daemon or the cadence last saved. A command that may start a session, as
`attach` does, starts a new one only
when there is no file; one that may not, as `resume` and the offline readers, answers `notFound`
then. A file whose bytes decode resumes the session they saved. A file whose bytes do not decode
is never taken for no file: the command starts nothing, leaves it as it is and answers `notDone`,
so a torn or emptied file, or one in a newer format, never costs the session itself, and `kill`
discards it (`recovery_exact`).

An attach to a saved session whose end record says its program ended shows its result to whoever
attaches, typist or watcher: its last screen, then how its program ended, and then discards it,
since it has been seen. Any other saved session, one a signal to its daemon saved or one whose
daemon ended without saying how its program ended, an attach resumes, or a watcher views
(`visit_result`). -/

namespace Linger.App.Recovery

/-- What a command does with a name no live session holds, from the bytes of its checkpoint,
`none` when there is no file: start a new session when there is none and `create` allows it,
resume the session the bytes decode to (`Checkpoint.loadBytes`), and otherwise start nothing,
answering `notFound` for no file and `notDone` for bytes that do not decode. -/
def decide (create : Bool) :
    Option ByteArray → Recovery (Linger.Session.Checkpoint.Ckpt Terminal.Vt.Vt)
  | none => if create then .fresh else .refuse .notFound
  | some bytes => ((Linger.Session.Checkpoint.loadBytes bytes).map .resume).getD (.refuse .notDone)

/-- What an attach does with a saved session, from the bytes of the name's end record, `none`
when there is none: show the result of a program that ended, tell how it ended and discard it,
in either mode; otherwise view the saved screen when `readOnly`, or resume the session. -/
def visit (readOnly : Bool) (record : Option (List UInt8)) : List Visit.Step :=
  match record.bind Linger.Session.Record.decode with
  | some (.ended outcome) => [.show, .tell outcome, .discard]
  | _ => if readOnly then [.show] else [.resume]

end Linger.App.Recovery
