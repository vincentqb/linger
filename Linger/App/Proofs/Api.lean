module

public import Linger.App.CoreSpec
import all Linger.App.CoreCode.Api
import all Linger.App.CoreCode.Commands
import all Linger.App.CoreCode.Entry
import all Linger.Target.CoreCode.Remote

/-! # A command line as a request, and a request as what it does

A command line that parses is a request of its first word's operation, the request takes the
transition its operation means, and a command answers what is true of what it found. -/

namespace Linger.App.Api

/-- The words after a command's word read as a request of that command's operation. -/
theorem parseOp_op {op : Commands.Op} {args : List String} {request : Request}
    (parsed : parseOp op args = some request) : request.op = op := by
  cases op <;> unfold parseOp at parsed <;> (repeat' split at parsed) <;>
    (try simp only [Option.map_eq_some_iff] at parsed) <;>
    (try obtain ⟨_, -, rfl⟩ := parsed) <;>
    simp_all [Request.op]

/-- **A command line that parses is a request of its first word's operation**: the row
`Commands.lookup` finds for that word. -/
theorem parse_op {argv : List String} {request : Request} (parsed : parse argv = some request) :
    (Commands.lookup (argv.headD "")).map (·.op) = some request.op := by
  cases argv with
  | nil => simp [parse] at parsed
  | cons word args =>
    simp only [parse, Option.bind_eq_some_iff] at parsed
    obtain ⟨command, found, parsed⟩ := parsed
    simp [found, parseOp_op parsed]

/-- **A request takes the transition its operation means.** -/
theorem plan_act (request : Request) : plan request = request.act := rfl

/-- **A command answers what is true of what it found.** -/
theorem answer_eq (found : Found) : answer found = found.answer := rfl

/-- `detach x` is the request to detach every client from `x`. -/
theorem parse_detach : parse ["detach", "x"] = some (.detach "x") := by rfl

/-- …which the entry gives the session CLI as it is. -/
theorem route_detach : Entry.route ["detach", "x"] = .session ["detach", "x"] := by rfl

end Linger.App.Api
