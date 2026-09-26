module

public section

namespace Tools.Entry

inductive Route where
  | selector
  | importSave (args : List String)
  | session (args : List String)
  deriving BEq, Repr

/-- Choose an executor without interpreting or changing its arguments. -/
def route (args : List String) (stdinTty stdoutTty : Bool) : Route :=
  match args with
  | [] => if stdinTty && stdoutTty then .selector else .session []
  | "import" :: rest => .importSave rest
  | _ => .session args

end Tools.Entry
