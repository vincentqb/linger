module

import Os.WorldCode

public section

/-! A cancellable command with one owner. Both pipe readers and the isolated
process group live until that owner collects or stops the job. -/

namespace Os.Shell.Command

/-- A started command and its two pipe readers, held by one owner until it collects the
job with `poll` or retires it with `stop`. -/
structure Job where
  /-- The process, leader of its own session and process group. -/
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }
  /-- Its standard output, read to the end on a dedicated task. -/
  stdout : Task (Except IO.Error String)
  /-- Its standard error, read to the end on a dedicated task. -/
  stderr : Task (Except IO.Error String)

/-- Spawn `executable` with `args` in a new session and process group, with stdin from
`/dev/null` and both outputs piped, and start draining each pipe on its own task. -/
def start (executable : String) (args : Array String) : IO Job := do
  let child ←
    IO.Process.spawn
        { cmd := executable, args, stdin := .null, stdout := .piped, stderr := .piped,
          setsid := true }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  return { child, stdout, stderr }

/-- `start`, with `input` the command's standard input: written whole once its pipes are being
read, then closed, so that the command reads it and then its end. For an input a pipe holds at
once, as a few lines of requests are: a longer one waits for the command to read it. -/
def startFeeding (executable : String) (args : Array String) (input : ByteArray) : IO Job := do
  let spawned ←
    IO.Process.spawn
        { cmd := executable, args, stdin := .piped, stdout := .piped, stderr := .piped,
          setsid := true }
  let (stdin, child) ← spawned.takeStdin
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
  -- a command that ends without reading closes its end first: what it did not take is lost
  try
    stdin.write input
    stdin.flush
  catch _ =>
    pure ()
  return { child, stdout, stderr }

/-- Drain the whole pipe while retaining at most `limit` bytes. After overflow,
keep draining so the child cannot block on a full pipe; refuse the result at EOF. -/
private def readLimited (handle : IO.FS.Handle) (limit : Nat) : IO String := do
  let mut bytes := ByteArray.empty
  let mut exceeded := false
  while true do
    let chunk ← handle.read 4096
    if chunk.isEmpty then
      break
    if !exceeded && bytes.size + chunk.size ≤ limit then
      bytes := bytes ++ chunk
    else
      exceeded := true
  if exceeded then
    throw (IO.userError s!"command output exceeds {limit} bytes")
  let some text := String.fromUTF8? bytes
    | throw (IO.userError "command output is not UTF-8")
  return text

/-- A cancellable command with bounded retained output. Standard error retains at
most 64 KiB; readers still drain both pipes after overflow until collection or cancellation. -/
def startLimited (executable : String) (args : Array String) (limit : Nat) : IO Job := do
  let child ←
    IO.Process.spawn
        { cmd := executable, args, stdin := .null, stdout := .piped, stderr := .piped,
          setsid := true }
  let stdout ← IO.asTask (readLimited child.stdout limit) Task.Priority.dedicated
  let stderr ← IO.asTask (readLimited child.stderr (64 * 1024)) Task.Priority.dedicated
  return { child, stdout, stderr }

/-- Collect only a completed child with closed pipes. Clear ownership immediately
after reaping, before a pipe error can throw: cleanup must never signal a reused PID. -/
def poll (pending : IO.Ref (Option Job)) : IO (Option IO.Process.Output) := do
  if let some job← pending.get then
    if (← IO.hasFinished job.stdout) && (← IO.hasFinished job.stderr) then
      if let some exitCode← job.child.tryWait then
        pending.set none
        let stdout ← IO.ofExcept (← IO.wait job.stdout)
        let stderr ← IO.ofExcept (← IO.wait job.stderr)
        return some { exitCode, stdout, stderr }
  return none

/-- Force-retire the job's process group. Darwin's `killpg` refuses a group whose only
member is the exited, unreaped leader (EPERM), so that refusal, or ESRCH, signals the
reserved leader PID itself. A child whose standard input was taken (`startFeeding`) is killed
alone, as Lean's runtime kills it, so the rest of its group, whose id the unreaped leader keeps, is
signalled too; a group with no process left has nothing to retire. -/
private def retireGroup (job : Job) : IO Unit := do
  try
    job.child.kill
  catch err =>
    match err with
    | .permissionDenied .. | .noSuchThing .. =>
      Os.Shell.kill job.child.pid 9
    | _ =>
      throw err
  try
    discard <| Os.Shell.signalGroup job.child.pid 9
  catch _ =>
    pure ()

/-- A command its owner converses with: the process, its standard input while the owner holds it
open, its standard output, which the owner reads a line at a time (`Talk.line`), and its standard
error, read to the end on a dedicated task, at most 64 KiB kept. -/
structure Talk where
  /-- The process, its standard input taken. -/
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }
  /-- Its standard input, until the owner closes it. -/
  input : IO.Ref (Option IO.FS.Handle)
  /-- Its standard error, read to the end on a dedicated task. -/
  stderr : Task (Except IO.Error String)
  /-- Whether it leads a session and process group of its own. -/
  isolated : Bool

/-- Start `executable` with `args`, its standard input and output on pipes its owner holds, and its
standard error read to the end on a dedicated task, at most 64 KiB kept. An `isolated` command
leads a new session and process group, so that it reaches no terminal; any other shares this
process's group and terminal, as a transport asking its user for a password does. -/
def talk (executable : String) (args : Array String) (isolated : Bool) : IO Talk := do
  let spawned ←
    IO.Process.spawn
        { cmd := executable, args, stdin := .piped, stdout := .piped, stderr := .piped,
          setsid := isolated }
  let (stdin, child) ← spawned.takeStdin
  let stderr ← IO.asTask (readLimited child.stderr (64 * 1024)) Task.Priority.dedicated
  return { child, input := ← IO.mkRef (some stdin), stderr, isolated }

/-- Write `text` to the command's standard input and flush it: whether all of it was written, which
it is not once the input is closed or the command no longer reads it. -/
def Talk.say (t : Talk) (text : String) : IO Bool := do
  match ← t.input.get with
  | none =>
    return false
  | some handle =>
    try
      handle.putStr text
      handle.flush
      return true
    catch _ =>
      return false

/-- Close the command's standard input, so that it reads its end. -/
def Talk.hangUp (t : Talk) : IO Unit := t.input.set none

/-- The next line the command writes to its standard output, its newline aside, as it comes; none
once its output ends or cannot be read. -/
def Talk.line (t : Talk) : IO (Option String) := do
  let line ←
    try
      t.child.stdout.getLine
    catch _ =>
      pure ""
  if line.isEmpty then
    return none
  return some ((line.dropSuffix "\n").copy)

/-- What the command wrote to its standard error, once it has ended it: empty when it is not text
or more than its cap. -/
def Talk.errors (t : Talk) : IO String := do
  return (← IO.wait t.stderr).toOption.getD ""

/-- Close the command's standard input and wait for it to end: its exit status. -/
def Talk.finish (t : Talk) : IO UInt32 := do
  t.hangUp
  t.child.wait

/-- End the command now: close its standard input, kill it, and its group when it leads one, and
reap it. -/
def Talk.stop (t : Talk) : IO Unit := do
  t.hangUp
  try
    if t.isolated then
      try
        discard <| Os.Shell.signalGroup t.child.pid 9
      catch _ =>
        pure ()
    t.child.kill
  catch _ =>
    pure ()
  try
    discard t.child.wait
  catch _ =>
    pure ()

/-- Optionally give the leader time to retire separately isolated children.
Then retire its group before reaping the leader, whose reserved PID identifies
the group even when a descendant still holds a pipe. Join both readers on every
path. Lean's child kill is forceful; the cooperative request uses SIGTERM. -/
def stop (pending : IO.Ref (Option Job)) (graceMs : Nat := 0) : IO Unit := do
  if let some job← pending.get then
    pending.set none
    try
      try
        try
          if graceMs > 0 then
            Os.Shell.kill job.child.pid 15
            let deadline := (← Os.Shell.monotonicMs) + graceMs
            repeat
              if (← IO.hasFinished job.stdout) && (← IO.hasFinished job.stderr) then
                break
              unless ← Os.Shell.nap deadline 5 do
                break
        finally
          retireGroup job
      finally
        discard job.child.wait
    finally
      discard <| IO.wait job.stdout
      discard <| IO.wait job.stderr

end Os.Shell.Command
