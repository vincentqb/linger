module

public section

/-! A cancellable command owned by one terminal loop. Both pipe readers and
the isolated process group live until that loop collects or stops the job. -/

namespace Linger.Runtime.Command

structure Job where
  child : IO.Process.Child { stdin := .null, stdout := .piped, stderr := .piped }
  stdout : Task (Except IO.Error String)
  stderr : Task (Except IO.Error String)

def start (executable : String) (args : Array String) : IO Job := do
  let child ←
    IO.Process.spawn
        { cmd := executable, args, stdin := .null, stdout := .piped, stderr := .piped,
          setsid := true }
  let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
  let stderr ← IO.asTask child.stderr.readToEnd Task.Priority.dedicated
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

/-- Retire the group before reaping its leader, whose reserved PID identifies the
group even when a descendant still holds a pipe. Join both readers on every path. -/
def stop (pending : IO.Ref (Option Job)) : IO Unit := do
  if let some job← pending.get then
    pending.set none
    try
      try
        job.child.kill
      finally
        discard job.child.wait
    finally
      discard <| IO.wait job.stdout
      discard <| IO.wait job.stderr

end Linger.Runtime.Command
