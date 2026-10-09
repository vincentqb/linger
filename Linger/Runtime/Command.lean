module

import Linger.Posix

public section

/-! A cancellable command with one owner. Both pipe readers and the isolated
process group live until that owner collects or stops the job. -/

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
            Linger.Posix.kill job.child.pid 15
            let deadline := (← Linger.Posix.monotonicMs) + graceMs
            while (← Linger.Posix.monotonicMs) < deadline do
              if (← IO.hasFinished job.stdout) && (← IO.hasFinished job.stderr) then
                break
              IO.sleep 5
        finally
          job.child.kill
      finally
        discard job.child.wait
    finally
      discard <| IO.wait job.stdout
      discard <| IO.wait job.stderr

end Linger.Runtime.Command
