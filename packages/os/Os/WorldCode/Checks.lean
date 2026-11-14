module

public import Os.WorldSpec
import SoftwareChallenge.Commands

/-! # The checks of the OS boundary's world claims

`Os.Wait.Lasts` says that a sleep lasts at least as long as it was asked to, and `Os.Exec.Keeps`
that an exec keeps the process, its children and the descriptors it does not close. Each claim
takes the behaviour it constrains as a parameter, which no Lean term computes: `slept` and `execd`
name them, and the checks observe them, by sleeping and reading the monotonic clock around each
sleep, and by running a process that execs. No program module imports this one. -/

namespace Os.Checks

/-- What the monotonic clock reads once a sleep of `ms` milliseconds, asked for when it read
`now`, returns: the observation `Os.Wait.Lasts` constrains. It has no body; the check below
observes it. -/
opaque slept : Nat → Nat → Nat

-- A sleep lasts at least as long as asked: around sleeps of 0, 1, 7 and 20 milliseconds, the
-- monotonic clock advances by at least as much.
Check Os.Wait.Lasts slept := do
  for ms in [0, 1, 7, 20] do
    let before ← IO.monoMsNow
    IO.sleep ms.toUInt32
    let after ← IO.monoMsNow
    unless before + ms ≤ after do
      throw (IO.userError s!"a sleep of {ms} ms returned {after - before} ms after it began")

/-- What a process is once an `execve` it made succeeded, its id, its children and its kept
descriptors, from what they were before: the observation `Os.Exec.Keeps` constrains. It has no
body; the check below observes it. -/
opaque execd : Nat → List Nat → List Nat → Nat × List Nat × List Nat

-- An exec keeps the process: a shell that started a child and holds the check's pipe at
-- descriptor 3 alone execs a second shell, which reads the same process id, finds the child's
-- parent is still that process, and writes through descriptor 3 to the pipe the check reads.
Check Os.Exec.Keeps execd := do
  let script :=
    "sleep 30 >/dev/null 2>&1 & child=$!\n" ++ "exec 3>&1 1>/dev/null\n" ++
      "echo \"before $$ $child\" >&3\n" ++
      "exec /bin/sh -c 'echo \"after $$ $(ps -o ppid= -p \"$1\" | tr -d \" \")\" >&3; " ++
      "kill \"$1\"' sh \"$child\"\n"
  let out ← IO.Process.output { cmd := "/bin/sh", args := #["-c", script] }
  match (out.stdout.splitOn "\n").map (·.splitOn " ") with
  | ["before", pid, _] :: ["after", pid', parent] :: _ =>
    unless pid == pid' do
      throw (IO.userError s!"a shell that was process {pid} reads {pid'} once it has exec'd")
    unless parent == pid do
      throw (IO.userError s!"the child of process {pid} has parent {parent} once it has exec'd")
  | _ =>
    throw
        (IO.userError
          s!"the exec'd shell wrote nothing through the descriptor it kept: {out.stdout} {out.stderr}")

end Os.Checks
