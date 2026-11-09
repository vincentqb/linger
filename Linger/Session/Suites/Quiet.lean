module

public import Verify.Harness
import Linger.Session

public section

/-! # Linger.Session.Suites.Quiet — an idle session costs no wakeup

Work follows events: a daemon sleeps until something happens or its session's next tick
(`Session.State.nextTick`), so a session whose program is quiet and whose state is saved wakes
its daemon for nothing at all. Wakeups are the context switches `/proc` counts for every thread
of the daemon; where there is no `/proc` (macOS) the counts are absent and those checks pass
vacuously, as the resident-set check in `Linger.Session.Suites.Resume` does. -/

namespace Linger.Session.Suites.Quiet

open Verify.Harness

/-- The context switches of every thread of `pid`, which only a wakeup adds to; `none` where
there is no `/proc`. -/
def wakeups (pid : UInt32) : IO (Option Nat) := do
  unless ← System.FilePath.pathExists "/proc/self/task" do
    return none
  let mut total := 0
  for task in ← System.FilePath.readDir s!"/proc/{pid}/task" do
    let status ← IO.FS.readFile (task.path / "status")
    for line in status.splitOn "\n" do
      if
          line.startsWith "voluntary_ctxt_switches:" ||
            line.startsWith "nonvoluntary_ctxt_switches:" then
        total := total + ((line.splitOn ":").getLastD "").trimAscii.toString.toNat?.getD 0
  return some total

/-- How many times the daemon `pid` woke in `ms` milliseconds; `none` where there is no `/proc`
or no pid. -/
def wakeupsOver (pid : Option UInt32) (ms : Nat) : IO (Option Nat) := do
  let some pid := pid | return none
  let some before ← wakeups pid | return none
  IO.sleep ms.toUInt32
  let some after ← wakeups pid | return none
  return some (after - before)

/-- The quiet suite: idle sessions, and sessions whose output has stopped, sleep. Nothing asks
either daemon anything between finding its pid and the last measurement, since a question is
an event that wakes it. -/
def run : IO UInt32 :=
  Env.suite "quiet" fun e => do
    let (idleRc, _, _) ← e.cli #["start", "q-idle", "/bin/sh", "-c", "exec sleep 1000"]
    -- the marker is an expansion, so only the program's output, not an echo, can show it
    let (burstRc, _, _) ←
      e.cli #["start", "q-burst", "/bin/sh", "-c", "echo QUIET-$((6*7)); exec sleep 1000"]
    let idlePid ← e.daemonPid "q-idle"
    let burstPid ← e.daemonPid "q-burst"
    -- longer than the freshness window, so the output's own deadline has passed, and the
    -- questions that found the pids are long answered
    IO.sleep (Linger.Session.freshMs + 1500).toUInt32
    let (idle, burst) ←
      do
        let measured ← IO.asTask (wakeupsOver idlePid 3000) Task.Priority.dedicated
        let burst ← wakeupsOver burstPid 3000
        pure (← IO.ofExcept (← IO.wait measured), burst)
    expect (idleRc == 0 && idlePid.isSome && idle.all (· == 0))
        s!"a session whose program prints nothing never wakes its daemon ({idle} in 3 s)"
    expect
        (burstRc == 0 && burstPid.isSome && burst.all (· == 0) &&
          has (← e.out #["capture", "--history", "q-burst"]) "QUIET-42")
        s!"a session whose output stopped and is saved sleeps ({burst} wakeups in 3 s)"
    e.killAll #["q-idle", "q-burst"]

end Linger.Session.Suites.Quiet
