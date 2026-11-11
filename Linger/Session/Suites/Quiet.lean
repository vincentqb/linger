module

public import Verify.Harness
import Linger.Session
public import Linger.Os.Spec
import SoftwareChallenge.Commands

public section

/-! # Linger.Session.Suites.Quiet — an idle session costs no wakeup

Work follows events: a daemon sleeps until something happens or its session's next tick
(`Session.State.nextTick`), so a session whose program is quiet and whose state is saved wakes
its daemon for nothing at all, and a summary reads what each daemon published to its name's end
record instead of asking it. Wakeups are the context switches `/proc` counts for every thread
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

/-- How many times the daemon `pid` woke while `action` ran, and what `action` gave; the count is
`none` where there is no `/proc` or no pid. -/
def wakeupsDuring {α : Type} (pid : Option UInt32) (action : IO α) : IO (Option Nat × α) := do
  let before ← pid.mapM wakeups
  let result ← action
  let after ← pid.mapM wakeups
  return (match before.join, after.join with
      | some b, some a => some (a - b)
      | _, _ => none,
      result)

/-- The quiet suite: idle sessions, and sessions whose output has stopped, sleep, a summary reads
what their daemons published instead of waking them, and a `send -` waiting for input sleeps.
Nothing asks either daemon anything between finding its pid and the last measurement, since a
question is an event that wakes it. -/
@[exercises Linger.Os.Poll.Sleeps]
def run : IO UInt32 :=
  Env.suite "quiet" fun e => do
    let (idleRc, _, _) ← e.cli #["start", "q-idle", "/bin/sh", "-c", "exec sleep 1000"]
    -- the marker is an expansion, so only the program's output, not an echo, can show it
    let (burstRc, _, _) ←
      e.cli #["start", "q-burst", "/bin/sh", "-c", "echo QUIET-$((6*7)); exec sleep 1000"]
    let idlePid ← e.daemonPid "q-idle"
    let burstPid ← e.daemonPid "q-burst"
    -- a `send -` that waits for input, connected before the settling sleep: it wakes only for
    -- input, a reply or a close, and its idle connection asks the daemon nothing
    let sender0 ←
      IO.Process.spawn
          { cmd := e.bin, args := #["send", "q-idle", "-"], env := e.procEnv, stdin := .piped,
            stdout := .null, stderr := .null }
    let (senderIn, sender) ← sender0.takeStdin
    -- longer than the freshness window, so the output's own deadline has passed, and the
    -- questions that found the pids are long answered
    IO.sleep (Linger.Session.freshMs + 1500).toUInt32
    let (idle, burst, sending) ←
      do
        let measured ← IO.asTask (wakeupsOver idlePid 3000) Task.Priority.dedicated
        let sent ← IO.asTask (wakeupsOver (some sender.pid) 3000) Task.Priority.dedicated
        let burst ← wakeupsOver burstPid 3000
        pure (← IO.ofExcept (← IO.wait measured), burst, ← IO.ofExcept (← IO.wait sent))
    -- the sender's input stays open until here, so it was waiting throughout
    try
      senderIn.flush
    catch _ =>
      pure ()
    reapOrKill sender 0
    -- the burst arrived while nobody looked, so a summary counts it, as asking would
    let (idleAsked, burstAsked, summaries) ←
      do
        let (idleAsked, (burstAsked, summaries)) ←
          wakeupsDuring idlePid <|
              wakeupsDuring burstPid <| (List.range 3).mapM fun _ => e.cli #["ls", "--summary"]
        pure (idleAsked, burstAsked, summaries)
    expect (idleRc == 0 && idlePid.isSome && idle.all (· == 0))
        s!"a session whose program prints nothing never wakes its daemon ({idle} in 3 s)"
    expect
        (burstRc == 0 && burstPid.isSome && burst.all (· == 0) &&
          has (← e.out #["capture", "--history", "q-burst"]) "QUIET-42")
        s!"a session whose output stopped and is saved sleeps ({burst} wakeups in 3 s)"
    let unread := s!"1{Linger.Display.Status.icon .wantsYou}\n"
    expect
        (idleAsked.all (· == 0) && burstAsked.all (· == 0) &&
          summaries.all (fun (rc, text, _) => rc == 0 && text == unread))
        s!"a summary reads what each daemon published and wakes none ({idleAsked} and {burstAsked} wakeups over three summaries: {summaries.map (·.2.1)})"
    expect (sending.all (· == 0)) s!"a send - waiting for input sleeps ({sending} wakeups in 3 s)"
    -- a new daemon publishes what it sees before it first sleeps, so even the first summary
    -- after it starts need not wake it
    let (freshRc, _, _) ← e.cli #["start", "q-fresh", "/bin/sh", "-c", "exec sleep 1000"]
    let published ←
      waitFor 2000 do
          match ← (IO.FS.readBinFile s!"{e.dir}/q-fresh.end").toBaseIO with
          | .ok bytes =>
            return (Linger.Session.Record.published bytes.toList).isSome
          | .error _ =>
            return false
    expect (freshRc == 0 && published)
        "a new daemon says in its end record what it sees before anyone asks it"
    e.killAll #["q-idle", "q-burst", "q-fresh"]

end Linger.Session.Suites.Quiet
