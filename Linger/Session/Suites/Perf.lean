module

public import Verify.Harness
import Linger.Display.Suites.Title
import Linger.Session.Suites.Resume
import Linger.Session.Suites.Robust

public section

/-! # Linger.Session.Suites.Perf — what the largest workloads cost, opt-in

The resume, robust and title suites check what their largest workloads produce, whatever the
host's speed (`Linger.Session.Suites.Resume.scaleRun`, `Linger.Session.Suites.Robust.hostileRun`,
`Linger.Session.Suites.Robust.burstRun` and `Linger.Display.Suites.Title.idleRun`); this suite
runs the same workloads and reports what they cost. Each cost prints with its budget and the
host's one-minute load average, so a slow run says how busy the host was. Budgets are about
five times the cost measured when they were set, so on an idle host only a pathological
regression exceeds one.

`suites perf` reports: a cost over its budget says so and fails nothing. `suites perf strict`
fails it. In either mode a workload that did not complete fails, since its cost would measure
nothing, and a cost the platform cannot measure (CPU time without `/proc`) says SKIP. Neither
runs in `scripts/verify.sh`, whose verdict must not depend on how fast the host is. -/

namespace Linger.Session.Suites.Perf

open Verify.Harness

/-- Budgets for `Resume.scaleRun` in milliseconds, about five times the cost measured when they
were set (fill 1.1 s, capture 0.56 s, replay 0.22 s, save 0.25 s): the 10,000-row fill,
`capture --history`, the reattach replay and the detach checkpoint. -/
def scaleBudgetMs : Nat × Nat × Nat × Nat := (5500, 3000, 1200, 1300)

/-- Budgets for `Robust.hostileRun` in milliseconds, about five times the cost measured when they
were set (write 0.33 s, info 0.15 s): the counted CSI write and the `info` answer after the
history flood. -/
def hostileBudgetMs : Nat × Nat := (1700, 800)

/-- Budget for `Robust.burstRun` in milliseconds, about five times the 0.44 s measured when it
was set: eight reads of one-byte input frames and the `info` answer after them. -/
def inputBurstBudgetMs : Nat := 2200

/-- Budget for `Title.idleRun`: the attached client's own CPU over `Title.idleWindowMs`, in
milliseconds, about five times the cost measured when it was set. It took 70 ms at a load of
134 (2026-11-12), so CPU time, too, grows with the host's load. -/
def idleBudgetMs : Nat := 100

/-- The host's one-minute load average as the system reports it: the first field of
`/proc/loadavg`, else of `sysctl -n vm.loadavg` (macOS, `{ 1.23 1.45 1.67 }`), else `unknown`. -/
def loadAverage : IO String := do
  let text ←
    if ← System.FilePath.pathExists "/proc/loadavg" then
      IO.FS.readFile "/proc/loadavg"
    else
      try
        pure (← IO.Process.output { cmd := "sysctl", args := #["-n", "vm.loadavg"] }).stdout
      catch _ =>
        pure ""
  let fields := (text.split fun c => c.isWhitespace || c == '{').toStringList.filter (· != "")
  return fields.headD "unknown"

/-- One cost in milliseconds, with its budget and the load average when it was reported: it fails
when the workload did not complete, and when it exceeds `budget` only if `strict`. A cost the
platform did not measure, `none`, says SKIP (`expectMeasured`). -/
def cost (strict : Bool) (label : String) (completed : Bool) (ms : Option Nat) (budget : Nat) :
    IO Unit := do
  let load ← loadAverage
  let over := ms.any (· > budget)
  let verdict :=
    if !completed then "did not complete"
    else if ms.isNone then "unmeasured here" else if over then "over budget" else "within budget"
  let shown := (ms.map fun ms => s!"{ms} ms").getD "unmeasured"
  expectMeasured ms.isSome (completed && (!over || !strict))
      s!"{label}: {shown}, {verdict} ({budget} ms), at load {load}"

/-- The performance suite: what the resume suite's full ring, the robust suite's hostile input
and input burst and the title suite's idle client cost against their budgets, failing a cost
over its budget only when `strict`. -/
def run (strict : Bool) : IO UInt32 :=
  Env.suite "perf" fun e => do
    IO.println
        s!"perf: {if strict then "strict" else "report"} mode, at load {← loadAverage}; \
          {if strict then "a cost over its budget fails" else "a cost over its budget fails nothing"}"
    let s ← Linger.Session.Suites.Resume.scaleRun e
    let (fill, capture, replay, save) := scaleBudgetMs
    cost strict "fill a full ring at 200 columns" s.filled s.fillMs fill
    cost strict "export it with capture --history" (s.historyRc == some 0) s.captureMs capture
    cost strict "replay it to a reattach" s.replayed s.replayMs replay
    cost strict "checkpoint it on detach" s.saved s.saveMs save
    let h ← Linger.Session.Suites.Robust.hostileRun e
    let (write, info) := hostileBudgetMs
    cost strict "write hostile counts and tab runs at 1000x1000" h.written h.writeMs write
    cost strict "answer info after a history flood" h.answered h.infoMs info
    let b ← Linger.Session.Suites.Robust.burstRun e
    cost strict "answer info after eight reads of one-byte input frames" (b.reading && b.answered)
        b.burstMs inputBurstBudgetMs
    let (attached, cpu) ← Linger.Display.Suites.Title.idleRun e
    cost strict
        s!"an idle attached client's own CPU over {Linger.Display.Suites.Title.idleWindowMs} ms"
        attached (cpu.map (·.1)) idleBudgetMs

end Linger.Session.Suites.Perf
