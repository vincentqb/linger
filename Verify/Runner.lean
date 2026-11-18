module

import Verify.Harness

public section

namespace Verify.Runner

/-- The words a linger process serves a session under, after its program and any `__dirs`: its
daemon's, whatever started it, and the image an upgrade carries it over to. -/
def daemonVerbs : List String := ["__daemon", "__start", "__resume", "__upgraded"]

/-- Whether a scratch directory's name carries one of `pids`, as each suite names the directories
it creates with its own pid: `linger-<slug>-<pid>` for its state directory (`Env.make`) and
`linger-<slug>-<pid>-<suffix>` for one `mktemp` makes. -/
def carries (pids : List UInt32) (name : String) : Bool :=
  name.startsWith "linger-" &&
    ((name.splitOn "-").drop 1).any fun part => pids.any (toString · == part)

/-- What a run of suites can leave behind, as one look sees it: the `linger-*` directories under
the scratch roots, `Verify.Harness.tempRoot` and `Verify.Harness.socketRoot`, and the processes
that serve a session, each its pid and command line. -/
structure Left where
  /-- The paths of the scratch directories. -/
  dirs : List String
  /-- The daemons: each pid and command line. -/
  daemons : List (Nat × String)

/-- One look at what is left: the scratch directories, and the daemons whose program is `linger`
or lies in a scratch directory `ours` names, from one `ps` read, as on Linux and macOS alike. -/
def Left.look (linger : String) (ours : String → Bool) : IO Left := do
  let mut dirs := []
  for root in [← Verify.Harness.tempRoot, Verify.Harness.socketRoot] do
    let entries ←
      try
        root.readDir
      catch _ =>
        pure #[]
    for entry in entries do
      if entry.fileName.startsWith "linger-" then
        if let .ok metadata← entry.path.symlinkMetadata.toBaseIO then
          if metadata.type == .dir then
            dirs := entry.path.toString :: dirs
  let out ← IO.Process.output { cmd := "ps", args := #["-e", "-ww", "-o", "pid=,args="] }
  let daemons :=
    (out.stdout.splitOn "\n").filterMap fun line =>
      match (line.split Char.isWhitespace).toStringList.filter (· != "") with
      | pid :: program :: args =>
        if
            args.any daemonVerbs.contains &&
              (program == linger || (program.splitOn "/").any ours) then
          pid.toNat?.map (·, line.trimAscii.toString)
        else none
      | _ => none
  return { dirs := dirs.eraseDups, daemons }

/-- What `after` holds that `before` did not: the scratch directories whose names `ours` says a
suite of the run created, and every daemon. -/
def Left.since (before after : Left) (ours : String → Bool) : Left :=
  {
    dirs :=
      after.dirs.filter fun dir =>
        !before.dirs.contains dir && ours ((System.FilePath.mk dir).fileName.getD ""),
    daemons := after.daemons.filter fun (pid, _) => !before.daemons.any (·.1 == pid) }

/-- Run independent suites in separate processes, with at most four alive.
The caller supplies the only assertion-count inventory: each suite's name, how many
checks it reports and how many of those say `SKIP`, which the platform could not
measure (`Verify.Harness.expectMeasured`); the rest must say `PASS`. Each process keeps
its combined output in its own log; ordinary `spawn` preserves inherited SIGINT.
Wait for every started suite even when another fails.

With `checkLeaks`, the run also fails when it leaves anything behind that it did not find: a
scratch directory a suite created (`carries`, of its pid), or a daemon running this checkout's
`linger`, or a program in such a directory, as the upgrade suite's copy is; a daemon may take a
moment to exit once it has let its name go, so the run waits for one for `patienceMs`. Only one
run of a checkout's suites checks at a time, as one writer works in a tree, and a run in another
checkout names its directories with its own suites' pids and runs its own `linger`. -/
def run (binary : String) (args : Array String) (logDir : System.FilePath)
    (specs : List (String × Nat × Nat)) (checkLeaks : Bool := false) : IO UInt32 := do
  let names := specs.map (·.1)
  if
      specs.isEmpty || names.eraseDups.length != names.length ||
        specs.any
          (fun (name, count, skips) =>
            name.isEmpty || !name.toList.all (fun c => c.isAlphanum || c == '-') || count == 0 ||
              skips ≥ count) then
    IO.eprintln
        "suites: expected distinct suite names with positive check counts, fewer of them skipped"
    return 2
  if (← IO.getEnv "LINGER_TEST_DIR").isSome then
    IO.eprintln
        "suites: concurrent suites require separate state directories; unset LINGER_TEST_DIR"
    return 2
  -- every suite runs the `linger` its state directory's `Env.make` names, from this directory
  let linger := ((← IO.currentDir) / ".lake" / "build" / "bin" / "linger").toString
  let before ← Left.look linger fun _ => false
  let started ← IO.mkRef ([] : List UInt32)
  let suite (name : String) (expected skips : Nat) : IO (String × Bool × Nat) := do
    let start ← IO.monoMsNow
    let log := logDir / s!"linger-{name}.out"
    -- Redirect in the child, not global Lean streams. All arguments remain
    -- argv elements, and exec keeps the process and signal disposition.
    let child ←
      IO.Process.spawn
          { cmd := "sh"
            args := #["-c", "exec \"$@\" > \"$0\" 2>&1", log.toString, binary] ++ args ++ #[name] }
    started.modify (child.pid :: ·)
    let code ← child.wait
    let text ← IO.FS.readFile log
    let lines := Verify.Harness.lines text
    let count := (lines.filter (·.startsWith "PASS ")).length
    let skipped := (lines.filter (·.startsWith "SKIP ")).length
    let ok :=
      code == 0 && lines.getLast? == some "FAILURES: 0" && count + skipped == expected &&
        skipped == skips &&
        !lines.any (·.startsWith "FAIL ")
    if !ok then
      IO.eprintln
          s!"suites: {name} failed (exit {code}, {count} passed and {skipped} skipped of \
            {expected} checks, {skips} to skip); see {log}"
    return (name, ok, (← IO.monoMsNow) - start)
  let failed ← IO.mkRef false
  Verify.Harness.parallel 4 (specs.map fun (name, expected, skips) => suite name expected skips) fun
      | .error e => do
        failed.set true
        IO.eprintln s!"suites: {e}"
      | .ok (name, ok, elapsed) => do
        unless ok do
          failed.set true
        IO.println s!"  {name}: {if ok then "OK" else "FAILED"} ({elapsed} ms)"
  if checkLeaks then
    let ours := carries (← started.get)
    let left : IO Left := do
      return before.since (← Left.look linger ours) ours
    let _ ← Verify.Harness.waitFor Verify.Harness.patienceMs (return (← left).daemons.isEmpty)
    let found ← left
    unless found.dirs.isEmpty do
      failed.set true
      IO.eprintln s!"suites: the run left scratch directories its suites created: {found.dirs}"
    unless found.daemons.isEmpty do
      failed.set true
      IO.eprintln s!"suites: the run left daemons running: {found.daemons.map (·.2)}"
  return if ← failed.get then 1 else 0

end Verify.Runner
