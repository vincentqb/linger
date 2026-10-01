module

public import E2E.Harness

public section

/-! # E2E.Ci — runner selection and Lake build reuse

`tests/ci-runners.sh` decides the GitHub matrix, and its two failure modes are both
silent and both expensive. Ask for macOS when nothing changed and a push bills several
times what it needs to; never ask for it and AGENTS.md's claim that the tree passes on
macOS stops being checked by anything. The billing arithmetic is recorded in
SCRATCHPAD.md.

`tests/gates.sh` greps the workflow for the shape — `fromJSON`, both runner names, a
`cron`, a `workflow_dispatch`, a `--since` — which catches deletion. It cannot catch
behaviour: a grep cannot tell you that a push to main yields ubuntu alone.

WHY THIS DRIVES A SHELL SCRIPT. The decision has to be callable by a workflow step
that compiles nothing (that is what makes the `gates` job cheap), so it is shell. It
lives in `tests/ci-runners.sh` rather than inline in the YAML precisely so this suite
can run the real thing: an inline `case` could only be tested by a second copy of
itself, and a suite asserting against a copy is the failure this repo's rules name
outright. The `schedule` arm is exercised against real temporary repositories with
real commit dates, because the bug that actually happened while writing it was a
QUOTING bug — an unquoted `--since=8 days ago` makes git read `days` as a revision,
git fails, the output is empty, and empty means "no commits", so macOS silently never
runs again. Only a real `git log` can catch that; a reimplementation cannot.

Build reuse is tested against the pinned Lake through this repository's wrapper,
in one temporary project. Source and dependency changes must invalidate artifacts,
`--rehash` must ignore stale artifact hashes, and `--wfail` must reject replayed
warnings even when a source file locally disables `warningAsError`.
-/

open E2E.Harness

namespace E2E.Ci

/-- Run the decision script, from `cwd` — which is where its `git log` looks. The
script itself is addressed absolutely, so the working directory can be a throwaway
repository rather than this one. -/
def runners (script cwd : String) (event ref : String) : IO String := do
  let out ← IO.Process.output { cmd := "sh", args := #[script, event, ref], cwd := some cwd }
  if out.exitCode != 0 then
    throw (IO.userError s!"ci-runners.sh failed ({out.exitCode}): {out.stderr}")
  return out.stdout.trimAscii.toString

/-- A throwaway git repository with one commit, dated `daysAgo` days back. Real
history, so the `--since` window is exercised rather than modelled.

Both dates are set, and that is the point: `git log --since` filters on the
COMMITTER date, while `--date=` sets only the author date. Setting just the author
date leaves the committer date at now, so a "45 days old" repo would still look fresh
and the negative check would pass for the wrong reason. `GIT_COMMITTER_DATE` will not
take approxidate ("45 days ago" is rejected outright), so git converts it: commit once
with approxidate, read the ISO value back, then amend with both set to it. -/
def repoWithCommit (daysAgo : Nat) : IO String := do
  let dir ← IO.FS.createTempDir
  let git := "git -c user.email=t@t -c user.name=t -c commit.gpgsign=false"
  let script :=
    s!"set -e; git init -q .; \
       {git} commit -q --allow-empty -m probe --date='{daysAgo} days ago'; \
       iso=\"$(git log -1 --format=%aI)\"; \
       GIT_COMMITTER_DATE=\"$iso\" {git} commit -q --amend --allow-empty --no-edit --date=\"$iso\""
  let out ← IO.Process.output { cmd := "sh", args := #["-c", script], cwd := some dir.toString }
  if out.exitCode != 0 then
    throw (IO.userError s!"probe repo setup failed: {out.stderr}")
  return dir.toString

/-- The repo root, so the script under test is the tracked one. -/
def repoRoot : IO String := do
  let out ← IO.Process.output { cmd := "git", args := #["rev-parse", "--show-toplevel"] }
  return out.stdout.trimAscii.toString

def ubuntuOnly : String := "[\"ubuntu-latest\"]"

def both : String := "[\"ubuntu-latest\", \"macos-latest\"]"

/-- Exercise Lake's actual traces and diagnostic replay without a clean rebuild. -/
def lakeBuilds (root : String) : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    IO.FS.createDirAll (dir / "Probe")
    IO.FS.writeFile (dir / "lean-toolchain") (← IO.FS.readFile s!"{root}/lean-toolchain")
    IO.FS.writeFile (dir / "lakefile.lean")
        "import Lake\nopen Lake DSL\npackage cacheProbe where\n\
       \x20 leanOptions := #[⟨`warningAsError, true⟩]\nlean_lib Probe\n"
    let source := dir / "Probe.lean"
    let dep := dir / "Probe" / "Dep.lean"
    let good := "import Probe.Dep\nexample : dependency = 1 := rfl\n"
    IO.FS.writeFile source good
    IO.FS.writeFile dep "def dependency : Nat := 1\n"
    let build := fun (flags : Array String) =>
      IO.Process.output
        { cmd := s!"{root}/lake"
          args := #["--dir", dir.toString, "--no-ansi", "--rehash"] ++ flags ++ #["build", "Probe"]
          cwd := some root }
    let seed : IO Unit := do
      let out ← build #["--wfail"]
      if out.exitCode != 0 then
        throw (IO.userError s!"Lake probe setup failed:\n{out.stdout}{out.stderr}")
    let check := fun (out : IO.Process.Output) (code : UInt32) (detail label : String) => do
      let ok := out.exitCode == code && has out.stdout detail
      if !ok then
        IO.eprintln s!"Lake probe exited {out.exitCode}:\n{out.stdout}{out.stderr}"
      expect ok label
    seed
    let mut f ←
      check (← build #["--wfail", "--no-build"]) 0 "All targets up-to-date"
          "unchanged Lake artifacts are reused without compilation"
    -- Keep the original .hash: trusting it would silently accept corrupt content.
    let artifact := dir / ".lake" / "build" / "lib" / "lean" / "Probe" / "Dep.olean"
    let compiled ← IO.FS.readBinFile artifact
    IO.FS.writeFile artifact "invalid cached dependency\n"
    f :=
      f +
        (←
          check (← build #["--wfail"]) 1 "invalid header"
              "a changed dependency artifact cannot hide behind its cached hash")
    IO.FS.writeBinFile artifact compiled
    seed
    IO.FS.writeFile dep "def dependency : Nat := 2\n"
    f :=
      f +
        (←
          check (← build #["--wfail"]) 1 "dependency = 1"
              "a changed dependency rechecks its cached importer")
    IO.FS.writeFile dep "def dependency : Nat := 1\n"
    seed
    IO.FS.writeFile source "import Probe.Dep\nexample : dependency = 2 := rfl\n"
    f :=
      f +
        (←
          check (← build #["--wfail"]) 1 "dependency = 2"
              "changed source cannot reuse a previously valid artifact")
    IO.FS.writeFile source
        "import Probe.Dep\nset_option warningAsError false\n\
       def warningProbe (unused : Nat) : Nat := dependency\n"
    let warning ← build #[]
    if warning.exitCode != 0 || !has warning.stdout "warning:" then
      throw (IO.userError s!"Lake warning setup failed:\n{warning.stdout}{warning.stderr}")
    f :=
      f +
        (←
          check (← build #["--wfail", "--no-build"]) 1 "warning:"
              "cached warnings fail even when warningAsError is locally disabled")
    return f
  finally
    IO.FS.removeDirAll dir

def run : IO UInt32 := do
  -- No `Env`, following `E2E/Coverage.lean`: this is not a pty suite, so it has no
  -- sockets, logs or checkpoints and needs no state directory. Making one anyway
  -- left an empty `/tmp/linger-ci-<pid>` behind on every failing run.
  let root ← repoRoot
  let script := s!"{root}/tests/ci-runners.sh"
  let mut f := 0
  -- The per-push path: ubuntu alone. This is the one that costs money when wrong.
  f :=
    f +
      (←
        expect ((← runners script root "push" "refs/heads/main") == ubuntuOnly)
            "a push to main asks for ubuntu alone")
  f :=
    f +
      (←
        expect ((← runners script root "pull_request" "refs/pull/7/merge") == ubuntuOnly)
            "a pull request asks for ubuntu alone")
  -- …and the three paths that do want the expensive runner.
  f :=
    f +
      (←
        expect ((← runners script root "push" "refs/tags/v1.2.3") == both)
            "a v* tag asks for both platforms")
  f :=
    f +
      (←
        expect ((← runners script root "workflow_dispatch" "refs/heads/main") == both)
            "a manual run asks for both platforms")
  -- The scheduled arm against real history, both ways. A repo whose only commit is
  -- older than the window must NOT pull in macOS; one inside it must.
  --
  -- Drive the real script for both valid histories and an unreadable one.
  -- Failure to inspect history must fail the job, not silently skip a platform.
  let fresh ← repoWithCommit 1
  let stale ← repoWithCommit 45
  try
    f :=
      f +
        (←
          expect ((← runners script fresh "schedule" "refs/heads/main") == both)
              "a scheduled run with a recent commit asks for both platforms")
    f :=
      f +
        (←
          expect ((← runners script stale "schedule" "refs/heads/main") == ubuntuOnly)
              "a scheduled run on an unchanged tree asks for ubuntu alone")
    IO.FS.removeDirAll (System.FilePath.mk fresh / ".git")
    let failed ←
      IO.Process.output
          { cmd := "sh", args := #[script, "schedule", "refs/heads/main"], cwd := some fresh }
    f :=
      f +
        (←
          expect (failed.exitCode != 0 && failed.stdout.trimAscii.isEmpty)
              "unreadable history fails without emitting a runner matrix")
  finally
    IO.FS.removeDirAll (System.FilePath.mk fresh)
    IO.FS.removeDirAll (System.FilePath.mk stale)
  f := f + (← lakeBuilds root)
  IO.println s!"FAILURES: {f}"
  return if f == 0 then 0 else 1

end E2E.Ci
