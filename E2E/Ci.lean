module

public import E2E.Harness

public section

/-! # E2E.Ci — which runners CI asks for

`tests/ci-runners.sh` decides the GitHub matrix, and its two failure modes are both
silent and both expensive. Ask for macOS when nothing changed and a push bills several
times what it needs to; never ask for it and AGENTS.md's claim that the tree passes on
macOS stops being checked by anything. The billing arithmetic is in the `ci.yml` header
and SCRATCHPAD, not here.

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
  -- `try`/`finally` because `runners` throws when the script exits non-zero, and a
  -- suite that leaks its fixtures on failure is exactly what this file's own commit
  -- fixed elsewhere. There is deliberately no third check on the `git log` itself:
  -- one was written and deleted, because it ran `git` from Lean with an argv array,
  -- where `--since=8 days ago` is one argument BY CONSTRUCTION — so it could not
  -- exhibit the shell quoting bug it claimed to guard, whatever the script said. The
  -- "recent commit" check above already catches that: an unquoted `--since` makes git
  -- fail, empty output reads as no commits, and the answer collapses to ubuntu.
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
  finally
    IO.FS.removeDirAll (System.FilePath.mk fresh)
    IO.FS.removeDirAll (System.FilePath.mk stale)
  IO.println s!"FAILURES: {f}"
  return if f == 0 then 0 else 1

end E2E.Ci
