module

public import E2E.Harness
public import E2E.Runner

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

/-- Child fixtures for the actual suite runner, including its signal and log contract. -/
def runnerProbe (dir name : String) : IO UInt32 := do
  if name.startsWith "job-" then
    IO.FS.writeFile s!"{dir}/{name}" ""
    unless ← waitFor 5000 (System.FilePath.pathExists s!"{dir}/release") do
      IO.println "FAILURES: 1"
      return 1
    let signal ←
      IO.Process.output
          { cmd := "sh", args := #["-c", "trap 'exit 9' INT; kill -s INT $$; exit 7"] }
    if signal.exitCode != 9 then
      IO.println "FAILURES: 1"
      return 1
    -- More than a pipe buffer on each stream: redirection must not deadlock.
    IO.eprint (String.ofList (List.replicate 70000 'e') ++ "\n")
    IO.print (String.ofList (List.replicate 70000 'o') ++ "\n")
  if name == "after-error" then
    IO.sleep 200
  if name == "reported-failure" then
    IO.println "FAIL extra fixture"
  IO.println "PASS fixture"
  IO.println (if name == "bad-verdict" then "FAILURES: 1" else "FAILURES: 0")
  return if name == "bad-exit" then 1 else 0

def suiteRunner : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    let binary := (← IO.appPath).toString
    let run := E2E.Runner.run binary #["--runner-probe", dir.toString] dir
    let jobs := (List.range 5).map fun n => (s!"job-{n}", 1)
    let batch ← (run jobs).asTask .dedicated
    let ready ←
      waitFor 5000 do
          return ((← dir.readDir).filter (·.fileName.startsWith "job-")).size == 4
    -- A negative assertion: keep the observation window before releasing them.
    IO.sleep 200
    let held ← dir.readDir
    IO.FS.writeFile (dir / "release") ""
    let code ← IO.ofExcept (← IO.wait batch)
    let logs ← jobs.mapM fun (name, _) => IO.FS.readFile (dir / s!"linger-{name}.out")
    let streams :=
      logs.all fun text =>
        ['e', 'o'].all fun c => (lines text).contains (String.ofList (List.replicate 70000 c))
    let mut f ←
      expect (ready && (held.filter (·.fileName.startsWith "job-")).size == 4)
          "suite runner overlaps four children and holds the fifth until a slot opens"
    f :=
      f +
        (←
          expect (code == 0 && streams && (← System.FilePath.pathExists (dir / "job-4")))
              "suite runner captures both streams, preserves SIGINT and waits for every child")
    let bad ← run [("bad-exit", 1), ("after-error", 1)]
    let peer ← IO.FS.readFile (dir / "linger-after-error.out")
    f :=
      f +
        (←
          expect (bad == 1 && peer.endsWith "FAILURES: 0\n")
              "suite runner rejects a nonzero exit and still waits for the other children")
    f :=
      f +
        (←
          expect ((← run [("bad-verdict", 1)]) == 1)
              "suite runner rejects an unsuccessful final verdict")
    f :=
      f + (← expect ((← run [("wrong-count", 2)]) == 1) "suite runner rejects missing assertions")
    let reported ← run [("reported-failure", 1)]
    let report ← IO.FS.readFile (dir / "linger-reported-failure.out")
    f :=
      f +
        (←
          expect (reported == 1 && report == "FAIL extra fixture\nPASS fixture\nFAILURES: 0\n")
              "suite runner rejects a reported failure despite a successful summary and keeps its log")
    f :=
      f +
        (←
          expect ((← run [("same", 1), ("same", 1)]) == 2)
              "suite runner rejects duplicate log identities before starting children")
    return f
  finally
    IO.FS.removeDirAll dir

/-- Execute the workflow's actual dependency step with controlled package tools. -/
def dependencyInstall (root : String) : IO Nat := do
  let workflow ← IO.FS.readFile s!"{root}/.github/workflows/ci.yml"
  let [_, rest] := workflow.splitOn "      - name: install test dependencies\n        run: |\n"
    | throw (IO.userError "missing or ambiguous dependency installation step")
  let script :=
    String.intercalate "\n"
      (((rest.splitOn "\n      - ").head!).splitOn "\n" |>.map (fun s => (s.drop 10).toString))
  let probe := fun (os mode : String) (present : List String) => do
    let dir ← IO.FS.createTempDir
    try
      -- Private tools and fresh state isolate each availability/index case.
      let sudo := dir / "sudo"
      let brew := dir / "brew"
      IO.FS.writeFile sudo
          "#!/bin/sh\n\
         test \"$1\" = apt-get || exit 90\n\
         shift\n\
         printf '%s\\0' apt-get \"$@\" >> \"$INSTALL_LOG\"\n\
         if [ \"$1\" = update ]; then\n\
         \x20 [ \"$INSTALL_MODE\" != update-fail ] || exit 93\n\
         \x20 : > \"$INSTALL_READY\"\n\
         elif [ \"$INSTALL_MODE\" = fail ]; then\n\
         \x20 exit 91\n\
         elif [ \"$INSTALL_MODE\" != fresh ] && [ ! -e \"$INSTALL_READY\" ]; then\n\
         \x20 exit 92\n\
         fi\n"
      IO.FS.writeFile brew
          "#!/bin/sh\n\
         printf '%s\\0' brew \"$@\" >> \"$INSTALL_LOG\"\n\
         [ \"$INSTALL_MODE\" != fail ]\n"
      for tool in present do
        IO.FS.writeFile (dir / tool) "#!/bin/sh\nexit 0\n"
      for file in [sudo, brew] ++ present.map (fun tool => dir / System.FilePath.mk tool) do
        Linger.Posix.chmod file.toString 0o700
      let log := dir / "install.log"
      IO.FS.writeFile log ""
      let out ←
        IO.Process.output
            { cmd := "/bin/bash", args := #["--noprofile", "--norc", "-e", "-c", script]
              env :=
                #[("RUNNER_OS", some os), ("PATH", some dir.toString),
                  ("INSTALL_LOG", some log.toString),
                  ("INSTALL_READY", some (dir / "install.ready").toString),
                  ("INSTALL_MODE", some mode)] }
      return (out.exitCode, ← IO.FS.readFile log)
    finally
      IO.FS.removeDirAll dir
  -- NUL separators distinguish separate package arguments from one quoted string.
  let install := "apt-get\x00install\x00-y\x00-qq\x00--no-install-recommends\x00"
  let fish := install ++ "fish\x00"
  let retry := fish ++ "apt-get\x00update\x00-qq\x00" ++ fish
  let mut f ←
    expect ((← probe "Linux" "fresh" ["clang"]) == (0, fish))
        "CI uses the runner's package index when installation succeeds"
  f :=
    f +
      (←
        expect ((← probe "Linux" "stale" ["clang"]) == (0, retry))
            "CI refreshes stale package indexes and retries installation")
  let bad ← probe "Linux" "fail" ["clang"]
  f :=
    f +
      (←
        expect (bad.1 != 0 && bad.2 == retry)
            "CI fails when dependency installation still fails after refreshing")
  let update ← probe "Linux" "update-fail" ["clang"]
  f :=
    f +
      (←
        expect (update.1 != 0 && update.2 == fish ++ "apt-get\x00update\x00-qq\x00")
            "CI stops when refreshing package indexes fails")
  f :=
    f +
      (←
        expect ((← probe "Linux" "fresh" ["fish", "clang"]) == (0, ""))
            "CI skips package tools when Linux dependencies are present")
  f :=
    f +
      (←
        expect ((← probe "Linux" "fresh" ["fish"]) == (0, install ++ "clang\x00"))
            "CI installs only clang when fish is present")
  f :=
    f +
      (←
        expect ((← probe "Linux" "fresh" []) == (0, install ++ "fish\x00clang\x00"))
            "CI installs both missing Linux dependencies in one invocation")
  f :=
    f +
      (←
        expect ((← probe "macOS" "fresh" ["fish"]) == (0, ""))
            "CI skips package tools when macOS fish is present")
  f :=
    f +
      (←
        expect ((← probe "macOS" "fresh" []) == (0, "brew\x00install\x00fish\x00"))
            "CI installs missing macOS fish through Homebrew")
  let mac ← probe "macOS" "fail" []
  f :=
    f +
      (←
        expect (mac.1 != 0 && mac.2 == "brew\x00install\x00fish\x00")
            "CI fails when macOS dependency installation fails")
  return f

/-- Verification reuse keys the tracked inputs, including names and modes.
Unstaged or untracked inputs cannot accidentally borrow an indexed receipt. -/
def verificationInputs (root : String) : IO Nat := do
  let dir ← IO.FS.createTempDir
  try
    let git := fun (args : Array String) => do
      let out ← IO.Process.output { cmd := "git", args, cwd := some dir.toString }
      unless out.exitCode == 0 do
        throw (IO.userError s!"verification fixture git failed: {out.stderr}")
    git #["init", "--quiet"]
    git #["config", "core.fileMode", "true"]
    IO.FS.createDirAll (dir / "specs" / "archive")
    let input := dir / "source with spaces.lean"
    IO.FS.writeFile input "def value := 1\n"
    IO.FS.writeFile (dir / "AGENTS.md") "Active work.\n"
    IO.FS.writeFile (dir / "SCRATCHPAD.md") "Earlier evidence.\n"
    IO.FS.writeFile (dir / "specs" / "active.md") "Active record.\n"
    git #["add", "."]
    let probe :=
      IO.Process.output
        { cmd := "sh", args := #[s!"{root}/tests/ci-inputs.sh"], cwd := some dir.toString }
    let original ← probe
    let key := original.stdout.trimAscii.toString
    let mut f ←
      expect (original.exitCode == 0 && key.length == 40)
          "verification inputs produce a content key"
    let checkKey := fun (same : Bool) => do
      let next ← probe
      return next.exitCode == 0 && next.stdout.trimAscii.toString.length == 40 &&
          ((next.stdout == original.stdout) == same)
    f := f + (← expect (← checkKey true) "unchanged inputs keep their verification key")
    for name in ["RUNNER_OS", "RUNNER_ARCH", "ImageOS", "ImageVersion"] do
      let value := (← IO.getEnv name).getD "" ++ "-changed"
      let image ←
        IO.Process.output
            { cmd := "sh", args := #[s!"{root}/tests/ci-inputs.sh"], cwd := some dir.toString,
              env := #[(name, some value)] }
      f :=
        f +
          (←
            expect (image.exitCode == 0 && image.stdout != original.stdout)
                s!"changed {name} invalidates completed verification")
    IO.FS.writeFile input "def value := 2\n"
    let dirty ← probe
    f :=
      f +
        (←
          expect (dirty.exitCode != 0 && dirty.stdout.isEmpty)
              "unstaged input changes cannot reuse an indexed verification")
    git #["add", "."]
    let changed ← probe
    f :=
      f +
        (←
          expect (changed.exitCode == 0 && changed.stdout != original.stdout)
              "changed source invalidates completed verification")
    IO.FS.writeFile input "def value := 1\n"
    git #["add", "."]
    let unknown := dir / "new-input.data"
    IO.FS.writeFile unknown "new input\n"
    let untracked ← probe
    f :=
      f +
        (←
          expect (untracked.exitCode != 0 && untracked.stdout.isEmpty)
              "untracked inputs fail closed before a verification key is emitted")
    git #["add", "."]
    f := f + (← expect (← checkKey false) "new input kinds invalidate completed verification")
    git #["rm", "--quiet", "-f", "new-input.data"]
    IO.FS.writeFile (dir / "AGENTS.md") "Completed work.\n"
    IO.FS.writeFile (dir / "SCRATCHPAD.md") "Earlier evidence.\nNew evidence.\n"
    git
        #["mv", (System.FilePath.mk "specs" / "active.md").toString,
          (System.FilePath.mk "specs" / "archive" / "active.md").toString]
    git #["add", "."]
    f := f + (← expect (← checkKey true) "work records and archiving preserve the verification key")
    IO.FS.writeFile (dir / "specs" / "new-script.sh") "#!/bin/sh\nexit 1\n"
    git #["add", "."]
    f := f + (← expect (← checkKey false) "a non-record input under specs invalidates verification")
    git #["rm", "--quiet", "-f", "specs/new-script.sh"]
    Linger.Posix.chmod input.toString 0o755
    git #["add", "."]
    f := f + (← expect (← checkKey false) "file mode changes invalidate verification")
    Linger.Posix.chmod input.toString 0o644
    git #["add", "."]
    git #["mv", "source with spaces.lean", "renamed.lean"]
    f :=
      f +
        (←
          expect (← checkKey false)
              "renamed input paths invalidate verification despite identical bytes")
    git #["rm", "--quiet", "-f", "renamed.lean"]
    let empty ← probe
    f :=
      f +
        (←
          expect (empty.exitCode != 0 && empty.stdout.isEmpty)
              "an empty verification inventory is rejected")
    IO.FS.removeDirAll (dir / ".git")
    let missing ← probe
    f :=
      f +
        (←
          expect (missing.exitCode != 0 && missing.stdout.isEmpty)
              "unreadable source inventory cannot emit a verification key")
    return f
  finally
    IO.FS.removeDirAll dir

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
  f := f + (← suiteRunner)
  f := f + (← dependencyInstall root)
  f := f + (← verificationInputs root)
  IO.println s!"FAILURES: {f}"
  return if f == 0 then 0 else 1

end E2E.Ci
