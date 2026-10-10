module

public import E2E.Harness

public section

/-! # E2E.Hygiene — source checks and pre-commit against real Git indexes

Fixtures run the repository's actual script from temporary repositories. A failed
fixture must name the offending path and check; an arbitrary subprocess error is
not evidence that hygiene worked. Installed hooks must check the staged snapshot
and preserve unstaged edits.
-/

namespace E2E.Hygiene

open E2E.Harness

private def fixtureEnv : Array (String × Option String) :=
  #[("GIT_DIR", none), ("GIT_WORK_TREE", none), ("GIT_INDEX_FILE", none),
    ("GIT_CONFIG_GLOBAL", some "/dev/null"), ("GIT_CONFIG_SYSTEM", some "/dev/null")]

private def command (cwd : System.FilePath) (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args, cwd := some cwd.toString, env := fixtureEnv }
  unless out.exitCode == 0 do
    throw (IO.userError s!"hygiene fixture setup ({cmd}): {out.stdout}{out.stderr}")
  return out.stdout

private def git (cwd : System.FilePath) (args : Array String) : IO String :=
  command cwd "git" (#["-c", "core.autocrlf=false", "-c", "core.safecrlf=false"] ++ args)

/-- Run the script from `cwd` and judge it: success, or exit 1 naming `path` and
`diagnostic`. `also` is read after the script runs and must hold too. -/
private def check (script : String) (cwd : System.FilePath) (path diagnostic label : String)
    (also : IO Bool := pure true) : IO Unit := do
  let out ←
    IO.Process.output
        { cmd := "sh", args := #[script], cwd := some cwd.toString, env := fixtureEnv }
  let verdict :=
    if diagnostic.isEmpty then out.exitCode == 0
    else out.exitCode == 1 && has out.stderr path && has out.stderr diagnostic
  let ok := verdict && (← also)
  unless ok do
    IO.eprintln s!"hygiene fixture exited {out.exitCode}:\n{out.stdout}{out.stderr}"
  expect ok label

/-- A fresh Git repository in its own temporary directory. -/
private def withRepo (body : System.FilePath → IO Unit) : IO Unit :=
  IO.FS.withTempDir fun repo => do
    let _ ← git repo #["init", "-q"]
    body repo

/-- One tracked file in a repository path with spaces; the check must also leave
the file's bytes unchanged. -/
private def fixture (script path content : String) (executable : Bool) (diagnostic label : String) :
    IO Unit :=
  IO.FS.withTempDir fun dir => do
    let repo := dir / "repo with spaces"
    IO.FS.createDirAll repo
    let _ ← git repo #["init", "-q"]
    let file := repo / path
    IO.FS.createDirAll file.parent.get!
    IO.FS.writeFile file content
    Linger.Posix.chmod file.toString (if executable then 0o755 else 0o644)
    let _ ← git repo #["add", "--", path]
    check script repo path diagnostic label (return (← IO.FS.readFile file) == content)

def run : IO UInt32 := do
  let root ← command (← IO.currentDir) "git" #["rev-parse", "--show-toplevel"]
  let script := s!"{root.trimAscii}/scripts/hygiene.sh"
  let atLimit := String.ofList (List.replicate (256 * 1024 - 1) 'x') ++ "\n"
  for (path, content, executable, diagnostic, label) in
    [("empty.txt", "", false, "", "hygiene accepts an empty file"),
      ("newline.txt", "\n", false, "", "hygiene accepts a single newline"),
      ("nested/a file.lean", "def café := \"λ\"\n\n-- end\n", false, "",
        "hygiene accepts Unicode, interior blank lines and paths with spaces"),
      ("line breaks.md", "first  \nsecond\n", false, "", "hygiene preserves Markdown hard breaks"),
      ("line breaks.Md", "first  \nsecond\n", false, "",
        "hygiene recognizes Markdown extensions case insensitively"),
      ("-odd=name\\with\ttab.txt", "clean\n", false, "",
        "hygiene handles option-like paths, backslashes and tabs"),
      ("script with spaces.sh", "#!/bin/sh\nexit 0\n", true, "",
        "hygiene accepts an executable with a shebang"),
      ("markers.txt", "text <<<<<<< main\ntext =======\ntext >>>>>>> branch\n", false, "",
        "hygiene accepts inline marker text"),
      ("history.md", "||||||| parent of a historical change\n", false, "",
        "hygiene preserves standalone base labels in the immutable history"),
      ("heading.md", "Heading\n========\n", false, "",
        "hygiene accepts Markdown heading underlines"),
      ("newline\nname.txt", "clean\n", false, "", "hygiene handles newlines in tracked paths"),
      ("source with spaces.lean", "def x := 0 \n", false, "trailing whitespace",
        "hygiene rejects trailing spaces"),
      ("tab.txt", "text\t\n", false, "trailing whitespace", "hygiene rejects trailing tabs"),
      ("one.md", "text \n", false, "trailing whitespace",
        "hygiene rejects one trailing Markdown space"),
      ("three.md", "text   \n", false, "trailing whitespace",
        "hygiene rejects extra Markdown spaces"),
      ("blank.md", "text\n  \nend\n", false, "trailing whitespace",
        "hygiene rejects whitespace-only Markdown lines"),
      ("tab.md", "text\t  \n", false, "trailing whitespace",
        "hygiene rejects tabs before Markdown hard breaks"),
      ("missing.txt", "text", false, "final newline", "hygiene rejects a missing final newline"),
      ("blank.txt", "text\n\n", false, "trailing blank",
        "hygiene rejects extra trailing blank lines"),
      ("blank-only.txt", "\n\n", false, "trailing blank",
        "hygiene rejects multiple newline-only lines"),
      ("crlf.txt", "text\r\n", false, "carriage return", "hygiene rejects CRLF"),
      ("mixed.txt", "first\nsecond\r\n", false, "carriage return",
        "hygiene rejects mixed line endings"),
      ("cr.txt", "first\rsecond\n", false, "carriage return",
        "hygiene rejects bare carriage returns"),
      ("ours.txt", "<<<<<<< main\n", false, "conflict marker",
        "hygiene rejects opening conflict markers"),
      ("separator.txt", "=======\n", false, "conflict marker",
        "hygiene rejects conflict separators"),
      ("theirs.txt", ">>>>>>> branch\n", false, "conflict marker",
        "hygiene rejects closing conflict markers"),
      ("bare.txt", "<<<<<<<\n", false, "conflict marker", "hygiene rejects bare conflict markers"),
      ("executable.txt", "text\n", true, "executable without shebang",
        "hygiene rejects executable text without a shebang"),
      ("script.sh", "#!/bin/sh\nexit 0\n", false, "shebang without executable",
        "hygiene rejects nonexecutable scripts"),
      ("empty-executable", "", true, "executable without shebang",
        "hygiene rejects empty executables"),
      ("limit.txt", atLimit, false, "", "hygiene accepts exactly 256 KiB"),
      ("too big.txt", "x" ++ atLimit, false, "256 KiB", "hygiene rejects one byte over 256 KiB"),
      ("SCRATCHPAD.md", "x" ++ atLimit, false, "256 KiB",
        "hygiene applies the size limit to former work logs"),
      ("nested/SCRATCHPAD.md", "x" ++ atLimit, false, "256 KiB",
        "hygiene applies the size limit to nested work logs"),
      ("SCRATCHPAD.md", "bad \n", false, "trailing whitespace",
        "hygiene checks whitespace in former work logs")] do
    fixture script path content executable diagnostic label
  withRepo fun repo => do
      IO.FS.writeFile (repo / "untracked file.txt") "bad \r\n\n"
      check script repo "" "" "hygiene ignores untracked files in an empty index"
  withRepo fun repo => do
      IO.FS.writeFile (repo / "target with spaces") "bad \r\n\n"
      let _ ← command repo "ln" #["-s", "target with spaces", "tracked link"]
      let _ ← git repo #["add", "--", "tracked link"]
      check script repo "" "" "hygiene does not follow tracked symbolic links"
  withRepo fun repo => do
      IO.FS.writeBinFile (repo / "binary fixture") (ByteArray.mk #[0, 13, 10, 32, 32, 255])
      let _ ← git repo #["add", "--", "binary fixture"]
      check script repo "" "" "hygiene skips binary text checks"
  withRepo fun repo => do
      IO.FS.writeBinFile (repo / "large binary") ((ByteArray.mk #[0]) ++ atLimit.toUTF8)
      let _ ← git repo #["add", "--", "large binary"]
      check script repo "large binary" "256 KiB" "hygiene still limits binary file size"
  withRepo fun repo => do
      IO.FS.writeFile (repo / "tracked.txt") "clean\n"
      let _ ← git repo #["add", "--", "tracked.txt"]
      IO.FS.writeFile (repo / "tracked.txt") "dirty \n"
      IO.FS.createDirAll (repo / "nested")
      check script (repo / "nested") "tracked.txt" "trailing whitespace"
          "hygiene checks working bytes and resolves the root from a subdirectory"
  withRepo fun repo => do
      IO.FS.writeFile (repo / "script.sh") "#!/bin/sh\nexit 0\n"
      Linger.Posix.chmod (repo / "script.sh").toString 0o755
      let _ ← git repo #["add", "--", "script.sh"]
      let _ ← git repo #["update-index", "--chmod=-x", "--", "script.sh"]
      check script repo "script.sh" "shebang without executable"
          "hygiene checks the executable mode that Git will publish"
  withRepo fun repo => do
      IO.FS.writeFile (repo / "missing.txt") "clean\n"
      let _ ← git repo #["add", "--", "missing.txt"]
      IO.FS.removeFile (repo / "missing.txt")
      check script repo "missing.txt" "not a regular file"
          "hygiene fails closed on a missing tracked file"
  withRepo fun repo => do
      IO.FS.writeFile (repo / "conflicted.txt") "clean\n"
      let _ ← git repo #["add", "--", "conflicted.txt"]
      let blob ← git repo #["rev-parse", ":conflicted.txt"]
      let _ ← git repo #["update-index", "--force-remove", "--", "conflicted.txt"]
      IO.FS.writeFile (repo / "index entries") s!"100644 {blob.trimAscii} 1\tconflicted.txt\n"
      let _ ← command repo "sh" #["-c", "git update-index --index-info < 'index entries'"]
      check script repo "conflicted.txt" "unmerged index entry"
          "hygiene rejects an unmerged index even with clean working bytes"
  withRepo fun repo => do
      IO.FS.writeFile (repo / ".git" / "index") "broken index\n"
      let out ←
        IO.Process.output
            { cmd := "sh", args := #[script], cwd := some repo.toString, env := fixtureEnv }
      expect (out.exitCode != 0 && has out.stderr "index")
          "hygiene propagates a failed Git inventory"
  IO.FS.withTempDir fun dir => do
      let out ←
        IO.Process.output
            { cmd := "sh", args := #[script], cwd := some dir.toString, env := fixtureEnv }
      expect (out.exitCode != 0 && has out.stderr "not a git repository")
          "hygiene fails when Git cannot provide the source inventory"
  IO.FS.withTempDir fun dir => do
      let repo := dir / "repo with spaces"
      let tools := dir / "tools"
      IO.FS.createDirAll repo
      IO.FS.createDirAll tools
      let _ ← git repo #["init", "-q"]
      IO.FS.createDirAll (repo / "scripts")
      IO.FS.writeFile (repo / "scripts" / "hygiene.sh") (← IO.FS.readFile script)
      IO.FS.writeFile (repo / "scripts" / "lint.sh")
          (← IO.FS.readFile s!"{root.trimAscii}/scripts/lint.sh")
      IO.FS.writeFile (repo / ".pre-commit-config.yaml")
          (← IO.FS.readFile s!"{root.trimAscii}/.pre-commit-config.yaml")
      -- Exercise the actual configuration without recursively running gates
      -- or linting this deliberately incomplete project.
      IO.FS.writeFile (repo / "scripts" / "gates.sh")
          "#!/bin/sh\nprintf 'source-gates:%s\\n' \"$*\" >> .git/hook-trace\n\
           if [ -f .git/reject-gates ]; then\n\
           printf '%s\\n' 'fixture: source gates rejected' >&2\nexit 42\nfi\n"
      for tool in ["actionlint", "lean-fmt"] do
        IO.FS.writeFile (tools / tool)
            s!"#!/bin/sh\nprintf '{tool}:%s\\n' \"$*\" >> .git/hook-trace\n\
               if [ -f \".git/reject-{tool}-$1\" ]; then\n\
               printf '%s\\n' 'fixture: {tool} rejected' >&2\nexit 43\nfi\n"
        Linger.Posix.chmod (tools / tool).toString 0o755
      for name in ["hygiene.sh", "gates.sh", "lint.sh"] do
        Linger.Posix.chmod (repo / "scripts" / name).toString 0o755
      IO.FS.writeFile (repo / "staged.txt") "clean\n"
      let _ ← git repo #["add", "--", ".pre-commit-config.yaml", "scripts", "staged.txt"]
      let commitArgs :=
        #["-c", "user.name=fixture", "-c", "user.email=fixture@example.invalid", "-c",
          "commit.gpgsign=false", "commit", "-q", "--allow-empty", "-m", "fixture"]
      let _ ← git repo commitArgs
      let env :=
        fixtureEnv ++
          #[("PATH", some s!"{tools}:{(← IO.getEnv "PATH").getD ""}"),
            ("PRE_COMMIT_HOME", some (dir / "cache").toString), ("SKIP", none),
            ("PRE_COMMIT_ALLOW_NO_CONFIG", none)]
      let invoke := fun cmd args => IO.Process.output { cmd, args, cwd := some repo.toString, env }
      let installed ← invoke "pre-commit" #["install"]
      unless installed.exitCode == 0 do
        throw (IO.userError s!"hook installation: {installed.stdout}{installed.stderr}")
      let trace := repo / ".git" / "hook-trace"
      let commit := do
        IO.FS.writeFile trace ""
        let out ← invoke "git" commitArgs
        return (out, ← IO.FS.readFile trace)
      let workflowTrace := "source-gates:\nactionlint:-shellcheck= -pyflakes=\n"
      let layoutTrace := workflowTrace ++ "lean-fmt:format --check\n"
      let expected := layoutTrace ++ "lean-fmt:check\n"
      let (empty, calls) ← commit
      expect (empty.exitCode == 0 && calls == expected)
          "pre-commit runs every check once with the intended arguments on an empty commit"
      IO.FS.writeFile (repo / "staged.txt") "bad \n"
      let _ ← git repo #["add", "--", "staged.txt"]
      IO.FS.writeFile (repo / "staged.txt") "clean\n"
      let (hidden, calls) ← commit
      expect
          (hidden.exitCode == 1 &&
            has (hidden.stdout ++ hidden.stderr) "staged.txt:1: trailing whitespace" &&
            calls.isEmpty)
          "pre-commit rejects invalid staged bytes hidden by an unstaged correction"
      expect
          ((← IO.FS.readFile (repo / "staged.txt")) == "clean\n" &&
            (← git repo #["show", ":staged.txt"]) == "bad \n")
          "pre-commit restores unstaged edits and preserves the rejected index"
      let _ ← git repo #["add", "--", "staged.txt"]
      IO.FS.writeFile (repo / "staged.txt") "unstaged \n"
      let (stagedOnly, calls) ← commit
      expect
          (stagedOnly.exitCode == 0 && calls == expected &&
            (← IO.FS.readFile (repo / "staged.txt")) == "unstaged \n" &&
            (← git repo #["show", "HEAD:staged.txt"]) == "clean\n")
          "pre-commit accepts a clean index without committing or changing unstaged bytes"
      let _ ← git repo #["add", "--", "staged.txt"]
      let (invalid, calls) ← commit
      expect
          (invalid.exitCode == 1 &&
            has (invalid.stdout ++ invalid.stderr) "staged.txt:1: trailing whitespace" &&
            calls.isEmpty)
          "pre-commit rejects fully staged invalid content before later checks"
      IO.FS.writeFile (repo / "staged.txt") "clean\n"
      let _ ← git repo #["add", "--", "staged.txt"]
      IO.FS.writeFile (repo / ".git" / "reject-gates") ""
      let (rejected, calls) ← commit
      expect
          (rejected.exitCode == 1 &&
            has (rejected.stdout ++ rejected.stderr) "fixture: source gates rejected" &&
            calls == "source-gates:\n")
          "pre-commit propagates source-gate failure and stops before optional tools"
      IO.FS.removeFile (repo / ".git" / "reject-gates")
      for (tool, arg, expectedCalls) in
        [("actionlint", "-shellcheck=", workflowTrace), ("lean-fmt", "format", layoutTrace),
          ("lean-fmt", "check", expected)] do
        let marker := repo / ".git" / s!"reject-{tool}-{arg}"
        IO.FS.writeFile marker ""
        let (rejected, calls) ← commit
        expect
            (rejected.exitCode == 1 &&
              has (rejected.stdout ++ rejected.stderr) s!"fixture: {tool} rejected" &&
              calls == expectedCalls)
            s!"pre-commit propagates {tool} {arg} failure and stops later checks"
        IO.FS.removeFile marker
      let _ ← git repo #["rm", "--", "staged.txt"]
      let (deleted, calls) ← commit
      expect (deleted.exitCode == 0 && calls == expected)
          "pre-commit runs every check on a deletion-only commit"
  finish

end E2E.Hygiene
