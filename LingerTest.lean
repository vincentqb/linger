module

import Linger.Posix

public section

/-! # lingertest — IO smoke tests for the Posix shim

Pure code is tested in `Tests/` at elaboration time; things that spawn
processes and poll fds need a real process. Each check prints PASS/FAIL;
exit code is the count of failures. Run via `./lake exe lingertest`.
-/

open Linger.Posix

def check (name : String) (cond : Bool) : IO Nat := do
  IO.println s!"{if cond then "PASS" else "FAIL"} {name}"
  return if cond then 0 else 1

def throws {α : Type} (action : IO α) : IO Bool := do
  try
    let _ ← action
    return false
  catch _ =>
    return true

/-- `action`'s answer, or `false` if asking threw — a path too long even to
stat is not a usable path. -/
def orFalse (action : IO Bool) : IO Bool := do
  try
    action
  catch _ =>
    return false

/-- Drain a pty until EOF or deadline, via poll — the daemon's read shape. -/
def drain (fd : UInt32) (deadlineMs : Nat) (acc : ByteArray) : IO ByteArray := do
  let mut out := acc
  while (← monotonicMs) < deadlineMs do
    let revs ← poll #[fd] #[POLLIN] 200
    let r := revs[0]!
    if r &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
      match ← read fd 65536 with
      | none =>
        return out -- EOF: child gone
      | some bs =>
        out := out ++ bs
  return out

/-- Poll-wait until the child is reaped or the deadline passes. -/
def reap (pid : UInt32) : IO Int64 := do
  let deadline := (← monotonicMs) + 5000
  let mut status : Int64 := -1
  while status == -1 && (← monotonicMs) < deadline do
    status ← waitpidNohang pid
    if status == -1 then
      IO.sleep 20
  return status

def testPtyEcho : IO Nat := do
  let (pid, master) ← spawnPty 80 24 "" "sh" #["-c", "echo hi-from-pty"] #["ZT=1"]
  let out ← drain master ((← monotonicMs) + 5000) .empty
  Linger.Posix.close master
  let mut fails := 0
  fails :=
    fails + (← check "pty spawn+echo roundtrip" ((String.fromUTF8! out).contains "hi-from-pty"))
  fails := fails + (← check "child reaped with status 0" ((← reap pid) == 0))
  return fails

def testPtyEnvAndInput : IO Nat := do
  -- the shell must see the extra env, and input written to the master
  -- must reach its stdin
  let (pid, master) ← spawnPty 80 24 "/" "sh" #[] #["LINGERTEST=marker42"]
  let _ ← write master "echo $LINGERTEST; pwd; exit\n".toUTF8 0
  let out ← drain master ((← monotonicMs) + 5000) .empty
  Linger.Posix.close master
  let txt := String.fromUTF8! out
  let mut fails := 0
  fails := fails + (← check "extra env visible in child" (txt.contains "marker42"))
  fails := fails + (← check "cwd honored" (txt.contains "\n/\r"))
  fails := fails + (← check "shell exited cleanly" ((← reap pid) == 0))
  return fails

def testUnixSocket : IO Nat := do
  let dir ← IO.FS.createTempDir
  let path := s!"{dir}/t.sock"
  let lfd ← unixListen path
  setNonblock lfd
  let mut fails := 0
  -- nothing pending yet
  fails := fails + (← check "accept on idle socket returns -1" ((← accept lfd) == -1))
  -- connect and pass bytes both ways
  let cfd := (← unixConnect path).toUInt64.toUInt32
  let revs ← poll #[lfd] #[POLLIN] 2000
  fails := fails + (← check "listen fd readable after connect" (revs[0]! &&& POLLIN != 0))
  let afd := (← accept lfd).toUInt64.toUInt32
  let _ ← write cfd "ping".toUTF8 0
  let revs2 ← poll #[afd] #[POLLIN] 2000
  fails := fails + (← check "accepted fd readable" (revs2[0]! &&& POLLIN != 0))
  let got := (← read afd 100).getD .empty
  fails := fails + (← check "bytes cross the socket" (String.fromUTF8! got == "ping"))
  -- peer-gone detection: close client, write from server side
  Linger.Posix.close cfd
  let w1 ← write afd "x".toUTF8 0
  let w2 ← write afd "x".toUTF8 0
  fails := fails + (← check "write to dead peer yields -1 (not a crash)" (w1 == -1 || w2 == -1))
  Linger.Posix.close afd
  Linger.Posix.close lfd
  IO.FS.removeDirAll dir
  -- connect to a nonexistent path: -ENOENT, not an exception
  let r ← unixConnect s!"{dir}/absent.sock"
  fails := fails + (← check "connect to absent socket is negative errno" (r < 0))
  return fails

def testWinsize : IO Nat := do
  let (pid, master) ← spawnPty 121 43 "" "sh" #["-c", "stty size; exit"] #[]
  let out ← drain master ((← monotonicMs) + 5000) .empty
  Linger.Posix.close master
  let _ ← reap pid
  -- stty prints "rows cols"
  check "pty spawned with requested winsize" ((String.fromUTF8! out).contains "43 121")

/-- The process wrappers must reject values POSIX reads as process-group or
"any child" selectors, and a wait status must only be read for a completed
requested child. Without this boundary, `waitpid(0, …, WNOHANG)` can report
another child of this process group and its status is inspected uninitialized. -/
def testProcessSelectors : IO Nat := do
  let mut fails := 0
  fails := fails + (← check "kill rejects pid 0" (← throws (kill 0 15)))
  fails := fails + (← check "alive rejects pid 0" (← throws (alive 0)))
  fails := fails + (← check "waitpidNohang rejects pid 0" (← throws (waitpidNohang 0)))
  -- Out-of-range for `pid_t`: these become negative selectors after the cast.
  let overflow : UInt32 := 0x80000000
  fails := fails + (← check "kill rejects out-of-range pid" (← throws (kill overflow 15)))
  fails := fails + (← check "alive rejects out-of-range pid" (← throws (alive overflow)))
  fails :=
    fails + (← check "waitpidNohang rejects out-of-range pid" (← throws (waitpidNohang overflow)))
  -- A live child of our own is still answered normally.
  let (pid, master) ← spawnPty 80 24 "" "sh" #["-c", "exit 3"] #[]
  let _ ← drain master ((← monotonicMs) + 5000) .empty
  Linger.Posix.close master
  fails := fails + (← check "waitpidNohang reports a real child's status" ((← reap pid) == 3))
  return fails

/-- A zero-length read is not EOF: `read(fd, buf, 0)` returns 0 without testing
for end of file, and `none` publicly means EOF.

No socket is set up, and that is the honest shape: `read` throws on `max == 0` before
it looks at the fd, so the eight lines of `unixListen`/`accept`/`write "ping"` that
used to precede this proved nothing — `read 999999 0` satisfies it identically. What
is pinned is the Lean guard. The shim carries the same refusal, but `readRaw` is
`private opaque` with no caller but the guarded wrapper, so that branch is
defence-in-depth against a future caller and no test can reach it today. -/
def testZeroLengthRead : IO Nat := do
  check "read of 0 bytes is refused, not reported as EOF" (← throws (read stdinFd 0))

/-- Child-side spawn failures must reach the parent. A missing program and a
malformed environment entry are both setup failures the caller has to see. -/
def testSpawnFailures : IO Nat := do
  let mut fails := 0
  fails :=
    fails +
      (←
        check "spawnPty reports a failed exec"
            (← throws (spawnPty 80 24 "" "linger-no-such-program-42" #[] #[])))
  fails :=
    fails +
      (←
        check "spawnPty rejects a malformed environment entry"
            (← throws (spawnPty 80 24 "" "sh" #["-c", "exit 0"] #["NOEQUALS"])))
  let dir ← IO.FS.createTempDir
  fails :=
    fails +
      (←
        check "spawnDetached reports a failed exec"
            (← throws (spawnDetached "linger-no-such-program-42" #[] s!"{dir}/log")))
  -- `execvp`'s ENOEXEC fallback: an executable file that is not an executable image
  -- (no shebang) is handed to the shell. The rewrite from `execvp` to `execve` dropped
  -- it, silently narrowing `linger attach <name> <cmd>` for exactly those files, and
  -- nothing caught the narrowing — this is the check that would have.
  --
  -- Wrapped so a missing fallback is a named FAIL and later checks still run.
  let script := s!"{dir}/noshebang"
  IO.FS.writeFile script "echo shebangless-ran\n"
  chmod script 0o755
  let ran ←
    try
      let (pid, master) ← spawnPty 80 24 "" script #[] #[]
      let out ← drain master ((← monotonicMs) + 5000) .empty
      Linger.Posix.close master
      let _ ← reap pid
      pure ((String.fromUTF8! out).contains "shebangless-ran")
    catch _ =>
      pure false
  fails := fails + (← check "a shebang-less executable still runs (execvp's ENOEXEC fallback)" ran)
  IO.FS.removeDirAll dir
  return fails

/-- Capture an exited child or its spawn error, cleaning up even when a check fails. -/
def ptyResult (cwd prog : String) (args extraEnv : Array String := #[]) (cols : UInt32 := 80)
    (rows : UInt32 := 24) : IO (Except String (String × Int64)) := do
  try
    let (pid, master) ← spawnPty cols rows cwd prog args extraEnv
    try
      let out ← drain master ((← monotonicMs) + 5000) .empty
      let status ← reap pid
      return .ok (String.fromUTF8! out, status)
    finally
      Linger.Posix.close master
      if (← waitpidNohang pid) == -1 then
        kill pid 9
        let _ ← reap pid
  catch e =>
    return .error e.toString

def resultIs (result : Except String (String × Int64)) (text : String) : Bool :=
  match result with
  | .ok (out, status) => out == text ++ "\r\n" && status == 0
  | .error _ => false

def resultFailed (result : Except String (String × Int64)) : Bool :=
  match result with
  | .error _ => true
  | .ok _ => false

/-- A direct failing path supplies the platform's error; no errno numbers in Lean. -/
def sameError (direct searched : Except String (String × Int64)) : Bool :=
  match direct, searched with
  | .error a, .error b => a == b
  | _, _ => false

def testPtyPath : IO Nat :=
  IO.FS.withTempDir fun dir => do
    let first := dir / "first"
    let second := dir / "second"
    IO.FS.createDir first
    IO.FS.createDir second
    for (path, text) in
      #[(dir / "pick", "cwd"), (first / "pick", "first"), (second / "pick", "second"),
        (dir / "local-only", "local"), (first / "remote-only", "remote")] do
      IO.FS.writeFile path s!"#!/bin/sh\necho {text}\n"
      chmod path.toString 0o755
    let mut fails := 0
    let run := fun prog path => ptyResult dir.toString prog #[] #[s!"PATH={path}"]
    fails :=
      fails +
        (←
          check "PATH order takes precedence over cwd"
              (resultIs (← run "pick" s!"{first}:{second}") "first"))
    fails :=
      fails +
        (←
          check "PATH excludes a command present only in cwd"
              (resultFailed (← run "local-only" first.toString)))
    fails :=
      fails +
        (←
          check "a trailing empty PATH component includes cwd"
              (resultIs (← run "local-only" s!"{first}:") "local"))
    fails :=
      fails + (← check "an empty PATH includes cwd" (resultIs (← run "local-only" "") "local"))
    fails :=
      fails +
        (←
          check "a slash-qualified command bypasses PATH"
              (resultIs (← run "./pick" first.toString) "cwd"))
    IO.FS.writeFile (dir / "not-a-directory") ""
    fails :=
      fails +
        (←
          check "PATH skips a nondirectory component"
              (resultIs (← run "remote-only" s!"{dir}/not-a-directory:{first}") "remote"))
    let denied := first / "denied"
    IO.FS.writeFile denied "#!/bin/sh\nexit 0\n"
    chmod denied.toString 0o600
    fails :=
      fails +
        (←
          check "PATH preserves permission denied ahead of a later miss"
              (sameError (← run denied.toString first.toString)
                (← run "denied" s!"{first}:{second}")))
    let _ ← IO.Process.run { cmd := "ln", args := #["-s", "loop", (dir / "loop").toString] }
    fails :=
      fails +
        (←
          check "PATH stops at a fatal lookup error"
              (sameError (← run s!"{dir}/loop/remote-only" first.toString)
                (← run "remote-only" s!"{dir}/loop:{first}")))
    let tooLong := String.ofList (List.replicate 4096 'x')
    fails :=
      fails +
        (←
          check "PATH skips a component exceeding its scratch buffer"
              (resultIs (← run "remote-only" s!"{tooLong}:{first}") "remote"))
    fails :=
      fails +
        (←
          check "an empty program is missing rather than a PATH directory"
              (sameError (← run s!"{dir}/missing" first.toString) (← run "" first.toString)))
    let script := first / "plain"
    IO.FS.writeFile script "printf 'path:%s:%s\\n' \"$1\" \"$LINGERTEST\"\n"
    chmod script.toString 0o755
    fails :=
      fails +
        (←
          check "PATH shell fallback preserves arguments and environment"
              (resultIs
                (←
                  ptyResult dir.toString "plain" #["two words"]
                      #[s!"PATH={first}", "LINGERTEST=child"])
                "path:two words:child"))
    fails :=
      fails +
        (←
          check "a vanished cwd falls back to the child's HOME"
              (resultIs (← ptyResult s!"{dir}/gone" "/bin/sh" #["-c", "pwd"] #[s!"HOME={first}"])
                (← IO.FS.realPath first).toString))
    return fails

/-- Run in a disposable process: closing stdio must not clobber the spawn report. -/
def closedStdioProbe (kind logPath : String) : IO UInt32 := do
  for fd in #[0, 1, 2] do
    Linger.Posix.close fd
  let passed : Bool ←
    if kind == "pty-error" then
      do
        pure (resultFailed (← ptyResult "" "/linger-test-no-such-program"))
    else if kind == "pty-ok" then
      do
        pure (resultIs (← ptyResult "" "/bin/sh" #["-c", "echo closed-pty"]) "closed-pty")
    else if kind == "detached-error" then
      throws (spawnDetached "/linger-test-no-such-program" #[] "")
    else
      orFalse do
          spawnDetached "/bin/sh" #["-c", "echo closed-out; echo closed-err >&2"] logPath
          return true
  let mut closed := true
  for fd in #[0, 1, 2] do
    closed := (← throws (setNonblock fd)) && closed
  return if passed && closed then 0 else 1

def testClosedStdio : IO Nat :=
  IO.FS.withTempDir fun dir => do
    let app := (← IO.appPath).toString
    let logPath := (dir / "detached.log").toString
    let mut fails := 0
    for kind in #["pty-error", "pty-ok", "detached-error", "detached-ok"] do
      let child ←
        IO.Process.output { cmd := app, args := #["--closed-stdio", kind, logPath], setsid := true }
      let mut passed := child.exitCode == 0
      if kind == "detached-ok" then
        let deadline := (← monotonicMs) + 5000
        let mut logged := false
        while !logged && (← monotonicMs) < deadline do
          logged ←
            orFalse do
                let text ← IO.FS.readFile logPath
                return text == "closed-out\nclosed-err\n"
          unless logged do
            IO.sleep 20
        passed := passed && logged
      fails := fails + (← check s!"spawn with closed stdio: {kind}" passed)
    return fails

/-- Preserve detached exec's PATH and text-script semantics when sharing the
preallocated exec machinery with PTY spawning. -/
def testDetachedPath : IO Nat :=
  IO.FS.withTempDir fun dir => do
    let bin := dir / "bin"
    IO.FS.createDir bin
    let prog := bin / "detached-plain"
    IO.FS.writeFile prog "printf '<%s><%s><%s>\\n' \"$1\" \"$2\" \"$LINGERTEST\"\n"
    chmod prog.toString 0o755
    IO.FS.writeFile (dir / "detached-plain") "#!/bin/sh\necho wrong-cwd\n"
    chmod (dir / "detached-plain").toString 0o755
    let logPath := (dir / "detached.log").toString
    let child ←
      IO.Process.output
          { cmd := (← IO.appPath).toString, args := #["--detached-path-child", logPath],
            cwd := some dir, env := #[("PATH", some bin.toString), ("LINGERTEST", some "child")] }
    let deadline := (← monotonicMs) + 5000
    let mut logged := false
    while !logged && (← monotonicMs) < deadline do
      logged ←
        orFalse do
            return (← IO.FS.readFile logPath) == "<two words><><child>\n"
      unless logged do
        IO.sleep 20
    check "detached PATH shell fallback preserves arguments, environment and output"
        (child.exitCode == 0 && logged)

/-- POSIX strings cannot contain NUL: truncating one can name a different
resource or execute different arguments. Each fixture has a valid prefix so a
missing guard succeeds instead of accidentally passing on an unrelated error. -/
def testCStringInputs : IO Nat :=
  IO.FS.withTempDir fun dir => do
    let nul := String.singleton (Char.ofNat 0)
    let suffix := nul ++ "suffix"
    let mut fails := 0
    for (kind, cwd, prog, args, env) in
      #[("cwd", dir.toString ++ suffix, "/bin/sh", #["-c", "exit 0"], #[]),
        ("program", "", "/bin/sh" ++ suffix, #["-c", "exit 0"], #[]),
        ("argument", "", "/bin/sh", #["-c", "exit 0" ++ suffix], #[]),
        ("environment", "", "/bin/sh", #["-c", "exit 0"], #["A=ok" ++ suffix])] do
      fails :=
        fails +
          (←
            check s!"spawnPty rejects NUL in {kind}" (resultFailed (← ptyResult cwd prog args env)))
    fails :=
      fails +
        (←
          check "spawnPty rejects an empty environment key"
              (resultFailed (← ptyResult "" "/bin/sh" #["-c", "exit 0"] #["=value"])))
    fails :=
      fails +
        (←
          check "empty arguments, empty env values and UTF-8 survive exec"
              (resultIs
                (←
                  ptyResult "" "/bin/sh"
                      #["-c", "printf '<%s><%s><%s>\\n' \"$1\" \"$2\" \"$EMPTY\"", "fixture", "",
                        "héλ"]
                      #["EMPTY="])
                "<><héλ><>"))
    let socket := (dir / "socket").toString
    fails :=
      fails +
        (←
          check "unixListen rejects a NUL path"
              (←
                throws do
                    let fd ← unixListen (socket ++ suffix)
                    Linger.Posix.close fd))
    -- The broken listen above creates its valid prefix; give the connect fixture
    -- its own live socket so it cannot pass merely because a socket is absent.
    let socket2 := (dir / "connect").toString
    let lfd ← unixListen socket2
    try
      fails :=
        fails +
          (←
            check "unixConnect rejects a NUL path"
                (←
                  throws do
                      let fd ← unixConnect (socket2 ++ suffix)
                      if fd ≥ 0 then
                        Linger.Posix.close fd.toUInt64.toUInt32))
    finally
      Linger.Posix.close lfd
    fails :=
      fails +
        (←
          check "flock rejects a NUL path"
              (←
                throws do
                    let fd ← flock ((dir / "lock").toString ++ suffix)
                    if fd ≥ 0 then
                      Linger.Posix.close fd.toUInt64.toUInt32))
    let file := (dir / "mode").toString
    IO.FS.writeFile file ""
    fails := fails + (← check "chmod rejects a NUL path" (← throws (chmod (file ++ suffix) 0o600)))
    for (kind, prog, args, logPath) in
      #[("program", "/bin/sh" ++ suffix, #["-c", "exit 0"], ""),
        ("argument", "/bin/sh", #["-c", "exit 0" ++ suffix], ""),
        ("log path", "/bin/sh", #["-c", "exit 0"], (dir / "log").toString ++ suffix)] do
      fails :=
        fails +
          (←
            check s!"spawnDetached rejects NUL in {kind}"
                (← throws (spawnDetached prog args logPath)))
    return fails

/-- The public UInt32 dimensions must fit the kernel's unsigned-short fields
without wrapping. Zero retains POSIX's unspecified-size meaning. -/
def testWinsizeBounds : IO Nat := do
  let mut fails := 0
  for (label, cols, rows) in #[("columns", 65536, 24), ("rows", 80, 65536)] do
    fails :=
      fails +
        (←
          check s!"spawnPty rejects overflowing {label}"
              (resultFailed (← ptyResult "" "/bin/sh" #["-c", "exit 0"] #[] cols rows)))
  let (pid, master) ← spawnPty 80 24 "" "/bin/cat" #[] #[]
  try
    for (label, cols, rows) in #[("columns", 65536, 24), ("rows", 80, 65536)] do
      winsizeSet master 80 24
      let refused ← throws (winsizeSet master cols rows)
      fails :=
        fails +
          (←
            check s!"winsizeSet rejects overflowing {label} without changing the tty"
                (refused && (← winsizeGet master) == (80, 24)))
    let preserved ←
      orFalse do
          winsizeSet master 0 0
          let zero ← winsizeGet master
          winsizeSet master 65535 65535
          let largest ← winsizeGet master
          return zero == (0, 0) && largest == (65535, 65535)
    fails :=
      fails + (← check "winsizeSet preserves zero and the largest representable size" preserved)
  finally
    kill pid 9
    Linger.Posix.close master
    let _ ← reap pid
  return fails

/-- `getcwdOf` feeds the checkpoint's `cwd`, which a resume hands to `chdir`, so a
path it cannot report in full has to come back empty rather than cut: a truncated
path names a different directory, or none. The child walks past `PATH_MAX`
relatively with physical `cd`: a shell's logical `cd` may rebuild an absolute
path and reject it before the child reaches the length under test. -/
def testDeepCwd : IO Nat := do
  let seg := String.ofList (List.replicate 49 'd')
  let dir ← IO.FS.createTempDir
  let deep :=
    s!"for i in $(seq 90); do mkdir -p {seg} && cd -P {seg} || exit 1; done; echo deep; cat"
  let (pid, master) ← spawnPty 80 24 dir.toString "sh" #["-c", deep] #[]
  let out ← drain master ((← monotonicMs) + 5000) .empty
  let walked := (String.fromUTF8! out).contains "deep"
  let cwd ← getcwdOf pid
  -- Judged BEFORE the tree is removed. Evaluated after, `isDir` fails for *any*
  -- non-empty answer — a correctly reported full path included — so the check
  -- silently degraded to "the answer was empty" and could not distinguish a good
  -- non-empty path from a truncated one. That matters on macOS, where the sibling
  -- `#ifdef __APPLE__` branch NUL-terminates a libproc path rather than refusing it.
  let usable ← orFalse (if cwd == "" then pure true else System.FilePath.isDir cwd)
  kill pid 9
  Linger.Posix.close master
  let _ ← reap pid
  -- `removeDirAll` builds full paths, which this tree is too deep for; `rm -r`
  -- walks it with directory-relative openat.
  let _ ← IO.Process.run { cmd := "rm", args := #["-r", dir.toString] }
  let mut fails ← check "child walked past PATH_MAX" walked
  fails := fails + (← check "getcwdOf reports a usable directory or nothing" usable)
  return fails

def main (args : List String) : IO UInt32 := do
  if let ["--closed-stdio", kind, logPath] := args then
    return ← closedStdioProbe kind logPath
  if let ["--detached-path-child", logPath] := args then
    return if (← throws (spawnDetached "detached-plain" #["two words", ""] logPath)) then 1 else 0
  let mut fails := 0
  fails := fails + (← testPtyEcho)
  fails := fails + (← testPtyEnvAndInput)
  fails := fails + (← testUnixSocket)
  fails := fails + (← testWinsize)
  fails := fails + (← testProcessSelectors)
  fails := fails + (← testZeroLengthRead)
  fails := fails + (← testSpawnFailures)
  fails := fails + (← testPtyPath)
  fails := fails + (← testClosedStdio)
  fails := fails + (← testDetachedPath)
  fails := fails + (← testCStringInputs)
  fails := fails + (← testWinsizeBounds)
  fails := fails + (← testDeepCwd)
  IO.println (if fails == 0 then "ALL PASS" else s!"{fails} FAILURES")
  return fails.toUInt32
