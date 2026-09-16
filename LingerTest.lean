module

public import Linger.Posix

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

def contains (haystack needle : String) : Bool := (haystack.splitOn needle).length ≥ 2

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
partial def drain (fd : UInt32) (deadlineMs : UInt64) (acc : ByteArray) : IO ByteArray := do
  let now ← monotonicMs
  if now ≥ deadlineMs then
    return acc
  let revs ← poll #[fd] #[POLLIN] 200
  let r := revs[0]!
  if r &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
    drain fd deadlineMs acc
  else
    match ← read fd 65536 with
    | none =>
      return acc -- EOF: child gone
    | some bs =>
      drain fd deadlineMs (acc ++ bs)

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
    fails + (← check "pty spawn+echo roundtrip" (contains (String.fromUTF8! out) "hi-from-pty"))
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
  fails := fails + (← check "extra env visible in child" (contains txt "marker42"))
  fails := fails + (← check "cwd honored" (contains txt "\n/\r"))
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
  check "pty spawned with requested winsize" (contains (String.fromUTF8! out) "43 121")

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
  -- A live child of our own is still answered normally.
  let (pid, master) ← spawnPty 80 24 "" "sh" #["-c", "exit 3"] #[]
  let _ ← drain master ((← monotonicMs) + 5000) .empty
  Linger.Posix.close master
  fails := fails + (← check "waitpidNohang reports a real child's status" ((← reap pid) == 3))
  return fails

/-- A zero-length read is not EOF: `read(fd, buf, 0)` returns 0 without testing
for end of file, and `none` publicly means EOF. -/
def testZeroLengthRead : IO Nat := do
  let dir ← IO.FS.createTempDir
  let path := s!"{dir}/t.sock"
  let lfd ← unixListen path
  setNonblock lfd
  let cfd := (← unixConnect path).toUInt64.toUInt32
  let _ ← poll #[lfd] #[POLLIN] 2000
  let afd := (← accept lfd).toUInt64.toUInt32
  let _ ← write cfd "ping".toUTF8 0
  let _ ← poll #[afd] #[POLLIN] 2000
  let fails ← check "read of 0 bytes is refused, not reported as EOF" (← throws (read afd 0))
  Linger.Posix.close cfd
  Linger.Posix.close afd
  Linger.Posix.close lfd
  IO.FS.removeDirAll dir
  return fails

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
  IO.FS.removeDirAll dir
  return fails

/-- `getcwdOf` feeds the checkpoint's `cwd`, which a resume hands to `chdir`, so a
path it cannot report in full has to come back empty rather than cut: a truncated
path names a different directory, or none. The child walks past `PATH_MAX`
relatively, which is the only way to get a cwd longer than the buffer. -/
def testDeepCwd : IO Nat := do
  let seg := String.ofList (List.replicate 49 'd')
  let dir ← IO.FS.createTempDir
  let deep := s!"for i in $(seq 90); do mkdir -p {seg} && cd {seg} || exit 1; done; echo deep; cat"
  let (pid, master) ← spawnPty 80 24 dir.toString "sh" #["-c", deep] #[]
  let out ← drain master ((← monotonicMs) + 5000) .empty
  let walked := contains (String.fromUTF8! out) "deep"
  let cwd ← getcwdOf pid
  kill pid 9
  Linger.Posix.close master
  let _ ← reap pid
  -- `removeDirAll` builds full paths, which this tree is too deep for; `rm -r`
  -- walks it with directory-relative openat.
  let _ ← IO.Process.run { cmd := "rm", args := #["-r", dir.toString] }
  let mut fails ← check "child walked past PATH_MAX" walked
  let usable ← orFalse (if cwd == "" then pure true else System.FilePath.isDir cwd)
  fails := fails + (← check "getcwdOf reports a usable directory or nothing" usable)
  return fails

def main : IO UInt32 := do
  let mut fails := 0
  fails := fails + (← testPtyEcho)
  fails := fails + (← testPtyEnvAndInput)
  fails := fails + (← testUnixSocket)
  fails := fails + (← testWinsize)
  fails := fails + (← testProcessSelectors)
  fails := fails + (← testZeroLengthRead)
  fails := fails + (← testSpawnFailures)
  fails := fails + (← testDeepCwd)
  IO.println (if fails == 0 then "ALL PASS" else s!"{fails} FAILURES")
  return fails.toUInt32
