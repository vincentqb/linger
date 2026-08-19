import Linger.Posix
/-! # lingertest — IO smoke tests for the Posix shim

Pure code is tested in `Tests/` at elaboration time; things that spawn
processes and poll fds need a real process. Each check prints PASS/FAIL;
exit code is the count of failures. Run via `./lake exe lingertest`.
-/

open Linger.Posix

def check (name : String) (cond : Bool) : IO Nat := do
  IO.println s!"{if cond then "PASS" else "FAIL"} {name}"
  return if cond then 0 else 1

def contains (haystack needle : String) : Bool :=
  (haystack.splitOn needle).length ≥ 2

/-- Drain a pty until EOF or deadline, via poll — the daemon's read shape. -/
partial def drain (fd : UInt32) (deadlineMs : UInt64) (acc : ByteArray) : IO ByteArray := do
  let now ← monotonicMs
  if now ≥ deadlineMs then return acc
  let revs ← poll #[fd] #[POLLIN] 200
  let r := revs[0]!
  if r &&& (POLLIN ||| POLLHUP ||| POLLERR) == 0 then
    drain fd deadlineMs acc
  else
    match ← read fd 65536 with
    | none => return acc            -- EOF: child gone
    | some bs => drain fd deadlineMs (acc ++ bs)

/-- Poll-wait until the child is reaped or the deadline passes. -/
def reap (pid : UInt32) : IO Int64 := do
  let deadline := (← monotonicMs) + 5000
  let mut status : Int64 := -1
  while status == -1 && (← monotonicMs) < deadline do
    status ← waitpidNohang pid
    if status == -1 then IO.sleep 20
  return status

def testPtyEcho : IO Nat := do
  let (pid, master) ← spawnPty 80 24 "" "sh" #["-c", "echo hi-from-pty"] #["ZT=1"]
  let out ← drain master ((← monotonicMs) + 5000) .empty
  Linger.Posix.close master
  let mut fails := 0
  fails := fails + (← check "pty spawn+echo roundtrip" (contains (String.fromUTF8! out) "hi-from-pty"))
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

def main : IO UInt32 := do
  Linger.Posix.init
  let mut fails := 0
  fails := fails + (← testPtyEcho)
  fails := fails + (← testPtyEnvAndInput)
  fails := fails + (← testUnixSocket)
  fails := fails + (← testWinsize)
  IO.println (if fails == 0 then "ALL PASS" else s!"{fails} FAILURES")
  return fails.toUInt32
