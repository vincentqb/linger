module

import all Linger.Os.Boundary
public import Linger.Os.Spec
import Std.Async.System

public section

/-! # Linger.Os.Shell — the POSIX surface callers use

Every binding in `Linger.Os.Boundary` is private, and each is wrapped here under its own
name, so this module is the program's only route to `c/shim.c`. The wrappers check what
the C side cannot represent and state the binding's contract. A few operations are thin
wrappers over Lean core's own primitives rather than our shim — `getpid`, `chmod`,
`monotonicMs`, `realtimeS`, `stdinIsTty`, `gethostname` — so the shim is smaller for them.

Strings passed to the shim are checked for NUL before conversion to C strings.
Rejecting an unrepresentable value prevents a path or argument from silently
becoming its prefix. Empty strings retain each operation's documented meaning.
-/

namespace Linger.Os.Shell

/-- Reading will not block; on a listening socket, a connection is waiting. These poll(2)
bits are fixed here, and `c/shim.c` `_Static_assert`s them against each platform's ABI. -/
def POLLIN : UInt32 := 0x001

/-- Writing will not block. -/
def POLLOUT : UInt32 := 0x004

/-- An error condition; reported even when not requested. -/
def POLLERR : UInt32 := 0x008

/-- The peer hung up; reported even when not requested. -/
def POLLHUP : UInt32 := 0x010

/-- The descriptor is not open; reported even when not requested. -/
def POLLNVAL : UInt32 := 0x020

private def checkCString (what : String) (value : String) : IO Unit := do
  if value.contains '\x00' then
    throw (IO.userError s!"{what}: NUL cannot be represented in a POSIX string")

private def checkCommand (what prog : String) (args : Array String) : IO Unit := do
  checkCString s!"{what} program" prog
  for arg in args do
    checkCString s!"{what} argument" arg

private def checkWinsize (cols rows : UInt32) : IO Unit := do
  if cols > 0xFFFF || rows > 0xFFFF then
    throw (IO.userError "winsize: columns and rows must fit unsigned 16-bit fields")

/-- Daemon-side: survive controlling-terminal death. -/
def ignoreSighup : IO Unit := Boundary.ignoreSighup

/-- close(2); a close error is not actionable and is ignored. -/
def close (fd : UInt32) : IO Unit := Boundary.close fd

/-- Make reads and writes on `fd` return instead of blocking; throws if `fcntl` fails. -/
def setNonblock (fd : UInt32) : IO Unit := Boundary.setNonblock fd

/-- One read of at most 64 KiB. `none` = EOF (including pty EIO after the child
dies); `some #[]` = would block; EINTR is retried in C; other errors throw. `max = 0`
is refused: `read(fd, buf, 0)` returns 0 without testing for end of file, and `none`
here publicly means EOF. -/
def read (fd : UInt32) (max : USize) : IO (Option ByteArray) := do
  if max == 0 then
    throw (IO.userError "read: max must be positive (0 cannot distinguish EOF)")
  Boundary.read fd max

/-- One write attempt from `off`. `≥ 0` bytes written (0 = would block, or `off` is at or
past the end); `-1` = peer gone (EPIPE/ECONNRESET/EIO), a normal event for a daemon. EINTR
is retried; other errors throw. -/
def write (fd : UInt32) (bytes : ByteArray) (off : USize) : IO Int64 := Boundary.write fd bytes off

/-- Blocking full write over `write`. Would-block and a gone peer throw, as do `write`'s
own errors. -/
def writeAll (fd : UInt32) (bytes : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  while off < bytes.size do
    let n ← write fd bytes (USize.ofNat off)
    if n ≤ 0 then
      throw (IO.userError s!"write_all: peer gone (fd {fd})")
    off := off + n.toNatClampNeg

/-- poll(2). `fds` and `events` are parallel arrays; returns `revents`
per fd (all zero on timeout or EINTR). `timeoutMs < 0` waits forever.
Fails if the arrays differ in length, exceed 4096 fds or poll(2) itself fails — the
daemon polls its listener, its pty and at most `maxClients` clients, well under it. -/
def poll (fds events : Array UInt32) (timeoutMs : Int32) : IO (Array UInt32) :=
  Boundary.poll fds events timeoutMs

/-- What failed, in the operating system's words: entering the directory, or running the
program. -/
private def failureWords : Spawn.Failure → String
  | .directory why => s!"spawn_pty: chdir: {why}"
  | .notFound why | .notRunnable why => s!"spawn_pty: execve: {why}"

/-- posix_openpt + execve. A bare program is searched in the child's PATH;
slash-qualified programs run directly. Executable text without a shebang runs
through `/bin/sh`, preserving execvp's fallback.
`extraEnv` entries are `"K=V"` with a nonempty key. `cwd = ""` inherits; a cwd the child cannot
enter fails the start, whatever `$HOME` is: a resume chooses its directory before
(`Linger.Os.Env.resumeDir`). Dimensions must fit 16 bits.

Returns `(pid, master)`: the child, with SIGPIPE and SIGHUP at their defaults, and the
pty master, close-on-exec and blocking. A program that cannot start is a `Spawn.Failure`;
the other setup failures in the child throw. The C side reports both over a close-on-exec
pipe, so no pid is returned for a program that never ran. -/
def trySpawnPty (cols rows : UInt32) (cwd prog : String) (args : Array String)
    (extraEnv : Array String) : IO (Except Spawn.Failure (UInt32 × UInt32)) := do
  checkWinsize cols rows
  checkCString "spawnPty cwd" cwd
  checkCommand "spawnPty" prog args
  for entry in extraEnv do
    checkCString "spawnPty environment" entry
    unless entry.contains '=' && !entry.startsWith "=" do
      throw (IO.userError s!"spawnPty: environment entry '{entry}' is not K=V")
  match ← Boundary.spawnPty cols rows cwd prog args extraEnv with
  | .ok packed =>
    return .ok ((packed >>> 32).toUInt32, packed.toUInt32)
  | .error (1, why) =>
    return .error (.directory why)
  | .error (2, why) =>
    return .error (.notFound why)
  | .error (_, why) =>
    return .error (.notRunnable why)

/-- `trySpawnPty`, throwing when the program cannot start. -/
def spawnPty (cols rows : UInt32) (cwd prog : String) (args : Array String)
    (extraEnv : Array String) : IO (UInt32 × UInt32) := do
  match ← trySpawnPty cols rows cwd prog args extraEnv with
  | .ok started =>
    return started
  | .error failure =>
    throw (IO.userError (failureWords failure))

/-- (cols, rows) of the tty behind `fd`. Throws when TIOCGWINSZ fails, for example on a
descriptor that is not a terminal. -/
def winsizeGet (fd : UInt32) : IO (UInt32 × UInt32) := do
  let packed ← Boundary.winsizeGet fd
  return ((packed >>> 32).toUInt32, packed.toUInt32)

/-- Set (cols, rows); on a pty master the kernel then signals SIGWINCH to the foreground
process group, if the size changed. Dimensions that would wrap the kernel's unsigned
16-bit fields throw before the call; zero remains representable and means unspecified to
POSIX. A failed TIOCSWINSZ throws. -/
def winsizeSet (fd cols rows : UInt32) : IO Unit := do
  checkWinsize cols rows
  Boundary.winsizeSet fd cols rows

/-- Put `fd` in raw mode; returns the prior termios as an opaque blob. Throws when
tcgetattr or tcsetattr fails, for example on a descriptor that is not a terminal. -/
def termRaw (fd : UInt32) : IO ByteArray := Boundary.termRaw fd

/-- Restore a termios blob that `termRaw` returned for the same terminal. A blob of the
wrong size, or a failed tcsetattr, throws. -/
def termRestore (fd : UInt32) (saved : ByteArray) : IO Unit := Boundary.termRestore fd saved

/-- Bind + listen on a unix socket path; returns the listening fd, close-on-exec and
blocking. Throws on an empty or over-long path, or when socket, bind or listen fails.
Caller unlinks stale paths first (`connect` distinguishes stale from live). The kernel's
pending-connection backlog is separate from the daemon's admitted-client bound. -/
def unixListen (path : String) : IO UInt32 := do
  checkCString "unixListen path" path
  Boundary.unixListen path

/-- `≥ 0` connected fd, close-on-exec; `< 0` is `-errno` — ENOENT (no socket) and
ECONNREFUSED (stale socket, daemon dead) are expected outcomes, and an empty or
over-long path is ENAMETOOLONG. Failing to create or configure the socket throws.
With `nonblocking`, a busy listener fails immediately and a connected fd
stays nonblocking; the caller owns its reply deadline.
An unrepresentable NUL path throws before reaching the OS. -/
def unixConnect (path : String) (nonblocking : Bool := false) : IO Int64 := do
  checkCString "unixConnect path" path
  Boundary.unixConnect path nonblocking

/-- Accept on a nonblocking listen fd. `≥ 0` is the accepted fd; `-1` = nothing to
accept, including a connection aborted before it was taken. Other failures, such as
descriptor exhaustion, throw. The accepted fd is close-on-exec and blocking on every
platform; callers that poll it set nonblocking. -/
def accept (fd : UInt32) : IO Int64 := Boundary.accept fd

/-- Exclusive non-blocking `flock` on a lock file, created 0600 if missing; `≥ 0` is the
held fd (close-on-exec), `-1` means another process holds it, and other open or lock
failures throw. Chosen over an `O_EXCL`/`mkdir` lock because the kernel releases it
when the holder dies — no staleness timeout to invent, nothing left behind by a
SIGKILL or a power cut. Keep the fd open for the lifetime of the lock, and never
unlink the lock file. -/
def flock (path : String) : IO Int64 := do
  checkCString "flock path" path
  Boundary.flock path

/-- Double-fork + setsid + exec, with stdin on /dev/null and stdout and stderr appended
to `logPath` (created 0600), or on /dev/null when it is empty. Returns the program's pid
once it is exec'd and the intermediate child is reaped: no zombie, and not our child.

Setup and exec failures in the child reach us as an error rather than a silently dead
daemon: the C side reports them over the same close-on-exec pipe `spawnPty` uses. -/
def spawnDetached (prog : String) (args : Array String) (logPath : String) : IO UInt32 := do
  checkCommand "spawnDetached" prog args
  checkCString "spawnDetached log path" logPath
  Boundary.spawnDetached prog args logPath

/-- POSIX reads `0` as "every process in my group" and a negative `pid_t` as a
process group, so the process bindings take a proof that the pid is neither, which this check
returns. An out-of-range `UInt32` becomes negative in the C cast, which is the same hazard. -/
def checkPid (what : String) (pid : UInt32) : IO (PLift (0 < pid ∧ pid ≤ 0x7FFFFFFF)) := do
  if valid : 0 < pid ∧ pid ≤ 0x7FFFFFFF then
    return ⟨valid⟩
  throw (IO.userError s!"{what}: {pid} is not a process id (0 and negative values are selectors)")

/-- kill(2); ESRCH (already gone) is not an error, and other failures throw. -/
def kill (pid sig : UInt32) : IO Unit := do
  let ⟨valid⟩ ← checkPid "kill" pid
  Boundary.kill pid sig valid

/-- kill(pid, 0): is the process alive (and visible to us)? -/
def alive (pid : UInt32) : IO Bool := do
  let ⟨valid⟩ ← checkPid "alive" pid
  Boundary.alive pid valid

/-- What a non-blocking wait for a child found. -/
inductive Reaped where
  /-- The child is still running. -/
  | running
  /-- The child is not ours to wait for, or is already reaped. -/
  | unreapable
  /-- The child exited with this code. -/
  | exited (code : UInt8)
  /-- A signal with this number killed the child. -/
  | signaled (signal : UInt8)
  deriving Repr, DecidableEq

/-- A non-blocking wait for the child `pid`, which reaps it once it has ended unless `keep`. -/
private def waitNohang (what : String) (pid : UInt32) (keep : Bool) : IO Reaped := do
  let ⟨valid⟩ ← checkPid what pid
  let status ← Boundary.waitpidNohang pid keep valid
  if status == -1 then
    return .running
  if status < 0 then
    return .unreapable
  if status < 256 then
    return .exited status.toInt.toNat.toUInt8
  return .signaled (status - 256).toInt.toNat.toUInt8

/-- WNOHANG wait, saying how a reaped child ended: its exit code, or the signal that killed it.
`unreapable` covers `ECHILD` (not our child, or already reaped) and every other non-`EINTR`
failure alike, so a caller polls `alive` rather than waiting forever. -/
def reapNohang (pid : UInt32) : IO Reaped := waitNohang "reapNohang" pid false

/-- `reapNohang` that leaves an ended child unreaped, so its zombie keeps its pid, and with it
the id of the session it leads, from every other process until a reap. -/
def peekNohang (pid : UInt32) : IO Reaped := waitNohang "peekNohang" pid true

/-- A descriptor that becomes readable whenever a child of this process ends, so a poll loop
can wait for its program's end instead of asking on a timer. Each end makes at least one byte
readable; read it all before the next wait. Call it once per process, before starting the
program: it installs the process's SIGCHLD handler. -/
def childEndFd : IO UInt32 := Boundary.childEndFd

/-- Send `sig` to every process whose session id is `sid`, other than `sid` itself, and return
how many it reached; signal 0 only counts them. The caller keeps the session's leader, its
child, unreaped meanwhile (`peekNohang`), so no other session can have the id. On Linux a pid
that changes hands between the session read and the signal is never signalled; on macOS, and on
Linux before 5.3, that window remains. A process of another user is not reached. -/
def signalSession (sid sig : UInt32) : IO UInt32 := do
  let ⟨valid⟩ ← checkPid "signalSession" sid
  Boundary.signalSession sid sig valid

/-- WNOHANG waitpid as a shell reports it. `-1` the requested child is still running; `-2` it
is not reapable, as for `reapNohang`; `≥ 0` the exit status, 128 plus the signal's number if
signalled, with the zombie reaped. -/
def waitpidNohang (pid : UInt32) : IO Int64 := do
  match ← reapNohang pid with
  | .running =>
    return -1
  | .unreapable =>
    return -2
  | .exited code =>
    return code.toNat.toInt64
  | .signaled signal =>
    return 128 + signal.toNat.toInt64

/-- getuid(2): the real user id, which names the default socket directory. -/
def getuid : IO UInt32 := Boundary.getuid

/-- Is stdin a terminal? Thin wrapper over Lean core. -/
def stdinIsTty : IO Bool := do
  (← IO.getStdin).isTty

/-- POSIX `chmod`. Lean core already wraps `chmod(2)` (`lean_chmod`), so
this is core, not our shim. -/
def chmod (path : @& String) (mode : UInt32) : IO Unit := IO.Prim.setAccessRights path mode

/-- Our own pid. Lean core wraps `getpid(2)` (`lean_io_process_get_pid`). -/
def getpid : IO UInt32 := IO.Process.getPID

/-- Where pid's cwd currently points (`/proc/<pid>/cwd` on Linux, libproc on macOS);
"" if unreadable, including a path too long to read whole. -/
def getcwdOf (pid : UInt32) : IO String := Boundary.getcwdOf pid

/-- Machine hostname; empty only if the platform call fails. -/
def gethostname : IO String := do
  try
    Std.Async.System.getHostName
  catch _ =>
    pure ""

/-- CLOCK_MONOTONIC in ms — checkpoint cadence, poll deadlines. Lean
core's `IO.monoMsNow` supplies natural-number milliseconds directly. -/
def monotonicMs : IO Nat := IO.monoMsNow

/-- Unix epoch seconds — `created` timestamps in listings. -/
def realtimeS : IO UInt64 := do
  return UInt64.ofNat (← Std.Time.Timestamp.now).toSecondsSinceUnixEpoch.val.toNat

/-- Standard input's descriptor. -/
def stdinFd : UInt32 := 0

/-- Standard output's descriptor. -/
def stdoutFd : UInt32 := 1

end Linger.Os.Shell
