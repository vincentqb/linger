module

public import Linger.Core.Buf
import Std.Async.System

public section

/-! # Linger.Posix — the raw POSIX boundary

Most bindings map 1:1 onto `c/shim.c` (syscall + errno only; object
arguments are borrowed `@&`, so the shim never manages refcounts). A
few are thin wrappers over Lean core's own primitives rather than our
shim — `getpid`, `chmod`, `monotonicMs`, `realtimeS`, `stdinIsTty`,
`gethostname` — kept here so call sites see one uniform `Linger.Posix`
surface; the shim is smaller for it.

Strings passed to the shim are checked for NUL before conversion to C strings.
Rejecting an unrepresentable value prevents a path or argument from silently
becoming its prefix. Empty strings retain each operation's documented meaning.
-/

namespace Linger.Posix

/-- poll(2) bits. `c/shim.c` `_Static_assert`s these against each platform's ABI. -/
def POLLIN : UInt32 := 0x001

def POLLOUT : UInt32 := 0x004

def POLLERR : UInt32 := 0x008

def POLLHUP : UInt32 := 0x010

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
@[extern "linger_ignore_sighup"]
opaque ignoreSighup : IO Unit

@[extern "linger_close"]
opaque close (fd : UInt32) : IO Unit

@[extern "linger_set_nonblock"]
opaque setNonblock (fd : UInt32) : IO Unit

/-- One read. `none` = EOF (incl. pty-master EIO after the child dies);
`some #[]` = would block; EINTR retried in C. Reads at most 64 KiB. -/
@[extern "linger_read"]
private opaque readRaw (fd : UInt32) (max : USize) : IO (Option ByteArray)

/-- `max = 0` is refused: `read(fd, buf, 0)` returns 0 without testing for end
of file, and `none` here publicly means EOF. -/
def read (fd : UInt32) (max : USize) : IO (Option ByteArray) := do
  if max == 0 then
    throw (IO.userError "read: max must be positive (0 cannot distinguish EOF)")
  readRaw fd max

/-- One write attempt from `off`. `≥ 0` bytes written (0 = would block);
`-1` = peer gone (EPIPE/ECONNRESET/EIO), a normal event for a daemon. -/
@[extern "linger_write"]
opaque write (fd : UInt32) (bytes : @& ByteArray) (off : USize) : IO Int64

/-- Blocking full write over `write`; fails on would-block or peer gone. -/
def writeAll (fd : UInt32) (bytes : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  while off < bytes.size do
    let n ← write fd bytes (USize.ofNat off)
    if n ≤ 0 then
      throw (IO.userError s!"write_all: peer gone (fd {fd})")
    off := off + n.toNatClampNeg

/-- One write attempt for a `Linger.Core.Buf` queue, skipping the `sent` bytes the
flush loop already got out.
`Buf.writeFrom_owed` is the theorem that what reaches `write(2)` here is the debt
and nothing else.

`sent` is the flush loop's **transient** cursor, not stored state: a `Buf` holds
exactly the bytes still owed, and the loop calls `Buf.bufAdvance` once when it
stops. Passing the cursor here rather than re-slicing per iteration is what keeps a
flush to a single copy, as it was before the queue became a value.

This is a **Lean-level wrapper** over the existing `linger_write` extern, not a new
syscall: `SHIM_CAP` is untouched. Since the seal (specs/archive/lean-modules.md Step 2) it
could not read a `Buf`'s representation if it wanted to — `bytes` is `private`, and
this calls the one API window, `writeFrom`. What was "the one sanctioned read
outside Core" by convention is now the only one *possible*; `tests/gates.sh`'s greps
still gate `Linger/Runtime/*` against declaring parallel byte buffers of its own,
the half privacy cannot see. -/
def writeBuf (fd : UInt32) (b : Linger.Core.Buf.Buf) (sent : Nat) : IO Int64 :=
  write fd (Linger.Core.Buf.writeFrom b) (USize.ofNat sent)

/-- poll(2). `fds` and `events` are parallel arrays; returns `revents`
per fd (all zero on timeout or EINTR). `timeoutMs < 0` waits forever.
Fails if the arrays differ in length or exceed 4096 fds — the daemon polls
one pty plus `maxClients` sockets, well under it. -/
@[extern "linger_poll"]
opaque poll (fds : @& Array UInt32) (events : @& Array UInt32) (timeoutMs : Int32) :
    IO (Array UInt32)

@[extern "linger_spawn_pty"]
private opaque spawnPtyRaw (cols rows : UInt32) (cwd : @& String) (prog : @& String)
    (args : @& Array String) (extraEnv : @& Array String) : IO UInt64

/-- posix_openpt + execve. A bare program is searched in the child's PATH;
slash-qualified programs run directly. Executable text without a shebang runs
through `/bin/sh`, preserving execvp's fallback.
`extraEnv` entries are `"K=V"` with a nonempty key. `cwd = ""` inherits;
a vanished cwd falls back to the child's `$HOME`, then the inherited cwd
(reboot-resume may restore a deleted directory). Dimensions must fit 16 bits.

Setup and exec failures in the child reach us as an error rather than a live
pid: the C side reports them over a close-on-exec pipe. -/
def spawnPty (cols rows : UInt32) (cwd prog : String) (args : Array String)
    (extraEnv : Array String) : IO (UInt32 × UInt32) := do
  checkWinsize cols rows
  checkCString "spawnPty cwd" cwd
  checkCommand "spawnPty" prog args
  for entry in extraEnv do
    checkCString "spawnPty environment" entry
    unless entry.contains '=' && !entry.startsWith "=" do
      throw (IO.userError s!"spawnPty: environment entry '{entry}' is not K=V")
  let packed ← spawnPtyRaw cols rows cwd prog args extraEnv
  return ((packed >>> 32).toUInt32, packed.toUInt32)

@[extern "linger_winsize_get"]
private opaque winsizeGetRaw (fd : UInt32) : IO UInt64

/-- (cols, rows) of the tty behind `fd`. -/
def winsizeGet (fd : UInt32) : IO (UInt32 × UInt32) := do
  let packed ← winsizeGetRaw fd
  return ((packed >>> 32).toUInt32, packed.toUInt32)

@[extern "linger_winsize_set"]
private opaque winsizeSetRaw (fd cols rows : UInt32) : IO Unit

/-- Set (cols, rows); on a pty master the kernel SIGWINCHes the child.
Refuses dimensions that would wrap the kernel's unsigned 16-bit fields;
zero remains representable and means unspecified to POSIX. -/
def winsizeSet (fd cols rows : UInt32) : IO Unit := do
  checkWinsize cols rows
  winsizeSetRaw fd cols rows

/-- Put `fd` in raw mode; returns the prior termios as an opaque blob. -/
@[extern "linger_term_raw"]
opaque termRaw (fd : UInt32) : IO ByteArray

@[extern "linger_term_restore"]
opaque termRestore (fd : UInt32) (saved : @& ByteArray) : IO Unit

@[extern "linger_unix_listen"]
private opaque unixListenRaw (path : @& String) : IO UInt32

/-- Bind + listen on a unix socket path. Caller unlinks stale paths
first (`connect` distinguishes stale from live). The kernel's pending-connection
backlog is separate from the daemon's admitted-client bound. -/
def unixListen (path : String) : IO UInt32 := do
  checkCString "unixListen path" path
  unixListenRaw path

@[extern "linger_unix_connect"]
private opaque unixConnectRaw (path : @& String) (nonblocking : Bool) : IO Int64

/-- `≥ 0` connected fd; `< 0` is `-errno` — ENOENT (no socket) and
ECONNREFUSED (stale socket, daemon dead) are expected outcomes.
With `nonblocking`, a busy listener fails immediately and a connected fd
stays nonblocking; the caller owns its reply deadline.
An unrepresentable NUL path throws before reaching the OS. -/
def unixConnect (path : String) (nonblocking : Bool := false) : IO Int64 := do
  checkCString "unixConnect path" path
  unixConnectRaw path nonblocking

/-- Accept on a nonblocking listen fd. `-1` = nothing to accept. -/
@[extern "linger_accept"]
opaque accept (fd : UInt32) : IO Int64

@[extern "linger_flock"]
private opaque flockRaw (path : @& String) : IO Int64

/-- Exclusive non-blocking `flock` on a lock file; `≥ 0` is the held
fd, `-1` means another process holds it. Chosen over an `O_EXCL`/
`mkdir` lock because the kernel releases it when the holder dies — no
staleness timeout to invent, nothing left behind by a SIGKILL or a
power cut. Keep the fd open for the lifetime of the lock, and never
unlink the lock file. -/
def flock (path : String) : IO Int64 := do
  checkCString "flock path" path
  flockRaw path

@[extern "linger_spawn_detached"]
private opaque spawnDetachedRaw (prog : @& String) (args : @& Array String) (logPath : @& String) :
    IO Unit

/-- Double-fork + setsid + exec, with stdio on `logPath` (append) or /dev/null.
Returns after the intermediate child is reaped: no zombie.

Setup and exec failures in the child reach us as an error rather than a silently dead
daemon: the C side reports them over the same close-on-exec pipe `spawnPty` uses. -/
def spawnDetached (prog : String) (args : Array String) (logPath : String) : IO Unit := do
  checkCommand "spawnDetached" prog args
  checkCString "spawnDetached log path" logPath
  spawnDetachedRaw prog args logPath

@[extern "linger_exec"]
private opaque execRaw (prog : @& String) (args : @& Array String) : IO Unit

/-- execvp — replaces this process on success. -/
def exec (prog : String) (args : Array String) : IO Unit := do
  checkCommand "exec" prog args
  execRaw prog args

/-- kill(2); ESRCH (already gone) is not an error. -/
@[extern "linger_kill"]
private opaque killRaw (pid sig : UInt32) : IO Unit

/-- kill(pid, 0): is the process alive (and visible to us)? -/
@[extern "linger_alive"]
private opaque aliveRaw (pid : UInt32) : IO Bool

/-- WNOHANG waitpid. `-1` the requested child is still running; `-2` it is not
reapable — `ECHILD` (not our child, or already reaped) and every other non-`EINTR`
failure alike, so a caller polls `alive` rather than waiting forever; `≥ 0` exit
status (128+sig if signalled), zombie reaped. -/
@[extern "linger_waitpid_nohang"]
private opaque waitpidNohangRaw (pid : UInt32) : IO Int64

/-- POSIX reads `0` as "every process in my group" and a negative `pid_t` as a
process group, so the process wrappers below accept only a real pid. An
out-of-range `UInt32` becomes negative in the C cast, which is the same hazard. -/
def checkPid (what : String) (pid : UInt32) : IO Unit := do
  if pid == 0 || pid > 0x7FFFFFFF then
    throw (IO.userError s!"{what}: {pid} is not a process id (0 and negative values are selectors)")

def kill (pid sig : UInt32) : IO Unit := do
  checkPid "kill" pid
  killRaw pid sig

def alive (pid : UInt32) : IO Bool := do
  checkPid "alive" pid
  aliveRaw pid

def waitpidNohang (pid : UInt32) : IO Int64 := do
  checkPid "waitpidNohang" pid
  waitpidNohangRaw pid

@[extern "linger_getuid"]
opaque getuid : IO UInt32

/-- Is stdin a terminal? Thin wrapper over Lean core. -/
def stdinIsTty : IO Bool := do
  (← IO.getStdin).isTty

/-- POSIX `chmod`. Lean core already wraps `chmod(2)` (`lean_chmod`), so
this is core, not our shim. -/
def chmod (path : @& String) (mode : UInt32) : IO Unit := IO.Prim.setAccessRights path mode

/-- Our own pid. Lean core wraps `getpid(2)` (`lean_io_process_get_pid`). -/
def getpid : IO UInt32 := IO.Process.getPID

/-- Where pid's cwd currently points (`/proc/<pid>/cwd`); "" if unreadable. -/
@[extern "linger_getcwd_of"]
opaque getcwdOf (pid : UInt32) : IO String

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

/-- Standard fds, named. -/
def stdinFd : UInt32 := 0

def stdoutFd : UInt32 := 1

end Linger.Posix
