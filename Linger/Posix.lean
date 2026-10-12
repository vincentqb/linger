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
@[extern "linger_ignore_sighup"]
opaque ignoreSighup : IO Unit

/-- close(2); a close error is not actionable and is ignored. -/
@[extern "linger_close"]
opaque close (fd : UInt32) : IO Unit

/-- Make reads and writes on `fd` return instead of blocking; throws if `fcntl` fails. -/
@[extern "linger_set_nonblock"]
opaque setNonblock (fd : UInt32) : IO Unit

@[extern "linger_read"]
private opaque readRaw (fd : UInt32) (max : USize) : IO (Option ByteArray)

/-- One read of at most 64 KiB. `none` = EOF (including pty EIO after the child
dies); `some #[]` = would block; EINTR is retried in C; other errors throw. `max = 0`
is refused: `read(fd, buf, 0)` returns 0 without testing for end of file, and `none`
here publicly means EOF. -/
def read (fd : UInt32) (max : USize) : IO (Option ByteArray) := do
  if max == 0 then
    throw (IO.userError "read: max must be positive (0 cannot distinguish EOF)")
  readRaw fd max

/-- One write attempt from `off`. `≥ 0` bytes written (0 = would block, or `off` is at or
past the end); `-1` = peer gone (EPIPE/ECONNRESET/EIO), a normal event for a daemon. EINTR
is retried; other errors throw. -/
@[extern "linger_write"]
opaque write (fd : UInt32) (bytes : @& ByteArray) (off : USize) : IO Int64

/-- Blocking full write over `write`. Would-block and a gone peer throw, as do `write`'s
own errors. -/
def writeAll (fd : UInt32) (bytes : ByteArray) : IO Unit := do
  let mut off : Nat := 0
  while off < bytes.size do
    let n ← write fd bytes (USize.ofNat off)
    if n ≤ 0 then
      throw (IO.userError s!"write_all: peer gone (fd {fd})")
    off := off + n.toNatClampNeg

/-- One write attempt for a `Linger.Core.Buf` queue, skipping the `sent` bytes the
flush loop already got out. The result is `write`'s: `≥ 0` bytes written (0 = would
block, or nothing is owed past `sent`); `-1` = peer gone; other errors throw.
`Buf.writeFrom` is the byte view of the debt, so what reaches `write(2)` here is the debt
and nothing else: `Buf.bufSize_eq_owedLen` shows the queue retains no more, and
`Buf.bufAdvance_writeFrom` gives what the loop leaves after advancing.

`sent` is the flush loop's **transient** cursor, not stored state: a `Buf` holds
exactly the bytes still owed, and the loop calls `Buf.bufAdvance` once when it
stops. Passing the cursor here rather than re-slicing per iteration keeps a flush
to a single copy.

This is a **Lean-level wrapper** over the existing `linger_write` extern, not a new
syscall. It cannot read a `Buf`'s representation — `bytes` is `private`, and this
calls the one API window, `writeFrom`. `scripts/gates.sh`'s greps still gate
`Linger/Runtime/*` against declaring parallel byte buffers of its own, the half privacy
cannot see. -/
def writeBuf (fd : UInt32) (b : Linger.Core.Buf.Buf) (sent : Nat) : IO Int64 :=
  write fd (Linger.Core.Buf.writeFrom b) (USize.ofNat sent)

/-- poll(2). `fds` and `events` are parallel arrays; returns `revents`
per fd (all zero on timeout or EINTR). `timeoutMs < 0` waits forever.
Fails if the arrays differ in length, exceed 4096 fds or poll(2) itself fails — the
daemon polls its listener, its pty and at most `maxClients` clients, well under it. -/
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

Returns `(pid, master)`: the child, with SIGPIPE and SIGHUP at their defaults, and the
pty master, close-on-exec and blocking. Setup and exec failures in the child reach us
as an error rather than a live pid: the C side reports them over a close-on-exec pipe. -/
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

/-- (cols, rows) of the tty behind `fd`. Throws when TIOCGWINSZ fails, for example on a
descriptor that is not a terminal. -/
def winsizeGet (fd : UInt32) : IO (UInt32 × UInt32) := do
  let packed ← winsizeGetRaw fd
  return ((packed >>> 32).toUInt32, packed.toUInt32)

@[extern "linger_winsize_set"]
private opaque winsizeSetRaw (fd cols rows : UInt32) : IO Unit

/-- Set (cols, rows); on a pty master the kernel then signals SIGWINCH to the foreground
process group, if the size changed. Dimensions that would wrap the kernel's unsigned
16-bit fields throw before the call; zero remains representable and means unspecified to
POSIX. A failed TIOCSWINSZ throws. -/
def winsizeSet (fd cols rows : UInt32) : IO Unit := do
  checkWinsize cols rows
  winsizeSetRaw fd cols rows

/-- Put `fd` in raw mode; returns the prior termios as an opaque blob. Throws when
tcgetattr or tcsetattr fails, for example on a descriptor that is not a terminal. -/
@[extern "linger_term_raw"]
opaque termRaw (fd : UInt32) : IO ByteArray

/-- Restore a termios blob that `termRaw` returned for the same terminal. A blob of the
wrong size, or a failed tcsetattr, throws. -/
@[extern "linger_term_restore"]
opaque termRestore (fd : UInt32) (saved : @& ByteArray) : IO Unit

@[extern "linger_unix_listen"]
private opaque unixListenRaw (path : @& String) : IO UInt32

/-- Bind + listen on a unix socket path; returns the listening fd, close-on-exec and
blocking. Throws on an empty or over-long path, or when socket, bind or listen fails.
Caller unlinks stale paths first (`connect` distinguishes stale from live). The kernel's
pending-connection backlog is separate from the daemon's admitted-client bound. -/
def unixListen (path : String) : IO UInt32 := do
  checkCString "unixListen path" path
  unixListenRaw path

@[extern "linger_unix_connect"]
private opaque unixConnectRaw (path : @& String) (nonblocking : Bool) : IO Int64

/-- `≥ 0` connected fd, close-on-exec; `< 0` is `-errno` — ENOENT (no socket) and
ECONNREFUSED (stale socket, daemon dead) are expected outcomes, and an empty or
over-long path is ENAMETOOLONG. Failing to create or configure the socket throws.
With `nonblocking`, a busy listener fails immediately and a connected fd
stays nonblocking; the caller owns its reply deadline.
An unrepresentable NUL path throws before reaching the OS. -/
def unixConnect (path : String) (nonblocking : Bool := false) : IO Int64 := do
  checkCString "unixConnect path" path
  unixConnectRaw path nonblocking

/-- Accept on a nonblocking listen fd. `≥ 0` is the accepted fd; `-1` = nothing to
accept, including a connection aborted before it was taken. Other failures, such as
descriptor exhaustion, throw. The accepted fd is close-on-exec and blocking on every
platform; callers that poll it set nonblocking. -/
@[extern "linger_accept"]
opaque accept (fd : UInt32) : IO Int64

@[extern "linger_flock"]
private opaque flockRaw (path : @& String) : IO Int64

/-- Exclusive non-blocking `flock` on a lock file, created 0600 if missing; `≥ 0` is the
held fd (close-on-exec), `-1` means another process holds it, and other open or lock
failures throw. Chosen over an `O_EXCL`/`mkdir` lock because the kernel releases it
when the holder dies — no staleness timeout to invent, nothing left behind by a
SIGKILL or a power cut. Keep the fd open for the lifetime of the lock, and never
unlink the lock file. -/
def flock (path : String) : IO Int64 := do
  checkCString "flock path" path
  flockRaw path

@[extern "linger_spawn_detached"]
private opaque spawnDetachedRaw (prog : @& String) (args : @& Array String) (logPath : @& String) :
    IO UInt32

/-- Double-fork + setsid + exec, with stdin on /dev/null and stdout and stderr appended
to `logPath` (created 0600), or on /dev/null when it is empty. Returns the program's pid
once it is exec'd and the intermediate child is reaped: no zombie, and not our child.

Setup and exec failures in the child reach us as an error rather than a silently dead
daemon: the C side reports them over the same close-on-exec pipe `spawnPty` uses. -/
def spawnDetached (prog : String) (args : Array String) (logPath : String) : IO UInt32 := do
  checkCommand "spawnDetached" prog args
  checkCString "spawnDetached log path" logPath
  spawnDetachedRaw prog args logPath

@[extern "linger_kill"]
private opaque killRaw (pid sig : UInt32) : IO Unit

@[extern "linger_alive"]
private opaque aliveRaw (pid : UInt32) : IO Bool

@[extern "linger_waitpid_nohang"]
private opaque waitpidNohangRaw (pid : UInt32) : IO Int64

/-- POSIX reads `0` as "every process in my group" and a negative `pid_t` as a
process group, so the process wrappers below accept only a real pid. An
out-of-range `UInt32` becomes negative in the C cast, which is the same hazard. -/
def checkPid (what : String) (pid : UInt32) : IO Unit := do
  if pid == 0 || pid > 0x7FFFFFFF then
    throw (IO.userError s!"{what}: {pid} is not a process id (0 and negative values are selectors)")

/-- kill(2); ESRCH (already gone) is not an error, and other failures throw. -/
def kill (pid sig : UInt32) : IO Unit := do
  checkPid "kill" pid
  killRaw pid sig

/-- kill(pid, 0): is the process alive (and visible to us)? -/
def alive (pid : UInt32) : IO Bool := do
  checkPid "alive" pid
  aliveRaw pid

/-- WNOHANG waitpid. `-1` the requested child is still running; `-2` it is not
reapable — `ECHILD` (not our child, or already reaped) and every other non-`EINTR`
failure alike, so a caller polls `alive` rather than waiting forever; `≥ 0` exit
status (128+sig if signalled), zombie reaped. -/
def waitpidNohang (pid : UInt32) : IO Int64 := do
  checkPid "waitpidNohang" pid
  waitpidNohangRaw pid

/-- getuid(2): the real user id, which names the default socket directory. -/
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

/-- Where pid's cwd currently points (`/proc/<pid>/cwd` on Linux, libproc on macOS);
"" if unreadable, including a path too long to read whole. -/
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

/-- Standard input's descriptor. -/
def stdinFd : UInt32 := 0

/-- Standard output's descriptor. -/
def stdoutFd : UInt32 := 1

end Linger.Posix
