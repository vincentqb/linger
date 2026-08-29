module

public import Linger.Core.Buf

public section

/-! # Linger.Posix — the only module that touches the OS

Most bindings map 1:1 onto `c/shim.c` (syscall + errno only; object
arguments are borrowed `@&`, so the shim never manages refcounts). A
few are thin wrappers over Lean core's own primitives rather than our
shim — `getpid`, `chmod`, `monotonicMs` — kept here so call sites see
one uniform `Linger.Posix` surface; the shim is smaller for it.
-/

namespace Linger.Posix

/-- Linux poll(2) bits. `c/shim.c` `_Static_assert`s these against the ABI. -/
def POLLIN   : UInt32 := 0x001
def POLLOUT  : UInt32 := 0x004
def POLLERR  : UInt32 := 0x008
def POLLHUP  : UInt32 := 0x010
def POLLNVAL : UInt32 := 0x020

/-- Ignore SIGPIPE process-wide. Call first in every `main`: a peer
vanishing between `poll` and `write` must surface as an error code, not
kill the process. -/
@[extern "linger_init"] opaque init : IO Unit

/-- Daemon-side: survive controlling-terminal death. -/
@[extern "linger_ignore_sighup"] opaque ignoreSighup : IO Unit

@[extern "linger_close"] opaque close (fd : UInt32) : IO Unit

@[extern "linger_set_nonblock"] opaque setNonblock (fd : UInt32) : IO Unit

/-- One read. `none` = EOF (incl. pty-master EIO after the child dies);
`some #[]` = would block; EINTR retried in C. Reads at most 64 KiB. -/
@[extern "linger_read"] opaque read (fd : UInt32) (max : USize) : IO (Option ByteArray)

/-- One write attempt from `off`. `≥ 0` bytes written (0 = would block);
`-1` = peer gone (EPIPE/ECONNRESET/EIO), a normal event for a daemon. -/
@[extern "linger_write"] opaque write (fd : UInt32) (bytes : @& ByteArray) (off : USize) : IO Int64

/-- Blocking full write, for fds whose slowness is our own (client stdout). -/
@[extern "linger_write_all"] opaque writeAll (fd : UInt32) (bytes : @& ByteArray) : IO Unit

/-- One write attempt for a `Linger.Core.Buf` queue, skipping the `sent` bytes the
flush loop already got out.
`Buf.writeFrom_owed` is the theorem that what reaches `write(2)` here is the debt
and nothing else.

`sent` is the flush loop's **transient** cursor, not stored state: a `Buf` holds
exactly the bytes still owed, and the loop calls `Buf.bufAdvance` once when it
stops. Passing the cursor here rather than re-slicing per iteration is what keeps a
flush to a single copy, as it was before the queue became a value.

This is a **Lean-level wrapper** over the existing `linger_write` extern, not a new
syscall: `SHIM_CAP` is untouched. Since the seal (specs/lean-modules.md Step 2) it
could not read a `Buf`'s representation if it wanted to — `bytes` is `private`, and
this calls the one API window, `writeFrom`. What was "the one sanctioned read
outside Core" by convention is now the only one *possible*; `tests/e2e.sh`'s greps
still gate `Linger/Runtime/*` against declaring parallel byte buffers of its own,
the half privacy cannot see. -/
def writeBuf (fd : UInt32) (b : Linger.Core.Buf.Buf) (sent : Nat) : IO Int64 :=
  write fd (Linger.Core.Buf.writeFrom b) (USize.ofNat sent)

/-- poll(2). `fds` and `events` are parallel arrays; returns `revents`
per fd (all zero on timeout or EINTR). `timeoutMs < 0` waits forever. -/
@[extern "linger_poll"] opaque poll (fds : @& Array UInt32) (events : @& Array UInt32)
    (timeoutMs : Int32) : IO (Array UInt32)

@[extern "linger_spawn_pty"] private opaque spawnPtyRaw (cols rows : UInt32)
    (cwd : @& String) (prog : @& String) (args : @& Array String)
    (extraEnv : @& Array String) : IO UInt64

/-- forkpty + execvp. `extraEnv` entries are `"K=V"`. `cwd = ""`
inherits; a vanished cwd falls back to `$HOME` rather than failing
(reboot-resume may restore a deleted directory). -/
def spawnPty (cols rows : UInt32) (cwd prog : String) (args : Array String)
    (extraEnv : Array String) : IO (UInt32 × UInt32) := do
  let packed ← spawnPtyRaw cols rows cwd prog args extraEnv
  return ((packed >>> 32).toUInt32, packed.toUInt32)

@[extern "linger_winsize_get"] private opaque winsizeGetRaw (fd : UInt32) : IO UInt64

/-- (cols, rows) of the tty behind `fd`. -/
def winsizeGet (fd : UInt32) : IO (UInt32 × UInt32) := do
  let packed ← winsizeGetRaw fd
  return ((packed >>> 32).toUInt32, packed.toUInt32)

/-- Set (cols, rows); on a pty master the kernel SIGWINCHes the child. -/
@[extern "linger_winsize_set"] opaque winsizeSet (fd cols rows : UInt32) : IO Unit

/-- Put `fd` in raw mode; returns the prior termios as an opaque blob. -/
@[extern "linger_term_raw"] opaque termRaw (fd : UInt32) : IO ByteArray

@[extern "linger_term_restore"] opaque termRestore (fd : UInt32) (saved : @& ByteArray) : IO Unit

/-- Bind + listen on a unix socket path. Caller unlinks stale paths
first (`connect` distinguishes stale from live). -/
@[extern "linger_unix_listen"] opaque unixListen (path : @& String) : IO UInt32

/-- `≥ 0` connected fd; `< 0` is `-errno` — ENOENT (no socket) and
ECONNREFUSED (stale socket, daemon dead) are expected outcomes. -/
@[extern "linger_unix_connect"] opaque unixConnect (path : @& String) : IO Int64

/-- Accept on a nonblocking listen fd. `-1` = nothing to accept. -/
@[extern "linger_accept"] opaque accept (fd : UInt32) : IO Int64

/-- Exclusive non-blocking `flock` on a lock file; `≥ 0` is the held
fd, `-1` means another process holds it. Chosen over an `O_EXCL`/
`mkdir` lock because the kernel releases it when the holder dies — no
staleness timeout to invent, nothing left behind by a SIGKILL or a
power cut. Keep the fd open for the lifetime of the lock, and never
unlink the lock file. -/
@[extern "linger_flock"] opaque flock (path : @& String) : IO Int64

/-- Double-fork + setsid + execvp with stdio on `logPath` (append) or
/dev/null. Returns after the intermediate child is reaped: no zombie. -/
@[extern "linger_spawn_detached"] opaque spawnDetached (prog : @& String)
    (args : @& Array String) (logPath : @& String) : IO Unit

/-- execvp — replaces this process on success. -/
@[extern "linger_exec"] opaque exec (prog : @& String) (args : @& Array String) : IO Unit

/-- kill(2); ESRCH (already gone) is not an error. -/
@[extern "linger_kill"] opaque kill (pid sig : UInt32) : IO Unit

/-- kill(pid, 0): is the process alive (and visible to us)? -/
@[extern "linger_alive"] opaque alive (pid : UInt32) : IO Bool

/-- WNOHANG waitpid. `-1` running; `-2` not our child (use `alive`);
`≥ 0` exit status (128+sig if signalled), zombie reaped. -/
@[extern "linger_waitpid_nohang"] opaque waitpidNohang (pid : UInt32) : IO Int64

@[extern "linger_getuid"] opaque getuid : IO UInt32
@[extern "linger_isatty"] opaque isatty (fd : UInt32) : IO Bool

/-- POSIX `chmod`. Lean core already wraps `chmod(2)` (`lean_chmod`), so
this is core, not our shim. -/
def chmod (path : @& String) (mode : UInt32) : IO Unit :=
  IO.Prim.setAccessRights path mode

/-- Our own pid. Lean core wraps `getpid(2)` (`lean_io_process_get_pid`). -/
def getpid : IO UInt32 := IO.Process.getPID

/-- Where pid's cwd currently points (`/proc/<pid>/cwd`); "" if unreadable. -/
@[extern "linger_getcwd_of"] opaque getcwdOf (pid : UInt32) : IO String

@[extern "linger_gethostname"] opaque gethostname : IO String

/-- CLOCK_MONOTONIC in ms — checkpoint cadence, poll deadlines. Lean
core's `IO.monoMsNow` is exactly this clock, so no shim needed. -/
def monotonicMs : IO UInt64 := do return UInt64.ofNat (← IO.monoMsNow)

/-- Unix epoch seconds — `created` timestamps in listings. (Lean core
has no wall clock, so this one stays a shim call.) -/
@[extern "linger_realtime_s"] opaque realtimeS : IO UInt64

/-- Standard fds, named. -/
def stdinFd : UInt32 := 0
def stdoutFd : UInt32 := 1

end Linger.Posix
