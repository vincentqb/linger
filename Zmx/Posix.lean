/-! # Zmx.Posix — the only module that touches the OS

Every binding maps 1:1 onto `c/shim.c`. Semantics are documented here
(the Lean face); the C side is syscall + errno only. Object arguments
are all borrowed (`@&`), so the shim never manages Lean refcounts.
-/

namespace Zmx.Posix

/-- Linux poll(2) bits. `c/shim.c` `_Static_assert`s these against the ABI. -/
def POLLIN   : UInt32 := 0x001
def POLLOUT  : UInt32 := 0x004
def POLLERR  : UInt32 := 0x008
def POLLHUP  : UInt32 := 0x010
def POLLNVAL : UInt32 := 0x020

/-- Ignore SIGPIPE process-wide. Call first in every `main`: a peer
vanishing between `poll` and `write` must surface as an error code, not
kill the process. -/
@[extern "zmx_init"] opaque init : IO Unit

/-- Daemon-side: survive controlling-terminal death. -/
@[extern "zmx_ignore_sighup"] opaque ignoreSighup : IO Unit

@[extern "zmx_close"] opaque close (fd : UInt32) : IO Unit

@[extern "zmx_set_nonblock"] opaque setNonblock (fd : UInt32) : IO Unit

/-- One read. `none` = EOF (incl. pty-master EIO after the child dies);
`some #[]` = would block; EINTR retried in C. Reads at most 64 KiB. -/
@[extern "zmx_read"] opaque read (fd : UInt32) (max : USize) : IO (Option ByteArray)

/-- One write attempt from `off`. `≥ 0` bytes written (0 = would block);
`-1` = peer gone (EPIPE/ECONNRESET/EIO), a normal event for a daemon. -/
@[extern "zmx_write"] opaque write (fd : UInt32) (bytes : @& ByteArray) (off : USize) : IO Int64

/-- Blocking full write, for fds whose slowness is our own (client stdout). -/
@[extern "zmx_write_all"] opaque writeAll (fd : UInt32) (bytes : @& ByteArray) : IO Unit

/-- poll(2). `fds` and `events` are parallel arrays; returns `revents`
per fd (all zero on timeout or EINTR). `timeoutMs < 0` waits forever. -/
@[extern "zmx_poll"] opaque poll (fds : @& Array UInt32) (events : @& Array UInt32)
    (timeoutMs : Int32) : IO (Array UInt32)

@[extern "zmx_spawn_pty"] private opaque spawnPtyRaw (cols rows : UInt32)
    (cwd : @& String) (prog : @& String) (args : @& Array String)
    (extraEnv : @& Array String) : IO UInt64

/-- forkpty + execvp. `extraEnv` entries are `"K=V"`. `cwd = ""`
inherits; a vanished cwd falls back to `$HOME` rather than failing
(reboot-resume may restore a deleted directory). -/
def spawnPty (cols rows : UInt32) (cwd prog : String) (args : Array String)
    (extraEnv : Array String) : IO (UInt32 × UInt32) := do
  let packed ← spawnPtyRaw cols rows cwd prog args extraEnv
  return ((packed >>> 32).toUInt32, packed.toUInt32)

@[extern "zmx_winsize_get"] private opaque winsizeGetRaw (fd : UInt32) : IO UInt64

/-- (cols, rows) of the tty behind `fd`. -/
def winsizeGet (fd : UInt32) : IO (UInt32 × UInt32) := do
  let packed ← winsizeGetRaw fd
  return ((packed >>> 32).toUInt32, packed.toUInt32)

/-- Set (cols, rows); on a pty master the kernel SIGWINCHes the child. -/
@[extern "zmx_winsize_set"] opaque winsizeSet (fd cols rows : UInt32) : IO Unit

/-- Put `fd` in raw mode; returns the prior termios as an opaque blob. -/
@[extern "zmx_term_raw"] opaque termRaw (fd : UInt32) : IO ByteArray

@[extern "zmx_term_restore"] opaque termRestore (fd : UInt32) (saved : @& ByteArray) : IO Unit

/-- Bind + listen on a unix socket path. Caller unlinks stale paths
first (`connect` distinguishes stale from live). -/
@[extern "zmx_unix_listen"] opaque unixListen (path : @& String) : IO UInt32

/-- `≥ 0` connected fd; `< 0` is `-errno` — ENOENT (no socket) and
ECONNREFUSED (stale socket, daemon dead) are expected outcomes. -/
@[extern "zmx_unix_connect"] opaque unixConnect (path : @& String) : IO Int64

/-- Accept on a nonblocking listen fd. `-1` = nothing to accept. -/
@[extern "zmx_accept"] opaque accept (fd : UInt32) : IO Int64

/-- Double-fork + setsid + execvp with stdio on `logPath` (append) or
/dev/null. Returns after the intermediate child is reaped: no zombie. -/
@[extern "zmx_spawn_detached"] opaque spawnDetached (prog : @& String)
    (args : @& Array String) (logPath : @& String) : IO Unit

/-- execvp — replaces this process on success. -/
@[extern "zmx_exec"] opaque exec (prog : @& String) (args : @& Array String) : IO Unit

/-- kill(2); ESRCH (already gone) is not an error. -/
@[extern "zmx_kill"] opaque kill (pid sig : UInt32) : IO Unit

/-- kill(pid, 0): is the process alive (and visible to us)? -/
@[extern "zmx_alive"] opaque alive (pid : UInt32) : IO Bool

/-- WNOHANG waitpid. `-1` running; `-2` not our child (use `alive`);
`≥ 0` exit status (128+sig if signalled), zombie reaped. -/
@[extern "zmx_waitpid_nohang"] opaque waitpidNohang (pid : UInt32) : IO Int64

@[extern "zmx_getpid"] opaque getpid : IO UInt32
@[extern "zmx_getuid"] opaque getuid : IO UInt32
@[extern "zmx_isatty"] opaque isatty (fd : UInt32) : IO Bool
@[extern "zmx_chmod"] opaque chmod (path : @& String) (mode : UInt32) : IO Unit

/-- Where pid's cwd currently points (`/proc/<pid>/cwd`); "" if unreadable. -/
@[extern "zmx_getcwd_of"] opaque getcwdOf (pid : UInt32) : IO String

@[extern "zmx_gethostname"] opaque gethostname : IO String

/-- CLOCK_MONOTONIC in ms — checkpoint cadence, poll deadlines. -/
@[extern "zmx_monotonic_ms"] opaque monotonicMs : IO UInt64

/-- Unix epoch seconds — `created` timestamps in listings. -/
@[extern "zmx_realtime_s"] opaque realtimeS : IO UInt64

/-- Standard fds, named. -/
def stdinFd : UInt32 := 0
def stdoutFd : UInt32 := 1

end Zmx.Posix
