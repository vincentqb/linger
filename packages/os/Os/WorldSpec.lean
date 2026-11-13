module

import SoftwareChallenge.Commands

public section

/-! # The foreign declarations, and the world claim the waits rest on

Every `@[extern]` in the program, each bound 1:1 to a wrapper in `packages/os/c/shim.c` (syscall +
errno only; object arguments are borrowed `@&`, so the shim never manages refcounts).
Nothing here has a Lean body to prove. Every binding is private: `Os.WorldCode`, the one module
that imports this one, wraps each binding under the same name in `Os.Shell`, checks the
arguments the C side cannot represent, and states the contract in the wrapper's docstring.
A binding that signals or waits for a process takes a proof that its pid is a real one, which
the C call never sees. `Linger.Os.Suites.Shim` and the live suites exercise those contracts.

The world claim `Wait.Lasts` says that a sleep lasts at least as long as it was asked to, which
the bounded waits of `Os.Shell.nap` rest on. -/

namespace Os.Boundary

@[extern "linger_ignore_sighup"]
private opaque ignoreSighup : IO Unit

@[extern "linger_close"]
private opaque close (fd : UInt32) : IO Unit

@[extern "linger_set_nonblock"]
private opaque setNonblock (fd : UInt32) : IO Unit

@[extern "linger_read"]
private opaque read (fd : UInt32) (max : USize) : IO (Option ByteArray)

@[extern "linger_write"]
private opaque write (fd : UInt32) (bytes : @& ByteArray) (off : USize) : IO Int64

@[extern "linger_poll"]
private opaque poll (fds : @& Array UInt32) (events : @& Array UInt32) (timeoutMs : Int32) :
    IO (Array UInt32)

@[extern "linger_spawn_pty"]
private opaque spawnPty (cols rows : UInt32) (cwd : @& String) (prog : @& String)
    (args : @& Array String) (extraEnv : @& Array String) (dispositions mask descriptors : Bool) :
    IO (Except (UInt8 × String) UInt64)

@[extern "linger_winsize_get"]
private opaque winsizeGet (fd : UInt32) : IO UInt64

@[extern "linger_winsize_set"]
private opaque winsizeSet (fd cols rows : UInt32) : IO Unit

@[extern "linger_term_raw"]
private opaque termRaw (fd : UInt32) : IO ByteArray

@[extern "linger_term_restore"]
private opaque termRestore (fd : UInt32) (saved : @& ByteArray) : IO Unit

@[extern "linger_unix_listen"]
private opaque unixListen (path : @& String) : IO UInt32

@[extern "linger_unix_connect"]
private opaque unixConnect (path : @& String) (nonblocking : Bool) : IO Int64

@[extern "linger_accept"]
private opaque accept (fd : UInt32) : IO Int64

@[extern "linger_flock"]
private opaque flock (path : @& String) : IO Int64

@[extern "linger_fsync_path"]
private opaque fsyncPath (path : @& String) (directory : Bool) : IO Bool

@[extern "linger_spawn_detached"]
private opaque spawnDetached (prog : @& String) (args : @& Array String) (logPath : @& String) :
    IO UInt32

@[extern "linger_kill"]
private opaque kill (pid sig : UInt32) (valid : 0 < pid ∧ pid ≤ 0x7FFFFFFF) : IO Unit

@[extern "linger_alive"]
private opaque alive (pid : UInt32) (valid : 0 < pid ∧ pid ≤ 0x7FFFFFFF) : IO Bool

@[extern "linger_waitpid_nohang"]
private opaque waitpidNohang (pid : UInt32) (keep : Bool) (valid : 0 < pid ∧ pid ≤ 0x7FFFFFFF) :
    IO Int64

@[extern "linger_signal_pipe"]
private opaque signalPipe : IO UInt32

@[extern "linger_signal_session"]
private opaque signalSession (sid sig : UInt32) (valid : 0 < sid ∧ sid ≤ 0x7FFFFFFF) : IO UInt32

@[extern "linger_getuid"]
private opaque getuid : IO UInt32

@[extern "linger_getcwd_of"]
private opaque getcwdOf (pid : UInt32) : IO String

end Os.Boundary

namespace Os.Wait

/-- A sleep of `ms` milliseconds asked for when the monotonic clock reads `now` returns, and the
clock then reads `after now ms`, at least `ms` later. A clock reading, after `IO.sleep ms`
returns, less than `ms` above the one before it falsifies it, as would a sleep that never
returns. -/
WorldClaim Lasts (after : Nat → Nat → Nat) := ∀ now ms, now + ms ≤ after now ms

end Os.Wait
