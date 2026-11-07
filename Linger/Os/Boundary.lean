module

public section

/-! # Linger.Os.Boundary — the foreign declarations

Every `@[extern]` in the program, each bound 1:1 to a wrapper in `c/shim.c` (syscall +
errno only; object arguments are borrowed `@&`, so the shim never manages refcounts).
Nothing here has a Lean body to prove. Every declaration is private: `Linger.Os.Shell`,
the one module that imports this one, wraps each binding under the same name, checks the
arguments the C side cannot represent, and states the contract in the wrapper's docstring.
`Linger.Os.Suites.Shim` and the live suites exercise those contracts. -/

namespace Linger.Os.Boundary

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
    (args : @& Array String) (extraEnv : @& Array String) : IO UInt64

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

@[extern "linger_spawn_detached"]
private opaque spawnDetached (prog : @& String) (args : @& Array String) (logPath : @& String) :
    IO UInt32

@[extern "linger_kill"]
private opaque kill (pid sig : UInt32) : IO Unit

@[extern "linger_alive"]
private opaque alive (pid : UInt32) : IO Bool

@[extern "linger_waitpid_nohang"]
private opaque waitpidNohang (pid : UInt32) (keep : Bool) : IO Int64

@[extern "linger_signal_session"]
private opaque signalSession (sid sig : UInt32) : IO UInt32

@[extern "linger_getuid"]
private opaque getuid : IO UInt32

@[extern "linger_getcwd_of"]
private opaque getcwdOf (pid : UInt32) : IO String

end Linger.Os.Boundary
