module

public section

/-! # The foreign declarations, and the world claims the waits, the exec and the names rest on

Every `@[extern]` in the program, each bound 1:1 to a wrapper in `packages/os/c/shim.c` (syscall +
errno only; object arguments are borrowed `@&`, so the shim never manages refcounts).
Nothing here has a Lean body to prove. Every binding is private: `Os.WorldCode`, the one module
that imports this one, wraps each binding under the same name in `Os.Shell`, checks the
arguments the C side cannot represent, and states the contract in the wrapper's docstring.
A binding that signals or waits for a process takes a proof that its pid is a real one, which
the C call never sees. `Linger.Os.Suites.Shim` and the live suites exercise those contracts.

The world claim `Wait.Lasts` says that a sleep lasts at least as long as it was asked to, which
the bounded waits of `Os.Shell.nap` rest on, `Exec.Keeps` that an exec keeps the process, its
children and the descriptors it does not close, which an upgrade of a session's daemon rests on,
`Place.NoReplace` that a link or a rename that may not replace never replaces a name, which the
names of sessions rest on, `Lock.Tells` that `fstat` and `stat` tell the file a descriptor
holds from the one a path names, which a lock that its holder may delete rests on
(`Os.Shell.flock`), and `Signal.Group` that a signal to a process group reaches every member,
which a session's ending rests on (`Os.Shell.signalGroup`). -/

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

@[extern "linger_socket_pair"]
private opaque socketPair : IO UInt64

@[extern "linger_accept"]
private opaque accept (fd : UInt32) : IO Int64

@[extern "linger_flock"]
private opaque flock (path : @& String) : IO Int64

@[extern "linger_link_new"]
private opaque linkNew (src dst : @& String) : IO Bool

@[extern "linger_rename_new"]
private opaque renameNew (src dst : @& String) : IO Bool

@[extern "linger_names_held"]
private opaque namesHeld (fd : UInt32) (path : @& String) : IO Bool

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
private opaque signalPipe (adoptRead adoptWrite : UInt32) : IO UInt64

@[extern "linger_exec_image"]
private opaque execImage (prog : @& String) (args : @& Array String) (keep : @& Array UInt32) :
    IO Unit

@[extern "linger_signal_session"]
private opaque signalSession (sid sig : UInt32) (valid : 0 < sid ∧ sid ≤ 0x7FFFFFFF) : IO UInt32

@[extern "linger_kill_group"]
private opaque killGroup (pgid sig : UInt32) (valid : 1 < pgid ∧ pgid ≤ 0x7FFFFFFF) : IO Bool

@[extern "linger_environ_names"]
private opaque environNames : IO (Array String)

@[extern "linger_getuid"]
private opaque getuid : IO UInt32

@[extern "linger_getcwd_of"]
private opaque getcwdOf (pid : UInt32) : IO String

@[extern "linger_tcgetpgrp"]
private opaque tcgetpgrp (fd : UInt32) : IO Int64

@[extern "linger_tty_echo"]
private opaque ttyEcho (fd : UInt32) : IO Int64

@[extern "linger_dgram_bind"]
private opaque dgramBind (path : @& String) : IO UInt32

@[extern "linger_dgram_send"]
private opaque dgramSend (path : @& String) (bytes : @& ByteArray) : IO Int64

@[extern "linger_cmdline_of"]
private opaque cmdlineOf (pid : UInt32) (valid : 0 < pid ∧ pid ≤ 0x7FFFFFFF) : IO ByteArray

end Os.Boundary

namespace Os.Wait

/-- A sleep of `ms` milliseconds asked for when the monotonic clock reads `now` returns, and the
clock then reads `after now ms`, at least `ms` later. A clock reading, after `IO.sleep ms`
returns, less than `ms` above the one before it falsifies it, as would a sleep that never
returns. -/
@[expose, reducible]
def Lasts (after : Nat → Nat → Nat) : Prop := ∀ now ms, now + ms ≤ after now ms

end Os.Wait

namespace Os.Exec

/-- An `execve` that succeeds replaces the program a process runs and nothing else of what the
process is: a process with id `pid`, children `children` and the descriptors `kept` open without
close-on-exec, by number, is, after the exec, `exec pid children kept`, with the same id, the
same children and the same descriptors open at the same numbers. A new image that reads another
id, misses a child of the old one, or finds a kept descriptor closed or holding something else
falsifies it. -/
@[expose, reducible]
def Keeps (exec : Nat → List Nat → List Nat → Nat × List Nat × List Nat) : Prop :=
  ∀ pid children kept, exec pid children kept = (pid, children, kept)

end Os.Exec

namespace Os.Place

/-- A link (`Os.Shell.linkNew`), or a rename that may not replace (`Os.Shell.renameNew`), never
replaces what a name names. `placed rename names src dst` is what the names of a directory name
once linger placed `src`'s file at `dst`, linking it or, with `rename`, renaming it, from what
they named before, `names`: each name the file it names, or `none`; and `none` when the call
failed. Onto a name that names a file it fails, changing nothing. When it succeeds, `dst` names
the file `src` named, a rename leaves `src` naming nothing, and no other name changes. Two
processes that place onto one name at once therefore leave it naming the first one's file, and
the second fails. A call that succeeds while `dst` names a file, or that leaves `dst` naming
another file, falsifies it. A file system that cannot rename without replacing fails every
rename, which the claim allows. -/
@[expose, reducible]
def NoReplace
    (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)) :
    Prop :=
  ∀ rename names src dst,
    ((names dst).isSome → placed rename names src dst = none) ∧
      ∀ after,
        placed rename names src dst = some after →
          src ≠ dst ∧
            after dst = names src ∧
            after src = (if rename then none else names src) ∧
            ∀ other, other ≠ src → other ≠ dst → after other = names other

end Os.Place

namespace Os.Lock

/-- `fstat` and `stat` tell the file a descriptor holds from the one a path names: `reads named`
is what `Os.Shell.namesHeld` answers of a descriptor that holds a file open and a path, when the
path names that file (`named`) and when it names another file or none, as once the file was
unlinked and another created there. A file a descriptor holds open keeps its device and inode
numbers, which no other file has while it is open, so the answer is true exactly when the path
names the held file. A path that names the held file and reads false, or names another or none
and reads true, falsifies it. -/
@[expose, reducible]
def Tells (reads : Bool → Bool) : Prop := ∀ named, reads named = named

end Os.Lock

namespace Os.Signal

/-- A signal to a process group reaches every process of the group. `member pgid pid` says
whether the process `pid` is in the process group `pgid` when `Os.Shell.signalGroup` signals it,
and `reaches pgid pid` whether that signal reaches `pid`: kill(2) of `-pgid` delivers to every
member at once, one forked since included. A member the signal misses falsifies it. A process
that left the group, with `setsid` or `setpgid`, is no member. -/
@[expose, reducible]
def Group (member reaches : Nat → Nat → Bool) : Prop :=
  ∀ pgid pid, member pgid pid = true → reaches pgid pid = true

end Os.Signal

namespace Os.Dgram

/-- Datagrams sent to a Unix socket's path arrive whole and in order. `received cap sent` is what
the datagram socket bound there reads, one read of at most `cap` bytes for each datagram, of the
datagrams `sent`, sent to it one after another, each sent whole (`Os.Shell.dgramSend` answered
that it sent all of it) and each of at most `cap` bytes: exactly those datagrams, in the order
they were sent, none cut short, merged, split, repeated or reordered. A read that returns part of
one of them, two at once or one out of its order falsifies it. Of a datagram the socket's queue
had no room for, which the send refuses, it says nothing. -/
@[expose, reducible]
def Whole (received : Nat → List (List UInt8) → List (List UInt8)) : Prop :=
  ∀ cap sent, (∀ d ∈ sent, d.length ≤ cap) → received cap sent = sent

end Os.Dgram
