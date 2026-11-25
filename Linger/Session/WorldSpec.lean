module

public import Linger.Session.CoreSpec

public section

/-! # What session headlines assume of the world

The world claims the session headlines take as hypotheses, each over the foreign behaviour it
constrains, which it takes as a parameter, and each with the observation that would falsify it:
what the file system keeps of what linger saves, what a program in raw mode reads, what a started
program sees of its start, what a pty reports of its foreground and of its echo, how SIGKILL and poll(2) behave, that the effect executor answers every
effect, and that the operating system grants a lock only when no process holds it. -/

namespace Linger.Session

/-- The file system keeps what linger saves as a name's end record whole: once linger saved
`bytes`, writing them to a temporary file and renaming that over the record, a reader reads
exactly `bytes` until linger saves or removes the record again. A reader that sees part of a
record, an older one, or a mix of two falsifies it. -/
@[expose, reducible]
def Record.Kept (afterSave : List UInt8 → Option (List UInt8)) : Prop :=
  ∀ bytes, afterSave bytes = some bytes

/-- The file system keeps what linger replaces whole and durably through a crash, power loss
included. `afterCrash old new synced` is what a reader finds at a path once the machine crashed
while linger replaced the file there, which held `old` (`none` for no file), with `new`: writing
a temporary sibling, flushing it to the device, renaming it over the path and flushing the
directory (`Os.Shell.replaceFile`); `synced` says whether both flushes had returned. Once they
have, the path holds `new` whole; before, it holds the old file or the new one, never part of
either. A reader that finds anything else there after a crash, such as an empty file, a file cut
short, a mix of two, or the old file once both flushes returned, falsifies it. No suite cuts the
power: the resume suite kills a daemon with SIGKILL while it saves, which tests the tear and not
the flush. -/
@[expose, reducible]
def Disk.Durable (afterCrash : Option ByteArray → ByteArray → Bool → Option ByteArray) : Prop :=
  ∀ old new,
    afterCrash old new true = some new ∧
      (afterCrash old new false = old ∨ afterCrash old new false = some new)

/-- The kernel hands a program whose terminal is in raw mode exactly the bytes linger writes to
its session's pty, in order: `reads mode written` is what a program whose terminal is in `mode`
reads once linger wrote `written`. A program in raw mode that reads a byte linger did not write,
misses one it wrote or reads two in another order falsifies it, a control byte as much as any
other. Of any other mode it says nothing: in the cooked mode a terminal starts in, the line
discipline edits lines and turns ^C into SIGINT instead of a byte to read. -/
@[expose, reducible]
def Pty.Delivers (reads : Pty.Mode → ByteArray → ByteArray) : Prop :=
  ∀ written, reads .raw written = written

/-- The operating system reports a pty's foreground process, its words and its directory, as the
process sees them. `reported master` is what linger reads of the terminal whose master is
`master` (`Os.Shell.foreground`): the leader of its foreground process group, with that process's
words and directory; `seen master` is the same leader as it sees itself, the words it runs with
and the directory it is in. A report that names a process other than the foreground group's
leader, or other words or another directory than that process sees, falsifies it. Of a terminal
with no foreground group, or whose group's leader has ended, the report is `none`, and the claim
says nothing. On Linux `/proc` answers; on macOS `sysctl` and `libproc` do, which no macOS host
has checked yet. -/
@[expose, reducible]
def Pty.Foreground (reported seen : UInt32 → Option Foreground) : Prop :=
  ∀ master fg, reported master = some fg → seen master = some fg

/-- A pty reports whether it echoes what is typed as its program last set it. `reported master` is
what linger reads of the terminal whose master is `master` (`Os.Shell.echoOf`), its termios `ECHO`
flag, and `set master` is that flag as the program last set it on its own end of the terminal, as
`stty echo` and `stty -echo` do: the two ends share one setting. A report of echo off from a
terminal whose program last turned it on, or of echo on from one whose program turned it off,
falsifies it. Of a descriptor that is no terminal the report is `none`, and the claim says
nothing. -/
@[expose, reducible]
def Pty.Echo (reported set : UInt32 → Option Bool) : Prop :=
  ∀ master echo, reported master = some echo → set master = some echo

/-- The operating system runs what linger asks, and nothing else. A program that `start dir prog
args extra reset` starts sees the words `prog` and then `args`, runs in `dir`, and reads each
variable as the last pair of `extra` that names it says, its value or, for `none`, no such
variable, or else as `inherited` has it: the environment of the command that asked for the
session, which its daemon runs with. A program that cannot start is `none`. A started program
that sees other words, another directory, another value or a variable `extra` unsets falsifies
it. -/
@[expose, reducible]
def Spawn.Runs (inherited : String → Option String)
    (start :
      String →
        String →
        Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started) :
    Prop :=
  ∀ dir prog args extra reset started,
    start dir prog args extra reset = some started →
      started.argv = prog :: args.toList ∧
        started.dir = dir ∧ ∀ key, started.env key = (extra.reverse.lookup key).getD (inherited key)

/-- The operating system starts a program as clean as its start asks. A program that `start dir
prog args extra reset` starts has its session's terminal on descriptors 0, 1 and 2, and with
`reset.dispositions` ignores no signal, with `reset.mask` blocks none, and with
`reset.descriptors` has no other descriptor open, whatever the command that asked for the session
ignored, blocked or left open. A program so started that finds a signal ignored or blocked, a
descriptor from 3 up open, or another file than its terminal on 0, 1 or 2 falsifies it, as its
`SigIgn`, `SigBlk` and `fd` entries under `/proc` show on Linux. -/
@[expose, reducible]
def Spawn.Clean
    (start :
      String →
        String →
        Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started) :
    Prop :=
  ∀ dir prog args extra reset started,
    start dir prog args extra reset = some started →
      (∀ fd, fd < 3 → started.descriptor fd = some .terminal) ∧
        (reset.dispositions = true → ∀ sig, started.ignored sig = false) ∧
        (reset.mask = true → ∀ sig, started.blocked sig = false) ∧
        (reset.descriptors = true → ∀ fd, 3 ≤ fd → started.descriptor fd = none)

/-- SIGKILL ends a process within a second. `gone sig ms pid` says whether the process `pid` has
ended `ms` milliseconds after signal `sig` reached it: SIGKILL, which no process can catch,
ignore or block, has ended each process it reached once a second has passed, whatever the process
was doing. A process that SIGKILL reached and that still runs a second later falsifies it, as one
stuck in the kernel does. A signal reaches only a running process of the sender's user, so of a
terminal session linger's signals miss a process that left it with `setsid`, one that runs as
another user and one forked after linger looked for the session's processes; on macOS, and on
Linux before 5.3, a pid freed and reused between reading its session and signalling it could
receive them instead. -/
@[expose, reducible]
def Signal.Ends (gone : UInt32 → Nat → Nat → Bool) : Prop := ∀ pid ms, 1000 ≤ ms → gone 9 ms pid

/-- poll(2) waits out its timeout. `quiet timeout ms` says that a poll with that timeout returned
after `ms` milliseconds with none of its descriptors ready and no signal caught. Such a poll
returns no sooner than its timeout, and, with a negative timeout, which waits for an event,
never. A ready descriptor or a signal may end a poll sooner, as the SIGCHLD a daemon hears its
program end by does, and a loaded host may end it later. A poll that returns before its timeout
with nothing ready and no signal caught falsifies it, as does one with a negative timeout that
returns so at all. -/
@[expose, reducible]
def Poll.Sleeps (quiet : Int32 → Nat → Prop) : Prop :=
  ∀ timeout ms, quiet timeout ms → 0 ≤ timeout.toInt ∧ timeout.toInt ≤ ms

end Linger.Session

namespace Linger.Session.Driver

/-- The effect executor answers every effect: `execute st world eff` gives the world it leaves and
the effect's reply, which may say that the effect failed, its client gone, its checkpoint unsaved
or its stopped program's ending unknown. This is a premise about executing effects, not an
assumption that the event driver succeeds. An effect that raises instead of answering, as a
write a client's transport refuses could, falsifies it. -/
@[expose, reducible]
def Responds {S World Plan ε : Type}
    (execute : S → World → (eff : Effect Plan) → Except ε (World × Reply eff)) : Prop :=
  ∀ st world eff, ∃ answer, execute st world eff = .ok answer

end Linger.Session.Driver

namespace Linger.Session.Claim

/-- The operating system grants a lock only when no process holds it, as `flock` does on the file
a lock file's path names, when only a holder deletes that file and a process that locks a file
then checks that the path still names it, and locks the path's file again when not
(`Os.Shell.flock`, which `Os.Lock.Tells` lets tell them apart). Two processes holding the lock
of the file one path names at once falsify it. -/
@[expose, reducible]
def Exclusive (grant : State → Nat → Nat → Bool) : Prop :=
  ∀ s actor resource, grant s actor resource = true → s.locks resource = none

end Linger.Session.Claim
