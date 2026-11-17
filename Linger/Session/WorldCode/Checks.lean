module

public import Linger.Session.WorldSpec
import Linger.Session.CoreCode
import Linger.Session.WorldCode.Daemon
import Os.WorldCode
import Os.WorldSpec
import Terminal.CoreCode.Replay
import SoftwareChallenge.Commands

/-! # The checks of the session's world claims

Each world claim the session headlines rest on has a check here, which tests the foreign
behaviour the claim constrains on the host it runs on, with its own programs, terminals, files and
sockets. A claim takes that behaviour as a parameter, which no Lean term computes: each check
names it with a constant of this module, which has no body, and observes it by running the real
thing. Each says what it covers; the claims are of every input. No program module imports this
one. -/

namespace Linger.Session.Checks

open Os.Shell

/-- Whether `done` holds before the monotonic clock reaches `deadline`, asked every 10 ms. -/
def within (deadline : Nat) (done : IO Bool) : IO Bool := do
  repeat
    if ← done then
      return true
    unless ← nap deadline 10 do
      return ← done
  return false

/-- Whether `needle` occurs in `hay`. -/
def occurs (needle hay : List UInt8) : Bool :=
  (List.range (hay.length + 1)).any fun i => (hay.drop i).take needle.length == needle

/-- Whether what the terminal `fd` shows holds `text` before the clock reaches `deadline`. -/
def shows (fd : UInt32) (text : String) (deadline : Nat) : IO Bool := do
  let mut seen : List UInt8 := []
  repeat
    if occurs text.toUTF8.toList seen then
      return true
    if (← monotonicMs) ≥ deadline then
      return false
    let revs ← poll #[fd] #[POLLIN] 50
    if revs.getD 0 0 &&& (POLLIN ||| POLLHUP) != 0 then
      match ← read fd 4096 with
      | some bytes =>
        seen := seen ++ bytes.toList
      | none =>
        return occurs text.toUTF8.toList seen
  return false

/-- Stop the program `pid` that `spawnPty` started, unless it was reaped: kill it, wait up to
10 s for it to end, reap it, and close its terminal. -/
def stop (pid master : UInt32) (reaped : Bool := false) : IO Unit := do
  try
    unless reaped do
      kill pid 9
      discard <|
          within ((← monotonicMs) + 10000) do
            return (← reapNohang pid) != .running
  finally
    close master

/-- Fail the check, saying why. -/
def refute {α : Type} (why : String) : IO α := throw (IO.userError why)

/-- What a reader reads of a name's end record once linger saved `bytes` there: the observation
`Record.Kept` constrains. -/
opaque readsBack : List UInt8 → Option (List UInt8)

-- A record saved as linger saves one, through `Os.Shell.replaceFile`, reads back whole at every
-- size, from none to a mebibyte; and a reader that reads while it is saved over and over reads
-- one saved record whole each time, never part of one or a mix of two.
Check Record.Kept readsBack := do
  IO.FS.withTempDir fun dir => do
      let path := (dir / "name.record").toString
      for size in [0, 1, 4095, 4096, 65537, 1048576] do
        let bytes := (List.range size).map fun i => (i * 7 + size).toUInt8
        replaceFile path (ByteArray.mk bytes.toArray)
        let read := (← IO.FS.readBinFile path).toList
        unless read == bytes do
          refute s!"a record of {size} bytes read back as {read.length} bytes"
      -- version `v` is `4096 + 97 * v` bytes, each `v`: a reader can tell any part or mix from it
      let version (v : Nat) := ByteArray.mk (List.replicate (4096 + 97 * v) v.toUInt8).toArray
      replaceFile path (version 0)
      let saved ← IO.mkRef false
      let reader ←
        IO.asTask do
            let mut torn : Option Nat := none
            repeat
              let read := (← IO.FS.readBinFile path).toList
              let whole :=
                match read.head? with
                | some v => read.length == 4096 + 97 * v.toNat && read.all (· == v)
                | none => false
              if !whole then
                torn := some read.length
              if (← saved.get) || torn.isSome then
                break
            return torn
      for v in List.range 64 do
        replaceFile path (version (v + 1))
      saved.set true
      match ← IO.wait reader with
      | .ok none =>
        pure ()
      | .ok (some length) =>
        refute
            s!"a reader read {length} bytes of a record being saved: part of one, or a mix of two"
      | .error err =>
        refute s!"a reader could not read a record being saved: {err}"

/-- What a reader finds at a path once the machine crashed while linger replaced the file there:
the observation `Disk.Durable` constrains. -/
opaque afterCrash : Option ByteArray → ByteArray → Bool → Option ByteArray

-- No check cuts the power. This one checks what a reader finds once both of `replaceFile`'s
-- flushes have returned and no crash came: over an old file and over none, a fresh descriptor
-- reads the new file whole, the temporary sibling is gone, and the file flushes again.
Check Disk.Durable afterCrash := do
  IO.FS.withTempDir fun dir => do
      let path := (dir / "name.ckpt").toString
      for (old, new) in [(none, 0), (some 1, 70000), (some 70000, 3)] do
        if let some size := old then
          replaceFile path (ByteArray.mk (List.replicate size 1).toArray)
        let bytes := (List.range new).map fun i => (i * 13 + 5).toUInt8
        replaceFile path (ByteArray.mk bytes.toArray)
        let read := (← IO.FS.readBinFile path).toList
        unless read == bytes do
          refute s!"a replaced file of {new} bytes read back as {read.length} bytes"
        if ← System.FilePath.pathExists (path ++ ".tmp") then
          refute "a replaced file left its temporary sibling behind"
        unless ← fsyncPath path do
          refute "a replaced file did not flush"

/-- What a program whose terminal is in a mode reads once its pty was written: the observation
`Pty.Delivers` constrains. -/
opaque rawReads : Pty.Mode → ByteArray → ByteArray

-- A program whose terminal is in raw mode reads every byte written to its pty, one for one and
-- in order: the program sets raw mode with `stty raw -echo`, says so, and copies what it reads to
-- a file, and the check writes every byte value, the control bytes, DEL and bytes that are no
-- UTF-8 among them, then the same in reverse order.
Check Pty.Delivers rawReads := do
  IO.FS.withTempDir fun dir => do
      let file := (dir / "raw.input").toString
      let (pid, master) ←
        spawnPty 80 24 "" "/bin/sh"
            #["-c", "stty raw -echo; printf ready; exec cat > \"$1\"", "sh", file] #[]
      try
        unless ← shows master "ready" ((← monotonicMs) + 10000) do
          refute "the program did not set raw mode"
        let every := (List.range 256).map UInt8.ofNat
        let payload := every ++ every.reverse
        writeAll master (ByteArray.mk payload.toArray)
        let readBack : IO (List UInt8) := do
          return (((← (IO.FS.readBinFile file).toBaseIO).toOption).map (·.toList)).getD []
        discard <|
            within ((← monotonicMs) + 10000) do
              return (← readBack).length ≥ payload.length
        let got ← readBack
        unless got == payload do
          let differs :=
            ((got.zip payload).findIdx? fun (a, b) => a != b).getD (min got.length payload.length)
          refute
              s!"a program in raw mode read {got.length} of {payload.length} bytes, the same up \
          to byte {differs}"
      finally
        stop pid master

/-- The environment of the process that starts a program: an observation `Spawn.Runs`
constrains, which the started program inherits. -/
opaque inherited : String → Option String

/-- What a program a start asks for sees of its start, `none` when it cannot start: the
observation `Spawn.Runs` and `Spawn.Clean` constrain. -/
opaque started :
    String →
      String → Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started

/-- Start `/bin/sh` in a new terminal, in `dir`, running `script` with `words` and the extra
environment `extra`, as a session's program starts, and give the lines it leaves in `out` once
it writes them there, or `none` if it does not within 10 s. -/
def startedSees (dir out script : String) (words extra : Array String) (reset : SpawnReset := {}) :
    IO (Option (List String)) := do
  let (pid, master) ← spawnPty 80 24 dir "/bin/sh" (#["-c", script] ++ words) extra reset
  try
    unless ← within ((← monotonicMs) + 10000) (System.FilePath.pathExists out) do
      return none
    return some ((← IO.FS.readFile out).splitOn "\x00")
  finally
    stop pid master

-- A started program sees the words, the directory and the environment its start asked for: a
-- shell started in a new terminal, in a directory of its own, with words a shell would expand,
-- split or quote, with variables that override what it inherits, the last setting of one
-- winning, and one it inherits unset, writes what it sees to a file: its directory, its words and
-- each variable.
Check Spawn.Runs inherited started := do
  IO.FS.withTempDir fun dir => do
      let out := (dir / "started").toString
      let words := #["w0", "two words", "$HOME `id` * ;", "ü ✓", ""]
      let script :=
        "printf '%s\\000' \"$(pwd -P)\" \"$0\" \"$@\" \"$LINGER_CHECK\" \"${HOME-unset}\" \"$PATH\" > \
        \"$LINGER_CHECK_OUT.part\" && mv \"$LINGER_CHECK_OUT.part\" \"$LINGER_CHECK_OUT\""
      let extra :=
        #["LINGER_CHECK=first", s!"LINGER_CHECK_OUT={out}", "LINGER_CHECK=last", s!"HOME={dir}",
          "HOME"]
      let some seen ←
        startedSees dir.toString out script words
            extra | refute "the started program did not say what it sees"
      let wanted :=
        [(← IO.FS.realPath dir).toString] ++ words.toList ++
          ["last", "unset", (← IO.getEnv "PATH").getD "", ""]
      unless seen == wanted do
        refute s!"a started program saw {seen}, not {wanted}"

/-- The text of the file at `path`, or nothing if it cannot be read. -/
def textOf (path : String) : IO String := do
  return ((← (IO.FS.readFile path).toBaseIO).toOption).getD ""

/-- What linger reads of the foreground of the terminal whose master is the argument: the
observation `Pty.Foreground` constrains. -/
opaque reportedForeground : UInt32 → Option Foreground

/-- The foreground's leader of the terminal whose master is the argument, as it sees itself: the
observation `Pty.Foreground` compares the report with. -/
opaque seenForeground : UInt32 → Option Foreground

/-- What `Os.Shell.foreground` reports of the terminal `master`, once it reports `words` or the
clock reaches `deadline`. -/
def reportsWithin (master : UInt32) (words : List String) (deadline : Nat) :
    IO (Option (UInt32 × List String × String)) := do
  let mut report ← foreground master
  while (report.map (·.2.1)) != some words && (← monotonicMs) < deadline do
    IO.sleep 20
    report ← foreground master
  return report

-- The operating system reports a pty's foreground as its leader sees itself: a shell started in a
-- new terminal, with words a shell would split or quote, moves to a directory of its own and
-- writes the directory it sees there, while it is its terminal's foreground, and is reported with
-- its pid, its words and that directory; then an interactive shell in a new terminal runs a
-- `sleep`, a job of its own, in another directory it moves to, and the foreground reported is
-- that `sleep`, with its words and that directory. It runs on macOS too, where `sysctl` and
-- `libproc` answer, but no macOS host has run it yet.
Check Pty.Foreground reportedForeground seenForeground := do
  IO.FS.withTempDir fun dir => do
      let out := (dir / "seen").toString
      IO.FS.createDir (dir / "moved")
      IO.FS.createDir (dir / "job")
      let script := "cd moved && pwd -P > \"$1.part\" && mv \"$1.part\" \"$1\" && exec sleep 60"
      let words := #["-c", script, "two words", out, "ü ✓"]
      let (pid, master) ← spawnPty 80 24 dir.toString "/bin/sh" words #[]
      try
        unless ← within ((← monotonicMs) + 10000) (System.FilePath.pathExists out) do
          refute "the started shell did not say where it is"
        let seen := ((← IO.FS.readFile out).splitOn "\n").headD ""
        match ← reportsWithin master ["sleep", "60"] ((← monotonicMs) + 10000) with
        | some (group, argv, cwd) =>
          unless group == pid && argv == ["sleep", "60"] && cwd == seen do
            refute
                s!"the foreground of a started program, {pid} running sleep 60 in {seen}, \
            was reported as {group} running {argv} in {cwd}"
        | none =>
          refute "a started program's terminal reported no foreground"
      finally
        stop pid master
      let (shell, master) ← spawnPty 80 24 dir.toString "/bin/sh" #["-i"] #[]
      try
        writeAll master ("cd job && sleep 61\n".toUTF8)
        let job := (← IO.FS.realPath (dir / "job")).toString
        match ← reportsWithin master ["sleep", "61"] ((← monotonicMs) + 10000) with
        | some (group, argv, cwd) =>
          try
            unless group != shell && argv == ["sleep", "61"] && cwd == job do
              refute
                  s!"the foreground job sleep 61 in {job} of an interactive shell {shell} was \
              reported as {group} running {argv} in {cwd}"
          finally
            kill group 9
        | none =>
          refute "an interactive shell's terminal reported no foreground job"
      finally
        stop shell master

/-- What linger reads of whether the terminal whose master is the argument echoes: the observation
`Pty.Echo` constrains. -/
opaque reportedEcho : UInt32 → Option Bool

/-- Whether the terminal whose master is the argument echoes, as its program last set it on its
own end: the observation `Pty.Echo` compares the report with. -/
opaque setEcho : UInt32 → Option Bool

/-- What `Os.Shell.echoOf` reports of the terminal `master`, once it reports `wanted` or the clock
reaches `deadline`. -/
def echoWithin (master : UInt32) (wanted : Bool) (deadline : Nat) : IO (Option Bool) := do
  let mut report ← echoOf master
  while report != some wanted && (← monotonicMs) < deadline do
    IO.sleep 20
    report ← echoOf master
  return report

-- A pty reports its echo as its program last set it: a shell in a new terminal turns echo off on
-- its own end, says so in a file, and waits for a line, then turns echo on again and says so;
-- after each, linger reads the flag through the master, and it is what the shell set. The shell
-- reads its line with echo off, and the master reads no echo of it.
Check Pty.Echo reportedEcho setEcho := do
  IO.FS.withTempDir fun dir => do
      let off := (dir / "off").toString
      let on := (dir / "on").toString
      let script :=
        "stty -echo && : > \"$1\" && read -r line && stty echo && : > \"$2\" && exec sleep 60"
      let (pid, master) ← spawnPty 80 24 dir.toString "/bin/sh" #["-c", script, "sh", off, on] #[]
      try
        unless ← within ((← monotonicMs) + 10000) (System.FilePath.pathExists off) do
          refute "the started shell did not turn echo off"
        let silent ← echoWithin master false ((← monotonicMs) + 10000)
        unless silent == some false do
          refute s!"a terminal whose program turned echo off reported echo {silent}"
        writeAll master ("go\n".toUTF8)
        unless ← within ((← monotonicMs) + 10000) (System.FilePath.pathExists on) do
          refute "the started shell did not turn echo on"
        let echoing ← echoWithin master true ((← monotonicMs) + 10000)
        unless echoing == some true do
          refute s!"a terminal whose program turned echo on reported echo {echoing}"
      finally
        stop pid master

-- A started program holds no more than its start asks for, whatever the process that starts it
-- holds: that process ignores SIGHUP, as a daemon does, and the program, a shell, finds its
-- terminal on descriptors 0, 1 and 2, no other descriptor from 3 to 64 open, and SIGHUP and
-- SIGINT able to reach it; on Linux, once it is `sleep`, which changes none of it, its `/proc`
-- entry shows no signal ignored or blocked and, once `sleep` has closed what it opens as it
-- starts, only descriptors 0, 1 and 2, all its terminal.
-- The runner holds no descriptor a start could pass on, so the descriptors' reset goes untested.
Check Spawn.Clean started := do
  IO.FS.withTempDir fun dir => do
      let out := (dir / "clean").toString
      ignoreSighup
      let probe :=
        "if [ -t 0 ] && [ -t 1 ] && [ -t 2 ]; then tty=yes; else tty=no; fi; open=; n=3; \
        while [ \"$n\" -le 64 ]; do if [ -e \"/dev/fd/$n\" ]; then open=\"$open $n\"; fi; \
        n=$((n + 1)); done; /bin/sh -c 'trap \"exit 9\" HUP; kill -s HUP $$; exit 7'; hup=$?; \
        /bin/sh -c 'trap \"exit 9\" INT; kill -s INT $$; exit 7'; int=$?; \
        printf '%s\\000' \"$tty\" \"$open\" \"$hup\" \"$int\" > \"$1.part\" && mv \"$1.part\" \"$1\"; \
        exec sleep 60"
      let (pid, master) ← spawnPty 80 24 dir.toString "/bin/sh" #["-c", probe, "sh", out] #[]
      try
        unless ← within ((← monotonicMs) + 10000) (System.FilePath.pathExists out) do
          refute "the started program did not say what it holds"
        match (← IO.FS.readFile out).splitOn "\x00" with
        | [tty, opened, hup, int, ""] =>
          unless tty == "yes" do
            refute "a started program does not have its terminal on descriptors 0, 1 and 2"
          unless opened.isEmpty do
            refute s!"a started program holds descriptors{opened} open"
          unless hup == "9" && int == "9" do
            refute s!"SIGHUP or SIGINT cannot reach a started program ({hup}, {int})"
        | seen =>
          refute s!"a started program said {seen}"
        if ← System.FilePath.pathExists "/proc/self/status" then
          let entry := s!"/proc/{pid}"
          let slept : IO Bool := do
            return (← textOf s!"{entry}/cmdline").startsWith "sleep"
          unless ← within ((← monotonicMs) + 10000) slept do
            refute "the started program did not become sleep"
          let masks :=
            ((← textOf s!"{entry}/status").splitOn "\n").filter fun line =>
              line.startsWith "SigIgn:" || line.startsWith "SigBlk:"
          unless
            masks.length == 2 &&
              masks.all fun line =>
                ((line.splitOn ":").getD 1 "").trimAscii.toString.all (· == '0') do
            refute s!"a started program finds signals ignored or blocked: {masks}"
          -- What `sleep` opens itself while it starts, its libraries and the locale archive,
          -- closes before it sleeps, and what it inherited stays open: so the check waits for
          -- the descriptors to be its terminal's alone, and a start that passed one on fails.
          let held : IO (Array String × Array String) := do
            let fds := ((← System.FilePath.readDir s!"{entry}/fd").map (·.fileName)).qsort (· < ·)
            let targets ←
              fds.mapM fun fd => do
                  return ((← (IO.FS.realPath s!"{entry}/fd/{fd}").toBaseIO).toOption.map
                          (·.toString)).getD
                      ""
            return (fds, targets)
          let clean : IO Bool := do
            let (fds, targets) ← held
            return fds.toList == ["0", "1", "2"] && targets.all (some · == targets[0]?)
          unless ← within ((← monotonicMs) + 10000) clean do
            let (fds, targets) ← held
            refute s!"a started program holds descriptors {fds} on {targets}"
      finally
        stop pid master

/-- Whether a process has ended a number of milliseconds after a signal reached it: the
observation `Signal.Ends` constrains. -/
opaque ended : UInt32 → Nat → Nat → Bool

-- SIGKILL ends a process within a second: a program in a terminal session of its own, which
-- ignores SIGTERM, SIGINT and SIGHUP and sleeps, has ended a second after SIGKILL reached it.
Check Signal.Ends ended := do
  let (pid, master) ←
    spawnPty 80 24 "" "/bin/sh" #["-c", "trap '' TERM INT HUP; printf ready; exec sleep 60"] #[]
  let reaped ← IO.mkRef false
  try
    unless ← shows master "ready" ((← monotonicMs) + 10000) do
      refute "the program did not start"
    kill pid 9
    let sent ← monotonicMs
    let gone ←
      within (sent + 1000) do
          match ← reapNohang pid with
          | .running =>
            return false
          | _ =>
            reaped.set true
            return true
    unless gone do
      refute "a process SIGKILL reached still ran a second later"
  finally
    stop pid master (← reaped.get)

/-- Whether a poll with a timeout returned after a number of milliseconds with nothing ready and
no signal caught: the observation `Poll.Sleeps` constrains. -/
opaque quiet : Int32 → Nat → Prop

-- poll(2) waits out its timeout: a poll of a listening socket nobody connects to, with timeouts
-- from 0 to 50 ms, returns with nothing ready no sooner than its timeout; and one with a negative
-- timeout waits for its event, returning only once a connection arrives 100 ms later.
Check Poll.Sleeps quiet := do
  IO.FS.withTempDir fun dir => do
      let path := (dir / "p.sock").toString
      let listen ← unixListen path
      try
        for timeout in [0, 1, 5, 20, 50] do
          let before ← monotonicMs
          let revs ← poll #[listen] #[POLLIN] (Int32.ofNat timeout)
          let after ← monotonicMs
          unless revs.all (· == 0) do
            refute s!"a socket nobody connects to was ready ({revs})"
          unless before + timeout ≤ after do
            refute s!"a poll of {timeout} ms returned after {after - before} ms with nothing ready"
        let before ← monotonicMs
        let connector ←
          IO.asTask do
              IO.sleep 100
              unixConnect path
        let revs ← poll #[listen] #[POLLIN] (-1)
        let after ← monotonicMs
        if let .ok fd := ← IO.wait connector then
          if fd ≥ 0 then
            close fd.toUInt64.toUInt32
        unless revs.getD 0 0 &&& POLLIN != 0 && before + 100 ≤ after do
          refute s!"a poll with no timeout returned after {after - before} ms ({revs})"
      finally
        close listen

/-- What linger's effect executor answers for an effect in a world, as `Driver.Responds` reads
an executor: the world it leaves and the effect's reply, or what it raises. -/
opaque answers :
    State →
      Shell.Daemon.Rt →
      (eff : Effect Terminal.Replay.Plan) → Except IO.Error (Shell.Daemon.Rt × Driver.Reply eff)

/-- A daemon's transport to a client that connected to `listen` at `path` and hung up. -/
def hungUp (listen : UInt32) (path : String) : IO Shell.Daemon.Conn := do
  let client ← unixConnect path
  unless client ≥ 0 do
    refute s!"could not connect to the check's socket ({client})"
  let served ← accept listen
  unless served ≥ 0 do
    refute s!"could not accept the check's connection ({served})"
  close client.toUInt64.toUInt32
  return { fd := served.toUInt64.toUInt32 }

-- The daemon's effect executor answers every effect, the world it acts on failing: each kind of
-- effect, run through `Daemon.runEffect` against clients that hung up, a terminal descriptor
-- that is no terminal, checkpoint hooks that raise and a program in a terminal session of its
-- own, returns its reply and the events the driver feeds back for it: a client gone, nothing,
-- or how the stopped program ended. It covers each kind of effect once, in one failing world;
-- the claim is of every state, world and effect.
Check Driver.Responds answers := do
  IO.FS.withTempDir fun dir => do
      let path := (dir / "d.sock").toString
      let listen ← unixListen path
      let (pid, master) ← spawnPty 80 24 "" "/bin/sh" #["-c", "exec sleep 60"] #[]
      let reaped ← IO.mkRef false
      try
        let sent ← hungUp listen path
        let replayed ← hungUp listen path
        let closed ← hungUp listen path
        let st := State.boot (Terminal.Vt.Vt.init 80 24) [] []
        let rt : Shell.Daemon.Rt :=
          { st, listenFd := listen, ptyFd := 0xFFFFFF, childPid := pid,
            conns := [sent, replayed, closed],
            saveCkpt := fun _ => refute "the check's checkpoint fails",
            dropCkpt := refute "the check's delete fails" }
        let expect (eff : Effect Terminal.Replay.Plan) (rt : Shell.Daemon.Rt)
          (fed : List Event → Bool) : IO Shell.Daemon.Rt := do
          let (rt, events) ← Shell.Daemon.runEffect rt eff
          unless fed events do
            refute s!"an effect was answered with the events {repr events}"
          return rt
        let gone (c : Shell.Daemon.Conn) (events : List Event) : Bool :=
          match events with
          | [.closed id] => id == c.fd.toNat
          | _ => false
        let rt ← expect (.send sent.fd.toNat (.output [65])) rt (gone sent)
        let rt ←
          expect (.replay replayed.fd.toNat (Terminal.Replay.start st.terminal)) rt (gone replayed)
        let rt ← expect (.close closed.fd.toNat) rt (gone closed)
        let rt ← expect (.send 0xFFFFFF (.output [66])) rt (·.isEmpty)
        let rt ← expect (.writePty [1, 2, 3]) rt (·.isEmpty)
        let rt ← expect (.resizePty 100 30) rt (·.isEmpty)
        let rt ← expect .checkpoint rt (·.isEmpty)
        let rt ← expect .dropCheckpoint rt (·.isEmpty)
        let rt ← expect (.record (.running none)) rt (·.isEmpty)
        let rt ←
          expect .stopProgram rt fun
              | [.stopped _] => true
              | _ => false
        let rt ← expect .exit rt (·.isEmpty)
        unless rt.exiting do
          refute "the executor did not keep that an effect asked the daemon to exit"
        reaped.set
            (←
              within ((← monotonicMs) + 10000) do
                  return (← reapNohang pid) != .running)
      finally
        stop pid master (← reaped.get)
        close listen

/-- Which lock attempts the operating system grants, in a state of the locks: the observation
`Claim.Exclusive` constrains. -/
opaque grants : Claim.State → Nat → Nat → Bool

-- The operating system grants a lock only when no one holds it: while one open of a lock file
-- holds its `flock`, as a daemon's does, another open of it does not get it, and once the holder
-- lets it go, the next does.
Check Claim.Exclusive grants := do
  IO.FS.withTempDir fun dir => do
      let path := (dir / "name.lock").toString
      let first ← flock path
      unless first ≥ 0 do
        refute s!"a free lock file's lock was refused ({first})"
      let second ← flock path
      if second ≥ 0 then
        close second.toUInt64.toUInt32
        close first.toUInt64.toUInt32
        refute "two opens of one lock file held its lock at once"
      close first.toUInt64.toUInt32
      let third ← flock path
      unless third ≥ 0 do
        refute s!"a lock file's lock was refused once its holder let it go ({third})"
      close third.toUInt64.toUInt32

/-- What the names of a directory name once a session's name is placed, as a start places an
entry, with a link, or as a rename moves one, with a rename that may not replace: the observation
`Os.Place.NoReplace` constrains, which `one_name` rests on. It has no body; the check below
observes it. -/
opaque placedNames : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)

-- A start and a rename onto one name leave it naming one entry: in a directory of its own, four
-- links and four renames that may not replace, at once, from eight files that each hold their
-- own ID, onto one free name; exactly one succeeds, the name holds that one's ID, every linked
-- source stays and every renamed source that lost stays too.
Check Os.Place.NoReplace placedNames := do
  IO.FS.withTempDir fun dir => do
      let sources := (List.range 8).map fun i => (decide (i < 4), s!"src{i}")
      for (_, source) in sources do
        IO.FS.writeFile (dir / source) source
      let target := (dir / "name").toString
      let tasks ←
        sources.mapM fun (links, source) =>
            IO.asTask
              (if links then Os.Shell.linkNew (dir / source).toString target
              else Os.Shell.renameNew (dir / source).toString target)
              Task.Priority.dedicated
      let mut winners := []
      for ((_, source), task) in sources.zip tasks do
        if ← IO.ofExcept (← IO.wait task) then
          winners := winners ++ [source]
      let [winner] := winners
        | throw (IO.userError s!"of four links and four renames onto one name, {winners} succeeded")
      unless (← IO.FS.readFile target) == winner do
        throw (IO.userError s!"the name holds {← IO.FS.readFile target}, not {winner}'s ID")
      for (links, source) in sources do
        let kept ← (dir / source).pathExists
        unless kept == (links || source != winner) do
          throw (IO.userError s!"placing a name moved or kept {source} wrongly")

/-- What a daemon is once the exec of an upgrade succeeded, its id, its children and its kept
descriptors, from what they were before: the observation `Os.Exec.Keeps` constrains, which
`upgrade_keeps` rests on. It has no body; the check below observes it. -/
opaque upgraded : Nat → List Nat → List Nat → Nat × List Nat × List Nat

-- An exec keeps the process, its child and a kept descriptor: a shell that started a child and
-- holds the check's pipe at descriptor 3 alone execs a second shell, which reads the same process
-- id, finds the child's parent is still that process, and writes through descriptor 3 to the
-- pipe the check reads. The upgrade suite upgrades live sessions the same way.
Check Os.Exec.Keeps upgraded := do
  let script :=
    "sleep 30 >/dev/null 2>&1 & child=$!\n" ++ "exec 3>&1 1>/dev/null\n" ++
      "echo \"before $$ $child\" >&3\n" ++
      "exec /bin/sh -c 'echo \"after $$ $(ps -o ppid= -p \"$1\" | tr -d \" \")\" >&3; " ++
      "kill \"$1\"' sh \"$child\"\n"
  let out ← IO.Process.output { cmd := "/bin/sh", args := #["-c", script] }
  match (out.stdout.splitOn "\n").map (·.splitOn " ") with
  | ["before", pid, _] :: ["after", pid', parent] :: _ =>
    unless pid == pid' do
      throw (IO.userError s!"a shell that was process {pid} reads {pid'} once it has exec'd")
    unless parent == pid do
      throw (IO.userError s!"the child of process {pid} has parent {parent} once it has exec'd")
  | _ =>
    throw
        (IO.userError
          s!"the exec'd shell wrote nothing through the descriptor it kept: {out.stdout} {out.stderr}")

/-- Whether a process is in the process group of a session's program when its ending signals
the group: the membership `Os.Signal.Group` speaks of, which `ending_clean` rests on. It has no
body; the check below observes it. -/
opaque inProgramGroup : Nat → Nat → Bool

/-- Whether the signal a session's ending sends to its program's process group
(`Os.Shell.signalGroup`) reaches a process: the observation `Os.Signal.Group` constrains. It has no
body; the check below observes it. -/
opaque endingReaches : Nat → Nat → Bool

-- A session's ending reaches every process of its program's group: a program in a terminal session
-- and a process group of its own starts two jobs in its group, each of which, like the program,
-- notes the SIGHUP an ending sends first in a file of its own and keeps running; one signal to the
-- group, and each of the three notes it.
Check Os.Signal.Group inProgramGroup endingReaches := do
  IO.FS.withTempDir fun dir => do
      let first := Linger.Session.ending.head?.map (·.signal) |>.getD 1
      let note (who : String) := s!"trap ': > {dir}/{who}' HUP"
      let member (who : String) := s!"({note who}; while :; do sleep 0.05; done) &"
      let script :=
        s!"{member "first"} {member "second"} {note "program"}; " ++
          s!"ps -o pgid= -p $! > {dir}/group.part && mv {dir}/group.part {dir}/group; " ++
          "while :; do sleep 0.05; done"
      let (pid, master) ← spawnPty 80 24 "" "/bin/sh" #["-c", script] #[]
      try
        unless ← within ((← monotonicMs) + 10000) (System.FilePath.pathExists (dir / "group")) do
          refute "the program did not start its jobs"
        let pgid := (← IO.FS.readFile (dir / "group")).trimAscii.toString
        unless pgid == toString pid do
          refute s!"a job of the program {pid} is in the process group {pgid}"
        unless ← signalGroup pid first do
          refute s!"the program's process group {pid} had no process to signal"
        let noted : IO Bool := do
          return (← (dir / "program").pathExists) && (← (dir / "first").pathExists) &&
              (← (dir / "second").pathExists)
        unless ← within ((← monotonicMs) + 5000) noted do
          refute "a process of the program's group did not note the signal sent to the group"
      finally
        discard <| (signalGroup pid 9).toBaseIO
        stop pid master

end Linger.Session.Checks
