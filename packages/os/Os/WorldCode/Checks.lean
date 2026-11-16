module

public import Os.WorldSpec
import Os.WorldCode
import SoftwareChallenge.Commands

/-! # The checks of the OS boundary's world claims

`Os.Wait.Lasts` says that a sleep lasts at least as long as it was asked to, `Os.Exec.Keeps`
that an exec keeps the process, its children and the descriptors it does not close,
`Os.Place.NoReplace` that a link or a rename that may not replace never replaces a name, and
`Os.Lock.Tells` that `fstat` and `stat` tell the file a descriptor holds from the one a path
names. Each claim takes the behaviour it constrains as a parameter, which no Lean term computes:
`slept`, `execd`, `placedBy` and `told` name them, and the checks observe them, by sleeping and
reading the monotonic clock around each sleep, by running a process that execs, by placing names
in a directory of their own, eight at once onto one, and by locking, deleting and creating lock
files. No program module imports this one. -/

namespace Os.Checks

/-- What the monotonic clock reads once a sleep of `ms` milliseconds, asked for when it read
`now`, returns: the observation `Os.Wait.Lasts` constrains. It has no body; the check below
observes it. -/
opaque slept : Nat → Nat → Nat

-- A sleep lasts at least as long as asked: around sleeps of 0, 1, 7 and 20 milliseconds, the
-- monotonic clock advances by at least as much.
Check Os.Wait.Lasts slept := do
  for ms in [0, 1, 7, 20] do
    let before ← IO.monoMsNow
    IO.sleep ms.toUInt32
    let after ← IO.monoMsNow
    unless before + ms ≤ after do
      throw (IO.userError s!"a sleep of {ms} ms returned {after - before} ms after it began")

/-- What a process is once an `execve` it made succeeded, its id, its children and its kept
descriptors, from what they were before: the observation `Os.Exec.Keeps` constrains. It has no
body; the check below observes it. -/
opaque execd : Nat → List Nat → List Nat → Nat × List Nat × List Nat

-- An exec keeps the process: a shell that started a child and holds the check's pipe at
-- descriptor 3 alone execs a second shell, which reads the same process id, finds the child's
-- parent is still that process, and writes through descriptor 3 to the pipe the check reads.
Check Os.Exec.Keeps execd := do
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

/-- What the names of a directory name once a link or a rename that may not replace placed one
name at another: the observation `Os.Place.NoReplace` constrains. It has no body; the check below
observes it. -/
opaque placedBy : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)

-- A name is never replaced: in a directory of its own, a link and a rename onto a name that names
-- a file both fail and leave both names as they were; onto a free name, a link leaves both names
-- naming the file and a rename only the new one; and of eight renames at once onto one free
-- name, from eight files, exactly one succeeds, and the name names that one's file.
Check Os.Place.NoReplace placedBy := do
  IO.FS.withTempDir fun dir => do
      let at_ (name : String) := (dir / name).toString
      let read (name : String) : IO (Option String) := do
        if ← (dir / name).pathExists then
          return some (← IO.FS.readFile (dir / name))
        return none
      IO.FS.writeFile (dir / "a") "a"
      IO.FS.writeFile (dir / "b") "b"
      for rename in [false, true] do
        let placed ←
          if rename then
            Os.Shell.renameNew (at_ "a") (at_ "b")
          else
            Os.Shell.linkNew (at_ "a") (at_ "b")
        unless !placed && (← read "a") == some "a" && (← read "b") == some "b" do
          throw
              (IO.userError
                s!"a {if rename then "rename" else "link"} onto a name that names a \
          file replaced it or moved its source")
      unless
        (← Os.Shell.linkNew (at_ "a") (at_ "c")) && (← read "a") == some "a" &&
          (← read "c") == some "a" do
        throw (IO.userError "a link onto a free name did not leave both names naming the file")
      unless
        (← Os.Shell.renameNew (at_ "c") (at_ "d")) && (← read "c") == none &&
          (← read "d") == some "a" do
        throw (IO.userError "a rename onto a free name did not move the name alone")
      let sources := (List.range 8).map fun i => s!"src{i}"
      for source in sources do
        IO.FS.writeFile (dir / source) source
      let tasks ←
        sources.mapM fun source =>
            IO.asTask (Os.Shell.renameNew (at_ source) (at_ "target")) Task.Priority.dedicated
      let mut winners := []
      for (source, task) in sources.zip tasks do
        if ← IO.ofExcept (← IO.wait task) then
          winners := winners ++ [source]
      match winners with
      | [winner] =>
        unless (← read "target") == some winner do
          throw
              (IO.userError
                s!"the name eight renames raced onto names {← read "target"}, \
          not the file of {winner}, whose rename alone succeeded")
      | _ =>
        throw (IO.userError s!"of eight renames at once onto one free name, {winners} succeeded")

/-- What `Os.Shell.namesHeld` answers of a descriptor that holds a file open and a path, when the
path names that file and when it names another or none: the observation `Os.Lock.Tells`
constrains. It has no body; the check below observes it. -/
opaque told : Bool → Bool

-- `fstat` and `stat` tell a held file from the one a path names, round after round: a locked file
-- the path names reads true; once its holder deleted it the path names none, and once another
-- file is created there, another, and both read false while the descriptor holds the first; the
-- path's new file, locked, reads true, and while it is held no second lock of the path is granted.
Check Os.Lock.Tells told := do
  let dir ← IO.FS.createTempDir
  try
    let path := (dir / "check.lock").toString
    for round in [0:16] do
      let first ← Os.Shell.flock path
      unless first ≥ 0 do
        throw (IO.userError s!"round {round}: a fresh lock file was not granted")
      let held := first.toUInt64.toUInt32
      try
        unless ← Os.Shell.namesHeld held path do
          throw (IO.userError s!"round {round}: a locked file the path names reads as another")
        Os.Shell.unlinkHeld held path
        if ← Os.Shell.namesHeld held path then
          throw (IO.userError s!"round {round}: a deleted lock file reads as the path's")
        let second ← Os.Shell.flock path
        unless second ≥ 0 do
          throw (IO.userError s!"round {round}: the path's new file was not granted")
        let fresh := second.toUInt64.toUInt32
        try
          if ← Os.Shell.namesHeld held path then
            throw
                (IO.userError
                  s!"round {round}: a file created after a delete reads as the held one")
          unless ← Os.Shell.namesHeld fresh path do
            throw (IO.userError s!"round {round}: the path's new file reads as another")
          let third ← Os.Shell.flock path
          if third ≥ 0 then
            Os.Shell.close third.toUInt64.toUInt32
            throw (IO.userError s!"round {round}: a second lock of a held path was granted")
        finally
          Os.Shell.unlinkHeld fresh path
          Os.Shell.close fresh
      finally
        Os.Shell.close held
  finally
    IO.FS.removeDirAll dir

end Os.Checks
