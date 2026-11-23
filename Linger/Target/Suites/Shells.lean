module

public import Verify.Harness
import Linger.App.CoreCode.Serve
import Linger.App.CoreCode.Json
import Linger.Target.WorldCode.Checks

public section

/-! # `linger serve` through every login shell here

SSH hands the command line `ssh -T host linger serve` gives it to the login shell of the remote
account, which runs it as `<shell> -c 'linger serve'`. This suite does the same with each shell
this host has, with a `linger` of its own that writes the words it is given and writes back every
byte it reads, and checks that each shell runs `linger` with exactly `serve` and carries every byte
either way (`Remote.Transport.Delivers`); then that this checkout's `linger`, run so, shakes hands
and answers a call, as a host's does. -/

namespace Linger.Target.Suites.Shells

open Verify.Harness
open Linger.Target.Checks (hostile echoLinger through)

/-- The first file called `name` in a directory of `path`. -/
def onPath (path name : String) : IO (Option String) := do
  for dir in path.splitOn ":" do
    if !dir.isEmpty && (← System.FilePath.pathExists s!"{dir}/{name}") then
      return some s!"{dir}/{name}"
  return none

/-- The shells suite: `linger serve` through each shell this host has, then the real binary
through one. -/
def run : IO UInt32 :=
  Env.suite "shells" fun e => do
    let root := System.FilePath.mk s!"{e.dir}/shells"
    let bin := root / "bin"
    IO.FS.createDirAll bin
    IO.FS.writeFile (bin / "linger") echoLinger
    Os.Shell.chmod (bin / "linger").toString 0o755
    let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
    let shells ←
      Linger.Target.Checks.shells.filterMapM fun name => do
          return (← onPath path name).map (name, ·)
    let names := String.intercalate " " (shells.map (·.1))
    let mut misnamed : List String := []
    let mut changed : List String := []
    for (name, shell) in shells do
      for bytes in hostile do
        let (wrote, given) ← through root bin [shell, "-c", "linger serve"] bytes
        unless given == ["serve"] do
          misnamed := misnamed ++ [s!"{name}: {repr given}"]
        unless wrote.toList == bytes do
          changed := changed ++ [s!"{name}: {bytes.length} bytes as {wrote.size}"]
    expect (!shells.isEmpty && misnamed.isEmpty)
        s!"each shell here runs linger with exactly serve ({names})\
          {if misnamed.isEmpty then "" else s!": not {misnamed.take 3}"}"
    expect (!shells.isEmpty && changed.isEmpty)
        s!"each shell here carries every byte either way ({names})\
          {if changed.isEmpty then "" else s!": {changed.take 3}"}"
    -- the real binary, through a shell, as a host's `serve`
    let far := root / "far"
    let real := root / "real"
    IO.FS.createDirAll far
    IO.FS.createDirAll real
    IO.FS.writeFile (real / "linger")
        s!"#!/bin/sh\nLINGER_DIR={shellQuote far.toString} exec {shellQuote e.bin} \"$@\"\n"
    Os.Shell.chmod (real / "linger").toString 0o755
    let (wrote, _) ←
      through root real ["sh", "-c", "linger serve"]
          (Linger.App.Serve.Remote.lines "sessions/list" (.obj [])).toUTF8.toList
    let messages :=
      ((String.fromUTF8? wrote).getD "").splitOn "\n" |>.filterMap Linger.App.Serve.Json.parse
    expect (Linger.App.Serve.Remote.heard messages 0 matches .answered .done _)
        "this linger, run as linger serve through a shell, shakes hands and answers sessions/list"

end Linger.Target.Suites.Shells
