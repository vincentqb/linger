module

public import Linger.Target.WorldSpec
import Linger.Target.CoreCode.Remote
import Os.WorldCode
meta import SoftwareChallenge.Attributes -- shake: keep

/-! # The checks of the remote commands' world claims

`Transport.Delivers` says that a transport runs `linger serve` there and carries every byte
either way exactly, or runs nothing. The claim takes the world's reading as a parameter, which no
Lean term computes, so its checks, tests marked `@[tests Remote.Transport.Delivers]`, observe it
through the transports that run linger here, with no host to reach, with a `linger` of the check's
own first on `PATH` that, given `serve` and nothing else, writes back every byte it reads, so that
the bytes come back exactly when the transport ran `linger serve` and carried them both ways. No
program module imports this one; `Verify.Checks` runs its tests. -/

namespace Linger.Target.Checks

/-- The shells an account may log in with. Each one this host has is tried, here and by the
shells suite. -/
public def shells : List String :=
  ["sh", "bash", "zsh", "fish", "dash", "ksh", "mksh", "yash", "posh", "tcsh", "csh"]

/-- Bytes a transport could change, drop, add or reorder: every byte value, in order and in
reverse, NUL, newlines, carriage returns, an escape, invalid UTF-8, a run longer than a pipe holds,
and the lines a handshake writes. -/
public def hostile : List (List UInt8) :=
  [(List.range 256).map UInt8.ofNat, ((List.range 256).map UInt8.ofNat).reverse, [0], [10, 13, 10],
    [27, 91, 50, 74], [195, 40, 255, 254],
    (List.range 300000).map fun i => UInt8.ofNat (i * 7 % 251),
    ("{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{}}\n" ++
        "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\"}\n").toUTF8.toList]

/-- A `linger` for the checks: it writes the words it is given to `$LINGER_ARGV`, and, given `serve`
and nothing else, writes back every byte it reads. -/
public def echoLinger : String :=
  "#!/bin/sh\nprintf '%s\\000' \"$@\" > \"$LINGER_ARGV\"\n" ++
    "if [ \"$#\" -eq 1 ] && [ \"$1\" = serve ]; then exec cat; fi\nexit 99\n"

/-- Run `argv` in `dir`, with `bin` first on `PATH` and a home of its own, writing `bytes` to its
standard input and then its end: what it wrote to its standard output, and the words the
check's `linger` was given. -/
public def through (dir bin : System.FilePath) (argv : List String) (bytes : List UInt8) :
    IO (ByteArray × List String) := do
  let argvFile := dir / "argv"
  if ← argvFile.pathExists then
    IO.FS.removeFile argvFile
  let some program := argv.head? | throw (IO.userError "a command names a program")
  let path := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
  let child0 ←
    IO.Process.spawn
        { cmd := program, args := argv.tail.toArray, cwd := some dir, stdin := .piped,
          stdout := .piped, stderr := .null,
          env :=
            #[("PATH", some s!"{bin}:{path}"), ("HOME", some dir.toString),
              ("XDG_CONFIG_HOME", some dir.toString), ("ZDOTDIR", some dir.toString), ("ENV", none),
              ("BASH_ENV", none), ("LINGER_ARGV", some argvFile.toString)] }
  let (input, child) ← child0.takeStdin
  let output ← IO.asTask child.stdout.readBinToEnd Task.Priority.dedicated
  let writing ←
    IO.asTask
        (do
          try
            input.write (ByteArray.mk bytes.toArray)
            input.flush
          catch _ =>
            pure ())
        Task.Priority.dedicated
  discard <| IO.wait writing
  let wrote ← IO.ofExcept (← IO.wait output)
  discard child.wait
  let given ←
    if ← argvFile.pathExists then
      pure (((← IO.FS.readFile argvFile).splitOn "\x00").dropLast)
    else
      pure []
  return (wrote, given)

/-- Run `transport`'s command, then `linger serve`, with `echoLinger` first on `PATH`, writing each
set of `hostile` bytes, and throw unless the `linger` was given exactly `serve` and every byte came
back as it went. -/
def carries (transport : Linger.Target.Remote.Transport) : IO Unit := do
  IO.FS.withTempDir fun dir => do
      let bin := dir / "bin"
      IO.FS.createDirAll bin
      IO.FS.writeFile (bin / "linger") echoLinger
      Os.Shell.chmod (bin / "linger").toString 0o755
      for bytes in hostile do
        let (wrote, given) ← through dir bin (Linger.Target.Remote.argv transport) bytes
        unless given == ["serve"] do
          throw (IO.userError s!"{transport.command} ran linger with {repr given}")
        unless wrote.toList == bytes do
          throw
              (IO.userError
                s!"{transport.command} carried {bytes.length} bytes as {wrote.size} other bytes")

/-- `env`, a command that runs its words here, runs `linger serve` and carries every byte either
way, as `docker exec -i` and `kubectl exec -i` do. -/
@[tests Remote.Transport.Delivers]
public def checkEnvDelivers : IO Unit := carries { command := ["env"] }

/-- A command shaped as ssh's is, which joins the words after it with spaces and hands the line to a
login shell, as sshd hands it to the remote account's: `sh -c 'exec sh -c "$*"'` runs `linger serve`
and carries every byte either way, as `ssh -T` does. -/
@[tests Remote.Transport.Delivers]
public def checkSshDelivers : IO Unit :=
  carries { command := ["sh", "-c", "exec sh -c \"$*\"", "ssh"] }

end Linger.Target.Checks
