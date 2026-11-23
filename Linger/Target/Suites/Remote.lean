module

public import Verify.Harness
public import Linger.App.CoreSpec
import Linger.App.WorldCode
import Os.WorldCode.Command
import Linger.Target.CoreCode.Remote
import Linger.Session.WorldCode.Client
import Linger.Session.CoreCode.Checkpoint
import Linger.App.CoreCode.Api
import Linger.App.CoreCode.Json
import Terminal.CoreCode.Render
import Terminal.CoreCode.Vt

public section

/-! Remote hosts through `serve`. Every command on `name@host` runs `linger serve` on the host
through its transport and calls its request's method there, and `ls -r` lists each host through
its `serve`. The far linger is this checkout's binary under a state directory of its own: the
remotes file names a script that stands for a transport such as `docker exec`, and a fake `ssh` on
`PATH` hands its command line to `/bin/sh`, as sshd hands it to a login shell, where `linger` is
the far linger. A host whose linger does not speak `serve`, one whose `serve` sends hostile
records and one that cannot be reached are scripts too, and every check runs under a `HOME` of
the suite's own. -/

namespace Linger.Target.Suites.Remote

open Verify.Harness
open Os.Shell (chmod)

private def devHost : String := "dev-a"

private def deadHost : String := "dead"

private def evilHost : String := "evil"

private def userHost : String := s!"me@{devHost}"

private def goodName : String := "remote-work"

private def hostileName : String := "../../etc/passwd\x01"

/-- What linger runs after a host's command: `linger serve`, and nothing else. -/
private def served : List String := ["linger", "serve"]

/-- What a host whose linger does not speak `serve` is told, after its name. -/
private def withoutServe : String := "runs a linger without serve; install a current linger there"

private def dupMsg : String :=
  match Linger.Target.Remote.checkHosts [devHost, devHost] with
  | .error m => m
  | .ok _ => "checkHosts accepted a duplicate host"

/-- A fake ssh: it writes its words to `log`, then hands the command line after the host to
`/bin/sh`, as sshd hands it to the login shell of the account; the dead host answers nothing and
exits 255, and the evil host's `serve` is `evil`'s lines, whatever it is asked. -/
private def fakeSsh (log evil : String) : String :=
  "#!/bin/sh\n" ++ s!"printf '%s\\000' \"$@\" > {shellQuote log}\n" ++ "while [ $# -gt 0 ]; do\n" ++
    "  case \"$1\" in\n" ++
    "    -o) shift 2 ;;\n" ++
    "    -t|-T) shift ;;\n" ++
    "    --) shift; break ;;\n" ++
    "    *) break ;;\n" ++
    "  esac\n" ++
    "done\n" ++
    "host=\"$1\"; shift\n" ++
    s!"if [ \"$host\" = \"{deadHost}\" ]; then\n" ++
    "  printf '\\033]2;remote-lost\\007\\033]2;partial'\n" ++
    "  exit 255\n" ++
    "fi\n" ++
    s!"if [ \"$host\" = \"{evilHost}\" ]; then exec cat {shellQuote evil}; fi\n" ++
    "exec /bin/sh -c \"$*\"\n"

/-- The `linger` a fake ssh's shell finds: this checkout's binary under the far state directory. -/
private def farLinger (bin far : String) : String :=
  s!"#!/bin/sh\nLINGER_DIR={shellQuote far} exec {shellQuote bin} \"$@\"\n"

/-- A host's `serve` that answers the handshake and then lists a session whose command holds an
escape sequence and a session whose name holds a path and a control character. -/
private def evilLines : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"protocolVersion\":\"1\"}}\n" ++
    "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"answer\":\"done\",\"code\":0,\"records\":[" ++
    s!"\{\"name\":\"{goodName}\",\"state\":\"live\",\"clients\":\"1\",\"cmd\":\"vim\\u001b[31mINJECT\"}," ++
    "{\"name\":\"../../etc/passwd\\u0001\",\"state\":\"resumable\"}]}}\n"

/-- A transport for the checks: a script that writes the words it is given to `log`, then runs
them, `linger` first, as this checkout's `linger` under `state`, the state directory of a far
machine's linger. Words that do not start with `linger` are no command linger sends. -/
def fakeTransport (linger log state : String) : String :=
  "#!/bin/sh\n" ++ s!"printf '%s\\000' \"$@\" > {shellQuote log}\n" ++
    "[ \"$1\" = linger ] || exit 99\n" ++
    "shift\n" ++
    s!"LINGER_DIR={shellQuote state} exec {shellQuote linger} \"$@\"\n"

/-- A transport to a host whose linger is from before `serve`: it writes the words it is given to
`log`, and its linger answers `serve` as a command line it does not take, with usage, exit 2. -/
private def olderLinger (log : String) : String :=
  "#!/bin/sh\n" ++ s!"printf '%s\\000' \"$@\" > {shellQuote log}\n" ++
    "echo 'usage: linger <command>' >&2\n" ++
    "exit 2\n"

/-- One field of the row a porcelain listing names `name`: a `name` record opens a row, and
later keys belong to it until the next one. -/
private def rowField (recs : List (String × String)) (name field : String) : Option String :=
  ((((recs.dropWhile (· != ("name", name))).drop 1).takeWhile (·.1 != "name")).find?
        (·.1 == field)).map
    (·.2)

/-- NUL framing preserves empty arguments, embedded spaces and newlines. -/
def readArgs (path : System.FilePath) : IO (List String) := do
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    return if text.isEmpty then [] else (text.splitOn "\x00").dropLast
  return []

/-- A descendant keeps the SSH pipes open until its owner terminates the group. It outlives
every ceiling a discovery check waits under, so a command or stop that waited for the pipes
to close would outlast that ceiling however fast the host. -/
def discoveryLeaf (root host : String) : IO UInt32 := do
  IO.FS.writeFile s!"{root}/{host}.leaf.tmp" (toString (← Os.Shell.getpid))
  IO.FS.rename s!"{root}/{host}.leaf.tmp" s!"{root}/{host}.leaf"
  IO.sleep (2 * hangMs).toUInt32
  return 0

/-- What a host's `serve` writes for `ls -r` when it lists one session, `name`, running `cmd`: its
`initialize` result, then its `sessions/list` result, one JSON-RPC message a line. -/
def servedRows (name cmd : String) : String :=
  "{\"jsonrpc\":\"2.0\",\"id\":1,\"result\":{\"protocolVersion\":\"1\"}}\n" ++
    "{\"jsonrpc\":\"2.0\",\"id\":2,\"result\":{\"answer\":\"done\",\"code\":0,\"records\":" ++
    s!"[\{\"name\":\"{name}\",\"state\":\"live\",\"cmd\":\"{cmd}\"}]}}\n"

/-- Re-entered through a minimal fake SSH executable. The first host waits for
the second and a local info request, so serial discovery cannot pass. Stalled
hosts emit plausible rows but never complete before their group is cancelled. Each answers as a
host's `serve` does. -/
def discoverySsh (root : String) (args : List String) : IO UInt32 := do
  let some host := ((args.dropWhile (· != "--")).drop 1).head? | return 2
  IO.FS.writeFile s!"{root}/{host}.started" ""
  if host.startsWith "stall-" then
    let child ←
      IO.Process.spawn { cmd := (← IO.appPath).toString, args := #["--discovery-leaf", root, host] }
    IO.print (servedRows host "stalled")
    (← IO.getStdout).flush
    return ← child.wait
  if host == "first" then
    let started ←
      waitFor 5000 do
          return (← System.FilePath.pathExists s!"{root}/second.started") &&
              (← System.FilePath.pathExists s!"{root}/local.request")
    unless started do
      return 1
    IO.sleep 100
  IO.print (servedRows goodName host)
  return 0

/-- The local peer answers only after remote discovery has started. -/
def discoveryInfo (root : String) : IO UInt32 := do
  let listener ← Os.Shell.unixListen s!"{root}/state/local.sock"
  Os.Shell.setNonblock listener
  try
    IO.FS.writeFile s!"{root}/local.ready" ""
    let deadline := (← Os.Shell.monotonicMs) + 5000
    while (← Os.Shell.monotonicMs) < deadline do
      let accepted ← Os.Shell.accept listener
      if accepted < 0 then
        IO.sleep 10
        continue
      let fd := accepted.toUInt64.toUInt32
      try
        let ready ← Os.Shell.poll #[fd] #[Os.Shell.POLLIN] 2000
        if ready[0]! == 0 then
          return 1
        discard <| Os.Shell.read fd 4096
        IO.FS.writeFile s!"{root}/local.request" ""
        unless ← waitFor 5000 (System.FilePath.pathExists s!"{root}/first.started") do
          return 1
        Linger.Session.Shell.Client.sendMsg fd (.infoReply "cmd\tlocal-concurrent\n".toUTF8.toList)
        Linger.Session.Shell.Client.sendMsg fd .done
        return 0
      finally
        Os.Shell.close fd
    return 1
  finally
    Os.Shell.close listener

private def discoverySetup (e : Env) (slug : String) : IO (Env × String × String) := do
  let root := s!"{e.dir}/{slug}"
  let state := { e with dir := s!"{root}/state" }
  let bin := s!"{root}/bin"
  IO.FS.createDirAll state.dir
  IO.FS.createDirAll bin
  let self ← IO.appPath
  IO.FS.writeFile s!"{bin}/ssh"
      s!"#!/bin/sh\nexec {shellQuote self.toString} --discovery-ssh {shellQuote root} \"$@\"\n"
  chmod s!"{bin}/ssh" 0o755
  return (state, root, s!"{bin}:{(← IO.getEnv "PATH").getD "/usr/bin:/bin"}")

/-- A terminated descendant may briefly await the system reaper. -/
private def discoveryGone (root host : String) : IO Bool := do
  let path := s!"{root}/{host}.leaf"
  unless ← System.FilePath.pathExists path do
    return false
  let pid := (← IO.FS.readFile path).toNat?.getD 0
  return pid > 0 && !(← Os.Shell.alive (UInt32.ofNat pid))

/-- Retire fixture descendants even when intentionally breaking group cleanup. -/
private def cleanupDiscovery (root : String) : IO Unit := do
  for entry in ← (System.FilePath.mk root).readDir do
    if entry.fileName.endsWith ".leaf" then
      let host := (entry.fileName.dropEnd 5).toString
      unless ← discoveryGone root host do
        if let some pid := (← IO.FS.readFile entry.path).toNat? then
          try
            Os.Shell.kill (UInt32.ofNat pid) 15
          catch _ =>
            pure ()

private def discoveryChecks (e : Env) : IO Unit := do
  let (state, root, path) ← discoverySetup e "barrier"
  let server ←
    IO.Process.spawn
        { cmd := (← IO.appPath).toString, args := #["--discovery-info", root], stdout := .null,
          stderr := .null }
  try
    unless ← waitFor 5000 (System.FilePath.pathExists s!"{root}/local.ready") do
      throw (IO.userError "discovery info server did not start")
    let (code, output, _) ←
      state.cliEnv #[("PATH", some path)] #["ls", "--porcelain", "-r", "first,second"]
    let fields := records output
    expect (code == 0 && fields.contains ("cmd", "local-concurrent"))
        "local queries overlap remote discovery"
    expect
        (fields.filter (·.1 == "name") ==
          [("name", "local"), ("name", s!"{goodName}@first"), ("name", s!"{goodName}@second")])
        "SSH queries overlap and retain host order despite reversed completion"
  finally
    reapOrKill server 0
  let (state, root, path) ← discoverySetup e "deadline"
  let limit := Linger.App.Api.remoteQueryLimit
  let hosts := (List.range (limit + 1)).map (fun i => s!"stall-{i}")
  let active := hosts.take limit
  let start ← Os.Shell.monotonicMs
  let command ←
    IO.Process.spawn
        { cmd := e.bin,
          args := #["ls", "--porcelain", "-r", String.intercalate "," ("quick" :: hosts)],
          env := state.procEnv ++ #[("PATH", some path)], stdout := .piped, stderr := .null }
  try
    let last := s!"{root}/{hosts.getLast!}.started"
    let ready ←
      waitFor patienceMs do
          active.allM fun host => System.FilePath.pathExists s!"{root}/{host}.leaf"
    expect (ready && !(← System.FilePath.pathExists last))
        "remote discovery limits simultaneous SSH jobs and reuses completed slots"
    -- The stalled hosts hold every slot until the deadline, so with one deadline for all of them
    -- the last host never starts, while a deadline per job would free a slot for it; and their
    -- descendants outlive `hangMs`, so a command that waited for the pipes would too.
    let code ← waitProcess command (Linger.App.Api.remoteQueryTimeoutMs + hangMs)
    let elapsed := (← Os.Shell.monotonicMs) - start
    let lastStarted ← System.FilePath.pathExists last
    let stopped ← waitFor patienceMs (active.allM (discoveryGone root))
    if code.isNone then
      cleanupDiscovery root
      command.kill
      discard command.wait
    let output ← command.stdout.readToEnd
    expect (code == some 0 && !lastStarted)
        s!"remote commands share one deadline even when pipes stay open ({elapsed} ms)"
    expect ((records output).filter (·.1 == "name") == [("name", s!"{goodName}@quick")])
        "only complete remote replies contribute rows"
    expect (ready && stopped) "deadline retires every SSH descendant holding a pipe"
  finally
    cleanupDiscovery root
  let root := s!"{e.dir}/stop"
  IO.FS.createDirAll root
  let pending ←
    IO.mkRef
        (some
          (←
            Os.Shell.Command.start (← IO.appPath).toString
                #["--discovery-ssh", root, "--", "stall-stop"]))
  try
    let ready ← waitFor patienceMs (System.FilePath.pathExists s!"{root}/stall-stop.leaf")
    let start ← Os.Shell.monotonicMs
    -- the leaf holds the pipes past `hangMs`, so a stop that waited for them would too
    Os.Shell.Command.stop pending 100
    let elapsed := (← Os.Shell.monotonicMs) - start
    let stopped ← waitFor patienceMs (discoveryGone root "stall-stop")
    expect (ready && stopped && elapsed < hangMs && (← pending.get).isNone)
        s!"cooperative stop force-retires descendants that retain pipes after their leader exits ({elapsed} ms)"
  finally
    Os.Shell.Command.stop pending
    cleanupDiscovery root
  -- Once its pipes close, the leader is an unreaped zombie until stop reaps it; Darwin's
  -- killpg refuses a group whose only member is that zombie.
  let exited ← IO.mkRef (some (← Os.Shell.Command.start "/bin/sh" #["-c", "exit 0"]))
  let finished ←
    waitFor patienceMs do
        let some job ← exited.get | return false
        return (← IO.hasFinished job.stdout) && (← IO.hasFinished job.stderr)
  let outcome ← (Os.Shell.Command.stop exited).toBaseIO
  if let .error err := outcome then
    IO.eprintln s!"remote: stopping an exited job failed: {err}"
  expect (finished && outcome matches .ok _) "stopping a job whose leader already exited succeeds"
  let (state, root, path) ← discoverySetup e "cancel"
  IO.FS.createDirAll s!"{root}/.config/linger"
  IO.FS.writeFile s!"{root}/.config/linger/remotes" "stall-cancel\n"
  -- A chooser that waited for its listing instead of cancelling it would end only at the
  -- listing's shared deadline, which starts after the chooser does: so the chooser must end
  -- within that deadline of its own start. That deadline caps the regression, so it is the
  -- bound; the host would have to stretch the chooser's start and cancellation to the remote
  -- deadline itself, which would leave its remote discovery nothing to show either. The leaf
  -- outlives `hangMs`, so a cancellation that left it running is seen below.
  let spawned ← Os.Shell.monotonicMs
  let chooser ← state.spawnEnv #[s!"PATH={path}", s!"HOME={root}"] #["attach"]
  try
    let ready ← waitFor patienceMs (System.FilePath.pathExists s!"{root}/stall-cancel.leaf")
    chooser.type "\x03"
    let code ← chooser.reap patienceMs
    let lived := (← Os.Shell.monotonicMs) - spawned
    expect (ready && code == 130 && lived < Linger.App.Api.remoteQueryTimeoutMs)
        s!"cancelling bare attach retires discovery before the remote deadline ({lived} ms)"
    let stopped ← waitFor patienceMs (discoveryGone root "stall-cancel")
    expect (ready && stopped) "chooser cancellation reaches SSH descendants"
  finally
    cleanupDiscovery root
    chooser.bye (sendDetach := false)
  -- A signal that stops `ls -r` while a host stalls retires its transports' groups, and then the
  -- signal ends the listing, as it ends a program that does not catch it, so its caller sees the
  -- signal itself.
  let (state, root, path) ← discoverySetup e "signal"
  let listing ←
    IO.Process.spawn
        { cmd := e.bin, args := #["ls", "--porcelain", "-r", "stall-signal"],
          env := state.procEnv ++ #[("PATH", some path)], stdin := .null, stdout := .null,
          stderr := .null }
  try
    let ready ← waitFor patienceMs (System.FilePath.pathExists s!"{root}/stall-signal.leaf")
    Os.Shell.kill listing.pid 15
    let ended ← endingOf listing.pid patienceMs
    let stopped ← waitFor patienceMs (discoveryGone root "stall-signal")
    expect (ready && ended == some (.signaled 15) && stopped)
        s!"SIGTERM to ls -r retires its SSH descendants and then ends it ({repr ended})"
  finally
    cleanupDiscovery root
    reapOrKill listing 0

/-- The discovery checks alone, as `suites remote discovery` runs them. -/
def runDiscovery : IO UInt32 := Env.suite "discovery" discoveryChecks

/-- What the suite's hosts need: the local and far namespaces, the environment that finds the fake
ssh and the suite's `HOME`, as pairs for a command and as `K=V` for a terminal, and the logs of
the fake ssh, the far host's transport and the older host's. -/
private structure Hosts where
  /-- The far linger's namespace. -/
  far : Env
  /-- `PATH` and `HOME` for a command. -/
  procPath : Array (String × Option String)
  /-- `PATH` and `HOME` for a terminal client. -/
  ptyPath : Array String
  /-- What the fake ssh was last given. -/
  sshLog : System.FilePath
  /-- What the far host's transport was last given. -/
  queryLog : System.FilePath
  /-- What the older host's transport was last given. -/
  olderLog : System.FilePath

/-- Run `args` here, the far host's transport log emptied first: its status, its output, its
error output, and whether the transport ran `linger serve` and nothing else. -/
private def Hosts.viaServe (h : Hosts) (e : Env) (args : Array String) :
    IO (UInt32 × String × String × Bool) := do
  IO.FS.writeFile h.queryLog ""
  let (rc, out, err) ← e.cliEnv h.procPath args
  return (rc, out, err, (← readArgs h.queryLog) == served)

/-- `ls -r`: each host's rows through its `serve`, an unreachable host and one whose linger does not
speak `serve` as `?`, and what a hostile `serve` lists dropped or scrubbed. -/
private def listingChecks (e : Env) (h : Hosts) : IO Unit := do
  let (drc, _, derr) ← e.cliEnv h.procPath #["ls", "-r", s!"{devHost},{devHost}"]
  expect (drc != 0 && has derr dupMsg) "duplicate remote host errors loudly"
  let (rrc, out, _) ← e.cliEnv h.procPath #["ls", "-r", s!"{devHost},{deadHost}"]
  let (_, pout, _) ← e.cliEnv h.procPath #["ls", "--porcelain", "-r", s!"{devHost},{deadHost}"]
  let recs := records pout
  let status ← h.far.field "alpha" "status"
  expect (rrc == 0 && has out "localsess" && has out s!"alpha@{devHost}")
      "remote listing exits cleanly, local sessions alongside the remote ones"
  expect (status.isSome && rowField recs s!"alpha@{devHost}" "status" == status)
      "a host's session is listed as name@host, with the status its linger reports"
  expect
      (has out s!"? @{deadHost}" && has pout s!"host\t{deadHost}\nstatus\tunknown\n" &&
        !recs.any (fun kv => kv.1 == "name" && kv.2.endsWith s!"@{deadHost}"))
      "an unreachable host lists as ?, with no session rows"
  IO.FS.writeFile h.sshLog ""
  let (_, _, _) ← e.cliEnv h.procPath #["ls", "--porcelain", "-r", devHost]
  expect ((← readArgs h.sshLog) == ["-T", "--", devHost] ++ served)
      "ls -r runs linger serve on a host the remotes file does not name through ssh -T"
  let (_, eout, _) ← e.cliEnv h.procPath #["ls", "-r", evilHost]
  let (_, epout, _) ← e.cliEnv h.procPath #["ls", "--porcelain", "-r", evilHost]
  let erecs := records epout
  expect
      (!has eout "/etc/passwd" &&
        erecs.filter (·.1 == "name") ==
          [("name", "localsess"), ("name", s!"{goodName}@{evilHost}")])
      "invalid remote names are dropped without manufacturing another target"
  expect
      (!has eout "\x1b" && rowField erecs s!"{goodName}@{evilHost}" "cmd" == some "vim[31mINJECT")
      "remote display escape sequences are scrubbed"
  IO.FS.writeFile h.olderLog ""
  let (orc, oout, oerr) ← e.cliEnv h.procPath #["ls", "-r", "old"]
  let (_, opout, _) ← e.cliEnv h.procPath #["ls", "--porcelain", "-r", "old"]
  expect
      (orc == 0 && has oout "? @old" && has opout "host\told\n" &&
        has opout s!"reason\told {withoutServe}\n" &&
        has oerr s!"old {withoutServe}" &&
        (← readArgs h.olderLog) == served)
      "a host whose linger does not speak serve lists as ?, its porcelain row saying why"

/-- Every command on `name@far` runs `serve` there and answers as the far linger does. -/
private def verbChecks (e : Env) (h : Hosts) : IO Unit := do
  let (startRc, _, _, startServed) ← h.viaServe e #["start", "work@far", "/bin/sh"]
  let started ← waitFor patienceMs (return (← h.far.field "work" "status").isSome)
  expect (startRc == 0 && startServed && started)
      "start name@host starts the session on its host through its serve"
  let (sendRc, _, _, sendServed) ← h.viaServe e #["send", "work@far", "echo SENT-$((6*7))\r"]
  let screen ← IO.mkRef ""
  let captured ←
    waitFor patienceMs do
        let (_, shown, _) ← e.cliEnv h.procPath #["capture", "work@far"]
        screen.set shown
        return has shown "SENT-42"
  let (_, _, _, captureServed) ← h.viaServe e #["capture", "work@far"]
  expect (sendRc == 0 && sendServed && captured && captureServed)
      "send name@host types into the far session, and capture name@host shows its screen"
  let (historyRc, history, _, historyServed) ← h.viaServe e #["capture", "--history", "work@far"]
  expect (historyRc == 0 && historyServed && has history "SENT-42")
      "capture --history name@host shows the far session's history"
  let (listRc, listed, _, listServed) ← h.viaServe e #["ls", "work@far", "--porcelain"]
  let cmd ← h.far.field "work" "cmd"
  let (humanRc, human, _) ← e.cliEnv h.procPath #["ls", "work@far"]
  expect
      (listRc == 0 && listServed && cmd.isSome &&
        rowField (records listed) "work@far" "cmd" == cmd &&
        humanRc == 0 &&
        has human "work@far")
      "ls name@host gives the far session's record, named name@host"
  let (resizeRc, _, _, resizeServed) ← h.viaServe e #["resize", "work@far", "120", "40"]
  let sized ←
    waitFor patienceMs do
        return (← h.far.info "work" "cols") == some "120" &&
            (← h.far.info "work" "rows") == some "40"
  expect (resizeRc == 0 && resizeServed && sized) "resize name@host sizes the far session"
  let (renameRc, _, _, renameServed) ← h.viaServe e #["rename", "work@far", "moved"]
  let renamed ← h.far.field "moved" "status"
  let old ← h.far.field "work" "status"
  expect (renameRc == 0 && renameServed && renamed.isSome && old.isNone)
      "rename name@host renames the far session"
  let (detachRc, _, _, detachServed) ← h.viaServe e #["detach", "moved@far"]
  let runs ← h.far.field "moved" "status"
  expect (detachRc == 0 && detachServed && runs.isSome)
      "detach name@host detaches the far session's clients, the session running on"
  let (upgradeRc, upgraded, _, upgradeServed) ← h.viaServe e #["upgrade", "moved@far"]
  expect (upgradeRc == 0 && upgradeServed && has upgraded "upgraded moved@far")
      s!"upgrade name@host carries the far session over, and says so as name@host ({upgradeRc})"
  let (endsRc, _, _) ←
    e.cliEnv h.procPath #["start", "ends@far", "/bin/sh", "-c", "sleep 1; exit 7"]
  let (waitRc, _, _, waitServed) ← h.viaServe e #["wait", "ends@far"]
  expect (endsRc == 0 && waitRc == 7 && waitServed)
      s!"wait name@host answers as the far program ended ({waitRc})"
  IO.FS.writeBinFile s!"{h.far.dir}/rs.ckpt"
      (Linger.Session.Checkpoint.saveBytes ⟨Terminal.Vt.Vt.init 40 5, h.far.dir, []⟩)
  let (resumeRc, _, _, resumeServed) ← h.viaServe e #["resume", "rs@far"]
  let resumed ← waitFor patienceMs (return (← h.far.info "rs" "pid").isSome)
  expect (resumeRc == 0 && resumeServed && resumed) "resume name@host resumes the far saved session"
  let (killRc, _, _, killServed) ← h.viaServe e #["kill", "moved@far"]
  let gone ← waitFor patienceMs (return (← h.far.field "moved" "status").isNone)
  expect (killRc == 0 && killServed && gone) "kill name@host ends the far session"
  let (missingRc, _, missingErr, missingServed) ← h.viaServe e #["kill", "nosuch@far"]
  expect
      (missingRc == 127 && missingServed && has missingErr "linger: far: " &&
        has missingErr "nosuch")
      s!"a far linger's answer is the command's, and what it said is said as its host's ({missingRc})"
  let sink := s!"{e.dir}/sink"
  let ready := s!"{e.dir}/sink.ready"
  let payload := ByteArray.mk #[0, 3, 10, 27, 127, 195, 169, 255]
  let (sinkRc, _, _) ←
    e.cliEnv h.procPath
        #["start", "sink@far", "/bin/sh", "-c",
          s!"stty raw -echo && : > {shellQuote ready} && exec head -c {payload.size} > {shellQuote sink}"]
  let armed ← waitFor patienceMs (System.FilePath.pathExists ready)
  IO.FS.writeFile h.queryLog ""
  let sender0 ←
    IO.Process.spawn
        { cmd := e.bin, args := #["send", "sink@far", "-"], env := e.procEnv ++ h.procPath,
          stdin := .piped, stdout := .null, stderr := .inherit }
  let sender ←
    do
      let (input, child) ← sender0.takeStdin
      input.write payload
      input.flush
      pure child
  let senderRc ← waitOrKill sender hangMs
  let arrived ←
    waitFor patienceMs do
        return ((← (IO.FS.readBinFile sink).toBaseIO).toOption.map (·.toList)) ==
            some payload.toList
  expect
      (sinkRc == 0 && armed && senderRc == some 0 && arrived && (← readArgs h.queryLog) == served)
      "send name@host - delivers standard input byte-exact, NUL and invalid UTF-8 included"
  h.far.killAll #["ends", "rs", "sink"]

/-- An attach on `name@host` is the local attach client, its daemon the host's `session/attach`. -/
private def attachChecks (e : Env) (h : Hosts) : IO Unit := do
  let (termRc, _, _) ← e.cliEnv h.procPath #["start", "term@far", "/bin/sh"]
  IO.FS.writeFile h.queryLog ""
  let c ← e.spawnEnv h.ptyPath #["attach", "term@far"] 100 24
  let acc ← IO.mkRef ByteArray.empty
  let prompted ← c.awaitText acc (fun out => hasText out "$ ")
  c.type "echo TRANSPORT-$((40+2))\r"
  let answered ← c.awaitText acc (fun out => hasText out "TRANSPORT-42")
  c.type "printf '\\033]2;remote-editor\\007'\r"
  let titled ←
    c.awaitText acc fun out =>
        let title := ((Terminal.Vt.Vt.init 100 24).feed out.toList).windowTitle
        has title "term@far" && has title "remote-editor"
  c.detach
  let attachRc ← c.reap patienceMs
  let shown := (← acc.get) ++ (← drain c.fd hangMs)
  c.bye (sendDetach := false)
  let live ← h.far.field "term" "status"
  let clients ← h.far.field "term" "clients"
  expect (termRc == 0 && prompted && answered && (← readArgs h.queryLog) == served)
      "an attach on name@host types into the far session and shows its output, through its serve"
  expect titled "a remote attach's title names name@host and the far program's title"
  expect (attachRc == 0 && live.isSome && clients != some "1")
      s!"the detach key leaves a remote attach, the far session running ({attachRc})"
  expect
      (hasBytes shown Terminal.Render.leaveAnsi &&
        ((Terminal.Vt.Vt.init 100 24).feed shown.toList).windowTitle.isEmpty)
      "a remote attach hands the terminal back and clears the title"
  let w ← e.spawnEnv h.ptyPath #["attach", "--read-only", "term@far"] 100 24
  let wacc ← IO.mkRef ByteArray.empty
  let painted ← w.awaitText wacc (fun out => hasText out "TRANSPORT-42")
  let (roRc, _, _) ← e.cliEnv h.procPath #["send", "term@far", "echo RO-$((2*3))\r"]
  let watched ← w.awaitText wacc (fun out => hasText out "RO-6")
  w.type "echo TYPED-$((3*3))\r"
  -- what the session prints after the keys were typed shows whether they reached it
  let (doneRc, _, _) ← e.cliEnv h.procPath #["send", "term@far", "echo DONE-$((1+1))\r"]
  let done ← w.awaitText wacc (fun out => hasText out "DONE-2")
  w.detach
  let watchRc ← w.reap patienceMs
  w.bye (sendDetach := false)
  let (_, screen, _) ← e.cliEnv h.procPath #["capture", "term@far"]
  expect
      (painted && roRc == 0 && watched && doneRc == 0 && done && watchRc == 0 &&
        !has screen "TYPED-9")
      "a read-only attach on name@host shows the far session and types nothing into it"
  let k ←
    e.spawnEnv h.ptyPath
        #["attach", "made@far", "/bin/sh", "-c", "printf '%s|%s|\\n' \"$1\" \"$2\"; exec sleep 600",
          "sh", "two words", "a'b\"c"]
        100 24
  let kacc ← IO.mkRef ByteArray.empty
  let made ← k.awaitText kacc (fun out => hasText out "two words|a'b\"c|")
  k.detach
  let madeRc ← k.reap patienceMs
  k.bye (sendDetach := false)
  expect (made && madeRc == 0)
      "an attach on name@host that starts the session runs exactly its command's words"
  IO.FS.writeFile h.sshLog ""
  let s ← e.spawnEnv h.ptyPath #["attach", s!"term@{devHost}"] 100 24
  let sacc ← IO.mkRef ByteArray.empty
  let sshShown ← s.awaitText sacc (fun out => hasText out "RO-6")
  s.detach
  let sshRc ← s.reap patienceMs
  s.bye (sendDetach := false)
  expect (sshShown && sshRc == 0 && (← readArgs h.sshLog) == ["-T", "--", devHost] ++ served)
      "an attach through ssh runs ssh -T, with no terminal at the far end"
  IO.FS.writeFile h.sshLog ""
  let u ← e.spawnEnv h.ptyPath #["attach", s!"term@{userHost}"] 100 24
  let uacc ← IO.mkRef ByteArray.empty
  let userShown ← u.awaitText uacc (fun out => hasText out "RO-6")
  u.detach
  let _ ← u.reap patienceMs
  u.bye (sendDetach := false)
  expect (userShown && (← readArgs h.sshLog) == ["-T", "--", userHost] ++ served)
      "user@host round-trips through the first-at split"
  let lost ← e.spawnEnv h.ptyPath #["attach", s!"x@{deadHost}"] 100 24
  let lostBytes ← drain lost.fd hangMs
  let lostRc ← lost.reap patienceMs
  lost.bye (sendDetach := false)
  expect (lostRc == 1 && !hasText lostBytes "remote-lost")
      s!"an attach to a host that does not answer is refused, and nothing its transport wrote reaches the terminal ({lostRc})"
  let o ← e.spawnEnv h.ptyPath #["attach", "--", "--read-only@far"] 100 24
  let oacc ← IO.mkRef ByteArray.empty
  let optionPrompt ← o.awaitText oacc (fun out => hasText out "$ ")
  o.detach
  let optionRc ← o.reap patienceMs
  o.bye (sendDetach := false)
  let optionLive ← h.far.field "--read-only" "status"
  expect (optionPrompt && optionRc == 0 && optionLive.isSome)
      "a remote attach separates options from an option-like session name"
  for args in [#["attach", "term@far"], #["attach", "--read-only", "term@far"]] do
    IO.FS.writeFile h.queryLog ""
    let (rc, _, _) ← e.cliEnv h.procPath args
    expect (rc != 0 && (← readArgs h.queryLog).isEmpty)
        s!"remote {repr args} requires terminal input and output"
  h.far.killAll #["term", "made", "--read-only"]

/-- The bytes the `session/output` updates among `lines` carry, in order. -/
private def outputOf (lines : Array String) : ByteArray :=
  lines.foldl
    (fun acc line =>
      match Linger.App.Serve.Json.parse line with
      | some message =>
        if (message.member? "method").bind Linger.App.Serve.Json.text? == some "session/output" then
          match
            (((message.member? "params").bind (·.member? "data")).bind
                  Linger.App.Serve.Json.text?).bind
              (Linger.App.Serve.Base64.decode ·.toList) with
          | some bytes => acc ++ ByteArray.mk bytes.toArray
          | none => acc
        else acc
      | none => acc)
    ByteArray.empty

/-- `serve` reaches a remote session as the command line does: its `session/attach` of
`name@host` converses with the host's `session/attach`, keys in, output out, and a detach. -/
private def serveChecks (e : Env) (h : Hosts) : IO Unit := do
  let (startRc, _, _) ← e.cliEnv h.procPath #["start", "served@far", "/bin/sh"]
  let child0 ←
    IO.Process.spawn
        { cmd := e.bin, args := #["serve"], env := e.procEnv ++ h.procPath, stdin := .piped,
          stdout := .piped, stderr := .null }
  let (handle, child) ← child0.takeStdin
  let input ← IO.mkRef (some handle)
  let lines ← IO.mkRef (#[] : Array String)
  let out := child.stdout
  let reader ←
    IO.asTask
        (do
          let mut reading := true
          while reading do
            let line ← out.getLine
            if line.isEmpty then
              reading := false
            else
              lines.modify (·.push line))
        Task.Priority.dedicated
  let say (line : String) : IO Unit := do
    if let some handle← input.get then
      handle.putStr (line ++ "\n")
      handle.flush
  let sees (text : String) : IO Bool :=
    waitFor patienceMs (return hasText (outputOf (← lines.get)) text)
  try
    say
        "{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"initialize\",\"params\":{\"protocolVersion\":\"1\"}}"
    say "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":{}}"
    say
        "{\"jsonrpc\":\"2.0\",\"id\":2,\"method\":\"session/attach\",\"params\":{\"name\":\"served@far\"}}"
    say
        "{\"jsonrpc\":\"2.0\",\"id\":3,\"method\":\"session/resize\",\"params\":{\"subscription\":2,\"cols\":80,\"rows\":24}}"
    let prompted ← sees "$ "
    say
        s!"\{\"jsonrpc\":\"2.0\",\"id\":4,\"method\":\"session/input\",\"params\":\{\"subscription\":2,\"data\":\"{Linger.App.Serve.Base64.encode "echo SERVED-$((5*5))\r".toUTF8.toList}\"}}"
    let typed ← sees "SERVED-25"
    say
        "{\"jsonrpc\":\"2.0\",\"id\":5,\"method\":\"session/detach\",\"params\":{\"subscription\":2}}"
    let detached ←
      waitFor patienceMs do
          return (← lines.get).any fun line => has line "\"id\":5" && has line "\"done\""
    let live ← h.far.field "served" "status"
    -- `serve` reads its input's end once nothing holds the handle, and ends once its attach let go
    input.set none
    let exited ← waitOrKill child patienceMs
    expect (startRc == 0 && prompted && typed && detached && live.isSome && exited == some 0)
        s!"serve attaches to a session on a host as the command line does, through its host's serve, and ends when its input does ({exited})"
  finally
    input.set none
    -- a child the check already reaped counts as finished
    reapOrKill child hangMs
    discard <| IO.wait reader
    h.far.killAll #["served"]

/-- What is refused before anything runs on a host, or by the host. -/
private def refusalChecks (e : Env) (h : Hosts) : IO Unit := do
  IO.FS.writeFile h.olderLog ""
  let (killRc, _, killErr) ← e.cliEnv h.procPath #["kill", "x@old"]
  expect
      (killRc == 1 && has killErr s!"linger: old {withoutServe}" &&
        (← readArgs h.olderLog) == served)
      s!"a command on a host whose linger does not speak serve is refused, saying so ({killRc})"
  let a ← e.spawnEnv h.ptyPath #["attach", "x@old"] 100 24
  let reply ← drain a.fd hangMs
  let attachRc ← a.reap patienceMs
  a.bye (sendDetach := false)
  expect (attachRc == 1 && hasText reply withoutServe)
      s!"an attach on a host whose linger does not speak serve is refused, saying so ({attachRc})"
  for name in
    ["work@", hostileName ++ "@" ++ devHost, "work\x01;printf REMOTE-INJECTED@" ++ devHost,
      "work\x01$(printf REMOTE-INJECTED)@" ++ devHost, "work\x01 'two words'@" ++ devHost,
      "work\nprintf REMOTE-INJECTED@" ++ devHost] do
    IO.FS.writeFile h.sshLog ""
    let c ← e.spawnEnv h.ptyPath #["attach", name] 100 24
    let reply ← drain c.fd hangMs
    expect
        ((← c.reap patienceMs) == 2 && (← readArgs h.sshLog).isEmpty &&
          hasText reply "invalid session name")
        s!"invalid remote target is rejected before SSH: {repr name}"
    c.bye (sendDetach := false)
  let tag := s!"{goodName}@{devHost}"
  for args in
    [#["resize", tag, "0", "40"], #["set", tag, "x=ok", "=bad"], #["unset", tag, ""],
      #["wait", tag, "-bad name"], #["run", tag], #["send", tag],
      #["attach", "--read-only", tag, "sh"], #["capture", tag, "--history"]] do
    IO.FS.writeFile h.sshLog ""
    let (rc, _, _) ← e.cliEnv h.procPath args
    expect (rc == 2 && (← readArgs h.sshLog).isEmpty)
        s!"invalid arguments have no remote effects: {repr args}"

/-- The remotes file: each line a host and the command that runs linger there, its words never
quoted, and a line with no one meaning refused before any command runs. -/
private def fileChecks (e : Env) (h : Hosts) (remotes : System.FilePath) (query : String)
    (configured : String) : IO Unit := do
  -- a listing waits for each host a bounded time, then shows what it missed
  let listing ←
    IO.Process.spawn
        { cmd := e.bin, args := #["ls", "-r"], env := e.procEnv ++ h.procPath, stdout := .piped,
          stderr := .null }
  let printed ← IO.asTask listing.stdout.readToEnd Task.Priority.dedicated
  let code ← waitOrKill listing (Linger.App.Api.remoteQueryTimeoutMs + hangMs)
  let human ←
    if code.isSome then
      pure ((← IO.wait printed).toOption.getD "")
    else
      pure ""
  let (_, porcelain, _) ← e.cliEnv h.procPath #["ls", "--porcelain", "-r"]
  let stallPid := (System.FilePath.mk e.dir) / "transport" / "stall.pid"
  let retired ←
    match (← readText stallPid).trimAscii.toString.toNat? with
    | some pid =>
      waitFor patienceMs (return !(← Os.Shell.alive (UInt32.ofNat pid)))
    | none =>
      pure false
  expect
      (code == some 0 && has human "? @slow" && has human "? @down" &&
        has porcelain "host\tslow\nstatus\tunknown\n" &&
        has porcelain "host\tdown\nstatus\tunknown\n" &&
        has human "alpha@far" &&
        !(records porcelain).any
            (fun kv => kv.1 == "name" && (kv.2.endsWith "@slow" || kv.2.endsWith "@down")) &&
        retired)
      "a host whose command does not answer within the bounded wait lists as ?, and its command is retired"
  IO.FS.writeFile remotes s!"far {query} | extra\n"
  IO.FS.writeFile h.queryLog ""
  let (_, piped, _) ← e.cliEnv h.procPath #["ls", "--porcelain", "-r"]
  expect ((← readArgs h.queryLog) == ["|", "extra"] ++ served && has piped "host\tfar\n")
      "a remotes line's command is every word after its host, a | among them"
  for (shape, bad) in
    [("HOST COMMAND, then HOST COMMAND", s!"far {query}\nfar {query}"),
      ("a control character in a word", s!"far {query} \x01")] do
    IO.FS.writeFile remotes (bad ++ "\n")
    IO.FS.writeFile h.queryLog ""
    let (listRc, _, listErr) ← e.cliEnv h.procPath #["ls", "-r"]
    let (infoRc, _, infoErr) ← e.cliEnv h.procPath #["ls", "alpha@far", "--porcelain"]
    expect
        (listRc != 0 && has listErr "far" && infoRc != 0 && has infoErr "far" &&
          (← readArgs h.queryLog).isEmpty)
        s!"a remotes file with no one meaning is refused before any command runs: {shape}"
  IO.FS.writeFile remotes configured

/-- Only a nonempty HOME configures hosts, and `ls` reads its options in either order. -/
private def homeChecks (e : Env) (h : Hosts) : IO Unit := do
  expect
      ([["--porcelain", "-r", s!"{devHost},{deadHost}"],
            ["-r", s!"{devHost},{deadHost}", "--porcelain"]].all
        (fun args => Linger.App.Api.parseLs args == some (true, some [devHost, deadHost], [])))
      "ls accepts explicit hosts in either option order"
  expect
      (Linger.App.Api.parseLs ["-r", "--porcelain"] == some (true, some [], []) &&
        Linger.App.Api.parseLs ["--porcelain", "--remote"] == none &&
        Linger.App.Api.parseLs ["--remote", devHost] == none &&
        Linger.App.Api.parseLs ["work", "-r"] == none &&
        Linger.App.Api.parseLs ["-r", "--typo"] == none)
      "ls preserves options after -r, spells -r one way, takes no names with it and rejects unknown options"
  -- Only a nonempty HOME configures hosts (`remotesFile_eq_none_iff`). Decoy files
  -- under the working, XDG and temporary directories would run SSH if a fallback
  -- read them; world-writable `/tmp` itself is left to the theorem.
  let decoys := (System.FilePath.mk e.dir) / "decoys"
  let home := decoys / "home"
  for dir in
    [home / ".config", decoys / "cwd" / ".config", decoys / "xdg", decoys / "tmp" / ".config"] do
    IO.FS.createDirAll (dir / "linger")
    IO.FS.writeFile (dir / "linger" / "remotes") s!"{devHost}\n"
  for (label, value) in [("set", some home.toString), ("unset", none), ("empty", some "")] do
    IO.FS.writeFile h.sshLog ""
    let listed ←
      IO.Process.output
          { cmd := e.bin, args := #["ls", "-r"], cwd := some (decoys / "cwd"),
            env :=
              e.procEnv ++ h.procPath ++
                #[("HOME", value), ("XDG_CONFIG_HOME", some (decoys / "xdg").toString),
                  ("TMPDIR", some (decoys / "tmp").toString)] }
    let ssh ← readArgs h.sshLog
    let configured := value.isSome && value != some ""
    expect
        (listed.exitCode == 0 && has listed.stdout "localsess" &&
          (if configured then ssh.contains devHost && has listed.stdout s!"alpha@{devHost}"
          else ssh.isEmpty && !has listed.stdout s!"@{devHost}"))
        (if configured then "ls -r reads the remotes file under a set HOME"
        else s!"ls -r with HOME {label} reads no remotes file and runs no SSH")

/-- The hermetic remote suite: a fake `ssh` and a far linger on `PATH`, a `HOME` of the suite's
own, so no check reads the user's remotes file, and the far linger also reached through the
command a remotes file names. -/
def run : IO UInt32 :=
  Env.suite "remote" fun e => do
    let root := System.FilePath.mk e.dir
    let fakebin := root / "fakebin"
    let home := root / "home"
    let transport := root / "transport"
    let far : Env := { e with dir := (root / "far").toString }
    for dir in [fakebin, home / ".config" / "linger", transport, root / "far"] do
      IO.FS.createDirAll dir
    let script (path : System.FilePath) (body : String) : IO String := do
      IO.FS.writeFile path body
      chmod path.toString 0o755
      return path.toString
    let sshLog := root / "ssh.log"
    let evil := root / "evil.json"
    IO.FS.writeFile evil evilLines
    discard <| script (fakebin / "ssh") (fakeSsh sshLog.toString evil.toString)
    discard <| script (fakebin / "linger") (farLinger e.bin far.dir)
    let queryLog := transport / "query.log"
    let olderLog := transport / "older.log"
    let stallPid := transport / "stall.pid"
    let query ← script (transport / "query") (fakeTransport e.bin queryLog.toString far.dir)
    let older ← script (transport / "older") (olderLinger olderLog.toString)
    let stall ←
      script (transport / "stall")
          s!"#!/bin/sh\necho $$ > {shellQuote stallPid.toString}\nexec sleep 600\n"
    let failing ← script (transport / "failing") "#!/bin/sh\nexit 3\n"
    let remotes := home / ".config" / "linger" / "remotes"
    let configured :=
      String.intercalate "\n"
          ["# the remote suite's hosts", "", s!"far {query}", s!"old\t{older}", s!"slow {stall}",
            s!"  down {failing}  ", devHost] ++
        "\n"
    IO.FS.writeFile remotes configured
    let newPath := s!"{fakebin}:{(← IO.getEnv "PATH").getD "/usr/bin:/bin"}"
    let hosts : Hosts :=
      { far, procPath := #[("PATH", some newPath), ("HOME", some home.toString)],
        ptyPath := #[s!"PATH={newPath}", s!"HOME={home}"], sshLog, queryLog, olderLog }
    let _ ← e.typeInEnv hosts.procPath "localsess" #["echo local-content"]
    let (alphaRc, _, _) ← far.cli #["start", "alpha", "sleep", "600"]
    try
      expect (alphaRc == 0) "the far linger starts a session of its own"
      listingChecks e hosts
      verbChecks e hosts
      attachChecks e hosts
      serveChecks e hosts
      refusalChecks e hosts
      fileChecks e hosts remotes query configured
      homeChecks e hosts
    finally
      e.killAll #["localsess"]
      far.killAll
          #["alpha", "work", "moved", "ends", "rs", "sink", "term", "made", "--read-only", "served"]
    discoveryChecks e

end Linger.Target.Suites.Remote
