module

public import Verify.Harness
public import Linger.App.CoreSpec
import Linger.App.WorldCode
import Linger.App.CoreCode.Entry
import Os.WorldCode.Command
import Linger.Target.CoreCode.Remote
import Linger.Target.CoreSpec
import Linger.Session.WorldCode.Client

public section

/-! Remote listing and command transport. A fake SSH hands its command line to `/bin/sh`, as
sshd hands it to a login shell; a fake remote linger records the words it receives, which the
checks read as the remote entry routes them (`Entry.route`). The shells suite runs the same
command lines through every login shell this host has. The remotes file's commands reach a far
linger, this checkout's binary under a state directory of its own, through scripts that stand
for a transport such as `docker exec`; every check runs under a `HOME` of the suite's own. -/

namespace Linger.Target.Suites.Remote

open Verify.Harness
open Os.Shell (chmod)
open Linger.Target.Remote (encodeWord)

private def devHost : String := "dev-a"

private def deadHost : String := "dead"

private def userHost : String := s!"me@{devHost}"

private def goodName : String := "remote-work"

private def hostileName : String := "../../etc/passwd\x01"

private def attachMark : String := "FAKE-ATTACH-OK"

private def dupMsg : String :=
  match Linger.Target.Remote.checkHosts [devHost, devHost] with
  | .error m => m
  | .ok _ => "checkHosts accepted a duplicate host"

private def fakeSsh (log : String) : String :=
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
    "exec /bin/sh -c \"$*\"\n"

private def fakeLinger : String :=
  "#!/bin/sh\n" ++ "printf '%s\\000' \"$@\" > \"$LINGER_REMOTE_ARGS\"\n" ++ "rows() {\n" ++
    s!"  printf 'name\\t{goodName}\\nstate\\tlive\\nclients\\t1\\ncmd\\tvim\\033[31mINJECT\\nlabel.env\\tprod\\n\\n'\n" ++
    s!"  printf 'name\\t{hostileName}\\nstate\\tresumable\\n\\n'\n" ++
    "  printf 'garbage line with no tabs\\n\\n'\n" ++
    "}\n" ++
    "case \"$1\" in\n" ++
    s!"  {Linger.Target.Remote.marker})\n" ++
    "    case \"$2\" in\n" ++
    s!"      {encodeWord "ls"}) rows ;;\n" ++
    s!"      {encodeWord "attach"}) printf '\\033]2;remote-editor\\007{attachMark}\\n' ;;\n" ++
    s!"      {encodeWord "send"}) if [ \"$4\" = {encodeWord "-"} ]; then cat > \"$LINGER_REMOTE_STDIN\"; fi ;;\n" ++
    "    esac ;;\n" ++
    "esac\n" ++
    "exit 0\n"

/-- A transport for the checks: a script that writes the words it is given to `log`, then runs
them, `linger` first, as this checkout's `linger` under `state`, the state directory of a far
machine's linger. Words that do not start with `linger` are no command linger sends. -/
def fakeTransport (linger log state : String) : String :=
  "#!/bin/sh\n" ++ s!"printf '%s\\000' \"$@\" > {shellQuote log}\n" ++
    "[ \"$1\" = linger ] || exit 99\n" ++
    "shift\n" ++
    s!"LINGER_DIR={shellQuote state} exec {shellQuote linger} \"$@\"\n"

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

/-- Where the remote linger's entry routes the words the fake remote linger last received. -/
def remoteRoute (path : System.FilePath) : IO Linger.App.Entry.Route := do
  return Linger.App.Entry.route (← readArgs path)

/-- A descendant keeps the SSH pipes open until its owner terminates the group. It outlives
every ceiling a discovery check waits under, so a command or stop that waited for the pipes
to close would outlast that ceiling however fast the host. -/
def discoveryLeaf (root host : String) : IO UInt32 := do
  IO.FS.writeFile s!"{root}/{host}.leaf.tmp" (toString (← Os.Shell.getpid))
  IO.FS.rename s!"{root}/{host}.leaf.tmp" s!"{root}/{host}.leaf"
  IO.sleep (2 * hangMs).toUInt32
  return 0

/-- Re-entered through a minimal fake SSH executable. The first host waits for
the second and a local info request, so serial discovery cannot pass. Stalled
hosts emit plausible rows but never complete before their group is cancelled. -/
def discoverySsh (root : String) (args : List String) : IO UInt32 := do
  let some host := ((args.dropWhile (· != "--")).drop 1).head? | return 2
  IO.FS.writeFile s!"{root}/{host}.started" ""
  if host.startsWith "stall-" then
    let child ←
      IO.Process.spawn { cmd := (← IO.appPath).toString, args := #["--discovery-leaf", root, host] }
    IO.println s!"name\t{host}\nstate\tlive\n"
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
  IO.println s!"name\t{goodName}\nstate\tlive\ncmd\t{host}\n"
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

/-- The remotes file's commands, against a far linger: this checkout's `linger` under a state
directory of its own, reached through scripts in the suite's directory that stand for ssh,
`docker exec` or `kubectl exec`, which `procPath` and `ptyPath` find under `home`. -/
private def transportChecks (e : Env) (procPath : Array (String × Option String))
    (ptyPath : Array String) (home sshLog : System.FilePath) : IO Unit := do
  let root := (System.FilePath.mk e.dir) / "transport"
  let far : Env := { e with dir := (root / "far").toString }
  IO.FS.createDirAll (root / "far")
  IO.FS.createDirAll (home / ".config" / "linger")
  let script (name body : String) : IO String := do
    let path := root / name
    IO.FS.writeFile path body
    chmod path.toString 0o755
    return path.toString
  let queryLog := root / "query.log"
  let attachLog := root / "attach.log"
  let stallPid := root / "stall.pid"
  let query ← script "query" (fakeTransport e.bin queryLog.toString far.dir)
  let attach ← script "attach" (fakeTransport e.bin attachLog.toString far.dir)
  let stall ←
    script "stall" s!"#!/bin/sh\necho $$ > {shellQuote stallPid.toString}\nexec sleep 600\n"
  let failing ← script "failing" "#!/bin/sh\nexit 3\n"
  let remotes := home / ".config" / "linger" / "remotes"
  let configured :=
    ["# the remote suite's hosts", "", s!"far {query} | {attach}", s!"slow\t{stall}",
      s!"  down {failing}  ", devHost]
  IO.FS.writeFile remotes (String.intercalate "\n" configured ++ "\n")
  -- what linger runs after a host's command: `linger`, the marker, then the encoded words
  let sent (verb : String) (words : List String) : List String :=
    "linger" :: Linger.Target.Remote.marker :: (verb :: words).map encodeWord
  try
    let (startRc, _, _) ← far.cli #["start", "alpha", "sleep", "600"]
    IO.FS.writeFile sshLog ""
    let (rc, out, _) ← e.cliEnv procPath #["ls", "--porcelain", "-r"]
    let recs := records out
    let status ← far.field "alpha" "status"
    expect
        (startRc == 0 && rc == 0 && status.isSome && rowField recs "alpha@far" "status" == status &&
          (← readArgs queryLog) == sent "ls" ["--porcelain"] &&
          (← readArgs attachLog).isEmpty)
        "a host's line names the command that lists its sessions, each as name@host with the status its linger reports"
    expect
        (recs.contains ("name", s!"{goodName}@{devHost}") &&
          (← readArgs sshLog) == ["-T", "--", devHost] ++ sent "ls" ["--porcelain"])
        "a line that names only a host lists it through ssh -T, as such a line always did"
    -- a listing waits for each host a bounded time, then shows what it missed
    let listing ←
      IO.Process.spawn
          { cmd := e.bin, args := #["ls", "-r"], env := e.procEnv ++ procPath, stdout := .piped,
            stderr := .null }
    let printed ← IO.asTask listing.stdout.readToEnd Task.Priority.dedicated
    let code ← waitOrKill listing (Linger.App.Api.remoteQueryTimeoutMs + hangMs)
    let human ←
      if code.isSome then
        pure ((← IO.wait printed).toOption.getD "")
      else
        pure ""
    let (_, porcelain, _) ← e.cliEnv procPath #["ls", "--porcelain", "-r"]
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
          !(records porcelain).any
              (fun kv => kv.1 == "name" && (kv.2.endsWith "@slow" || kv.2.endsWith "@down")) &&
          retired)
        "a host whose command does not answer within the bounded wait lists as ?, and its command is retired"
    let c ← e.spawnEnv ptyPath #["attach", "work@far"] 100 24
    let acc ← IO.mkRef ByteArray.empty
    let prompted ← c.awaitText acc (fun out => hasText out "$ ")
    c.type "echo TRANSPORT-$((40+2))\r"
    let answered ← c.awaitText acc (fun out => hasText out "TRANSPORT-42")
    c.detach
    let attachRc ← c.reap patienceMs
    c.bye (sendDetach := false)
    let (liveRc, _, _) ← far.cli #["ls", "work", "--porcelain"]
    expect
        (prompted && answered && attachRc == 0 && liveRc == 0 &&
          (← readArgs attachLog) == sent "attach" ["work"])
        "an attach goes through the host's attach command, which gives the far session the terminal"
    let (sendRc, _, _) ← e.cliEnv procPath #["send", "work@far", "echo SENT-$((6*7))\r"]
    let captured ←
      waitFor patienceMs do
          let (_, screen, _) ← e.cliEnv procPath #["capture", "work@far"]
          return has screen "SENT-42"
    let captureWords ← readArgs queryLog
    let (killRc, _, _) ← e.cliEnv procPath #["kill", "work@far"]
    let gone := (← far.field "work" "status").isNone
    expect
        (sendRc == 0 && captured && captureWords == sent "capture" ["work"] && killRc == 0 && gone)
        "every other verb on name@host goes through the host's query command, with its exact words"
    for (shape, bad) in
      [("HOST QUERY |", s!"far {query} |"), ("HOST | ATTACH", s!"far | {attach}"),
        ("HOST |", "far |"),
        ("HOST QUERY | ATTACH | ATTACH", s!"far {query} | {attach} | {attach}"),
        ("HOST QUERY, then HOST ATTACH", s!"far {query}\nfar {attach}")] do
      IO.FS.writeFile remotes (bad ++ "\n")
      IO.FS.writeFile queryLog ""
      IO.FS.writeFile attachLog ""
      let (listRc, _, listErr) ← e.cliEnv procPath #["ls", "-r"]
      let (infoRc, _, infoErr) ← e.cliEnv procPath #["ls", "alpha@far", "--porcelain"]
      expect
          (listRc != 0 && has listErr "far" && infoRc != 0 && has infoErr "far" &&
            (← readArgs queryLog).isEmpty &&
            (← readArgs attachLog).isEmpty)
          s!"a remotes line without one meaning is refused before any command runs: {shape}"
  finally
    far.killAll #["alpha", "work"]

/-- The hermetic remote suite: a fake `ssh` and a fake remote `linger` on `PATH`, a `HOME` of the
suite's own, so no check reads the user's remotes file, and a far linger reached through the
commands a remotes file names. -/
def run : IO UInt32 :=
  Env.suite "remote" fun e => do
    let fakebin := (System.FilePath.mk e.dir) / "fakebin"
    IO.FS.createDirAll fakebin
    let home := (System.FilePath.mk e.dir) / "home"
    IO.FS.createDirAll home
    let log := (System.FilePath.mk e.dir) / "ssh.log"
    let remoteArgs := (System.FilePath.mk e.dir) / "remote-args"
    let remoteStdin := (System.FilePath.mk e.dir) / "remote-stdin"
    let injected := (System.FilePath.mk e.dir) / "injected"
    let sshPath := fakebin / "ssh"
    IO.FS.writeFile sshPath (fakeSsh log.toString)
    chmod sshPath.toString 0o755
    let lingerPath := fakebin / "linger"
    IO.FS.writeFile lingerPath fakeLinger
    chmod lingerPath.toString 0o755
    let path0 := (← IO.getEnv "PATH").getD "/usr/bin:/bin"
    let newPath := s!"{fakebin.toString}:{path0}"
    let procPath : Array (String × Option String) :=
      #[("PATH", some newPath), ("HOME", some home.toString),
        ("LINGER_REMOTE_ARGS", some remoteArgs.toString),
        ("LINGER_REMOTE_STDIN", some remoteStdin.toString)]
    let ptyPath : Array String :=
      #[s!"PATH={newPath}", s!"HOME={home}", s!"LINGER_REMOTE_ARGS={remoteArgs}",
        s!"LINGER_REMOTE_STDIN={remoteStdin}"]
    let _ ← e.typeInEnv procPath "localsess" #["echo local-content"]
    let tag := s!"{goodName}@{devHost}"
    try
      let (drc, _, derr) ← e.cliEnv procPath #["ls", "-r", s!"{devHost},{devHost}"]
      expect (drc != 0 && has derr dupMsg) "duplicate remote host errors loudly"
      let (rrc, out, _) ← e.cliEnv procPath #["ls", "-r", s!"{devHost},{deadHost}"]
      let (_, pout, _) ← e.cliEnv procPath #["ls", "--porcelain", "-r", s!"{devHost},{deadHost}"]
      let recs := records pout
      expect (rrc == 0) "remote listing exits cleanly"
      expect (has out "localsess") "local session listed alongside remotes"
      expect (has out tag && recs.contains ("name", tag))
          "remote session listed with its exact target"
      expect
          (!has out "/etc/passwd" &&
            recs.filter (·.1 == "name") == [("name", "localsess"), ("name", tag)])
          "invalid remote names are dropped without manufacturing another target"
      expect (!has out "\x1b") "remote display escape sequences are scrubbed"
      expect
          (has out s!"? @{deadHost}" && has pout s!"host\t{deadHost}\nstatus\tunknown\n" &&
            !recs.any (fun kv => kv.1 == "name" && kv.2.endsWith s!"@{deadHost}"))
          "an unreachable host lists as ?, with no session rows"
      let c1 ← e.spawnEnv ptyPath #["attach", tag] 100 24
      let attached ← drain c1.fd hangMs
      expect (hasText attached attachMark) "remote attach reaches linger"
      expect
          ((← readArgs log) ==
              ["-t", "--", devHost] ++
                (Linger.Target.Remote.command "attach" [goodName]).splitOn " " &&
            (← remoteRoute remoteArgs) == .session ["attach", goodName])
          "remote attach uses a PTY and preserves the target"
      expect
          ((← c1.reap patienceMs) == 0 && hasText attached "remote-editor" &&
            hasBytes attached Terminal.Render.leaveAnsi &&
            ((Terminal.Vt.Vt.init 100 24).feed attached.toList).windowTitle.isEmpty)
          "normal SSH handback clears the application title"
      c1.bye (sendDetach := false)
      let c2 ← e.spawnEnv ptyPath #["attach", s!"{goodName}@{userHost}"] 100 24
      let _ ← drain c2.fd hangMs
      expect
          ((← readArgs log) ==
            ["-t", "--", userHost] ++
              (Linger.Target.Remote.command "attach" [goodName]).splitOn " ")
          "user@host round-trips through the first-at split"
      c2.bye (sendDetach := false)
      let lost ← e.spawnEnv ptyPath #["attach", s!"{goodName}@{deadHost}"] 100 24
      let lostBytes ← drain lost.fd hangMs
      expect ((← lost.reap patienceMs) == 255) "lost SSH preserves its exit status"
      expect
          (hasText lostBytes "remote-lost" && hasBytes lostBytes Terminal.Render.leaveAnsi &&
            ((Terminal.Vt.Vt.init 100 24).feed lostBytes.toList).windowTitle.isEmpty)
          "lost SSH clears the title through a partial OSC"
      lost.bye (sendDetach := false)
      for name in
        ["work@", hostileName ++ "@" ++ devHost, "work\x01;printf REMOTE-INJECTED@" ++ devHost,
          "work\x01$(printf REMOTE-INJECTED)@" ++ devHost, "work\x01 'two words'@" ++ devHost,
          "work\nprintf REMOTE-INJECTED@" ++ devHost] do
        IO.FS.writeFile log ""
        let c ← e.spawnEnv ptyPath #["attach", name] 100 24
        let reply ← drain c.fd hangMs
        expect
            ((← c.reap patienceMs) == 2 && (← readArgs log).isEmpty &&
              hasText reply "invalid session name")
            s!"invalid remote target is rejected before SSH: {repr name}"
        c.bye (sendDetach := false)
      let words :=
        ["/bin/sh", "-c", "printf '%s' \"$1\"", "two words", "", s!"$(touch {injected})",
          "`printf REMOTE-INJECTED`", "line\nbreak", "a'b\"c\\d"]
      let commandClient ← e.spawnEnv ptyPath (["attach", tag] ++ words).toArray 100 24
      let _ ← drain commandClient.fd hangMs
      expect
          ((← commandClient.reap patienceMs) == 0 &&
            (← remoteRoute remoteArgs) == .session (["attach", goodName] ++ words) &&
            !(← injected.pathExists))
          "remote attach preserves every command argument through the shell"
      commandClient.bye (sendDetach := false)
      let watcher ← e.spawnEnv ptyPath #["attach", "--read-only", tag] 100 24
      let watched ← drain watcher.fd hangMs
      expect
          ((← watcher.reap patienceMs) == 0 &&
            (← remoteRoute remoteArgs) == .session ["attach", "--read-only", goodName] &&
            (← readArgs log).head? == some "-t" &&
            hasBytes watched Terminal.Render.leaveAnsi)
          "remote read-only attach retains its option and terminal handback"
      watcher.bye (sendDetach := false)
      for options in [[], ["--read-only"]] do
        let literal ←
          e.spawnEnv ptyPath (["attach"] ++ options ++ ["--", s!"--read-only@{devHost}"]).toArray
              100 24
        let _ ← drain literal.fd hangMs
        expect
            ((← literal.reap patienceMs) == 0 &&
              (← remoteRoute remoteArgs) ==
                .session (["attach"] ++ options ++ ["--", "--read-only"]))
            "remote attach separates options from an option-like session name"
        literal.bye (sendDetach := false)
      for (verb, canonical, options, args) in
        [("start", "start", [], words), ("resume", "resume", [], []), ("send", "send", [], words),
          ("detach", "detach", [], []), ("kill", "kill", [], []), ("ls", "ls", [], []),
          ("ls", "ls", ["--porcelain"], []), ("capture", "capture", [], []),
          ("capture", "capture", ["--history"], []), ("resize", "resize", [], ["120", "40"]),
          ("wait", "wait", [], []), ("rename", "rename", [], ["renamed"])] do
        let (rc, _, _) ← e.cliEnv procPath ([verb] ++ options ++ [tag] ++ args).toArray
        expect
            (rc == 0 &&
              (← remoteRoute remoteArgs) ==
                .session ([canonical] ++ options ++ [goodName] ++ args) &&
              (← readArgs log).head? == some "-T" &&
              !(← injected.pathExists))
            s!"remote {verb} uses the common non-PTY transport with exact arguments"
      for options in [[], ["--history"]] do
        let (rc, _, _) ←
          e.cliEnv procPath (["capture"] ++ options ++ ["--", s!"--history@{devHost}"]).toArray
        expect
            (rc == 0 &&
              (← remoteRoute remoteArgs) ==
                .session (["capture"] ++ options ++ ["--", "--history"]))
            "remote capture separates options from an option-like session name"
      let payload := ByteArray.mk #[0, 3, 10, 27, 127, 195, 169, 255]
      let sender0 ←
        IO.Process.spawn
            { cmd := e.bin, args := #["send", tag, "-"], env := e.procEnv ++ procPath,
              stdin := .piped, stdout := .null, stderr := .inherit }
      let sender ←
        do
          let (input, child) ← sender0.takeStdin
          input.write payload
          input.flush
          pure child
      let senderRc ← waitOrKill sender hangMs
      expect (senderRc == some 0 && (← IO.FS.readBinFile remoteStdin).toList == payload.toList)
          "remote send stdin is byte-exact, including NUL and invalid UTF-8"
      for args in
        [#["resize", tag, "0", "40"], #["set", tag, "x=ok", "=bad"], #["unset", tag, ""],
          #["wait", tag, "-bad name"], #["run", tag], #["send", tag],
          #["attach", "--read-only", tag, "sh"], #["capture", tag, "--history"]] do
        IO.FS.writeFile log ""
        let (rc, _, _) ← e.cliEnv procPath args
        expect (rc == 2 && (← readArgs log).isEmpty)
            s!"invalid arguments have no remote effects: {repr args}"
      for args in [#["attach", tag], #["attach", "--read-only", tag]] do
        IO.FS.writeFile log ""
        let (rc, _, _) ← e.cliEnv procPath args
        expect (rc != 0 && (← readArgs log).isEmpty)
            s!"remote {repr args} requires terminal input and output"
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
        [home / ".config", decoys / "cwd" / ".config", decoys / "xdg",
          decoys / "tmp" / ".config"] do
        IO.FS.createDirAll (dir / "linger")
        IO.FS.writeFile (dir / "linger" / "remotes") s!"{devHost}\n"
      for (label, value) in [("set", some home.toString), ("unset", none), ("empty", some "")] do
        IO.FS.writeFile log ""
        let listed ←
          IO.Process.output
              { cmd := e.bin, args := #["ls", "-r"], cwd := some (decoys / "cwd"),
                env :=
                  e.procEnv ++ procPath ++
                    #[("HOME", value), ("XDG_CONFIG_HOME", some (decoys / "xdg").toString),
                      ("TMPDIR", some (decoys / "tmp").toString)] }
        let ssh ← readArgs log
        let configured := value.isSome && value != some ""
        expect
            (listed.exitCode == 0 && has listed.stdout "localsess" &&
              (if configured then ssh.contains devHost && has listed.stdout tag
              else ssh.isEmpty && !has listed.stdout tag))
            (if configured then "ls -r reads the remotes file under a set HOME"
            else s!"ls -r with HOME {label} reads no remotes file and runs no SSH")
    finally
      e.killAll #["localsess"]
    transportChecks e procPath ptyPath home log
    discoveryChecks e

end Linger.Target.Suites.Remote
