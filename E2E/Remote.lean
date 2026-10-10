module

public import E2E.Harness
import Linger.Runtime.Cli
import Linger.Runtime.Command

public section

/-! Remote listing and command transport. A fake SSH executes the real POSIX
shell boundary; a fake remote linger records the resulting arguments. -/

namespace E2E.Remote

open E2E.Harness
open Linger.Posix (chmod)

def devHost : String := "dev-a"

def deadHost : String := "dead"

def userHost : String := s!"me@{devHost}"

def goodName : String := "remote-work"

def hostileName : String := "../../etc/passwd"

def attachMark : String := "FAKE-ATTACH-OK"

def dupMsg : String :=
  match Linger.Core.Remote.checkHosts [devHost, devHost] with
  | .error m => m
  | .ok _ => "checkHosts accepted a duplicate host"

def fakeSsh (log : String) : String :=
  "#!/bin/sh\n" ++ s!"printf '%s\\000' \"$@\" > {Linger.Core.Remote.shellQuote log}\n" ++
    "while [ $# -gt 0 ]; do\n" ++
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

def fakeLinger : String :=
  "#!/bin/sh\n" ++ "printf '%s\\000' \"$@\" > \"$LINGER_REMOTE_ARGS\"\n" ++ "case \"$1\" in\n" ++
    "  ls)\n" ++
    s!"    printf 'name\\t{goodName}\\nstate\\tlive\\nclients\\t1\\ncmd\\tvim\\033[31mINJECT\\nlabel.env\\tprod\\n\\n'\n" ++
    s!"    printf 'name\\t{hostileName}\\nstate\\tresumable\\n\\n'\n" ++
    "    printf 'garbage line with no tabs\\n\\n'\n" ++
    "    ;;\n" ++
    s!"  attach) printf '\\033]2;remote-editor\\007{attachMark}\\n' ;;\n" ++
    "  send) if [ \"$3\" = - ]; then cat > \"$LINGER_REMOTE_STDIN\"; fi ;;\n" ++
    "esac\n" ++
    "exit 0\n"

/-- NUL framing preserves empty arguments, embedded spaces and newlines. -/
def readArgs (path : System.FilePath) : IO (List String) := do
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    return if text.isEmpty then [] else (text.splitOn "\x00").dropLast
  return []

/-- A descendant keeps the SSH pipes open until its owner terminates the group. -/
def discoveryLeaf (root host : String) : IO UInt32 := do
  IO.FS.writeFile s!"{root}/{host}.leaf.tmp" (toString (← Linger.Posix.getpid))
  IO.FS.rename s!"{root}/{host}.leaf.tmp" s!"{root}/{host}.leaf"
  IO.sleep 15000
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
  let listener ← Linger.Posix.unixListen s!"{root}/state/local.sock"
  Linger.Posix.setNonblock listener
  try
    IO.FS.writeFile s!"{root}/local.ready" ""
    let deadline := (← Linger.Posix.monotonicMs) + 5000
    while (← Linger.Posix.monotonicMs) < deadline do
      let accepted ← Linger.Posix.accept listener
      if accepted < 0 then
        IO.sleep 10
        continue
      let fd := accepted.toUInt64.toUInt32
      try
        let ready ← Linger.Posix.poll #[fd] #[Linger.Posix.POLLIN] 2000
        if ready[0]! == 0 then
          return 1
        discard <| Linger.Posix.read fd 4096
        IO.FS.writeFile s!"{root}/local.request" ""
        unless ← waitFor 5000 (System.FilePath.pathExists s!"{root}/first.started") do
          return 1
        Linger.Runtime.Client.sendMsg fd (.infoReply "cmd\tlocal-concurrent\n".toUTF8.toList)
        Linger.Runtime.Client.sendMsg fd .done
        return 0
      finally
        Linger.Posix.close fd
    return 1
  finally
    Linger.Posix.close listener

private def discoverySetup (e : Env) (slug : String) : IO (Env × String × String) := do
  let root := s!"{e.dir}/{slug}"
  let state := { e with dir := s!"{root}/state" }
  let bin := s!"{root}/bin"
  IO.FS.createDirAll state.dir
  IO.FS.createDirAll bin
  let self ← IO.appPath
  IO.FS.writeFile s!"{bin}/ssh"
      s!"#!/bin/sh\nexec {Linger.Core.Remote.shellQuote self.toString} --discovery-ssh {Linger.Core.Remote.shellQuote root} \"$@\"\n"
  chmod s!"{bin}/ssh" 0o755
  return (state, root, s!"{bin}:{(← IO.getEnv "PATH").getD "/usr/bin:/bin"}")

/-- A terminated descendant may briefly await the system reaper. -/
private def discoveryGone (root host : String) : IO Bool := do
  let path := s!"{root}/{host}.leaf"
  unless ← System.FilePath.pathExists path do
    return false
  let pid := (← IO.FS.readFile path).toNat?.getD 0
  return pid > 0 && !(← Linger.Posix.alive (UInt32.ofNat pid))

/-- Retire fixture descendants even when intentionally breaking group cleanup. -/
private def cleanupDiscovery (root : String) : IO Unit := do
  for entry in ← (System.FilePath.mk root).readDir do
    if entry.fileName.endsWith ".leaf" then
      let host := (entry.fileName.dropEnd 5).toString
      unless ← discoveryGone root host do
        if let some pid := (← IO.FS.readFile entry.path).toNat? then
          try
            Linger.Posix.kill (UInt32.ofNat pid) 15
          catch _ =>
            pure ()

def discoveryChecks (e : Env) : IO Unit := do
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
    if (← server.tryWait).isNone then
      server.kill
      discard server.wait
  let (state, root, path) ← discoverySetup e "deadline"
  let limit := Linger.Runtime.Cli.remoteQueryLimit
  let hosts := (List.range (limit + 1)).map (fun i => s!"stall-{i}")
  let active := hosts.take limit
  let start ← Linger.Posix.monotonicMs
  let command ←
    IO.Process.spawn
        { cmd := e.bin,
          args := #["ls", "--porcelain", "-r", String.intercalate "," ("quick" :: hosts)],
          env := state.procEnv ++ #[("PATH", some path)], stdout := .piped, stderr := .null }
  try
    let ready ←
      waitFor 2000 do
          active.allM fun host => System.FilePath.pathExists s!"{root}/{host}.leaf"
    expect (ready && !(← System.FilePath.pathExists s!"{root}/{hosts.getLast!}.started"))
        "remote discovery limits simultaneous SSH jobs and reuses completed slots"
    let code ← waitProcess command (Linger.Runtime.Cli.remoteQueryTimeoutMs + 1500)
    let elapsed := (← Linger.Posix.monotonicMs) - start
    let stopped ← waitFor 2000 (active.allM (discoveryGone root))
    if code.isNone then
      cleanupDiscovery root
      command.kill
      discard command.wait
    let output ← command.stdout.readToEnd
    expect (code == some 0 && elapsed < Linger.Runtime.Cli.remoteQueryTimeoutMs + 1500)
        "remote commands share one deadline even when pipes stay open"
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
            Linger.Runtime.Command.start (← IO.appPath).toString
                #["--discovery-ssh", root, "--", "stall-stop"]))
  try
    let ready ← waitFor 2000 (System.FilePath.pathExists s!"{root}/stall-stop.leaf")
    let start ← Linger.Posix.monotonicMs
    Linger.Runtime.Command.stop pending 100
    let elapsed := (← Linger.Posix.monotonicMs) - start
    let stopped ← waitFor 2000 (discoveryGone root "stall-stop")
    expect (ready && stopped && elapsed < 1500 && (← pending.get).isNone)
        "cooperative stop force-retires descendants that retain pipes after their leader exits"
  finally
    Linger.Runtime.Command.stop pending
    cleanupDiscovery root
  let (state, root, path) ← discoverySetup e "cancel"
  IO.FS.createDirAll s!"{root}/.config/linger"
  IO.FS.writeFile s!"{root}/.config/linger/remotes" "stall-cancel\n"
  let chooser ← state.spawnEnv #[s!"PATH={path}", s!"HOME={root}"] #["attach"]
  try
    let ready ← waitFor 2000 (System.FilePath.pathExists s!"{root}/stall-cancel.leaf")
    let start ← Linger.Posix.monotonicMs
    chooser.type "\x03"
    let code ← chooser.reap 1500
    expect (ready && code == 130 && (← Linger.Posix.monotonicMs) - start < 1500)
        "cancelling bare attach retires discovery promptly"
    let stopped ← waitFor 2000 (discoveryGone root "stall-cancel")
    expect (ready && stopped) "chooser cancellation reaches SSH descendants"
  finally
    cleanupDiscovery root
    chooser.bye (sendDetach := false)

def runDiscovery : IO UInt32 := Env.suite "discovery" discoveryChecks

def run : IO UInt32 :=
  Env.suite "remote" fun e => do
    let fakebin := (System.FilePath.mk e.dir) / "fakebin"
    IO.FS.createDirAll fakebin
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
      #[("PATH", some newPath), ("LINGER_REMOTE_ARGS", some remoteArgs.toString),
        ("LINGER_REMOTE_STDIN", some remoteStdin.toString)]
    let ptyPath : Array String :=
      #[s!"PATH={newPath}", s!"LINGER_REMOTE_ARGS={remoteArgs}",
        s!"LINGER_REMOTE_STDIN={remoteStdin}"]
    let _ ← e.cliEnv procPath #["run", "localsess", "echo local-content"]
    let tag := s!"{goodName}@{devHost}"
    try
      let (drc, _, derr) ← e.cliEnv procPath #["-r", s!"{devHost},{devHost}"]
      expect (drc != 0 && has derr dupMsg) "duplicate remote host errors loudly"
      let (rrc, out, _) ← e.cliEnv procPath #["-r", s!"{devHost},{deadHost}"]
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
          (!has out s!"@{deadHost}" &&
            !recs.any (fun kv => kv.1 == "name" && kv.2.endsWith s!"@{deadHost}"))
          "unreachable host contributes no rows"
      let c1 ← e.spawnEnv ptyPath #["attach", tag] 100 24
      let attached ← drain c1.fd 2000
      expect (hasText attached attachMark) "remote attach reaches linger"
      expect
          ((← readArgs log) ==
              ["-t", "--", devHost, Linger.Core.Remote.command "attach" goodName []] &&
            (← readArgs remoteArgs) == ["attach", goodName])
          "remote attach uses a PTY and preserves the target"
      expect
          ((← c1.reap 1500) == 0 && hasText attached "remote-editor" &&
            hasBytes attached Linger.Core.Render.leaveAnsi &&
            ((Linger.Core.Vt.Vt.init 100 24).feed attached.toList).windowTitle.isEmpty)
          "normal SSH handback clears the application title"
      c1.bye (sendDetach := false)
      let c2 ← e.spawnEnv ptyPath #["attach", s!"{goodName}@{userHost}"] 100 24
      let _ ← drain c2.fd 2000
      expect
          ((← readArgs log) ==
            ["-t", "--", userHost, Linger.Core.Remote.command "attach" goodName []])
          "user@host round-trips through the first-at split"
      c2.bye (sendDetach := false)
      let lost ← e.spawnEnv ptyPath #["attach", s!"{goodName}@{deadHost}"] 100 24
      let lostBytes ← drain lost.fd 2000
      expect ((← lost.reap 1500) == 255) "lost SSH preserves its exit status"
      expect
          (hasText lostBytes "remote-lost" && hasBytes lostBytes Linger.Core.Render.leaveAnsi &&
            ((Linger.Core.Vt.Vt.init 100 24).feed lostBytes.toList).windowTitle.isEmpty)
          "lost SSH clears the title through a partial OSC"
      lost.bye (sendDetach := false)
      for name in
        ["work@", hostileName ++ "@" ++ devHost, "work;printf REMOTE-INJECTED@" ++ devHost,
          "work$(printf REMOTE-INJECTED)@" ++ devHost, "work 'two words'@" ++ devHost,
          "work\nprintf REMOTE-INJECTED@" ++ devHost] do
        IO.FS.writeFile log ""
        let c ← e.spawnEnv ptyPath #["attach", name] 100 24
        let reply ← drain c.fd 1500
        expect
            ((← c.reap 1500) == 2 && (← readArgs log).isEmpty &&
              hasText reply "invalid session name")
            s!"invalid remote target is rejected before SSH: {repr name}"
        c.bye (sendDetach := false)
      let words :=
        ["/bin/sh", "-c", "printf '%s' \"$1\"", "two words", "", s!"$(touch {injected})",
          "`printf REMOTE-INJECTED`", "line\nbreak", "a'b\"c\\d"]
      let commandClient ← e.spawnEnv ptyPath (["attach", tag] ++ words).toArray 100 24
      let _ ← drain commandClient.fd 2000
      expect
          ((← commandClient.reap 1500) == 0 &&
            (← readArgs remoteArgs) == ["attach", goodName] ++ words &&
            !(← injected.pathExists))
          "remote attach preserves every command argument through the shell"
      commandClient.bye (sendDetach := false)
      let watcher ← e.spawnEnv ptyPath #["attach", "--read-only", tag] 100 24
      let watched ← drain watcher.fd 2000
      expect
          ((← watcher.reap 1500) == 0 &&
            (← readArgs remoteArgs) == ["attach", "--read-only", goodName] &&
            (← readArgs log).head? == some "-t" &&
            hasBytes watched Linger.Core.Render.leaveAnsi)
          "remote read-only attach retains its option and terminal handback"
      watcher.bye (sendDetach := false)
      for options in [[], ["--read-only"]] do
        let literal ←
          e.spawnEnv ptyPath (["attach"] ++ options ++ ["--", s!"--read-only@{devHost}"]).toArray
              100 24
        let _ ← drain literal.fd 1000
        expect
            ((← literal.reap 1000) == 0 &&
              (← readArgs remoteArgs) == ["attach"] ++ options ++ ["--", "--read-only"])
            "remote attach separates options from an option-like session name"
        literal.bye (sendDetach := false)
      for (verb, canonical, options, args) in
        [("run", "run", [], words), ("r", "run", [], ["echo", "yes"]), ("send", "send", [], words),
          ("s", "send", [], ["two words"]), ("detach", "detach", [], []), ("kill", "kill", [], []),
          ("info", "info", [], []), ("capture", "capture", [], []), ("c", "capture", [], []),
          ("capture", "capture", ["--history"], []), ("c", "capture", ["--history"], []),
          ("resize", "resize", [], ["120", "40"]), ("wait", "wait", [], []), ("get", "get", [], []),
          ("set", "set", [], ["x=two words", "y='$(printf X)'", "empty="]),
          ("unset", "unset", [], ["x", "y"]), ("clear", "clear", [], [])] do
        let (rc, _, _) ← e.cliEnv procPath ([verb] ++ options ++ [tag] ++ args).toArray
        expect
            (rc == 0 && (← readArgs remoteArgs) == [canonical] ++ options ++ [goodName] ++ args &&
              (← readArgs log).head? == some "-T" &&
              !(← injected.pathExists))
            s!"remote {verb} uses the common non-PTY transport with exact arguments"
      for options in [[], ["--history"]] do
        let (rc, _, _) ←
          e.cliEnv procPath (["capture"] ++ options ++ ["--", s!"--history@{devHost}"]).toArray
        expect (rc == 0 && (← readArgs remoteArgs) == ["capture"] ++ options ++ ["--", "--history"])
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
      let senderRc ← waitProcess sender 3000
      if senderRc.isNone then
        sender.kill
        discard sender.wait
      expect (senderRc == some 0 && (← IO.FS.readBinFile remoteStdin).toList == payload.toList)
          "remote send stdin is byte-exact, including NUL and invalid UTF-8"
      for args in
        [#["resize", tag, "0", "40"], #["set", tag, "x=ok", "=bad"], #["unset", tag, ""],
          #["wait", tag, "bad name"], #["run", tag], #["send", tag],
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
                ["-r", s!"{devHost},{deadHost}", "--porcelain"],
                ["--remote", s!"{devHost},{deadHost}", "--porcelain"]].all
            (fun args => Linger.Runtime.Cli.parseLs args == some (true, some [devHost, deadHost])))
          "ls accepts explicit hosts in either option order"
      expect
          (Linger.Runtime.Cli.parseLs ["-r", "--porcelain"] == some (true, some []) &&
            Linger.Runtime.Cli.parseLs ["--porcelain", "--remote"] == some (true, some []) &&
            Linger.Runtime.Cli.parseLs ["-r", "--typo"] == none)
          "ls preserves options after -r and rejects unknown options"
    finally
      e.killAll #["localsess"]
    discoveryChecks e

end E2E.Remote
