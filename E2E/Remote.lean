module

public import E2E.Harness
public import Linger.Core.Remote
public import Linger.Runtime.Cli

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
    s!"  attach|watch) printf '\\033]2;remote-editor\\007{attachMark}\\n' ;;\n" ++
    "  send) if [ \"$3\" = - ]; then cat > \"$LINGER_REMOTE_STDIN\"; fi ;;\n" ++
    "esac\n" ++
    "exit 0\n"

/-- NUL framing preserves empty arguments, embedded spaces and newlines. -/
def readArgs (path : System.FilePath) : IO (List String) := do
  if ← path.pathExists then
    let text ← IO.FS.readFile path
    return if text.isEmpty then [] else (text.splitOn "\x00").dropLast
  return []

def run : IO UInt32 := do
  let e ← Env.make "remote"
  let mut f := 0
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
  IO.sleep 500
  let tag := s!"{goodName}@{devHost}"
  try
    let (drc, _, derr) ← e.cliEnv procPath #["-r", s!"{devHost},{devHost}"]
    f := f + (← expect (drc != 0 && has derr dupMsg) "duplicate remote host errors loudly")
    let (rrc, out, _) ← e.cliEnv procPath #["-r", s!"{devHost},{deadHost}"]
    let (_, pout, _) ← e.cliEnv procPath #["ls", "--porcelain", "-r", s!"{devHost},{deadHost}"]
    let recs := records pout
    f := f + (← expect (rrc == 0) "remote listing exits cleanly")
    f := f + (← expect (has out "localsess") "local session listed alongside remotes")
    f :=
      f +
        (←
          expect (has out tag && recs.contains ("name", tag))
              "remote session listed with its exact target")
    f :=
      f +
        (←
          expect
              (!has out "/etc/passwd" &&
                recs.filter (·.1 == "name") == [("name", "localsess"), ("name", tag)])
              "invalid remote names are dropped without manufacturing another target")
    f := f + (← expect (!has out "\x1b") "remote display escape sequences are scrubbed")
    f :=
      f +
        (←
          expect
              (!has out s!"@{deadHost}" &&
                !recs.any (fun kv => kv.1 == "name" && kv.2.endsWith s!"@{deadHost}"))
              "unreachable host contributes no rows")
    let c1 ← e.spawnEnv ptyPath #["attach", tag] 100 24
    let attached ← drain c1.fd 2000
    f := f + (← expect (hasText attached attachMark) "remote attach reaches linger")
    f :=
      f +
        (←
          expect
              ((← readArgs log) ==
                  ["-t", "--", devHost, Linger.Core.Remote.command "attach" goodName []] &&
                (← readArgs remoteArgs) == ["attach", goodName])
              "remote attach uses a PTY and preserves the target")
    f :=
      f +
        (←
          expect
              ((← c1.reap 1500) == 0 && hasText attached "remote-editor" &&
                hasBytes attached Linger.Core.Render.leaveAnsi &&
                ((Linger.Core.Vt.Vt.init 100 24).feed attached.toList).windowTitle.isEmpty)
              "normal SSH handback clears the application title")
    c1.bye (sendDetach := false)
    let c2 ← e.spawnEnv ptyPath #["attach", s!"{goodName}@{userHost}"] 100 24
    let _ ← drain c2.fd 2000
    f :=
      f +
        (←
          expect
              ((← readArgs log) ==
                ["-t", "--", userHost, Linger.Core.Remote.command "attach" goodName []])
              "user@host round-trips through the first-at split")
    c2.bye (sendDetach := false)
    let lost ← e.spawnEnv ptyPath #["attach", s!"{goodName}@{deadHost}"] 100 24
    let lostBytes ← drain lost.fd 2000
    f := f + (← expect ((← lost.reap 1500) == 255) "lost SSH preserves its exit status")
    f :=
      f +
        (←
          expect
              (hasText lostBytes "remote-lost" && hasBytes lostBytes Linger.Core.Render.leaveAnsi &&
                ((Linger.Core.Vt.Vt.init 100 24).feed lostBytes.toList).windowTitle.isEmpty)
              "lost SSH clears the title through a partial OSC")
    lost.bye (sendDetach := false)
    for name in
      ["work@", hostileName ++ "@" ++ devHost, "work;printf REMOTE-INJECTED@" ++ devHost,
        "work$(printf REMOTE-INJECTED)@" ++ devHost, "work 'two words'@" ++ devHost,
        "work\nprintf REMOTE-INJECTED@" ++ devHost] do
      IO.FS.writeFile log ""
      let c ← e.spawnEnv ptyPath #["attach", name] 100 24
      let reply ← drain c.fd 1500
      f :=
        f +
          (←
            expect
                ((← c.reap 1500) == 2 && (← readArgs log).isEmpty &&
                  hasText reply "invalid session name")
                s!"invalid remote target is rejected before SSH: {repr name}")
      c.bye (sendDetach := false)
    let words :=
      ["/bin/sh", "-c", "printf '%s' \"$1\"", "two words", "", s!"$(touch {injected})",
        "`printf REMOTE-INJECTED`", "line\nbreak", "a'b\"c\\d"]
    let commandClient ← e.spawnEnv ptyPath (["attach", tag] ++ words).toArray 100 24
    let _ ← drain commandClient.fd 2000
    f :=
      f +
        (←
          expect
              ((← commandClient.reap 1500) == 0 &&
                (← readArgs remoteArgs) == ["attach", goodName] ++ words &&
                !(← injected.pathExists))
              "remote attach preserves every command argument through the shell")
    commandClient.bye (sendDetach := false)
    let watcher ← e.spawnEnv ptyPath #["watch", tag] 100 24
    let watched ← drain watcher.fd 2000
    f :=
      f +
        (←
          expect
              ((← watcher.reap 1500) == 0 && (← readArgs remoteArgs) == ["watch", goodName] &&
                (← readArgs log).head? == some "-t" &&
                hasBytes watched Linger.Core.Render.leaveAnsi)
              "remote watch retains read-only semantics and terminal handback")
    watcher.bye (sendDetach := false)
    for (verb, canonical, args) in
      [("run", "run", words), ("r", "run", ["echo", "yes"]), ("send", "send", words),
        ("s", "send", ["two words"]), ("detach", "detach", []), ("kill", "kill", []),
        ("info", "info", []), ("capture", "capture", []), ("c", "capture", []),
        ("history", "history", []), ("hi", "history", []), ("resize", "resize", ["120", "40"]),
        ("wait", "wait", []), ("get", "get", []),
        ("set", "set", ["x=two words", "y='$(printf X)'", "empty="]),
        ("unset", "unset", ["x", "y"]), ("clear", "clear", [])] do
      let (rc, _, _) ← e.cliEnv procPath ([verb, tag] ++ args).toArray
      f :=
        f +
          (←
            expect
                (rc == 0 && (← readArgs remoteArgs) == [canonical, goodName] ++ args &&
                  (← readArgs log).head? == some "-T" &&
                  !(← injected.pathExists))
                s!"remote {verb} uses the common non-PTY transport with exact arguments")
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
    f :=
      f +
        (←
          expect (senderRc == some 0 && (← IO.FS.readBinFile remoteStdin).toList == payload.toList)
              "remote send stdin is byte-exact, including NUL and invalid UTF-8")
    for args in
      [#["resize", tag, "0", "40"], #["set", tag, "x=ok", "=bad"], #["unset", tag, ""],
        #["wait", tag, "bad name"], #["run", tag], #["send", tag]] do
      IO.FS.writeFile log ""
      let (rc, _, _) ← e.cliEnv procPath args
      f :=
        f +
          (←
            expect (rc == 2 && (← readArgs log).isEmpty)
                s!"invalid arguments have no remote effects: {repr args}")
    for verb in ["attach", "watch"] do
      IO.FS.writeFile log ""
      let (rc, _, _) ← e.cliEnv procPath #[verb, tag]
      f :=
        f +
          (←
            expect (rc != 0 && (← readArgs log).isEmpty)
                s!"remote {verb} requires terminal input and output")
    f :=
      f +
        (←
          expect
              ([["--porcelain", "-r", s!"{devHost},{deadHost}"],
                    ["-r", s!"{devHost},{deadHost}", "--porcelain"],
                    ["--remote", s!"{devHost},{deadHost}", "--porcelain"]].all
                (fun args =>
                  Linger.Runtime.Cli.parseLs args == some (true, some [devHost, deadHost])))
              "ls accepts explicit hosts in either option order")
    f :=
      f +
        (←
          expect
              (Linger.Runtime.Cli.parseLs ["-r", "--porcelain"] == some (true, some []) &&
                Linger.Runtime.Cli.parseLs ["--porcelain", "--remote"] == some (true, some []) &&
                Linger.Runtime.Cli.parseLs ["-r", "--typo"] == none)
              "ls preserves options after -r and rejects unknown options")
  finally
    e.killAll #["localsess"]
  verdict e f

end E2E.Remote
