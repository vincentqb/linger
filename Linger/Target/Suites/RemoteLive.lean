module

import Verify.Harness
import Linger.Target.Suites.Remote

public section

/-! # Linger.Target.Suites.RemoteLive — the remote path against a second linger

With `LINGER_REMOTE=<host>`, `./lake exe suites remote-live` drives a real host that ssh reaches,
with `linger` on its non-interactive `PATH` and two live sessions named `alpha` and `beta`; ssh
finds the host's key in its own configuration. Without it, the far side is this checkout's
`linger` under a state directory of its own, reached through a transport script in the suite's
directory, which starts `alpha` and `beta` there, and an `ssh` first on `PATH` that refuses to
run, so no check reaches the network. Either way the suite writes its own remotes file under a
`HOME` of its own and never reads the user's. It is not in `scripts/verify.sh`: its real-host mode
needs preconditions outside the repo. -/

namespace Linger.Target.Suites.RemoteLive

open Verify.Harness

/-- Strip `ESC [` through the first final character in `@`–`~` so remote prompt
painting does not hide markers. An incomplete CSI consumes the rest of the string. -/
def stripCsi (s : String) : String :=
  let rec go (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '\x1b' :: '[' :: rest => go (rest.dropWhile (fun c => !(c ≥ '@' && c ≤ '~'))).tail acc
    | c :: rest => go rest (c :: acc)
  termination_by cs.length
  decreasing_by
    · have := (List.dropWhile_sublist (l := rest) (fun c => !(c ≥ '@' && c ≤ '~'))).length_le
      simp only [List.length_cons, List.length_tail]
      omega
    · simp_wf
  String.ofList (go s.toList [])

/-- Run the suite against `LINGER_REMOTE`, or against a far linger in a state directory of its
own when it is unset. -/
def run : IO UInt32 := do
  let real ← IO.getEnv "LINGER_REMOTE"
  Env.suite "live" fun e => do
      let home := s!"{e.dir}/home"
      IO.FS.createDirAll s!"{home}/.config/linger"
      let remotes := s!"{home}/.config/linger/remotes"
      let far : Env := { e with dir := s!"{e.dir}/far" }
      let host := real.getD "far"
      -- `SSH_AUTH_SOCK` removed for every child (`("K", none)` is a removal), so a
      -- wedged local ssh-agent cannot hang an `ssh` linger runs
      let mut env : Array (String × Option String) :=
        #[("SSH_AUTH_SOCK", none), ("HOME", some home)]
      match real with
      | some name =>
        IO.FS.writeFile remotes s!"{name}\n"
      | none =>
        let bin := s!"{e.dir}/bin"
        IO.FS.createDirAll bin
        IO.FS.createDirAll far.dir
        IO.FS.writeFile s!"{bin}/ssh" "#!/bin/sh\nexit 255\n"
        IO.FS.writeFile s!"{e.dir}/transport"
            (Linger.Target.Suites.Remote.fakeTransport e.bin s!"{e.dir}/transport.log" far.dir)
        for script in [s!"{bin}/ssh", s!"{e.dir}/transport"] do
          Os.Shell.chmod script 0o755
        IO.FS.writeFile remotes s!"far {e.dir}/transport\n"
        env := env.push ("PATH", some s!"{bin}:{(← IO.getEnv "PATH").getD "/usr/bin:/bin"}")
        for name in ["alpha", "beta"] do
          discard <| far.cli #["start", name, "/bin/sh"]
      let ptyEnv := env.map fun (key, value) => s!"{key}={value.getD ""}"
      try
        IO.println s!"driving the overview and a remote attach against {host}"
        -- the overview folds in the far linger's sessions through the remotes file's command
        let (_, out, _) ← e.cliEnv env #["-r"]
        expect (has out s!"alpha@{host}") s!"remote alpha@{host} listed through its transport"
        expect (has out s!"beta@{host}") s!"remote beta@{host} listed through its transport"
        -- `attach alpha@HOST` runs the host's attach command, then `linger` and the words
        -- `Remote.command` encodes for `attach alpha`, there
        let c ← e.spawnEnv ptyEnv #["attach", s!"alpha@{host}"] 110 30
        IO.sleep 3000
        let _ ← drain c.fd 2000
        c.type "echo REMOTE-HOST-$((40+2))\r"
        let seen := stripCsi (← drainStr c.fd 5000)
        expect (has seen "REMOTE-HOST-42") "attach name@host dropped into the far session's shell"
        -- detach (ctrl-\), leaving the session alive on the far side
        c.detach
        IO.sleep 1500
        c.bye (sendDetach := false)
        -- …and it must still be there, as the far linger's own porcelain says
        let (_, listing, _) ← e.cliEnv env #["ls", "--porcelain", "-r"]
        let recs := records listing
        let after := (recs.dropWhile (· != ("name", s!"alpha@{host}"))).drop 1
        expect
            (recs.contains ("name", s!"alpha@{host}") &&
              (after.takeWhile (·.1 != "name")).lookup "state" != some "resumable")
            "remote session survived detach (still listed live, from its linger's porcelain)"
      finally
        if real.isNone then
          far.killAll #["alpha", "beta"]

end Linger.Target.Suites.RemoteLive
