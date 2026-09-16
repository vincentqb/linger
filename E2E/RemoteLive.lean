module

public import E2E.Harness
public import Linger.Core.Remote

public section

/-! # E2E.RemoteLive — the remote path against a REAL second machine

Ported from `tests/remote_live_test.py`. Unlike `E2E.Remote` — which puts a fake
`ssh` on `PATH`, is hermetic, and is in the gate — this needs an actual reachable
host running a real `linger`, so it is **deliberately not in `tests/e2e.sh`**:

    LINGER_REMOTE=gpu2 ./lake exe e2e remote-live

Assumes the remote has `linger` on its non-interactive `PATH` and two live sessions
named `alpha` and `beta`. It is the only suite whose preconditions live outside the
repo, which is exactly why it is opt-in — a suite that cannot pass on a fresh
checkout must not be able to fail the gate.

WHAT THE PORT STRENGTHENS. The Python matched `'name\talpha'` as a substring of the
remote's porcelain; this parses it with `Linger.Core.Remote.parse` — the same
reader `Cli.listRemote` uses on a real peer's reply — so the check now exercises
the actual remote-parse contract instead of the bytes it happens to be built from.
`SSH_AUTH_SOCK` is still removed: `linger` shells out to `ssh`, and a wedged local
agent would hang that child. The host key comes from `~/.ssh/config`. -/

namespace E2E.RemoteLive

open E2E.Harness

/-- Strip CSI sequences so a real remote shell's prompt painting does not hide the
marker. The Python's `plain()`, without a regex: CSI is `ESC [`, parameter and
intermediate bytes, then one final in `@`–`~`. -/
partial def stripCsi (s : String) : String :=
  let rec go (cs : List Char) (acc : List Char) : List Char :=
    match cs with
    | [] => acc.reverse
    | '\x1b' :: '[' :: rest =>
      let rec skip (r : List Char) : List Char :=
        match r with
        | [] => []
        | c :: t => if c ≥ '@' && c ≤ '~' then t else skip t
      go (skip rest) acc
    | c :: rest => go rest (c :: acc)
  String.ofList (go s.toList [])

def run : IO UInt32 := do
  let e ← Env.make "live"
  let host := (← IO.getEnv "LINGER_REMOTE").getD "gpu2"
  let mut f := 0
  IO.println s!"driving local overview + remote attach against real host: {host}"
  -- `SSH_AUTH_SOCK` removed for every child (`("K", none)` is a removal), so a
  -- wedged local ssh-agent cannot hang the `ssh` linger spawns.
  let noAgent : Array (String × Option String) := #[("SSH_AUTH_SOCK", none)]
  -- the overview folds the remote's sessions in over real ssh
  let (_, out, _) ← e.cliEnv noAgent #["-r", host]
  f := f + (← expect (has out s!"alpha@{host}") s!"remote alpha@{host} listed over real ssh")
  f := f + (← expect (has out s!"beta@{host}") s!"remote beta@{host} listed over real ssh")
  -- `attach alpha@HOST` execs `ssh -t HOST linger attach alpha` → real remote shell
  let c ← e.spawnEnv #["SSH_AUTH_SOCK="] #["attach", s!"alpha@{host}"] 110 30
  IO.sleep 3000
  let _ ← drain c.fd 2000
  c.type "echo REMOTE-HOST-$(hostname)\r"
  let seen := stripCsi (← drainStr c.fd 5000)
  f :=
    f + (← expect (has seen "REMOTE-HOST-") "attach name@host dropped into the real remote shell")
  -- detach (ctrl-\), leaving the session alive on the remote
  c.detach
  IO.sleep 1500
  c.bye (sendDetach := false)
  -- …and it must still be there. Parsed through `Remote.parse`, the reader
  -- `Cli.listRemote` uses, rather than substring-matching the porcelain.
  let ssh ←
    IO.Process.output
        { cmd := "ssh",
          args :=
            #["-o", "BatchMode=yes", "-o", "ConnectTimeout=5", "--", host, "linger", "ls",
              "--porcelain"] }
  let rows := Linger.Core.Remote.parse ssh.stdout
  f :=
    f +
      (←
        expect (rows.any (fun r => r.name == "alpha" && r.live))
            "remote session survived detach (still listed live, via Remote.parse)")
  verdict e f

end E2E.RemoteLive
