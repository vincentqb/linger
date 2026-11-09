module

import Linger.Session.Suites.Watch
import Linger.Display.Suites.Status
import Linger.Session.Suites.Paths
import Linger.Terminal.Suites.Graphics
import Linger.Session.Suites.Agent
import Linger.Session.Suites.Resume
import Linger.Session.Suites.Attach
import Linger.Session.Suites.Delivery
import Linger.Session.Suites.Robust
import Linger.Target.Suites.Remote
import Linger.Terminal.Suites.Mediation
import Linger.Display.Suites.Title
import Linger.Import.Suites.Recipes
import Linger.Import.Suites.Interop
import Linger.App.Suites.Manager
import Linger.Target.Suites.RemoteLive
import Verify.Ci
import Verify.Hygiene
import Linger.Session.Suites.Identity
import Linger.Session.Suites.Quiet
import Verify.Runner

public section

/-! # The `suites` executable — the pty suites, dispatched by name

One executable, one `lean_exe`, one argv dispatch: `./lake exe suites watch`.
The suites share a harness; separate executable blocks would duplicate the same
lakefile stanza.

Each suite prints `PASS <name>` / `FAIL <name>` per check and `FAILURES: <n>` last;
`scripts/verify.sh` supplies the exact recorded check counts to the batch runner, whose
logs go to `LINGER_LOG_DIR` (default `Verify.Harness.tempRoot`). An unknown name is an error,
not a silent success. -/

def suites : List (String × IO UInt32) :=
  [("watch", Linger.Session.Suites.Watch.run), ("status", Linger.Display.Suites.Status.run),
    ("overview", Linger.Session.Suites.Paths.run),
    ("graphics", Linger.Terminal.Suites.Graphics.run), ("agent", Linger.Session.Suites.Agent.run),
    ("resume", Linger.Session.Suites.Resume.run), ("attach", Linger.Session.Suites.Attach.run),
    ("delivery", Linger.Session.Suites.Delivery.run), ("robust", Linger.Session.Suites.Robust.run),
    ("remote", Linger.Target.Suites.Remote.run), ("terminal", Linger.Terminal.Suites.Mediation.run),
    ("title", Linger.Display.Suites.Title.run), ("recipes", Linger.Import.Suites.Recipes.run),
    ("interop", Linger.Import.Suites.Interop.run), ("manager", Linger.App.Suites.Manager.run),
    -- opt-in: needs a real reachable host, so NOT in scripts/verify.sh
    ("remote-live", Linger.Target.Suites.RemoteLive.run),
    -- Verifier regression checks, separate from the live product suites.
    ("ci", Verify.Ci.run), ("hygiene", Verify.Hygiene.run),
    ("identity", Linger.Session.Suites.Identity.run), ("quiet", Linger.Session.Suites.Quiet.run)]

def main (args : List String) : IO UInt32 := do
  match args with
  -- Not a suite: the child `Linger.Terminal.Suites.Mediation` runs under its own session's pty, because
  -- the terminal query has to be written to the session's OWN tty and read back from
  -- it — nothing on this side of the pty can do either. Four argv elements, so it can
  -- never collide with a one-element suite name.
  | ["--probe", result, ready, trigger] =>
    Linger.Terminal.Suites.Mediation.probe result ready trigger
  | ["--winsize-probe", result] =>
    Linger.Session.Suites.Resume.winsizeProbe result
  | ["--title-probe"] =>
    Linger.Display.Suites.Title.probe
  | ["--title-attach-probe", name] =>
    Linger.Display.Suites.Title.attachProbe name
  | ["--paths-probe"] =>
    Linger.Session.Suites.Paths.probe
  | ["--malformed-server", socketPath, readyPath] =>
    Linger.Session.Suites.Agent.malformedServer socketPath readyPath
  | ["--info-server", socketPath, readyPath, mode] =>
    Linger.Session.Suites.Agent.infoServer socketPath readyPath mode
  | ["--stream-info-server", socketPath, readyPath] =>
    Linger.Session.Suites.Robust.streamInfoServer socketPath readyPath
  | "--discovery-ssh" :: root :: rest =>
    Linger.Target.Suites.Remote.discoverySsh root rest
  | ["--discovery-leaf", root, host] =>
    Linger.Target.Suites.Remote.discoveryLeaf root host
  | ["--discovery-info", root] =>
    Linger.Target.Suites.Remote.discoveryInfo root
  | ["--delivery-child", trigger] =>
    Linger.Session.Suites.Delivery.childProbe trigger
  | ["--delivery-server", dir] =>
    Linger.Session.Suites.Delivery.serveProbe dir
  | "--manager-probe" :: rest =>
    Linger.App.Suites.Manager.probe rest
  | "--import-probe" :: rest =>
    Linger.Import.Suites.Recipes.importProbe rest
  | ["--runner-probe", dir, name] =>
    Verify.Ci.runnerProbe dir name
  | "--suites" :: entries =>
    let specs :=
      entries.filterMap fun entry => do
        let [name, count] := entry.splitOn ":" | none
        if !(suites.any (·.1 == name)) then
          none
        else
          some (name, ← count.toNat?)
    if specs.length != entries.length then
      IO.eprintln "suites: expected known-suite:assertion-count"
      return 2
    -- `scripts/verify.sh` supplies a directory per run, so concurrent checkouts never share logs.
    let logDir :=
      ((← IO.getEnv "LINGER_LOG_DIR").filter (!·.isEmpty)).getD (← Verify.Harness.tempRoot).toString
    IO.println s!"  suite logs: {logDir}/linger-<suite>.out"
    Verify.Runner.run (← IO.appPath).toString #[] logDir specs
  | ["delivery", check] =>
    Linger.Session.Suites.Delivery.run (some check)
  | ["title", binary] =>
    Linger.Display.Suites.Title.run (some binary)
  | ["remote", "discovery"] =>
    Linger.Target.Suites.Remote.runDiscovery
  | ["watch", "checkpoint"] =>
    Linger.Session.Suites.Watch.runCheckpoint
  | [name] =>
    match suites.find? (·.1 == name) with
    | some (_, run) =>
      run
    | none =>
      IO.eprintln s!"suites: unknown suite '{name}'"
      IO.eprintln s!"     known: {String.intercalate " " (suites.map (·.1))}"
      return 2
  | _ =>
    IO.eprintln s!"usage: suites <suite>   ({String.intercalate " " (suites.map (·.1))})"
    return 2
