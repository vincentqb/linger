module

public import E2E.Watch
public import E2E.Status
public import E2E.Paths
public import E2E.Graphics
public import E2E.Agent
public import E2E.Resume
public import E2E.Attach
public import E2E.Delivery
public import E2E.Robust
public import E2E.Remote
public import E2E.Terminal
public import E2E.Title
public import E2E.Recipes
public import E2E.Interop
public import E2E.Manager
public import E2E.RemoteLive
public import E2E.Ci
public import E2E.Hygiene
public import E2E.Identity
public import E2E.Runner

public section

/-! # e2e — the pty suites, dispatched by name

One executable, one `lean_exe`, one argv dispatch: `./lake exe e2e watch`.
The suites share a harness; separate executable blocks would duplicate the same
lakefile stanza.

Each suite prints `PASS <name>` / `FAIL <name>` per check and `FAILURES: <n>` last;
`scripts/e2e.sh` supplies the exact recorded check counts to the batch runner. An
unknown name is an error, not a silent success. -/

def suites : List (String × IO UInt32) :=
  [("watch", E2E.Watch.run), ("status", E2E.Status.run), ("overview", E2E.Paths.run),
    ("graphics", E2E.Graphics.run), ("agent", E2E.Agent.run), ("resume", E2E.Resume.run),
    ("attach", E2E.Attach.run), ("delivery", E2E.Delivery.run), ("robust", E2E.Robust.run),
    ("remote", E2E.Remote.run), ("terminal", E2E.Terminal.run), ("title", E2E.Title.run),
    ("recipes", E2E.Recipes.run), ("interop", E2E.Interop.run), ("manager", E2E.Manager.run),
    -- opt-in: needs a real reachable host, so NOT in scripts/e2e.sh
    ("remote-live", E2E.RemoteLive.run),
    -- Verifier regression checks, separate from the live product suites.
    ("ci", E2E.Ci.run), ("hygiene", E2E.Hygiene.run), ("identity", E2E.Identity.run)]

def main (args : List String) : IO UInt32 := do
  match args with
  -- Not a suite: the child `E2E.Terminal` runs under its own session's pty. The
  -- Python suite re-entered itself the same way, because the terminal query has to
  -- be written to the session's OWN tty and read back from it — nothing on this
  -- side of the pty can do either. Four argv elements, so it can never collide
  -- with a one-element suite name.
  | ["--probe", result, ready, trigger] =>
    E2E.Terminal.probe result ready trigger
  | ["--winsize-probe", result] =>
    E2E.Resume.winsizeProbe result
  | ["--title-probe"] =>
    E2E.Title.probe
  | ["--title-attach-probe", name] =>
    E2E.Title.attachProbe name
  | ["--paths-probe"] =>
    E2E.Paths.probe
  | ["--malformed-server", socketPath, readyPath] =>
    E2E.Agent.malformedServer socketPath readyPath
  | ["--info-server", socketPath, readyPath, mode] =>
    E2E.Agent.infoServer socketPath readyPath mode
  | ["--stream-info-server", socketPath, readyPath] =>
    E2E.Robust.streamInfoServer socketPath readyPath
  | "--discovery-ssh" :: root :: rest =>
    E2E.Remote.discoverySsh root rest
  | ["--discovery-leaf", root, host] =>
    E2E.Remote.discoveryLeaf root host
  | ["--discovery-info", root] =>
    E2E.Remote.discoveryInfo root
  | ["--delivery-child", trigger] =>
    E2E.Delivery.childProbe trigger
  | ["--delivery-server", dir] =>
    E2E.Delivery.serveProbe dir
  | "--manager-probe" :: rest =>
    E2E.Manager.probe rest
  | "--import-probe" :: rest =>
    E2E.Recipes.importProbe rest
  | ["--runner-probe", dir, name] =>
    E2E.Ci.runnerProbe dir name
  | "--suites" :: entries =>
    let specs :=
      entries.filterMap fun entry => do
        let [name, count] := entry.splitOn ":" | none
        if !(suites.any (·.1 == name)) then
          none
        else
          some (name, ← count.toNat?)
    if specs.length != entries.length then
      IO.eprintln "e2e: expected known-suite:assertion-count"
      return 2
    E2E.Runner.run (← IO.appPath).toString #[] "/tmp" specs
  | ["delivery", check] =>
    E2E.Delivery.run (some check)
  | ["title", binary] =>
    E2E.Title.run (some binary)
  | ["remote", "discovery"] =>
    E2E.Remote.runDiscovery
  | ["watch", "checkpoint"] =>
    E2E.Watch.runCheckpoint
  | ["ls", "--summary"] =>
    match ← IO.getEnv "LINGER_E2E_TITLE_PIPE" with
    | some pipe =>
      E2E.Title.sampleProbe pipe
    | none =>
      IO.eprintln "e2e: missing title sampler fixture"
      return 2
  | [name] =>
    match suites.find? (·.1 == name) with
    | some (_, run) =>
      run
    | none =>
      IO.eprintln s!"e2e: unknown suite '{name}'"
      IO.eprintln s!"     known: {String.intercalate " " (suites.map (·.1))}"
      return 2
  | _ =>
    IO.eprintln s!"usage: e2e <suite>   ({String.intercalate " " (suites.map (·.1))})"
    return 2
