module

public import E2E.Watch
public import E2E.Status
public import E2E.Overview
public import E2E.Graphics
public import E2E.Agent
public import E2E.Resume
public import E2E.Attach
public import E2E.Robust
public import E2E.Remote
public import E2E.Terminal
public import E2E.RemoteLive
public import E2E.Coverage

public section

/-! # e2e — the pty suites, dispatched by name

One executable, one `lean_exe`, one argv dispatch: `./lake exe e2e watch`.
The suites share a harness; separate executable blocks would duplicate the same
lakefile stanza.

Each suite prints `PASS <name>` / `FAIL <name>` per check and `FAILURES: <n>` last;
`tests/e2e.sh` reads the verdict and requires the exact recorded check count. An
unknown name is an error, not a silent success. -/

def suites : List (String × IO UInt32) :=
  [("watch", E2E.Watch.run), ("status", E2E.Status.run), ("overview", E2E.Overview.run),
    ("graphics", E2E.Graphics.run), ("agent", E2E.Agent.run), ("resume", E2E.Resume.run),
    ("attach", E2E.Attach.run), ("robust", E2E.Robust.run), ("remote", E2E.Remote.run),
    ("terminal", E2E.Terminal.run),
    -- opt-in: needs a real reachable host, so NOT in tests/e2e.sh
    ("remote-live", E2E.RemoteLive.run),
    -- not a pty suite: the source-tree coverage ratchets (was tests/coverage.py)
    ("coverage", E2E.Coverage.run)]

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
