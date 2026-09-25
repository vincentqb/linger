module

public import E2E.Overview
public import Linger.Runtime.Paths

public section

/-! # E2E.Paths — directory fallback checks included in the overview suite

Each probe runs in a fresh process with all four directory variables explicitly
set or removed. It only resolves names, so a broken fallback cannot create a
directory at the filesystem root. -/

namespace E2E.Paths

open E2E.Harness

/-- Re-entered with the case's environment; even empty directories remain visible
as empty lines in the byte-exact response. -/
def probe : IO UInt32 := do
  IO.println (← Linger.Runtime.Paths.socketDir)
  IO.println (← Linger.Runtime.Paths.stateDir)
  return 0

def check (e : Env) (name sockets state : String)
    (override runtime stateHome home : Option String := none) : IO Nat := do
  let (rc, out, err) ←
    e.cliEnv
        #[("LINGER_DIR", override), ("XDG_RUNTIME_DIR", runtime), ("XDG_STATE_HOME", stateHome),
          ("HOME", home)]
        #["--paths-probe"]
  expect (rc == 0 && out == s!"{sockets}\n{state}\n" && err.isEmpty) name

def run : IO UInt32 := do
  -- Every probe overrides the harness's LINGER_DIR; no fixture directory is used.
  let e : Env := { bin := (← IO.appPath).toString, dir := "" }
  let uid ← Linger.Posix.getuid
  let host := Linger.Core.Name.sanitize (← Linger.Posix.gethostname)
  let sockets := s!"/tmp/linger-{uid}"
  let state := s!"{sockets}/state/{host}"
  let home := "/tmp/linger paths/home"
  let homeState := s!"{home}/.local/state/linger/{host}"
  let runtime := "/tmp/linger paths/runtime"
  let stateHome := "/tmp/linger paths/state"
  let xdgState := s!"{stateHome}/linger/{host}"
  let mut f := 0
  f := f + (← check e "unset directory variables use uid and host fallbacks" sockets state)
  f :=
    f + (← check e "empty XDG_RUNTIME_DIR uses the uid fallback" sockets state (runtime := some ""))
  f :=
    f +
      (←
        check e "empty XDG_STATE_HOME falls through to HOME" sockets homeState (stateHome :=
            some "") (home := some home))
  f :=
    f +
      (← check e "empty HOME uses the uid and host state fallback" sockets state (home := some ""))
  f :=
    f +
      (←
        check e "all empty fallback variables behave as absent" sockets state (runtime := some "")
            (stateHome := some "") (home := some ""))
  f :=
    f +
      (←
        check e "nonempty XDG directories take precedence and preserve spaces" s!"{runtime}/linger"
            xdgState (runtime := some runtime) (stateHome := some stateHome) (home := some home))
  f :=
    f +
      (←
        check e "nonempty HOME supplies state when XDG_STATE_HOME is absent" sockets homeState
            (home := some home))
  f :=
    f +
      (←
        check e "nonempty XDG_STATE_HOME takes precedence over empty HOME" sockets xdgState
            (stateHome := some stateHome) (home := some ""))
  f :=
    f +
      (←
        check e "LINGER_DIR overrides all fallback variables verbatim" "relative/override"
            "relative/override" (override := some "relative/override") (runtime := some runtime)
            (stateHome := some stateHome) (home := some home))
  f :=
    f +
      (←
        check e "explicitly empty LINGER_DIR remains an override" "" "" (override := some "")
            (runtime := some runtime) (stateHome := some stateHome) (home := some home))
  -- Stop on a failed path check; otherwise the overview owns the final verdict.
  if f != 0 then
    IO.println s!"FAILURES: {f}"
    return 1
  E2E.Overview.run

end E2E.Paths
