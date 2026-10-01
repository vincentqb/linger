module

public import E2E.Harness

public section

namespace E2E.Runner

/-- Run independent suites in separate processes, with at most four alive.
The caller supplies the only assertion-count inventory. Each process keeps its
combined output in its own log; ordinary `spawn` preserves inherited SIGINT.
Wait for every started suite even when another fails. -/
def run (binary : String) (args : Array String) (logDir : System.FilePath)
    (specs : List (String × Nat)) : IO UInt32 := do
  let names := specs.map (·.1)
  if
      specs.isEmpty || names.eraseDups.length != names.length ||
        specs.any
          (fun (name, count) =>
            name.isEmpty || !name.toList.all (fun c => c.isAlphanum || c == '-') || count == 0) then
    IO.eprintln "e2e: expected distinct suite names with positive assertion counts"
    return 2
  if (← IO.getEnv "LINGER_TEST_DIR").isSome then
    IO.eprintln "e2e: concurrent suites require separate state directories; unset LINGER_TEST_DIR"
    return 2
  let mut pending := specs
  let mut active : List (Task (Except IO.Error (String × Bool × Nat))) := []
  let mut failed := false
  while !pending.isEmpty || !active.isEmpty do
    while active.length < 4 && !pending.isEmpty do
      match pending with
      | [] =>
        pure ()
      | (name, expected) :: rest =>
        pending := rest
        let work : IO (String × Bool × Nat) := do
          let start ← IO.monoMsNow
          let log := logDir / s!"linger-{name}.out"
          -- Redirect in the child, not global Lean streams. All arguments remain
          -- argv elements, and exec keeps the process and signal disposition.
          let child ←
            IO.Process.spawn
                { cmd := "sh"
                  args :=
                    #["-c", "exec \"$@\" > \"$0\" 2>&1", log.toString, binary] ++ args ++ #[name] }
          let code ← child.wait
          let text ← IO.FS.readFile log
          let lines := E2E.Harness.lines text
          let count := (lines.filter (·.startsWith "PASS ")).length
          let ok := code == 0 && lines.getLast? == some "FAILURES: 0" && count == expected
          if !ok then
            IO.eprintln s!"e2e: {name} failed (exit {code}, {count}/{expected} checks); see {log}"
          return (name, ok, (← IO.monoMsNow) - start)
        active := (← work.asTask .dedicated) :: active
    match active with
    | [] =>
      pure ()
    | task :: rest =>
      let (result, remaining) ← IO.waitAny' (task :: rest)
      active := remaining
      match result with
      | .error e =>
        failed := true
        IO.eprintln s!"e2e: {e}"
      | .ok (name, ok, elapsed) =>
        failed := failed || !ok
        IO.println s!"  {name}: {if ok then "OK" else "FAILED"} ({elapsed} ms)"
  return if failed then 1 else 0

end E2E.Runner
