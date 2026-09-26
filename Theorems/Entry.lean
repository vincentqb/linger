module

public import Tools.Entry
import all Tools.Entry

public section

/-! Entry selection, importer ownership and exact command forwarding. -/

namespace Tools.Entry

theorem route_selector_iff (args : List String) (stdinTty stdoutTty : Bool) :
    Tools.Entry.route args stdinTty stdoutTty = .selector ↔
      args = [] ∧ stdinTty = true ∧ stdoutTty = true := by
  cases args with
  | nil => cases stdinTty <;> cases stdoutTty <;> simp [Tools.Entry.route]
  | cons command rest =>
    by_cases h : command = "import"
    · subst command
      simp [Tools.Entry.route]
    · simp [Tools.Entry.route, h]

theorem route_bare_noninteractive (stdinTty stdoutTty : Bool)
    (h : stdinTty = false ∨ stdoutTty = false) :
    Tools.Entry.route [] stdinTty stdoutTty = .session [] := by
  cases stdinTty <;> cases stdoutTty <;> simp_all [Tools.Entry.route]

theorem route_session_argv (command : String) (rest : List String) (stdinTty stdoutTty : Bool)
    (h : command ≠ "import") :
    Tools.Entry.route (command :: rest) stdinTty stdoutTty = .session (command :: rest) := by
  simp [Tools.Entry.route, h]

theorem route_session_streams (command : String) (rest : List String)
    (stdinA stdoutA stdinB stdoutB : Bool) (h : command ≠ "import") :
    Tools.Entry.route (command :: rest) stdinA stdoutA =
      Tools.Entry.route (command :: rest) stdinB stdoutB := by
  rw [route_session_argv command rest stdinA stdoutA h,
    route_session_argv command rest stdinB stdoutB h]

theorem route_daemon_argv (rest : List String) (stdinTty stdoutTty : Bool) :
    Tools.Entry.route ("__daemon" :: rest) stdinTty stdoutTty = .session ("__daemon" :: rest) := by
  exact route_session_argv "__daemon" rest stdinTty stdoutTty (by decide)

theorem route_ls_argv (rest : List String) (stdinTty stdoutTty : Bool) :
    Tools.Entry.route ("ls" :: rest) stdinTty stdoutTty = .session ("ls" :: rest) := by
  exact route_session_argv "ls" rest stdinTty stdoutTty (by decide)

theorem route_import_argv (rest : List String) (stdinTty stdoutTty : Bool) :
    Tools.Entry.route ("import" :: rest) stdinTty stdoutTty = .importSave rest := by rfl

theorem route_import_streams (rest : List String) (stdinA stdoutA stdinB stdoutB : Bool) :
    Tools.Entry.route ("import" :: rest) stdinA stdoutA =
      Tools.Entry.route ("import" :: rest) stdinB stdoutB := by
  rw [route_import_argv, route_import_argv]

end Tools.Entry
