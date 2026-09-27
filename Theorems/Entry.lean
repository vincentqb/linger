module

public import Tools.Entry
import all Tools.Entry

public section

/-! Entry selection, importer ownership and exact command forwarding. -/

namespace Tools.Entry

theorem route_bare_help : Tools.Entry.route [] = .session ["help"] := by rfl

theorem route_selector_iff (args : List String) :
    Tools.Entry.route args = .selector ↔ args = ["select"] := by
  unfold Tools.Entry.route
  split <;> simp_all

theorem route_session_argv (command : String) (rest : List String) (hImport : command ≠ "import")
    (hSelect : command ≠ "select" ∨ rest ≠ []) :
    Tools.Entry.route (command :: rest) = .session (command :: rest) := by
  cases rest <;> simp_all [Tools.Entry.route]

theorem route_select_operands (rest : List String) (h : rest ≠ []) :
    Tools.Entry.route ("select" :: rest) = .session ("select" :: rest) :=
  route_session_argv "select" rest (by decide) (.inr h)

theorem route_daemon_argv (rest : List String) :
    Tools.Entry.route ("__daemon" :: rest) = .session ("__daemon" :: rest) :=
  route_session_argv "__daemon" rest (by decide) (.inl (by decide))

theorem route_ls_argv (rest : List String) :
    Tools.Entry.route ("ls" :: rest) = .session ("ls" :: rest) :=
  route_session_argv "ls" rest (by decide) (.inl (by decide))

theorem route_import_argv (rest : List String) :
    Tools.Entry.route ("import" :: rest) = .importSave rest := by rfl

end Tools.Entry
