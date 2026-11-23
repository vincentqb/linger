module

import all Linger.App.CoreCode.Entry

/-! Entry selection and exact command forwarding. -/

namespace Linger.App.Entry

/-- **Where every command line goes** is where `Route.of` says. -/
theorem route_eq (args : List String) : route args = Route.of args := by
  unfold route Route.of
  split <;> simp_all

theorem route_bare_help : route [] = .session ["--help"] := by
  rw [route_eq]
  rfl

theorem route_selector_iff (args : List String) (readOnly : Bool) :
    route args = .selector readOnly ↔
      args = "attach" :: (if readOnly then ["--read-only"] else []) := by
  cases readOnly <;> unfold route <;> split <;> simp_all

theorem route_session_argv (command : String) (rest : List String)
    (hAttach : command ≠ "attach" ∨ (rest ≠ [] ∧ rest ≠ ["--read-only"])) :
    route (command :: rest) = .session (command :: rest) := by
  unfold route
  split <;> simp_all

theorem route_attach_operands (rest : List String) (h : rest ≠ [])
    (hReadOnly : rest ≠ ["--read-only"]) : route ("attach" :: rest) = .session ("attach" :: rest) :=
  route_session_argv "attach" rest (.inr ⟨h, hReadOnly⟩)

theorem route_select_argv (rest : List String) :
    route ("select" :: rest) = .session ("select" :: rest) :=
  route_session_argv "select" rest (.inl (by decide))

theorem route_daemon_argv (rest : List String) :
    route ("__daemon" :: rest) = .session ("__daemon" :: rest) :=
  route_session_argv "__daemon" rest (.inl (by decide))

theorem route_ls_argv (rest : List String) : route ("ls" :: rest) = .session ("ls" :: rest) :=
  route_session_argv "ls" rest (.inl (by decide))

/-- A `tmux` command line reaches the session CLI, which refuses it as a word it does not know. -/
theorem route_tmux_argv (rest : List String) : route ("tmux" :: rest) = .session ("tmux" :: rest) :=
  route_session_argv "tmux" rest (.inl (by decide))

theorem route_import_argv (rest : List String) :
    route ("import" :: rest) = .session ("import" :: rest) :=
  route_session_argv "import" rest (.inl (by decide))

theorem route_export_argv (rest : List String) :
    route ("export" :: rest) = .session ("export" :: rest) :=
  route_session_argv "export" rest (.inl (by decide))

end Linger.App.Entry
