module

public import Linger.Tools.Entry
import all Linger.Tools.Entry

public section

/-! Entry selection, interchange ownership and exact command forwarding. -/

namespace Linger.Tools.Entry

theorem route_bare_help : Linger.Tools.Entry.route [] = .session ["help"] := by rfl

theorem route_selector_iff (args : List String) (readOnly : Bool) :
    Linger.Tools.Entry.route args = .selector readOnly ↔
      args = "attach" :: (if readOnly then ["--read-only"] else []) ∨
        args = "a" :: (if readOnly then ["--read-only"] else []) := by
  cases readOnly <;> unfold Linger.Tools.Entry.route <;> split <;> simp_all

theorem route_session_argv (command : String) (rest : List String) (hTmux : command ≠ "tmux")
    (hAttach : command ≠ "attach" ∨ (rest ≠ [] ∧ rest ≠ ["--read-only"]))
    (hAlias : command ≠ "a" ∨ (rest ≠ [] ∧ rest ≠ ["--read-only"])) :
    Linger.Tools.Entry.route (command :: rest) = .session (command :: rest) := by
  unfold Linger.Tools.Entry.route
  split <;> simp_all

theorem route_attach_operands (rest : List String) (h : rest ≠ [])
    (hReadOnly : rest ≠ ["--read-only"]) :
    Linger.Tools.Entry.route ("attach" :: rest) = .session ("attach" :: rest) :=
  route_session_argv "attach" rest (by decide) (.inr ⟨h, hReadOnly⟩) (.inl (by decide))

theorem route_select_retired (rest : List String) :
    Linger.Tools.Entry.route ("select" :: rest) = .session ("select" :: rest) :=
  route_session_argv "select" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_daemon_argv (rest : List String) :
    Linger.Tools.Entry.route ("__daemon" :: rest) = .session ("__daemon" :: rest) :=
  route_session_argv "__daemon" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_ls_argv (rest : List String) :
    Linger.Tools.Entry.route ("ls" :: rest) = .session ("ls" :: rest) :=
  route_session_argv "ls" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_tmux_argv (rest : List String) :
    Linger.Tools.Entry.route ("tmux" :: rest) = .tmux rest := by rfl

theorem route_tmux_iff (args rest : List String) :
    Linger.Tools.Entry.route args = .tmux rest ↔ args = "tmux" :: rest := by
  unfold Linger.Tools.Entry.route
  split <;> simp_all

theorem route_import_argv (rest : List String) :
    Linger.Tools.Entry.route ("import" :: rest) = .session ("import" :: rest) :=
  route_session_argv "import" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_export_argv (rest : List String) :
    Linger.Tools.Entry.route ("export" :: rest) = .session ("export" :: rest) :=
  route_session_argv "export" rest (by decide) (.inl (by decide)) (.inl (by decide))

end Linger.Tools.Entry
