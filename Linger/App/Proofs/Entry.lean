module

import all Linger.App.Entry

/-! Entry selection, interchange ownership and exact command forwarding. -/

namespace Linger.App.Entry

theorem route_bare_help : Linger.App.Entry.route [] = .session ["help"] := by rfl

/-- Where every command line goes, in one statement. -/
theorem route_eq (args : List String) :
    Linger.App.Entry.route args =
      if args = [] then .session ["help"]
      else
        if args = ["attach"] ∨ args = ["a"] then .selector false
        else
          if args = ["attach", "--read-only"] ∨ args = ["a", "--read-only"] then .selector true
          else if args.head? = some "tmux" then .tmux args.tail else .session args := by
  unfold Linger.App.Entry.route
  split <;> simp_all
  rename_i tmux
  intro h
  cases args with
  | nil => simp at h
  | cons a rest =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact tmux rest rfl

theorem route_selector_iff (args : List String) (readOnly : Bool) :
    Linger.App.Entry.route args = .selector readOnly ↔
      args = "attach" :: (if readOnly then ["--read-only"] else []) ∨
        args = "a" :: (if readOnly then ["--read-only"] else []) := by
  cases readOnly <;> unfold Linger.App.Entry.route <;> split <;> simp_all

theorem route_session_argv (command : String) (rest : List String) (hTmux : command ≠ "tmux")
    (hAttach : command ≠ "attach" ∨ (rest ≠ [] ∧ rest ≠ ["--read-only"]))
    (hAlias : command ≠ "a" ∨ (rest ≠ [] ∧ rest ≠ ["--read-only"])) :
    Linger.App.Entry.route (command :: rest) = .session (command :: rest) := by
  unfold Linger.App.Entry.route
  split <;> simp_all

theorem route_attach_operands (rest : List String) (h : rest ≠ [])
    (hReadOnly : rest ≠ ["--read-only"]) :
    Linger.App.Entry.route ("attach" :: rest) = .session ("attach" :: rest) :=
  route_session_argv "attach" rest (by decide) (.inr ⟨h, hReadOnly⟩) (.inl (by decide))

theorem route_select_retired (rest : List String) :
    Linger.App.Entry.route ("select" :: rest) = .session ("select" :: rest) :=
  route_session_argv "select" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_daemon_argv (rest : List String) :
    Linger.App.Entry.route ("__daemon" :: rest) = .session ("__daemon" :: rest) :=
  route_session_argv "__daemon" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_ls_argv (rest : List String) :
    Linger.App.Entry.route ("ls" :: rest) = .session ("ls" :: rest) :=
  route_session_argv "ls" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_tmux_argv (rest : List String) :
    Linger.App.Entry.route ("tmux" :: rest) = .tmux rest := by rfl

theorem route_tmux_iff (args rest : List String) :
    Linger.App.Entry.route args = .tmux rest ↔ args = "tmux" :: rest := by
  unfold Linger.App.Entry.route
  split <;> simp_all

theorem route_import_argv (rest : List String) :
    Linger.App.Entry.route ("import" :: rest) = .session ("import" :: rest) :=
  route_session_argv "import" rest (by decide) (.inl (by decide)) (.inl (by decide))

theorem route_export_argv (rest : List String) :
    Linger.App.Entry.route ("export" :: rest) = .session ("export" :: rest) :=
  route_session_argv "export" rest (by decide) (.inl (by decide)) (.inl (by decide))

end Linger.App.Entry
