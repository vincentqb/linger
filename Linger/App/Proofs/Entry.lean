module

import all Linger.App.CoreCode.Entry
import Linger.Target.CoreSpec
import Linger.Target.CoreCode.Remote

/-! Entry selection, interchange ownership, exact command forwarding and encoded command
lines. -/

namespace Linger.App.Entry

open Linger.Target

/-- The words a command line's sender meant go where `Route.of` says. -/
theorem plain_eq (args : List String) : plain args = Route.of args := by
  unfold plain Route.of
  split <;> simp_all
  rename_i tmux
  intro h
  cases args with
  | nil => simp at h
  | cons a rest =>
    simp only [List.head?_cons, Option.some.injEq] at h
    subst h
    exact tmux rest rfl

/-- Where every command line goes, in one statement: an encoded one where its decoded words go,
or to a usage error when they do not decode, and any other where `Route.of` says. -/
theorem route_eq (args : List String) :
    route args =
      if args.head? = some Remote.marker then
        match Remote.decode args.tail with
        | some argv => Route.of argv
        | none => .malformed
      else Route.of args := by
  cases args with
  | nil => simp [route, plain_eq]
  | cons word encoded =>
    by_cases marked : word = Remote.marker
    · subst marked
      simp only [route, ↓reduceIte, List.head?_cons, List.tail_cons]
      split <;> simp_all [plain_eq]
    · simp [route, marked, plain_eq]

/-- A command line that does not start with `Remote.marker` goes where `Route.of` says. -/
theorem route_plain (args : List String) (unmarked : args.head? ≠ some Remote.marker) :
    route args = Route.of args := by
  rw [route_eq]
  simp [unmarked]

theorem route_bare_help : route [] = .session ["--help"] := by
  rw [route_plain [] (by simp)]
  rfl

theorem route_selector_iff (args : List String) (readOnly : Bool)
    (unmarked : args.head? ≠ some Remote.marker) :
    route args = .selector readOnly ↔
      args = "attach" :: (if readOnly then ["--read-only"] else []) := by
  rw [route_plain args unmarked, ← plain_eq]
  cases readOnly <;> unfold plain <;> split <;> simp_all

theorem route_session_argv (command : String) (rest : List String) (hTmux : command ≠ "tmux")
    (hAttach : command ≠ "attach" ∨ (rest ≠ [] ∧ rest ≠ ["--read-only"]))
    (hMarker : command ≠ Remote.marker) : route (command :: rest) = .session (command :: rest) := by
  rw [route_plain _ (by simpa using hMarker), ← plain_eq]
  unfold plain
  split <;> simp_all

theorem route_attach_operands (rest : List String) (h : rest ≠ [])
    (hReadOnly : rest ≠ ["--read-only"]) : route ("attach" :: rest) = .session ("attach" :: rest) :=
  route_session_argv "attach" rest (by decide) (.inr ⟨h, hReadOnly⟩) (by decide)

theorem route_select_retired (rest : List String) :
    route ("select" :: rest) = .session ("select" :: rest) :=
  route_session_argv "select" rest (by decide) (.inl (by decide)) (by decide)

theorem route_daemon_argv (rest : List String) :
    route ("__daemon" :: rest) = .session ("__daemon" :: rest) :=
  route_session_argv "__daemon" rest (by decide) (.inl (by decide)) (by decide)

theorem route_ls_argv (rest : List String) : route ("ls" :: rest) = .session ("ls" :: rest) :=
  route_session_argv "ls" rest (by decide) (.inl (by decide)) (by decide)

theorem route_tmux_argv (rest : List String) : route ("tmux" :: rest) = .tmux rest := by
  rw [route_plain _ (by simp [Remote.marker])]
  simp [Route.of]

theorem route_tmux_iff (args rest : List String) (unmarked : args.head? ≠ some Remote.marker) :
    route args = .tmux rest ↔ args = "tmux" :: rest := by
  rw [route_plain args unmarked, ← plain_eq]
  unfold plain
  split <;> simp_all

theorem route_import_argv (rest : List String) :
    route ("import" :: rest) = .session ("import" :: rest) :=
  route_session_argv "import" rest (by decide) (.inl (by decide)) (by decide)

theorem route_export_argv (rest : List String) :
    route ("export" :: rest) = .session ("export" :: rest) :=
  route_session_argv "export" rest (by decide) (.inl (by decide)) (by decide)

/-- An encoded command line goes where its decoded words go. -/
theorem route_encoded (encoded argv : List String) (decoded : Remote.decode encoded = some argv) :
    route (Remote.marker :: encoded) = Route.of argv := by simp [route_eq, decoded]

/-- An encoded command line that does not decode is a usage error. -/
theorem route_malformed (encoded : List String) (refused : Remote.decode encoded = none) :
    route (Remote.marker :: encoded) = .malformed := by simp [route_eq, refused]

end Linger.App.Entry
