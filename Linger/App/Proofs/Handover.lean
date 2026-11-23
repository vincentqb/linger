module

public import Linger.App.CoreCode.Handover
import all Linger.App.CoreCode.Handover

public section

/-! # Whether an attach hands the session's daemon over, proved

`plan` hands the daemon over exactly when the attach is writable, the daemon writes a handoff
format this binary reads and its build is lower or unreported (`plan_eq_handOver`), so after a
writable attach to a daemon that can hand its session over, the daemon's build is at least the
attaching binary's unless it refused the handoff (`after_plan`). -/

namespace Linger.App.Handover

/-- An attach hands the daemon over exactly when it is writable, the daemon writes a handoff
format this binary reads, and the daemon's build is lower than `b` or not reported. -/
theorem plan_eq_handOver (mode : Session.Mode) (b : Nat) (fields : List (String × String)) :
    plan mode b fields = .handOver ↔
      mode = .writable ∧
        (Daemon.ofInfo fields).hands = true ∧ (Daemon.ofInfo fields).older b = true := by
  unfold plan
  cases mode <;> by_cases hands : (Daemon.ofInfo fields).hands = true <;>
    by_cases older : (Daemon.ofInfo fields).older b = true <;>
    simp_all

/-- After a writable attach to a daemon that can hand its session over, the daemon's build is at
least the attaching binary's, or the attach handed it over and the daemon refused, keeping its
own. -/
theorem after_plan (mode : Session.Mode) (b : Nat) (fields : List (String × String)) (took : Bool)
    (writable : mode = .writable) (hands : (Daemon.ofInfo fields).hands = true) :
    (∃ n, after (plan mode b fields) took (Daemon.ofInfo fields) b = some n ∧ b ≤ n) ∨
      plan mode b fields = .handOver ∧
        took = false ∧
        after (plan mode b fields) took (Daemon.ofInfo fields) b =
          (Daemon.ofInfo fields).build := by
  by_cases older : (Daemon.ofInfo fields).older b = true
  · have handed : plan mode b fields = .handOver :=
      (plan_eq_handOver mode b fields).mpr ⟨writable, hands, older⟩
    rw [handed]
    cases took
    · exact .inr ⟨rfl, rfl, rfl⟩
    · exact .inl ⟨b, rfl, Nat.le_refl b⟩
  · have kept : plan mode b fields = .keep := by
      unfold plan
      simp [older]
    rw [kept]
    simp only [Daemon.older, Bool.not_eq_true, Option.all_eq_false] at older
    obtain ⟨n, built, lower⟩ := older
    exact .inl ⟨n, by simp [after, built], by simpa using lower⟩

end Linger.App.Handover
