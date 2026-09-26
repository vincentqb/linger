module

public import Tools.Resurrect
import all Tools.Resurrect
import Theorems.Name

public section

/-! Kernel-checked importer contracts.

The planner sees one existing-name snapshot. Sequential idempotence assumes that
the next snapshot includes every planned name; it says nothing about concurrent
creation or whether a caller successfully creates sessions or enters directories.
-/

namespace Tools.Resurrect

private theorem parseRow_sound (home : String) (line : Nat) (fields : List String) (pane : Pane)
    (h : parseRow home line fields = .ok (some pane)) :
    Linger.Core.Name.sanitize pane.name = pane.name ∧
      pane.dir.contains '\x00' = false ∧ pane.line = line := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))
  all_goals
    cases h
    simp_all

/-- Even discarded saved commands must have their sentinel and contain no NUL. -/
private theorem parseRow_command_valid (home : String) (line : Nat)
    (session window field3 field4 pane field6 cwd field8 field9 savedCommand : String)
    (parsed : Pane)
    (h :
      parseRow home line
          ["pane", session, window, field3, field4, pane, field6, cwd, field8, field9,
            savedCommand] =
        .ok (some parsed)) :
    savedCommand.startsWith ":" = true ∧ savedCommand.contains '\x00' = false := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))

/-- Replacing a well-formed, NUL-free saved command changes neither the parsed pane
nor any error caused by another field. The ignored fields are arbitrary. -/
private theorem parseRow_command_irrelevant (home : String) (line : Nat)
    (session window field3 field4 pane field6 cwd field8 field9 savedCommand replacement : String)
    (hs : savedCommand.startsWith ":" = true) (hr : replacement.startsWith ":" = true)
    (hns : savedCommand.contains '\x00' = false) (hnr : replacement.contains '\x00' = false) :
    parseRow home line
        ["pane", session, window, field3, field4, pane, field6, cwd, field8, field9, savedCommand] =
      parseRow home line
        ["pane", session, window, field3, field4, pane, field6, cwd, field8, field9,
          replacement] := by
  simp [parseRow, hs, hr, hns, hnr]

private theorem parseRows_sound (home : String) (line : Nat) (seen rows : List String)
    (panes : List Pane) (h : parseRows home line seen rows = .ok panes) :
    (∀ pane ∈ panes,
        Linger.Core.Name.sanitize pane.name = pane.name ∧ pane.dir.contains '\x00' = false) ∧
      (panes.map Pane.name).Nodup ∧ (∀ pane ∈ panes, pane.name ∉ seen) := by
  induction rows generalizing line seen panes with
  | nil =>
    simp only [parseRows, Except.ok.injEq] at h
    subst panes
    simp
  | cons row rows ih =>
    simp only [parseRows] at h
    cases hrow : parseRow home line (row.splitOn "\t") with
    | error error => simp [hrow] at h
    | ok result =>
      cases result with
      | none =>
        simp only [hrow] at h
        exact ih (line + 1) seen panes h
      | some pane =>
        simp only [hrow] at h
        split at h
        · cases h
        · rename_i hskip
          cases hrest : parseRows home (line + 1) (pane.name :: seen) rows with
          | error error => simp [hrest, Except.map] at h
          | ok rest =>
            simp only [hrest, Except.map, Except.ok.injEq] at h
            subst panes
            obtain ⟨valid, distinct, fresh⟩ := ih (line + 1) (pane.name :: seen) rest hrest
            obtain ⟨canonical, dir, -⟩ := parseRow_sound home line _ pane hrow
            refine ⟨?_, ?_, ?_⟩
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨canonical, dir⟩
              · exact valid p hp
            · simp only [List.map_cons, List.nodup_cons]
              refine ⟨?_, distinct⟩
              intro hm
              obtain ⟨p, hp, hn⟩ := List.mem_map.mp hm
              exact fresh p hp (by simp [hn])
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · simpa using hskip
              · intro hs
                exact fresh p hp (List.mem_cons_of_mem _ hs)

/-- Every successful save is nonempty, has distinct projected names already valid
for linger, and has NUL-free decoded directories. -/
theorem parseSave_valid (home content : String) (panes : List Pane)
    (h : parseSave home content = .ok panes) :
    panes ≠ [] ∧
      (panes.map Pane.name).Nodup ∧
      ∀ pane ∈ panes,
        Linger.Core.Name.sanitize pane.name = pane.name ∧
          Linger.Core.Name.Valid pane.name ∧ pane.dir.contains '\x00' = false := by
  unfold parseSave at h
  split at h
  · cases h
  · cases h
  · rename_i head tail hrows
    cases h
    obtain ⟨valid, distinct, -⟩ := parseRows_sound home 1 [] _ _ hrows
    refine ⟨by simp, distinct, ?_⟩
    intro pane hp
    obtain ⟨canonical, dir⟩ := valid pane hp
    refine ⟨canonical, ?_, dir⟩
    rw [← canonical]
    exact Linger.Core.Name.sanitize_valid pane.name

/-- Includes NUL introduced by home expansion, not just NUL in the raw save. -/
theorem parseSave_no_nul (home content : String) (panes : List Pane)
    (h : parseSave home content = .ok panes) (pane : Pane) (hp : pane ∈ panes) :
    pane.dir.contains '\x00' = false := ((parseSave_valid home content panes h).2.2 pane hp).2.2

/-- Membership pins every output field to one unmodified source record. -/
theorem mem_plan (existing : List String) (panes : List Pane) (pane : Pane) :
    pane ∈ plan existing panes ↔ pane ∈ panes ∧ pane.name ∉ existing := by simp [plan]

/-- Filtering never reorders or modifies records. -/
theorem plan_panes (existing : List String) (panes : List Pane) :
    plan existing panes = panes.filter (fun pane => !existing.contains pane.name) := by rfl

theorem plan_order (existing : List String) (panes : List Pane) :
    List.Sublist (plan existing panes) panes := by
  rw [plan_panes]
  exact List.filter_sublist

theorem plan_skips_existing (existing : List String) (panes : List Pane) (pane : Pane)
    (h : pane ∈ plan existing panes) :
    pane.name ∉ existing := ((mem_plan existing panes pane).mp h).2

/-- The planner requires distinct input names; successful parsing supplies that premise. -/
theorem plan_names_unique (existing : List String) (panes : List Pane)
    (distinct : (panes.map Pane.name).Nodup) : ((plan existing panes).map Pane.name).Nodup :=
  ((plan_order existing panes).map Pane.name).nodup distinct

/-- A subsequent snapshot containing every planned identity yields no actions,
without a distinctness premise. -/
theorem plan_sequential_idempotent (existing : List String) (panes : List Pane) :
    plan (existing ++ (plan existing panes).map Pane.name) panes = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro pane h
  obtain ⟨hp, hn⟩ := (mem_plan _ _ pane).mp h
  apply hn
  by_cases he : pane.name ∈ existing
  · exact List.mem_append_left _ he
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨pane, ?_, rfl⟩
    exact (mem_plan _ _ _).mpr ⟨hp, he⟩

end Tools.Resurrect
