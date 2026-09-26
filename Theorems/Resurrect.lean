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
      pane.dir.contains '\x00' = false ∧
      pane.command.contains '\x00' = false ∧ pane.line = line := by
  unfold parseRow at h
  repeat' (split at h <;> (try simp_all))
  all_goals
    cases h
    simp_all

private theorem parseRows_sound (home : String) (line : Nat) (seen rows : List String)
    (panes : List Pane) (h : parseRows home line seen rows = .ok panes) :
    (∀ pane ∈ panes,
        Linger.Core.Name.sanitize pane.name = pane.name ∧
          pane.dir.contains '\x00' = false ∧ pane.command.contains '\x00' = false) ∧
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
            obtain ⟨canonical, dir, command, -⟩ := parseRow_sound home line _ pane hrow
            refine ⟨?_, ?_, ?_⟩
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact ⟨canonical, dir, command⟩
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
for linger, and contains no NUL in either field that will cross a POSIX boundary. -/
theorem parseSave_valid (home content : String) (panes : List Pane)
    (h : parseSave home content = .ok panes) :
    panes ≠ [] ∧
      (panes.map Pane.name).Nodup ∧
      ∀ pane ∈ panes,
        Linger.Core.Name.sanitize pane.name = pane.name ∧
          Linger.Core.Name.Valid pane.name ∧
          pane.dir.contains '\x00' = false ∧ pane.command.contains '\x00' = false := by
  unfold parseSave at h
  split at h
  · cases h
  · cases h
  · rename_i head tail hrows
    cases h
    obtain ⟨valid, distinct, -⟩ := parseRows_sound home 1 [] _ _ hrows
    refine ⟨by simp, distinct, ?_⟩
    intro pane hp
    obtain ⟨canonical, dir, command⟩ := valid pane hp
    refine ⟨canonical, ?_, dir, command⟩
    rw [← canonical]
    exact Linger.Core.Name.sanitize_valid pane.name

/-- Includes NUL introduced by home expansion, not just NUL in the raw save. -/
theorem parseSave_no_nul (home content : String) (panes : List Pane)
    (h : parseSave home content = .ok panes) (pane : Pane) (hp : pane ∈ panes) :
    pane.dir.contains '\x00' = false ∧ pane.command.contains '\x00' = false :=
  ((parseSave_valid home content panes h).2.2 pane hp).2.2

/-- The allowlist is fixed, with no path, shell, or wildcard matching. -/
theorem mem_allowed (word : String) :
    word ∈ allowed ↔
      word = "vi" ∨
        word = "vim" ∨
        word = "view" ∨
        word = "nvim" ∨
        word = "emacs" ∨
        word = "man" ∨
        word = "less" ∨
        word = "more" ∨
        word = "tail" ∨
        word = "top" ∨ word = "htop" ∨ word = "irssi" ∨ word = "weechat" ∨ word = "mutt" := by
  simp [allowed]

/-- An empty result means that every ASCII-space-delimited piece is empty. -/
theorem firstWord_empty_iff (command : String) :
    firstWord command = "" ↔ ∀ word ∈ command.splitOn " ", word = "" := by
  unfold firstWord
  cases h : (command.splitOn " ").find? (· != "") with
  | none =>
    have hempty := List.find?_eq_none.mp h
    simpa using hempty
  | some word =>
    have hword := List.find?_some h
    have hmem := List.mem_of_find?_eq_some h
    simp only [bne_iff_ne] at hword
    simp only [Option.getD_some, hword, false_iff]
    intro hall
    exact hword (hall word hmem)

/-- The chosen nonempty word is the first such piece, not merely any matching word. -/
theorem firstWord_eq_iff (command word : String) (hne : word ≠ "") :
    firstWord command = word ↔
      ∃ before after,
        command.splitOn " " = before ++ word :: after ∧ ∀ previous ∈ before, previous = "" := by
  have hfind : firstWord command = word ↔ (command.splitOn " ").find? (· != "") = some word := by
    unfold firstWord
    cases h : (command.splitOn " ").find? (· != "") <;> simp [Ne.symm hne]
  rw [hfind, List.find?_eq_some_iff_append]
  simp [hne]

/-- Both directions: opt-in and the first-word policy are necessary and sufficient;
the selected command is the exact original string. -/
theorem restoreCommand_eq_some (restore : Bool) (pane : Pane) (command : String) :
    restoreCommand restore pane = some command ↔
      restore = true ∧ firstWord pane.command ∈ allowed ∧ command = pane.command := by
  cases restore
  · simp [restoreCommand]
  · by_cases h : firstWord pane.command ∈ allowed
    · simpa [restoreCommand, h] using (eq_comm : pane.command = command ↔ command = pane.command)
    · simp [restoreCommand, h]

theorem restoreCommand_off (pane : Pane) : restoreCommand false pane = none := by
  simp [restoreCommand]

/-- Membership pins every output field to one unmodified source record. -/
theorem mem_plan (restore : Bool) (existing : List String) (panes : List Pane)
    (planned : PlannedPane) :
    planned ∈ plan restore existing panes ↔
      planned.pane ∈ panes ∧
        planned.pane.name ∉ existing ∧ planned.command = restoreCommand restore planned.pane := by
  cases planned with
  | mk pane command =>
    simp only [plan, List.mem_map, List.mem_filter]
    constructor
    · rintro ⟨p, ⟨hp, hn⟩, he⟩
      cases he
      exact ⟨hp, by simpa using hn, rfl⟩
    · rintro ⟨hp, hn, hc⟩
      subst command
      exact ⟨pane, ⟨hp, by simpa using hn⟩, rfl⟩

/-- Filtering never reorders or modifies records, including their empty commands. -/
theorem plan_panes (restore : Bool) (existing : List String) (panes : List Pane) :
    (plan restore existing panes).map PlannedPane.pane =
      panes.filter (fun pane => !existing.contains pane.name) := by
  simp [plan, List.map_map, Function.comp_def]

theorem plan_order (restore : Bool) (existing : List String) (panes : List Pane) :
    List.Sublist ((plan restore existing panes).map PlannedPane.pane) panes := by
  rw [plan_panes]
  exact List.filter_sublist

theorem plan_skips_existing (restore : Bool) (existing : List String) (panes : List Pane)
    (planned : PlannedPane) (h : planned ∈ plan restore existing panes) :
    planned.pane.name ∉ existing := ((mem_plan restore existing panes planned).mp h).2.1

/-- The planner requires distinct input names; successful parsing supplies that premise. -/
theorem plan_names_unique (restore : Bool) (existing : List String) (panes : List Pane)
    (distinct : (panes.map Pane.name).Nodup) :
    ((plan restore existing panes).map (fun p => p.pane.name)).Nodup := by
  have h := (plan_order restore existing panes).map Pane.name
  simpa only [List.map_map, Function.comp_def] using h.nodup distinct

theorem plan_command_policy (restore : Bool) (existing : List String) (panes : List Pane)
    (planned : PlannedPane) (h : planned ∈ plan restore existing panes) (command : String) :
    planned.command = some command ↔
      restore = true ∧
        firstWord planned.pane.command ∈ allowed ∧ command = planned.pane.command := by
  rw [((mem_plan restore existing panes planned).mp h).2.2, restoreCommand_eq_some]

/-- A subsequent snapshot containing every planned identity yields no actions,
even if the process-restore choice changes. No distinctness premise is needed. -/
theorem plan_sequential_idempotent (restore nextRestore : Bool) (existing : List String)
    (panes : List Pane) :
    plan nextRestore (existing ++ (plan restore existing panes).map (fun p => p.pane.name)) panes =
      [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro planned h
  obtain ⟨hp, hn, -⟩ := (mem_plan _ _ _ planned).mp h
  apply hn
  by_cases he : planned.pane.name ∈ existing
  · exact List.mem_append_left _ he
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨{ pane := planned.pane, command := restoreCommand restore planned.pane }, ?_, rfl⟩
    exact (mem_plan _ _ _ _).mpr ⟨hp, he, rfl⟩

end Tools.Resurrect
