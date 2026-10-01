module

public import Tools.Resurrect
import all Tools.Resurrect
import all Linger.Core.Name
import Theorems.Name

public section

/-! Kernel-checked importer contracts.

The planner sees one existing-name snapshot. Sequential idempotence assumes that
the next snapshot includes every planned name; it says nothing about concurrent
creation or whether a caller successfully creates sessions or enters directories.
-/

namespace Tools.Resurrect

/-- Error text excludes C0, DEL and C1, including controls from filesystem errors. -/
theorem diagnostic_printable (message : String) (c : Char) (hc : c ∈ (diagnostic message).toList) :
    32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) := by
  rw [diagnostic, String.toList_map] at hc
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp hc
  split
  · rename_i h
    simpa using h
  · decide

/-- Already printable diagnostics retain every character, including Unicode and spaces. -/
theorem diagnostic_eq_self (message : String)
    (h : ∀ c ∈ message.toList, 32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat)) :
    diagnostic message = message := by
  apply String.toList_injective
  simp only [diagnostic, String.toList_map]
  calc
    _ = message.toList.map id :=
      List.map_congr_left
        (by
          intro c hc
          simp [h c hc])
    _ = _ := List.map_id _

/-- Common fields retain multiplicity and order while discarding line numbers. -/
theorem common_cons (pane : Pane) (panes : List Pane) :
    common (pane :: panes) = (pane.name, pane.dir) :: common panes := by rfl

/-- Native identity encoding reverses on the entire valid name alphabet. -/
theorem encodeName_reversible (name : String) (valid : Linger.Core.Name.Valid name) :
    ((encodeName name).drop 7).toString.map (fun c => if c == '~' then '.' else c) = name := by
  obtain ⟨-, -, alphabet, -⟩ := valid
  have htilde : ∀ c ∈ name.toList, c ≠ '~' := by
    intro c hc he
    subst c
    have := alphabet '~' hc
    simp [Linger.Core.Name.okChar] at this
  apply String.toList_injective
  simp only [String.Slice.toString_eq, String.toList_map, String.toList_copy_drop, encodeName,
    String.toList_append]
  change
    ((['l', 'i', 'n', 'g', 'e', 'r', '='] ++
                name.toList.map (fun c => if c == '.' then '~' else c)).drop
            7).map
        (fun c => if c == '~' then '.' else c) =
      name.toList
  simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero, List.map_map]
  calc
    _ = name.toList.map id :=
      List.map_congr_left
        (by
          intro c hc
          by_cases hd : c = '.' <;> simp [hd, htilde c hc])
    _ = _ := List.map_id _

private theorem projectName_native (name : String) (valid : Linger.Core.Name.Valid name) :
    projectName (encodeName name) "0" "0" = some name := by
  have hprefix : (encodeName name).startsWith "linger=" = true := by
    simp [encodeName, String.startsWith_string_iff, String.toList_append]
  unfold projectName
  rw [ite_eq_left hprefix, encodeName_reversible name valid]
  simp [Linger.Core.Name.sanitize_eq_self_of_valid name valid]

/-- Reserved names cannot be silently projected after a topology change. -/
private theorem projectName_reserved_topology (session window pane : String)
    (reserved : session.startsWith "linger=" = true) (changed : window ≠ "0" ∨ pane ≠ "0") :
    projectName session window pane = none := by
  rcases changed with changed | changed <;> simp [projectName, reserved, changed]

private theorem projectName_foreign (session window pane : String)
    (foreign : session.startsWith "linger=" = false) :
    projectName session window pane = some (session ++ "-w" ++ window ++ "-p" ++ pane) := by
  simp [projectName, foreign]

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

/-- Changing ignored pane fields and well-formed, NUL-free saved commands changes
neither the parsed pane nor errors from the fixed identity and directory fields. -/
private theorem parseRow_metadata_irrelevant (home : String) (line : Nat)
    (session window pane cwd : String)
    (windowActive windowFlags paneTitle paneActive currentCommand savedCommand : String)
    (otherWindowActive otherWindowFlags otherPaneTitle otherPaneActive otherCurrentCommand
      replacement : String)
    (hs : savedCommand.startsWith ":" = true) (hr : replacement.startsWith ":" = true)
    (hns : savedCommand.contains '\x00' = false) (hnr : replacement.contains '\x00' = false) :
    parseRow home line
        ["pane", session, window, windowActive, windowFlags, pane, paneTitle, cwd, paneActive,
          currentCommand, savedCommand] =
      parseRow home line
        ["pane", session, window, otherWindowActive, otherWindowFlags, pane, otherPaneTitle, cwd,
          otherPaneActive, otherCurrentCommand, replacement] := by
  simp [parseRow, hs, hr, hns, hnr]

/-- A non-pane row contributes no pane, whatever its remaining fields contain. -/
private theorem parseRow_other (home : String) (line : Nat) (fields : List String)
    (ignored : fields.head? ≠ some "pane") : parseRow home line fields = .ok none := by
  simp [parseRow, ignored]

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
    exact ⟨canonical, (Linger.Core.Name.sanitize_eq_self_iff _).mp canonical, dir⟩

/-- Includes NUL introduced by home expansion, not just NUL in the raw save. -/
theorem parseSave_no_nul (home content : String) (panes : List Pane)
    (h : parseSave home content = .ok panes) (pane : Pane) (hp : pane ∈ panes) :
    pane.dir.contains '\x00' = false := ((parseSave_valid home content panes h).2.2 pane hp).2.2

private theorem parseRow_home_independent (home : String) (line : Nat) (fields : List String)
    (parsed : Option Pane) (h : parseRow "\x00" line fields = .ok parsed) :
    parseRow home line fields = .ok parsed := by
  unfold parseRow at h ⊢
  repeat' (split at h <;> (try simp_all [String.contains_char_eq, String.toList_append]))

private theorem parseRows_home_independent (home : String) (line : Nat) (seen rows : List String)
    (panes : List Pane) (h : parseRows "\x00" line seen rows = .ok panes) :
    parseRows home line seen rows = .ok panes := by
  induction rows generalizing line seen panes with
  | nil => simpa [parseRows] using h
  | cons row rows ih =>
    simp only [parseRows] at h ⊢
    cases hrow : parseRow "\x00" line (row.splitOn "\t") with
    | error error => simp [hrow] at h
    | ok result =>
      rw [parseRow_home_independent home line _ result hrow]
      cases result with
      | none => exact ih (line + 1) seen panes (by simpa [hrow] using h)
      | some pane =>
        simp only [hrow] at h
        split at h
        · cases h
        · rename_i fresh
          simp only [fresh]
          cases hrest : parseRows "\x00" (line + 1) (pane.name :: seen) rows with
          | error error => simp [hrest, Except.map] at h
          | ok rest =>
            rw [ih (line + 1) (pane.name :: seen) rest hrest]
            simpa [hrest, Except.map] using h

/-- A successful parse with a NUL home performed no home expansion, so it
produces exactly the same panes for any actual home. -/
theorem parseSave_home_independent (home content : String) (panes : List Pane)
    (h : parseSave "\x00" content = .ok panes) : parseSave home content = .ok panes := by
  unfold parseSave at h ⊢
  split at h
  · cases h
  · cases h
  · rename_i pane rest parsed
    cases h
    rw [parseRows_home_independent home 1 [] _ _ parsed]

private theorem representableDir_iff (dir : String) :
    representableDir dir = true ↔
      dir.startsWith "/" = true ∧
        dir.endsWith " " = false ∧
        dir.contains "  " = false ∧
        ∀ c ∈ dir.toList,
          c ≠ '\\' ∧
            c ≠ '\x00' ∧
            c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '*' ∧ c ≠ '?' ∧ c ≠ '[' ∧ c ≠ '#' := by
  simp [representableDir, List.any_eq_false, and_assoc]

private theorem renderSave_checked (fields : List (String × String)) (content : String)
    (h : renderSave fields = .ok content) :
    ∃ panes, parseSave "\x00" content = .ok panes ∧ common panes = fields := by
  unfold renderSave at h
  split at h
  · cases h
  · dsimp only at h
    generalize text_eq : String.join (fields.map _) ++ _ = text at h
    cases parsed : parseSave "\x00" text with
    | error error => simp [parsed] at h
    | ok panes =>
      simp only [parsed] at h
      split at h
      · rename_i same
        cases h
        exact ⟨panes, parsed, by simpa using same⟩
      · cases h

/-- Generation cannot hide an unsupported cwd behind the parse certificate. -/
private theorem renderSave_directories (fields : List (String × String)) (content : String)
    (h : renderSave fields = .ok content) : ∀ field ∈ fields, representableDir field.2 = true := by
  unfold renderSave at h
  split at h
  · cases h
  · rename_i checked
    intro field member
    simpa using (List.find?_eq_none.mp checked) field member

/-- The generated common fields inherit the parser's complete validity contract. -/
theorem renderSave_valid (fields : List (String × String)) (content : String)
    (h : renderSave fields = .ok content) :
    fields ≠ [] ∧
      (fields.map Prod.fst).Nodup ∧
      ∀ field ∈ fields,
        Linger.Core.Name.sanitize field.1 = field.1 ∧
          Linger.Core.Name.Valid field.1 ∧ field.2.contains '\x00' = false := by
  obtain ⟨panes, parsed, same⟩ := renderSave_checked fields content h
  obtain ⟨nonempty, distinct, valid⟩ := parseSave_valid "\x00" content panes parsed
  rw [← same]
  refine ⟨?_, ?_, ?_⟩
  · simpa [common] using nonempty
  · simpa [common, List.map_map, Function.comp_def] using distinct
  · intro field member
    change field ∈ panes.map (fun pane => (pane.name, pane.dir)) at member
    obtain ⟨pane, hp, equal⟩ := List.mem_map.mp member
    subst field
    exact valid pane hp

theorem renderSave_empty (content : String) : renderSave [] ≠ .ok content := by
  intro h
  exact (renderSave_valid [] content h).1 rfl

/-- Successful generation certifies the actual serialized text, including its
delimiters, row layout, names and directories, for any import home. -/
theorem renderSave_roundtrip (home : String) (fields : List (String × String)) (content : String)
    (h : renderSave fields = .ok content) :
    ∃ panes, parseSave home content = .ok panes ∧ common panes = fields := by
  obtain ⟨panes, parsed, same⟩ := renderSave_checked fields content h
  exact ⟨panes, parseSave_home_independent home content panes parsed, same⟩

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
