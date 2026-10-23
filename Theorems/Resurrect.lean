module

import all Linger.Tools.Resurrect
import all Linger.Core.Name
import all Linger.Core.Vt
import Theorems.Name
import all Theorems.Vt
import all Theorems.Checkpoint

/-! Kernel-checked importer contracts.

The planner sees one existing-name snapshot. Sequential idempotence assumes that
the next snapshot includes every planned name; it says nothing about concurrent
creation or whether a caller successfully creates sessions or enters directories.
-/

namespace Linger.Tools.Resurrect

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

/-- Browsing preserves the complete name/cwd projection, including order and
multiplicity, independently of every display-only source field. -/
theorem catalogRows_common (content : String) (panes : List Pane) :
    (catalogRows content panes).map (fun row => (row.lookup "name", row.lookup "directory")) =
      (common panes).map (fun field => (some field.1, some field.2)) := by
  simp only [catalogRows, common, List.map_map]
  rfl

/-- A catalog row retains the source line used to diagnose an import failure. -/
theorem catalogRows_lines (content : String) (panes : List Pane) :
    (catalogRows content panes).map (fun row => row.lookup "line") =
      panes.map (fun pane => some (toString pane.line)) := by
  simp only [catalogRows, List.map_map]
  rfl

/-- Saved panes use the shared resumable badge, independently of saved commands
or whatever state the live tmux server has reached since the save. -/
theorem catalogRows_status (content : String) (panes : List Pane) (row : List (String × String))
    (member : row ∈ catalogRows content panes) :
    row.lookup "status" = some (Linger.Core.Status.name .resumable) := by
  unfold catalogRows at member
  obtain ⟨pane, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- Window titles, directories and commands cannot introduce terminal controls
into the human description, even though action metadata remains unmodified. -/
theorem catalogRows_printable (content : String) (panes : List Pane) (row : List (String × String))
    (member : row ∈ catalogRows content panes) (text : String)
    (description : row.lookup "cmd" = some text) (c : Char) (character : c ∈ text.toList) :
    32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) := by
  unfold catalogRows at member
  obtain ⟨pane, _, rfl⟩ := List.mem_map.mp member
  simp only [List.lookup_cons, beq_self_eq_true] at description
  change some (diagnostic _) = some text at description
  cases description
  exact diagnostic_printable _ c character

/-- Every description ends with the printable saved foreground command line,
falling back to the command name when the line is unavailable. -/
theorem catalogRows_command (content : String) (panes : List Pane) (row : List (String × String))
    (member : row ∈ catalogRows content panes) (command savedCommand text : String)
    (commandField : row.lookup "command" = some command)
    (savedField : row.lookup "saved-command" = some savedCommand)
    (description : row.lookup "cmd" = some text) :
    List.IsSuffix (diagnostic (if savedCommand.isEmpty then command else savedCommand)).toList
      text.toList := by
  unfold catalogRows at member
  obtain ⟨pane, _, rfl⟩ := List.mem_map.mp member
  change some (preparePane content panes pane).details.command = some command at commandField
  change
    some (preparePane content panes pane).details.savedCommand = some savedCommand at savedField
  cases commandField
  cases savedField
  simp only [List.lookup_cons, beq_self_eq_true] at description
  change some (diagnostic _) = some text at description
  cases description
  let foreground :=
    if (preparePane content panes pane).details.savedCommand.isEmpty then
      (preparePane content panes pane).details.command
    else (preparePane content panes pane).details.savedCommand
  change
    List.IsSuffix (diagnostic foreground).toList
      (diagnostic (if foreground.isEmpty then _ else _)).toList
  by_cases empty : foreground.isEmpty = true
  · have blank : foreground = "" := String.isEmpty_iff.mp empty
    simp [blank, diagnostic]
  · simp only [empty, Bool.false_eq_true, ite_false]
    change List.IsSuffix (diagnostic foreground).toList (diagnostic (_ ++ foreground)).toList
    simp only [diagnostic, String.toList_map, String.toList_append, List.map_append]
    exact List.suffix_append _ _

/-- A successful selection has exactly the displayed identity, directory and
source line; canonicalization is a guard, never a retargeting operation. -/
theorem selectedPane_exact (name dir : String) (line : Nat)
    (canonical : Linger.Core.Name.sanitize name = name) (nulFree : dir.contains '\x00' = false) :
    selectedPane name dir line = some { name, dir, line } := by
  simp [selectedPane, canonical, nulFree]

/-- Transported selection data cannot bypass the session-name or NUL guards. -/
theorem selectedPane_valid (name dir : String) (line : Nat) (pane : Pane)
    (selected : selectedPane name dir line = some pane) :
    pane = { name, dir, line } ∧
      Linger.Core.Name.Valid pane.name ∧ pane.dir.contains '\x00' = false := by
  unfold selectedPane at selected
  split at selected
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at guard
    cases selected
    exact ⟨rfl, (Linger.Core.Name.sanitize_eq_self_iff name).mp guard.1, guard.2⟩
  · cases selected

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

theorem projectName_native (name : String) (valid : Linger.Core.Name.Valid name) :
    projectName (encodeName name) "0" "0" = some name := by
  have hprefix : (encodeName name).startsWith "linger=" = true := by
    simp [encodeName, String.startsWith_string_iff, String.toList_append]
  unfold projectName
  rw [ite_eq_left hprefix, encodeName_reversible name valid]
  simp [Linger.Core.Name.sanitize_eq_self_of_valid name valid]

/-- Reserved names cannot be silently projected after a topology change. -/
theorem projectName_reserved_topology (session window pane : String)
    (reserved : session.startsWith "linger=" = true) (changed : window ≠ "0" ∨ pane ≠ "0") :
    projectName session window pane = none := by
  rcases changed with changed | changed <;> simp [projectName, reserved, changed]

theorem projectName_foreign (session window pane : String)
    (foreign : session.startsWith "linger=" = false) :
    projectName session window pane = some (session ++ "-w" ++ window ++ "-p" ++ pane) := by
  simp [projectName, foreign]

theorem parseRow_sound (home : String) (line : Nat) (fields : List String) (pane : Pane)
    (h : parseRow home line fields = .ok (some pane)) :
    Linger.Core.Name.sanitize pane.name = pane.name ∧
      pane.dir.contains '\x00' = false ∧ pane.line = line := by
  unfold parseRow at h
  grind

/-- Saved command metadata must have its sentinel and contain no NUL. -/
theorem parseRow_command_valid (home : String) (line : Nat)
    (session window field3 field4 pane field6 cwd field8 field9 savedCommand : String)
    (parsed : Pane)
    (h :
      parseRow home line
          ["pane", session, window, field3, field4, pane, field6, cwd, field8, field9,
            savedCommand] =
        .ok (some parsed)) :
    savedCommand.startsWith ":" = true ∧ savedCommand.contains '\x00' = false := by
  unfold parseRow at h
  grind

/-- Activity and window flags do not alter a pane's saved data or validation. -/
theorem parseRow_metadata_irrelevant (home : String) (line : Nat) (session window pane cwd : String)
    (windowActive windowFlags paneTitle paneActive currentCommand savedCommand : String)
    (otherWindowActive otherWindowFlags otherPaneActive : String) :
    parseRow home line
        ["pane", session, window, windowActive, windowFlags, pane, paneTitle, cwd, paneActive,
          currentCommand, savedCommand] =
      parseRow home line
        ["pane", session, window, otherWindowActive, otherWindowFlags, pane, paneTitle, cwd,
          otherPaneActive, currentCommand, savedCommand] := by
  rfl

/-- Successful parsing retains the exact source identity, title and foreground
command. Only the command-line sentinel is removed. -/
theorem parseRow_metadata (home : String) (line : Nat)
    (session window active flags index title cwd paneActive command savedCommand : String)
    (pane : Pane)
    (h :
      parseRow home line
          ["pane", session, window, active, flags, index, title, cwd, paneActive, command,
            savedCommand] =
        .ok (some pane)) :
    pane.details =
      { session, window, index, title, command,
        savedCommand := (savedCommand.drop 1).toString } := by
  unfold parseRow at h
  grind

/-- Each layout token contributes at most one leaf; parsing never multiplies
input-controlled layout nodes. -/
theorem layoutLeaves_bounded (tokens : List String) :
    (layoutLeaves tokens).length ≤ tokens.length := by
  induction tokens with
  | nil => simp [layoutLeaves]
  | cons size rest ih =>
    simp only [layoutLeaves]
    split
    · split <;> simp_all
      omega
    · simpa using Nat.le_trans ih (Nat.le_succ _)

/-- The public layout adapter inherits the bound on its delimiter-separated tokens. -/
theorem layoutSizes_bounded (layout : String) :
    (layoutSizes layout).length ≤
      ((layout.map fun c => if ['{', '}', '[', ']'].contains c then ',' else c).splitOn ",").length :=
  layoutLeaves_bounded _

/-- Window layout enrichment cannot retarget a pane, change its directory, or
replace its command and title metadata. -/
theorem preparePane_preserves (content : String) (panes : List Pane) (pane : Pane) :
    (preparePane content panes pane).name = pane.name ∧
      (preparePane content panes pane).dir = pane.dir ∧
      (preparePane content panes pane).line = pane.line ∧
      (preparePane content panes pane).details.session = pane.details.session ∧
      (preparePane content panes pane).details.window = pane.details.window ∧
      (preparePane content panes pane).details.index = pane.details.index ∧
      (preparePane content panes pane).details.title = pane.details.title ∧
      (preparePane content panes pane).details.command = pane.details.command ∧
      (preparePane content panes pane).details.savedCommand = pane.details.savedCommand := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- An accepted member uses the validated pane's exact source triple, and requires
that this triple still projects to its canonical linger identity. -/
theorem contentMember_exact (pane : Pane) (member : String)
    (h : contentMember pane = some member) :
    Linger.Core.Name.sanitize pane.name = pane.name ∧
      projectName pane.details.session pane.details.window pane.details.index = some pane.name ∧
      member =
        s!"./pane_contents/pane-{pane.details.session}:{pane.details.window}.{pane.details.index}" := by
  unfold contentMember at h
  split at h
  · rename_i guard
    simp only [Bool.and_eq_true, beq_iff_eq] at guard
    cases h
    exact ⟨guard.1, guard.2, rfl⟩
  · cases h

/-- Capture retention is fixed at eight MiB per pane. -/
theorem captureLimit_eq : captureLimit = 8 * 1024 * 1024 := by rfl

/-- Newline conversion can at most double the fixed capture byte budget, including
for content containing only newlines. -/
theorem captureBytes_bounded (contents : String) :
    (captureBytes contents).length ≤ 2 * captureLimit := by
  have expand (bytes : List UInt8) :
      (bytes.flatMap fun b => if b == 10 then [13, 10] else [b]).length ≤ 2 * bytes.length := by
    induction bytes with
    | nil => simp
    | cons b bs ih =>
      simp only [List.flatMap_cons, List.length_append]
      split <;> simp_all <;> omega
  dsimp only [captureBytes]
  split
  · have := expand (contents.toUTF8.toList.take captureLimit).dropLast
    have := List.length_take_le captureLimit contents.toUTF8.toList
    simp only [List.length_dropLast] at *
    omega
  · exact Nat.le_trans (expand _) (Nat.mul_le_mul_left 2 (List.length_take_le _ _))

/-- The notice displays the saved command line, falls back to its name, and adds
no output when both are absent. Command text passes through the printable adapter. -/
theorem commandNotice_eq (details : Details) :
    commandNotice details =
      let command :=
        if details.savedCommand.isEmpty then details.command else details.savedCommand
      if command.isEmpty then ""
      else
        "\x1b[0m\x1b(B\x0f\x1b[?7h\r\nSaved foreground command: " ++ diagnostic command ++ "\r\n" :=
  rfl

/-- Notice replay has 43 framing bytes and at most four bytes per input character,
including Unicode. Sanitization preserves character count. -/
theorem commandNotice_bounded (details : Details) :
    (commandNotice details).toUTF8.toList.length ≤
      43 + 4 * (details.command.length + details.savedCommand.length) := by
  have encode (s : String) : s.utf8ByteSize ≤ 4 * s.length := by
    have bound (cs : List Char) : cs.utf8Encode.size ≤ 4 * cs.length := by
      induction cs with
      | nil => simp
      | cons c cs ih =>
        have hc := Char.utf8Size_le_four c
        rw [List.utf8Encode_cons, ByteArray.size_append]
        simp only [List.utf8Encode_singleton, List.size_toByteArray,
          String.length_utf8EncodeChar, List.length_cons]
        omega
    simpa [String.length_toList] using bound s.toList
  have count (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
    have loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
        (ByteArray.toList.loop bs i r).length = r.length + (bs.size - i) := by
      fun_induction ByteArray.toList.loop bs i r with simp_all <;> omega
    simpa [ByteArray.toList] using loop s.toUTF8 0 []
  rw [count]
  let command := if details.savedCommand.isEmpty then details.command else details.savedCommand
  have chosen : command.length ≤ details.command.length + details.savedCommand.length := by
    dsimp only [command]
    split <;> omega
  have encoded := encode (diagnostic command)
  simp only [diagnostic, String.length_map] at encoded
  change (diagnostic command).utf8ByteSize ≤ 4 * command.length at encoded
  change
    (if command.isEmpty then ""
      else "\x1b[0m\x1b(B\x0f\x1b[?7h\r\nSaved foreground command: " ++ diagnostic command ++ "\r\n").utf8ByteSize ≤ _
  by_cases empty : command.isEmpty = true
  · simp only [empty, ite_true, String.utf8ByteSize_empty]
    omega
  · simp only [empty, Bool.false_eq_true, ite_false]
    rw [String.utf8ByteSize_append, String.utf8ByteSize_append]
    change 41 + (diagnostic command).utf8ByteSize + 2 ≤ _
    omega

/-- Captured parser state is quiesced before the notice is fed as terminal output,
and the resulting checkpoint is quiesced before it can be persisted. -/
theorem checkpoint_notice (pane : Pane) (contents : Option String) :
    (checkpoint pane contents).vt =
      (((Linger.Core.Vt.Vt.init pane.details.cols pane.details.rows).feed
            (captureBytes (contents.getD ""))).quiesce.feed
          (commandNotice pane.details).toUTF8.toList).quiesce :=
  rfl

/-- Imported terminal states are built solely through the public live-state
constructors and inherit the terminal's proved invariants. -/
theorem checkpoint_live (pane : Pane) (contents : Option String) :
    Linger.Core.Vt.LiveReachableVt (checkpoint pane contents).vt :=
  .quiesce (.feed (.quiesce (.feed (.init _ _) _)) _)

/-- Persisting an imported pane reads back the exact screen, scrollback, cwd and
metadata, including when the capture ended inside a terminal escape sequence. -/
theorem checkpoint_roundtrip (pane : Pane) (contents : Option String) :
    Linger.Core.Checkpoint.loadBytes (Linger.Core.Checkpoint.saveBytes (checkpoint pane contents)) =
      some (checkpoint pane contents) := by
  rw [Linger.Core.Checkpoint.loadBytes_saveBytes_live _ (checkpoint_live pane contents)]
  simp only [checkpoint, Linger.Core.Vt.Vt.quiesce]

/-- Every checkpoint records the exact saved command and distinguishes missing
captures from empty captures. Commands are data in labels. -/
theorem checkpoint_metadata (pane : Pane) (contents : Option String) :
    (checkpoint pane contents).cwd = pane.dir ∧
      (checkpoint pane contents).labels.lookup "tmux.command" = some pane.details.command ∧
      (checkpoint pane contents).labels.lookup "tmux.saved-command" = some pane.details.savedCommand ∧
      (checkpoint pane contents).labels.lookup "tmux.capture" =
        some (if contents.isSome then "saved" else "none") := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Selection carries the displayed pane metadata through the same exact-name
and NUL-free-directory guards as ordinary saved selections. -/
theorem selectedPane_metadata (name dir : String) (line : Nat) (details : Details)
    (canonical : Linger.Core.Name.sanitize name = name) (nulFree : dir.contains '\x00' = false) :
    selectedPane name dir line details = some { name, dir, line, details } := by
  simp [selectedPane, canonical, nulFree]

/-- A non-pane row contributes no pane, whatever its remaining fields contain. -/
theorem parseRow_other (home : String) (line : Nat) (fields : List String)
    (ignored : fields.head? ≠ some "pane") : parseRow home line fields = .ok none := by
  simp [parseRow, ignored]

theorem parseRows_sound (home : String) (line : Nat) (seen rows : List String) (panes : List Pane)
    (h : parseRows home line seen rows = .ok panes) :
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

theorem parseRow_home_independent (home : String) (line : Nat) (fields : List String)
    (parsed : Option Pane) (h : parseRow "\x00" line fields = .ok parsed) :
    parseRow home line fields = .ok parsed := by
  unfold parseRow at h ⊢
  repeat' (split at h <;> (try simp_all [String.contains_char_eq, String.toList_append]))

theorem parseRows_home_independent (home : String) (line : Nat) (seen rows : List String)
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

theorem representableDir_iff (dir : String) :
    representableDir dir = true ↔
      dir.startsWith "/" = true ∧
        dir.endsWith " " = false ∧
        dir.contains "  " = false ∧
        ∀ c ∈ dir.toList,
          c ≠ '\\' ∧
            c ≠ '\x00' ∧
            c ≠ '\t' ∧ c ≠ '\n' ∧ c ≠ '\r' ∧ c ≠ '*' ∧ c ≠ '?' ∧ c ≠ '[' ∧ c ≠ '#' := by
  simp [representableDir, List.any_eq_false, and_assoc]

theorem renderSave_checked (fields : List (String × String)) (content : String)
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
theorem renderSave_directories (fields : List (String × String)) (content : String)
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

end Linger.Tools.Resurrect
