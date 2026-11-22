module

public import Linger.App.CoreCode.Serve
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Serve
import all Linger.Display.CoreCode.Listing
import all Terminal.CoreCode.Vt
import all Terminal.CoreCode.Render
import all Terminal.Proofs.Vt

/-! # A session's terminal as rows: one renderer, exact updates, logs that count what they drop

A reader's line is the row as `capture` prints it, `Render.rowText`, with the runs of its
characters' pens, which expand to exactly those pens and are maximal; a screen's lines, each with a
line feed, are exactly what `capture` prints of a live terminal. The update from one screen to
another carries exactly the lines that changed, the numbers of those that went and the cursor and
title when they changed, and brings a reader holding the first to the second. A log's reading
after an entry is its reading before, the entry after it, with at most one place turned into a
gap, and a gap where an entry was dropped is counted, so no entry is dropped unseen. -/

namespace Linger.App.Serve

open Terminal.Vt

/-! ## Runs of pens -/

/-- The runs of a list of pens, one more pen in front. -/
theorem Span.runs_cons (pen : Pen) (pens : List Pen) :
    Span.runs (pen :: pens) =
      match Span.runs pens with
      | run :: rest =>
        if run.pen = pen then { run with length := run.length + 1 } :: rest
        else ⟨1, pen⟩ :: run :: rest
      | [] => [⟨1, pen⟩] := rfl

/-- **Runs expand to exactly the pens they were cut from.** -/
theorem Span.expand_runs : ∀ pens : List Pen, Span.expand (Span.runs pens) = pens
  | [] => rfl
  | pen :: pens => by
    have ih := Span.expand_runs pens
    rw [Span.runs_cons]
    split
    · rename_i run rest same
      rw [same] at ih
      split
      · rename_i samePen
        simp only [Span.expand, List.flatMap_cons] at ih ⊢
        rw [← ih, samePen, List.replicate_succ, List.cons_append]
      · simp only [Span.expand, List.flatMap_cons] at ih ⊢
        rw [← ih]
        simp
    · rename_i none
      rw [none] at ih
      simp only [Span.expand, List.flatMap_cons, List.flatMap_nil] at ih ⊢
      simp [← ih]

/-- A run cut from pens covers a character. -/
theorem Span.runs_positive : ∀ pens : List Pen, ∀ s ∈ Span.runs pens, 0 < s.length
  | [] => by simp [Span.runs]
  | pen :: pens => by
    have ih := Span.runs_positive pens
    rw [Span.runs_cons]
    split
    · rename_i run rest same
      rw [same] at ih
      split
      · intro s member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · simp
        · exact ih s (List.mem_cons_of_mem _ member)
      · intro s member
        simp only [List.mem_cons] at member
        rcases member with rfl | rfl | member
        · simp
        · exact ih _ List.mem_cons_self
        · exact ih s (List.mem_cons_of_mem _ member)
    · intro s member
      simp only [List.mem_singleton] at member
      subst member
      simp

/-- No two runs in turn share a pen, for runs cut from pens. -/
theorem Span.runs_distinct :
    ∀ pens : List Pen, ∀ pair ∈ (Span.runs pens).zip (Span.runs pens).tail, pair.1.pen ≠ pair.2.pen
  | [] => by simp [Span.runs]
  | pen :: pens => by
    have ih := Span.runs_distinct pens
    rw [Span.runs_cons]
    split
    · rename_i run rest same
      rw [same] at ih
      split
      · rename_i samePen
        cases rest with
        | nil => simp
        | cons next rest =>
          intro pair member
          simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at member ih
          rcases member with rfl | member
          · have := ih (run, next) (.inl rfl)
            exact this
          · exact ih pair (.inr member)
      · rename_i differs
        intro pair member
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at member
        rcases member with rfl | member
        · exact fun h => differs h.symm
        · exact ih pair (by simpa using member)
    · simp

/-- **Runs cut from pens are maximal.** -/
theorem Span.runs_compact (pens : List Pen) : Span.Compact (Span.runs pens) :=
  ⟨Span.runs_positive pens, Span.runs_distinct pens⟩

/-! ## One renderer -/

/-- A line's text is the row as `capture` prints it. -/
theorem Line.of_text (row : Row) : (Line.of row).text = Terminal.Render.rowText row := rfl

/-- A line's runs expand to the pens of its row's characters (`Line.pens`). -/
theorem Line.of_spans (row : Row) : Span.expand (Line.of row).spans = Line.pens row :=
  Span.expand_runs _

/-- A line's runs are maximal. -/
theorem Line.of_compact (row : Row) : Span.Compact (Line.of row).spans := Span.runs_compact _

/-- A screen's lines are its rows, each as `Line.of` renders it, top first. -/
theorem Screen.render_lines (v : Vt) :
    (Screen.render v).lines = (List.range v.rowCount).map fun y => Line.of (v.getRow y) := rfl

/-- A screen's cursor is the terminal's, and shows when the terminal shows it. -/
theorem Screen.render_cursor (v : Vt) :
    (Screen.render v).cursor =
      { x := v.cursorPos.1, y := v.cursorPos.2, visible := v.getModes.cursorVisible } := rfl

/-- A screen's title is the terminal's window title, as clean text. -/
theorem Screen.render_title (v : Vt) :
    (Screen.render v).title = v.windowTitle.map Terminal.Render.textChar := rfl

/-- The rows of an array, read one index after another up to its size, are the array's. -/
theorem range_getD (a : Array Row) (d : Row) :
    (List.range a.size).map (fun y => a.getD y d) = a.toList := by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    simp only [List.length_map, List.length_range] at h₁
    simp [Array.getD, h₁]

/-- **A live terminal's lines, each with a line feed, are what `capture` prints.** -/
theorem Screen.render_capture (v : Vt) (hv : LiveReachableVt v) :
    ((Screen.render v).lines.map fun line => line.text ++ [0x0A]).flatten =
      Terminal.Render.screenText v := by
  have size : v.grid.size = v.rows := (renderable_of_liveReachable hv).main.1
  rw [Screen.render_lines, List.map_map]
  unfold Terminal.Render.screenText
  rw [List.flatMap_def]
  congr 1
  have rows : v.rowCount = v.grid.size := by
    rw [size]; rfl
  rw [rows, ← range_getD v.grid (blankRow v.cols v.pen), List.map_map]
  rfl

/-- A fresh terminal of one cell prints, as `capture`, a line of nothing. -/
theorem screenText_init_one : Terminal.Render.screenText (Vt.init 1 1) = [0x0A] := by decide +kernel

/-- A second renderer that keeps the trailing blank of a fresh terminal of one cell writes the
blank. -/
theorem untrimmed_init_one :
    ((Screen.untrimmed (fun (v : Vt) => (List.range v.rowCount).map v.getRow)
              (Vt.init 1 1)).lines.map
          fun line => line.text ++ [0x0A]).flatten =
      [0x20, 0x0A] := by
  decide +kernel

/-! ## Exact updates -/

/-- A list of pairs whose keys are distinct holds a pair exactly where looking up its key finds
its value. -/
theorem lookup_iff_mem {β : Type} :
    ∀ (pairs : List (Nat × β)),
      (pairs.map (·.1)).Nodup → ∀ key value, pairs.lookup key = some value ↔ (key, value) ∈ pairs
  | [], _, key, value => by simp [List.lookup]
  | (k, v) :: rest, distinct, key, value => by
    simp only [List.map_cons, List.nodup_cons] at distinct
    obtain ⟨fresh, distinct⟩ := distinct
    have ih := lookup_iff_mem rest distinct key value
    by_cases here : key = k
    · subst here
      simp only [List.lookup, beq_self_eq_true, Option.some.injEq, List.mem_cons, Prod.mk.injEq,
        true_and]
      constructor
      · intro same
        exact .inl same.symm
      · intro member
        rcases member with same | member
        · exact same.symm
        · exact absurd (List.mem_map.mpr ⟨_, member, rfl⟩) fresh
    · have : (key == k) = false := by simpa using here
      simp only [List.lookup, this, List.mem_cons, Prod.mk.injEq, here, false_and, false_or]
      exact ih

/-- The lines that changed, by number: each line `latest` holds under a number that `told` holds
otherwise or not at all. -/
theorem changes_mem (told latest : Screen) (y : Nat) (line : Line) :
    (y, line) ∈ (Screen.changes told latest).lines ↔
      latest.lines[y]? = some line ∧ told.lines[y]? ≠ some line := by
  simp only [Screen.changes, List.mem_map, List.mem_filter, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨l, i, ⟨member, differs⟩, rfl, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?] at member
    exact ⟨member, by simpa using differs⟩
  · rintro ⟨holds, differs⟩
    exact ⟨line, y, ⟨List.mem_zipIdx_iff_getElem?.mpr holds, by simpa using differs⟩, rfl, rfl⟩

/-- The numbers of the lines that changed are distinct. -/
theorem changes_nodup (told latest : Screen) :
    ((Screen.changes told latest).lines.map (·.1)).Nodup := by
  have whole : (latest.lines.zipIdx.map (·.2)).Nodup := by
    rw [List.zipIdx_map_snd]
    exact List.nodup_range'
  have kept :=
    whole.sublist
      (List.Sublist.map (·.2)
        (List.filter_sublist (p := fun (x : Line × Nat) => told.lines[x.2]? != some x.1) (l :=
          latest.lines.zipIdx)))
  simpa [Screen.changes, List.map_map, Function.comp_def] using kept

/-- **The update from `told` to `latest` is exact.** -/
theorem changes_exact (told latest : Screen) :
    Screen.Exact told latest (Screen.changes told latest) := by
  have member := changes_mem told latest
  have distinct := changes_nodup told latest
  have removed :
    ∀ y,
      y ∈ (Screen.changes told latest).removed ↔
        told.lines[y]?.isSome ∧ latest.lines[y]? = none := by
    intro y
    simp only [Screen.changes, List.mem_filter, List.mem_range, decide_eq_true_eq,
      List.getElem?_eq_none_iff]
    have : told.lines[y]?.isSome = true ↔ y < told.lines.length := by simp
    rw [this]
  refine ⟨?_, ?_, ?_, member, distinct, removed, ?_, ?_, ?_⟩
  · intro y
    unfold Screen.View.line
    split
    · rename_i gone
      exact ((removed y).mp gone).2.symm
    · rename_i kept
      cases found : (Screen.changes told latest).lines.lookup y with
      | some line =>
        have := (member y line).mp ((lookup_iff_mem _ distinct y line).mp found)
        simp [this.1]
      | none =>
        simp only [Option.none_or]
        cases holds : latest.lines[y]? with
        | some line =>
          by_cases same : told.lines[y]? = some line
          · exact same
          · have := (member y line).mpr ⟨holds, same⟩
            rw [← lookup_iff_mem _ distinct] at this
            rw [this] at found
            cases found
        | none =>
          rw [removed y] at kept
          simp only [holds, and_true] at kept
          simp only [Option.isSome_iff_ne_none, ne_eq, Classical.not_not] at kept
          exact kept
  · by_cases same : told.cursor = latest.cursor <;> simp [Screen.changes, same]
  · by_cases same : told.title = latest.title <;> simp [Screen.changes, same]
  · simp only [Screen.changes]
    exact (List.nodup_range.filter _)
  · rfl
  · rfl

/-! ## Logs that count what they drop -/

/-- Masking is reflexive: a reading shows itself. -/
theorem Log.masks_refl {α : Type} : ∀ (l : List (Option α)), Log.Masks l l
  | [] => trivial
  | _ :: rest => ⟨.inl rfl, Log.masks_refl rest⟩

/-- Masking composes: a reading that masks one that masks another masks it. -/
theorem Log.masks_trans {α : Type} :
    ∀ (a b c : List (Option α)), Log.Masks a b → Log.Masks b c → Log.Masks a c
  | [], [], [], _, _ => trivial
  | _ :: a, _ :: b, _ :: c, ⟨xy, ab⟩, ⟨yz, bc⟩ =>
    ⟨by
      rcases xy with rfl | rfl
      · exact yz
      · exact .inr rfl, Log.masks_trans a b c ab bc⟩
  | [], [], _ :: _, _, h => h.elim
  | [], _ :: _, _, h, _ => h.elim
  | _ :: _, [], _, h, _ => h.elim
  | _ :: _, _ :: _, [], _, h => h.elim

/-- A reading that masks another has as many places. -/
theorem Log.masks_length {α : Type} : ∀ (a b : List (Option α)), Log.Masks a b → a.length = b.length
  | [], [], _ => rfl
  | _ :: a, _ :: b, ⟨_, rest⟩ => by simp [Log.masks_length a b rest]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- Masking appends. -/
theorem Log.masks_append {α : Type} :
    ∀ (a b c d : List (Option α)), Log.Masks a b → Log.Masks c d → Log.Masks (a ++ c) (b ++ d)
  | [], [], _, _, _, cd => cd
  | _ :: a, _ :: b, c, d, ⟨xy, ab⟩, cd => ⟨xy, Log.masks_append a b c d ab cd⟩
  | [], _ :: _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, h, _ => h.elim

/-- **One entry more**: a log's reading after an entry masks its reading before, then the entry. -/
theorem Log.masks_push {α : Type} (cap : Nat) (log : Log α) (entry : α) :
    Log.Masks (Log.push cap log entry).reads (log.reads ++ [some entry]) := by
  unfold Log.push
  split
  · simp only [Log.reads, List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    exact Log.masks_refl _
  · simp only [Log.reads]
    have whole :
      List.replicate log.dropped none ++ List.map some log.tail ++ [some entry] =
        List.replicate log.dropped none ++ (log.tail ++ [entry]).map some := by
      simp
    rw [whole, List.replicate_succ', List.append_assoc]
    apply Log.masks_append _ _ _ _ (Log.masks_refl _)
    cases whole : log.tail ++ [entry] with
    | nil => simp at whole
    | cons first
      rest =>
      simp only [List.drop_succ_cons, List.drop_zero, List.map_cons, List.singleton_append]
      exact ⟨.inr rfl, Log.masks_refl _⟩

/-- **Entries more**: a log's reading after entries masks its reading before, then the entries. -/
theorem Log.masks_fold {α : Type} (cap : Nat) :
    ∀ (entries : List α) (log : Log α),
      Log.Masks (entries.foldl (Log.push cap) log).reads (log.reads ++ entries.map some)
  | [], log => by simpa using Log.masks_refl log.reads
  | entry :: rest, log => by
    simp only [List.foldl_cons, List.map_cons]
    have ih := Log.masks_fold cap rest (Log.push cap log entry)
    refine Log.masks_trans _ _ _ ih ?_
    rw [show log.reads ++ some entry :: rest.map some = (log.reads ++ [some entry]) ++ rest.map some
        by simp]
    exact Log.masks_append _ _ _ _ (Log.masks_push cap log entry) (Log.masks_refl _)

/-- Gaps mask any reading of as many places. -/
theorem Log.masks_gaps {α : Type} :
    ∀ (l : List (Option α)), Log.Masks (List.replicate l.length none) l
  | [] => trivial
  | _ :: rest => ⟨.inr rfl, Log.masks_gaps rest⟩

/-- **A log with another's entries after its own** reads what it read before, then what the
other reads, some places turned into gaps. -/
theorem Log.append_masks {α : Type} (cap : Nat) (log more : Log α) :
    Log.Masks (Log.append cap log more).reads (log.reads ++ more.reads) := by
  unfold Log.append
  split
  · rename_i none
    have whole : more.reads = more.tail.map some := by simp [Log.reads, none]
    rw [whole]
    exact Log.masks_fold cap more.tail log
  · refine Log.masks_trans _ _ _ (Log.masks_fold cap more.tail _) ?_
    have gaps :
      List.replicate (log.dropped + log.tail.length + more.dropped) (none : Option α) =
        List.replicate
          (List.replicate log.dropped none ++ log.tail.map some ++
              List.replicate more.dropped none).length
          none := by
      simp only [List.length_append, List.length_replicate, List.length_map]
    have order :
      List.replicate log.dropped none ++ log.tail.map some ++
          (List.replicate more.dropped none ++ more.tail.map some) =
        (List.replicate log.dropped none ++ log.tail.map some ++
            List.replicate more.dropped none) ++
          more.tail.map some := by
      simp only [List.append_assoc]
    simp only [Log.reads, List.map_nil, List.append_nil]
    rw [gaps, order]
    exact Log.masks_append _ _ _ _ (Log.masks_gaps _) (Log.masks_refl _)

end Linger.App.Serve
