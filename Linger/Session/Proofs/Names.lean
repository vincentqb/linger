module

public import Linger.Session.CoreCode.Names
public import Os.WorldSpec
public import Linger.Target.CoreCode.Name
import all Linger.Session.CoreCode.Names
import Linger.Target.Proofs.Name

public section

/-! # Names lead to IDs one to one

In a table linger keeps (`Names.Wf`), `resolve` and `nameOf` are inverse, so no two names lead
to one ID (`resolve_iff_nameOf`, `resolve_injective`); with no entries, the old layout, every valid
name leads to itself (`resolve_nil`). A rename moves the name and keeps the ID (`rename_moves`), a
start's fresh ID joins the table without touching another name (`claim_fresh`), a fresh ID never
shows as a name (`nameOf_shown`), and of two placements onto one name the second fails
(`call_second_fails`). -/

namespace Linger.Session.Names

theorem lookup_mem {t : Table} {a i : String} (h : t.lookup a = some i) : (a, i) ∈ t := by
  induction t with
  | nil => simp at h
  | cons e t ih =>
    obtain ⟨k, v⟩ := e
    rw [List.lookup_cons] at h
    by_cases hk : a = k
    · subst hk
      simp at h
      simp [h]
    · have : (a == k) = false := by simpa using hk
      rw [this] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem lookup_none {t : Table} {a : String} (h : t.lookup a = none) : ∀ e ∈ t, e.1 ≠ a := by
  induction t with
  | nil => simp
  | cons e t ih =>
    obtain ⟨k, v⟩ := e
    rw [List.lookup_cons] at h
    by_cases hk : a = k
    · subst hk
      simp at h
    · have : (a == k) = false := by simpa using hk
      rw [this] at h
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact fun h' => hk h'.symm
      · exact ih h x hx

theorem lookup_of_none {t : Table} {a : String} (h : ∀ e ∈ t, e.1 ≠ a) : t.lookup a = none := by
  induction t with
  | nil => simp
  | cons e t ih =>
    obtain ⟨k, v⟩ := e
    rw [List.lookup_cons]
    have hk : (a == k) = false := by simpa using fun h' => h (k, v) (by simp) h'.symm
    rw [hk]
    exact ih fun x hx => h x (List.mem_cons_of_mem _ hx)

theorem lookup_of_mem {t : Table} (nd : (t.map (·.1)).Nodup) {a i : String} (h : (a, i) ∈ t) :
    t.lookup a = some i := by
  induction t with
  | nil => simp at h
  | cons e t ih =>
    obtain ⟨k, v⟩ := e
    rw [List.lookup_cons]
    simp only [List.map_cons, List.nodup_cons] at nd
    rcases List.mem_cons.mp h with hh | ht
    · cases hh
      simp
    · have hk : a ≠ k := by
        intro hak
        subst hak
        exact nd.1 (List.mem_map.mpr ⟨(a, i), ht, rfl⟩)
      have : (a == k) = false := by simpa using hk
      rw [this]
      exact ih nd.2 ht

theorem find_of_mem {t : Table} (nd : (t.map (·.2)).Nodup) {e : String × String} (h : e ∈ t) :
    t.find? (fun x => x.2 == e.2) = some e := by
  induction t with
  | nil => simp at h
  | cons x t ih =>
    simp only [List.map_cons, List.nodup_cons] at nd
    rw [List.find?_cons]
    rcases List.mem_cons.mp h with rfl | h
    · simp
    · have hx : x.2 ≠ e.2 := by
        intro hx
        exact nd.1 (List.mem_map.mpr ⟨e, h, hx.symm⟩)
      have : (x.2 == e.2) = false := by simpa using hx
      rw [this]
      exact ih nd.2 h

theorem check_some {s : String} (h : (Linger.Target.Name.check s).isSome = true) :
    Linger.Target.Name.check s = some s := by
  cases hc : Linger.Target.Name.check s with
  | none => simp [hc] at h
  | some r => exact congrArg some ((Linger.Target.Name.check_eq_some_iff s r).mp hc).1

/-- With no entries, as in the old layout, every valid name leads to itself. -/
theorem resolve_nil (a : String) : resolve [] a = Linger.Target.Name.check a := by
  unfold resolve
  simp only [List.lookup_nil, List.any_nil, Bool.not_false, Bool.and_true]
  cases hc : Linger.Target.Name.check a with
  | none => simp
  | some r =>
    have := ((Linger.Target.Name.check_eq_some_iff a r).mp hc).1
    simp [this]

/-- In a table linger keeps, a name leads to an ID exactly when that ID shows as the name. -/
theorem resolve_iff_nameOf {t : Table} (wf : Wf t) (a id : String) :
    resolve t a = some id ↔ nameOf t id = some a := by
  obtain ⟨names, ids⟩ := wf
  unfold resolve nameOf
  constructor
  · intro h
    cases hl : t.lookup a with
    | some j =>
      rw [hl] at h
      cases h
      have mem := lookup_mem hl
      have := find_of_mem ids mem
      simp only at this
      rw [this]
    | none =>
      rw [hl] at h
      simp only at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        have nofind : t.find? (fun e => e.2 == a) = none := by
          rw [List.find?_eq_none]
          intro x hx hp
          have : t.any (fun e => e.2 == a) = true := List.any_eq_true.mpr ⟨x, hx, hp⟩
          rw [hc.2] at this
          cases this
        rw [nofind]
        have nofst : t.any (fun e => e.1 == a) = false := by
          cases hany : t.any (fun e => e.1 == a) with
          | false => rfl
          | true =>
            obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp hany
            exact absurd (by simpa using hp) (lookup_none hl x hx)
        simp [hc.1, nofst]
      · cases h
  · intro h
    cases hf : t.find? (fun e => e.2 == id) with
    | some e =>
      rw [hf] at h
      cases h
      have mem := List.mem_of_find?_eq_some hf
      have snd : e.2 = id := by simpa using List.find?_some hf
      have := lookup_of_mem names (a := e.1) (i := e.2) mem
      rw [this, snd]
    | none =>
      rw [hf] at h
      simp only at h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
        have nolookup : t.lookup a = none := by
          apply lookup_of_none
          intro x hx hxa
          have : t.any (fun e => e.1 == a) = true := List.any_eq_true.mpr ⟨x, hx, by simp [hxa]⟩
          rw [hc.2] at this
          cases this
        rw [nolookup]
        have nosnd : t.any (fun e => e.2 == a) = false := by
          cases hany : t.any (fun e => e.2 == a) with
          | false => rfl
          | true =>
            obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp hany
            exact absurd hp (List.find?_eq_none.mp hf x hx)
        simp [hc.1, nosnd]
      · cases h

/-- In a table linger keeps, no two names lead to one ID. -/
theorem resolve_injective {t : Table} (wf : Wf t) {a b id : String} (ha : resolve t a = some id)
    (hb : resolve t b = some id) : a = b := by
  have := (resolve_iff_nameOf wf a id).mp ha
  rw [(resolve_iff_nameOf wf b id).mp hb] at this
  exact (Option.some.inj this).symm

theorem lookup_rename_new (t : Table) (old new id : String) :
    (rename t old new id).lookup new = some id := by simp [rename]

theorem lookup_filter_ne {t : Table} {old n : String} (h : n ≠ old) :
    (t.filter (fun e => e.1 != old)).lookup n = t.lookup n := by
  induction t with
  | nil => simp
  | cons e t ih =>
    obtain ⟨k, v⟩ := e
    by_cases hk : k = old
    · subst hk
      have : (n == k) = false := by simpa using h
      simp [List.lookup_cons, this, ih]
    · by_cases hn : n = k
      · subst hn
        simp [hk]
      · have : (n == k) = false := by simpa using hn
        simp [List.lookup_cons, hk, this, ih]

theorem lookup_filter_old (t : Table) (old : String) :
    (t.filter (fun e => e.1 != old)).lookup old = none := by
  apply lookup_of_none
  intro x hx
  have := (List.mem_filter.mp hx).2
  simpa using this

theorem any_snd_rename (t : Table) (old new id n : String) :
    (rename t old new id).any (fun e => e.2 == n) = true ↔
      (id = n ∨ ∃ x ∈ t, x.1 ≠ old ∧ x.2 = n) := by
  simp [rename, List.any_eq_true]

/-- The entry `old` has, if any, holds the ID `old` leads to. -/
theorem old_entries {t : Table} (names : (t.map (·.1)).Nodup) {old id : String}
    (found : resolve t old = some id) : ∀ x ∈ t, x.1 = old → x.2 = id := by
  intro x hx hxo
  unfold resolve at found
  have hl := lookup_of_mem names (a := x.1) (i := x.2) hx
  rw [hxo] at hl
  rw [hl] at found
  exact Option.some.inj found

/-- A rename keeps the table one a directory holds, moves the name to the same ID, leaves the
old name leading elsewhere, and changes no other name's ID. -/
theorem rename_moves {t : Table} (wf : Wf t) {old new id : String} (found : resolve t old = some id)
    (free : t.lookup new = none) (other : old ≠ new) :
    Wf (rename t old new id) ∧
      resolve (rename t old new id) new = some id ∧
      resolve (rename t old new id) old ≠ some id ∧
      ∀ n, n ≠ old → n ≠ new → resolve (rename t old new id) n = resolve t n := by
  obtain ⟨names, ids⟩ := wf
  have entries := old_entries names found
  -- `old` has an entry, or else its ID is itself and no entry leads to it
  have implicit : t.lookup old = none → id = old ∧ ∀ x ∈ t, x.2 ≠ old := by
    intro hl
    unfold resolve at found
    rw [hl] at found
    simp only at found
    split at found
    · rename_i hc
      cases found
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      refine ⟨rfl, fun x hx hxo => ?_⟩
      have : t.any (fun e => e.2 == old) = true := List.any_eq_true.mpr ⟨x, hx, by simp [hxo]⟩
      rw [hc.2] at this
      cases this
    · cases found
  have idFree : id ∉ (t.filter (fun e => e.1 != old)).map (·.2) := by
    intro hm
    obtain ⟨x, hx, hxid⟩ := List.mem_map.mp hm
    have ⟨xmem, xne⟩ := List.mem_filter.mp hx
    have xne : x.1 ≠ old := by simpa using xne
    cases hl : t.lookup old with
    | some j =>
      have omem := lookup_mem hl
      have j_id := entries _ omem rfl
      simp only at j_id
      subst j_id
      have e1 := find_of_mem ids omem
      have e2 := find_of_mem ids xmem
      simp only at e1 e2
      rw [hxid, e1] at e2
      cases e2
      exact xne rfl
    | none =>
      obtain ⟨rfl, none⟩ := implicit hl
      exact none x xmem hxid
  have wf' : Wf (rename t old new id) := by
    constructor
    · simp only [rename, List.map_cons, List.nodup_cons]
      refine ⟨?_, names.sublist ((List.filter_sublist).map _)⟩
      intro hm
      obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hm
      exact lookup_none free x (List.mem_filter.mp hx).1 hxn
    · simp only [rename, List.map_cons, List.nodup_cons]
      exact ⟨idFree, ids.sublist ((List.filter_sublist).map _)⟩
  refine ⟨wf', ?_, ?_, ?_⟩
  · unfold resolve
    rw [lookup_rename_new]
  · unfold resolve
    have : (rename t old new id).lookup old = none := by
      simp only [rename, List.lookup_cons]
      have : (old == new) = false := by simpa using other
      rw [this, lookup_filter_old]
    rw [this]
    simp only
    intro h
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hc
      have : (rename t old new old).any (fun e => e.2 == old) = true :=
        (any_snd_rename t old new old old).mpr (Or.inl rfl)
      rw [hc.2] at this
      cases this
    · cases h
  · intro n hno hnn
    unfold resolve
    have hlook : (rename t old new id).lookup n = t.lookup n := by
      simp only [rename, List.lookup_cons]
      have : (n == new) = false := by simpa using hnn
      rw [this, lookup_filter_ne hno]
    rw [hlook]
    cases t.lookup n with
    | some j => rfl
    | none =>
      simp only
      have same : (rename t old new id).any (fun e => e.2 == n) = t.any (fun e => e.2 == n) := by
        apply Bool.eq_iff_iff.mpr
        rw [any_snd_rename, List.any_eq_true]
        constructor
        · rintro (rfl | ⟨x, hx, _, hxn⟩)
          · cases hl : t.lookup old with
            | some j =>
              have omem := lookup_mem hl
              have := entries _ omem rfl
              exact ⟨_, omem, by simpa using this⟩
            | none => exact absurd (implicit hl).1 hno
          · exact ⟨x, hx, by simpa using hxn⟩
        · rintro ⟨x, hx, hxn⟩
          have hxn : x.2 = n := by simpa using hxn
          by_cases hxo : x.1 = old
          · exact Or.inl ((entries x hx hxo).symm.trans hxn)
          · exact Or.inr ⟨x, hx, hxo, hxn⟩
      rw [same]

/-- A start's fresh ID, which no entry holds, for a name that leads nowhere, keeps the table one
a directory holds, makes the name lead to the ID, and changes no other name's ID. -/
theorem claim_fresh {t : Table} (wf : Wf t) {name id : String} (unnamed : resolve t name = none)
    (fresh : Fresh id) (unused : id ∉ t.map (·.2)) :
    Wf (claim t name id) ∧
      resolve (claim t name id) name = some id ∧
      ∀ n, n ≠ name → resolve (claim t name id) n = resolve t n := by
  obtain ⟨names, ids⟩ := wf
  have hl : t.lookup name = none := by
    unfold resolve at unnamed
    cases h : t.lookup name with
    | none => rfl
    | some j =>
      rw [h] at unnamed; cases unnamed
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [claim, List.map_cons, List.nodup_cons]
    refine ⟨fun hm => ?_, names⟩
    obtain ⟨x, hx, hxn⟩ := List.mem_map.mp hm
    exact lookup_none hl x hx hxn
  · simp only [claim, List.map_cons, List.nodup_cons]
    exact ⟨unused, ids⟩
  · simp [resolve, claim]
  · intro n hn
    unfold resolve
    have : (claim t name id).lookup n = t.lookup n := by
      have : (n == name) = false := by simpa using hn
      simp [claim, List.lookup_cons, this]
    rw [this]
    cases t.lookup n with
    | some j => rfl
    | none =>
      simp only
      -- the fresh ID is no name, so no name's own ID is it
      have notName : (Linger.Target.Name.check n).isSome = true → id ≠ n := by
        intro hc hid
        subst hid
        obtain ⟨digits, hd, _, _⟩ := fresh
        have hv := ((Linger.Target.Name.check_eq_some_iff id id).mp (check_some hc)).2
        exact
          hv.2.2.2
            (by
              rw [hd]; rfl)
      by_cases hc : (Linger.Target.Name.check n).isSome = true
      · have hne := notName hc
        have : (id == n) = false := by simpa using hne
        simp only [claim, List.any_cons, this, Bool.false_or]
      · simp [hc]

/-- An ID shows as the name of its entry, or as itself only when it is a valid name: a fresh ID
never shows. -/
theorem nameOf_shown (t : Table) (id name : String) (shown : nameOf t id = some name) :
    (name, id) ∈ t ∨ Linger.Target.Name.check id = some name := by
  unfold nameOf at shown
  cases hf : t.find? (fun e => e.2 == id) with
  | some e =>
    rw [hf] at shown
    cases shown
    have mem := List.mem_of_find?_eq_some hf
    have snd : e.2 = id := by simpa using List.find?_some hf
    left
    rw [← snd]
    exact mem
  | none =>
    rw [hf] at shown
    simp only at shown
    split at shown
    · rename_i hc
      cases shown
      simp only [Bool.and_eq_true] at hc
      exact Or.inr (check_some hc.1)
    · cases shown

/-- `Rename.plan` refuses as its doc says, in that order. -/
theorem rename_plan_eq (valid oldHeld older newHeld : Bool) :
    Rename.plan valid oldHeld older newHeld =
      if !valid then .refuse .invalid
      else
        if !oldHeld then .refuse .missing
        else if newHeld then .refuse .taken else if older then .refuse .older else .move := by
  unfold Rename.plan
  rfl

/-- Linger places a name with a link or a rename that may not replace, never with one that
replaces. -/
theorem call_safe (op : Op) : call op = .link ∨ call op = .renameNew := by cases op <;> simp [call]

/-- Of two placements onto one name, whichever comes first, the second fails and the name keeps
the first one's file, when the operating system never replaces a name. -/
theorem call_second_fails
    {placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)}
    (noReplace : Os.Place.NoReplace placed) (first second : Op) {names : String → Option Nat}
    {src src' dst : String} {file : Nat} (named : names src = some file)
    {after : String → Option Nat}
    (placedFirst : (call first).run placed names src dst = some after) :
    after dst = some file ∧ (call second).run placed after src' dst = none := by
  have keeps : after dst = some file := by
    rcases call_safe first with h | h <;> rw [h] at placedFirst <;>
      simp only [Call.run] at placedFirst
    · rw [((noReplace false names src dst).2 after placedFirst).2.1, named]
    · rw [((noReplace true names src dst).2 after placedFirst).2.1, named]
  refine ⟨keeps, ?_⟩
  have taken : (after dst).isSome = true := by
    rw [keeps]; rfl
  rcases call_safe second with h | h <;> rw [h] <;> simp only [Call.run]
  · exact (noReplace false after src' dst).1 taken
  · exact (noReplace true after src' dst).1 taken

end Linger.Session.Names
