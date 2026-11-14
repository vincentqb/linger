module

import all Linger.Display.CoreCode.View
import all Linger.Display.CoreCode.Status

/-! # Views of many sessions — nothing that needs you is hidden, and every count adds up

A view's order lists every place once, those that ask for someone first and those whose session
ended well or can only be resumed last, and a running session
has one place whether it is printing or quiet; sorting by it loses no row, keeps the listing's
order within a place and moves no row whose session only starts or stops printing. Groups count exactly and add up to the
rows they sum up, a group's name starts every member's name, and the depth names are cut at is
the most even of those that help a summary. -/

namespace Linger.Display.View

open Linger.Display.Status (Status)

/-- Every status's place is in a view's order, -/
theorem place_mem_order (st : Status) : place st ∈ order := by cases st <;> decide

/-- …once. -/
theorem order_nodup : order.Nodup := by decide

/-- A quiet session's place is a printing one's. -/
theorem place_idle : place .idle = place .working := rfl

/-- A status asks for someone exactly when its place does. -/
theorem place_attention (st : Status) : place st ∈ Status.attention ↔ st ∈ Status.attention := by
  cases st <;> decide

/-- Rows that no two filters both keep are, between the two, the rows either keeps. -/
theorem filter_append_filter_perm {α : Type} (p q : α → Bool) (l : List α)
    (h : ∀ x, p x = true → q x = false) :
    (l.filter p ++ l.filter q).Perm (l.filter fun x => p x || q x) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    by_cases hp : p x = true
    · simp only [List.filter_cons, hp, h x hp, ite_true, Bool.true_or, List.cons_append]
      exact ih.cons x
    · cases hq : q x
      · simp only [List.filter_cons, hp, hq, Bool.false_or]
        simpa using ih
      · simp only [List.filter_cons, hp, hq, Bool.false_or]
        simpa using List.perm_middle.trans (ih.cons x)

/-- Filtering rows by each of distinct statuses keeps, in all, the rows with one of them. -/
theorem flatMap_filter_perm {α : Type} (status : α → Status) (rows : List α) :
    ∀ (os : List Status),
      os.Nodup →
        (os.flatMap fun st => rows.filter (status · == st)).Perm
          (rows.filter fun x => os.contains (status x))
  | [], _ => by simp
  | st :: os, hnd => by
    have ⟨hst, hos⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons]
    refine ((List.Perm.refl _).append (flatMap_filter_perm status rows os hos)).trans ?_
    refine (filter_append_filter_perm _ _ rows ?_).trans ?_
    · intro x hx
      simp only [beq_iff_eq] at hx
      rw [hx]
      cases hc : os.contains st
      · rfl
      · exact absurd (List.contains_iff_mem.mp hc) hst
    · simp only [List.contains_cons]
      exact List.Perm.refl _

/-- **A view loses no row**: sorting rows by status is a permutation of them. -/
theorem sort_perm {α : Type} (status : α → Status) (rows : List α) :
    (sort status rows).Perm rows := by
  have h :
    (order.flatMap fun st => rows.filter fun x => place (status x) == st).Perm
      (rows.filter fun x => order.contains (place (status x))) :=
    flatMap_filter_perm (fun x => place (status x)) rows order order_nodup
  have hall : (rows.filter fun x => order.contains (place (status x))) = rows := by
    apply List.filter_eq_self.mpr
    intro x _
    simpa using place_mem_order (status x)
  rw [hall] at h
  exact h

/-- **Nothing that needs you is hidden**: a view lists every row whose status asks for someone
before any row whose status does not. -/
theorem sort_attention_first {α : Type} (status : α → Status) (rows : List α) :
    ∃ first rest,
      sort status rows = first ++ rest ∧
        (∀ x ∈ first, status x ∈ Status.attention) ∧ ∀ x ∈ rest, status x ∉ Status.attention := by
  refine
    ⟨[Status.asks, .exitedBad, .unknown, .wantsYou].flatMap fun st =>
        rows.filter fun x => place (status x) == st,
      [Status.working, .exitedOk, .resumable].flatMap fun st =>
        rows.filter fun x => place (status x) == st,
      ?_, ?_, ?_⟩
  · rw [← List.flatMap_append]
    rfl
  · intro x hx
    simp only [List.mem_flatMap, List.mem_filter, beq_iff_eq] at hx
    obtain ⟨st, hst, _, heq⟩ := hx
    apply (place_attention (status x)).mp
    rw [heq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl | rfl <;> simp [Status.attention]
  · intro x hx
    simp only [List.mem_flatMap, List.mem_filter, beq_iff_eq] at hx
    obtain ⟨st, hst, _, heq⟩ := hx
    rw [← place_attention (status x), heq]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    rcases hst with rfl | rfl | rfl <;> simp [Status.attention]

/-- A status is done when its session ended well or can only be resumed: `✓` or `~`. -/
def done (st : Status) : Bool := st == .exitedOk || st == .resumable

/-- A view lists every row whose session is still to be done with before every row whose session
ended well or can only be resumed. -/
theorem sort_done_last {α : Type} (status : α → Status) (rows : List α) :
    ∃ first rest,
      sort status rows = first ++ rest ∧
        (∀ x ∈ first, done (status x) = false) ∧ ∀ x ∈ rest, done (status x) = true := by
  refine
    ⟨[Status.asks, .exitedBad, .unknown, .wantsYou, .working].flatMap fun st =>
        rows.filter fun x => place (status x) == st,
      [Status.exitedOk, .resumable].flatMap fun st => rows.filter fun x => place (status x) == st,
      ?_, ?_, ?_⟩
  · rw [← List.flatMap_append]
    rfl
  · intro x hx
    simp only [List.mem_flatMap, List.mem_filter, beq_iff_eq] at hx
    obtain ⟨st, hst, _, heq⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    revert heq
    cases status x <;> rcases hst with rfl | rfl | rfl | rfl | rfl <;> simp [place, done]
  · intro x hx
    simp only [List.mem_flatMap, List.mem_filter, beq_iff_eq] at hx
    obtain ⟨st, hst, _, heq⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    revert heq
    cases status x <;> rcases hst with rfl | rfl <;> simp [place, done]

/-- **What ended well or can only be resumed comes after what is live**: wherever a view's rows
are cut in two, a row above the cut whose session exited 0 or can only be resumed leaves no live
row, `⚑`, `⣿`, `⣷` or `⣀`, below it. -/
theorem sort_live_above_done {α : Type} (status : α → Status) (rows first rest : List α)
    (split : sort status rows = first ++ rest) (x : α) (above : x ∈ first)
    (ended : status x = .exitedOk ∨ status x = .resumable) (y : α) (below : y ∈ rest) :
    ¬(status y = .asks ∨ status y = .wantsYou ∨ status y = .working ∨ status y = .idle) := by
  obtain ⟨front, back, whole, live, settled⟩ := sort_done_last status rows
  rw [whole] at split
  have hx : done (status x) = true := by rcases ended with h | h <;> simp [h, done]
  rcases List.append_eq_append_iff.mp split with ⟨mid, hfirst, hback⟩ | ⟨mid, hfront, hrest⟩
  · have hy :=
      settled y
        (by
          rw [hback]; exact List.mem_append_right _ below)
    revert hy
    cases status y <;> simp [done]
  · exact
      absurd hx
        (by
          rw [live x
              (by
                rw [hfront]; exact List.mem_append_left _ above)];
          simp)

/-- Filtering by one status after filtering by distinct statuses keeps that status's rows when
it is among them, and none otherwise. -/
theorem flatMap_filter_filter {α : Type} (status : α → Status) (rows : List α) (st : Status) :
    ∀ (os : List Status),
      os.Nodup →
        (os.flatMap fun s => rows.filter (status · == s)).filter (status · == st) =
          if st ∈ os then rows.filter (status · == st) else []
  | [], _ => by simp
  | s :: os, hnd => by
    have ⟨hs, hos⟩ := List.nodup_cons.mp hnd
    rw [List.flatMap_cons, List.filter_append, flatMap_filter_filter status rows st os hos,
      List.filter_filter]
    by_cases hst : s = st
    · subst hst
      simp [hs]
    · have hnone : (rows.filter fun x => (status x == st) && (status x == s)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x _
        by_cases h : status x = st
        · simp [h, Ne.symm hst]
        · simp [h]
      simp only [hnone, List.nil_append, List.mem_cons]
      by_cases hin : st ∈ os
      · simp [hin]
      · simp [hin, Ne.symm hst]

/-- **A view keeps the listing's order within a place.** -/
theorem sort_stable {α : Type} (status : α → Status) (rows : List α) (st : Status) :
    (sort status rows).filter (fun x => place (status x) == st) =
      rows.filter fun x => place (status x) == st := by
  have h :
    (order.flatMap fun s => rows.filter fun x => place (status x) == s).filter
        (fun x => place (status x) == st) =
      if st ∈ order then rows.filter (fun x => place (status x) == st) else [] :=
    flatMap_filter_filter (fun x => place (status x)) rows st order order_nodup
  unfold sort
  rw [h]
  by_cases hst : st ∈ order
  · simp [hst]
  · simp only [hst, ite_false]
    symm
    apply List.filter_eq_nil_iff.mpr
    intro x _ heq
    exact hst ((beq_iff_eq.mp heq) ▸ place_mem_order (status x))

/-- **A row keeps its place while its session prints or goes quiet**: statuses that differ only
between `⣷` and `⣀` sort rows the same. -/
theorem sort_keeps_place {α : Type} (status status' : α → Status) (rows : List α)
    (h :
      ∀ x ∈ rows,
        status x = status' x ∨
          ((status x = .working ∨ status x = .idle) ∧ (status' x = .working ∨ status' x = .idle))) :
    sort status rows = sort status' rows := by
  have hp : ∀ x ∈ rows, place (status x) = place (status' x) := by
    intro x hx
    rcases h x hx with heq | ⟨h1, h2⟩
    · rw [heq]
    · rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp only [h1, h2, place_idle]
  unfold sort
  congr 1
  funext st
  exact List.filter_congr fun x hx => by rw [hp x hx]

/-- A view's header says how many rows it lists, -/
theorem headerParts_count (labels : List String) (statuses : List Status) :
    toString statuses.length ∈ headerParts labels statuses := by simp [headerParts]

/-- …and, when any ask for someone, how many do of each kind, over all of them
(`Status.summary_exact`). -/
theorem headerParts_summary (labels : List String) (statuses : List Status)
    (h : (Status.summary statuses).isEmpty = false) :
    Status.summary statuses ∈ headerParts labels statuses := by simp [headerParts, h]

/-- A target's group at any depth is the start of its characters. -/
theorem stemChars_prefix : ∀ (depth : Nat) (cs : List Char), stemChars depth cs <+: cs
  | _, [] => by simp [stemChars]
  | depth, c :: cs => by
    unfold stemChars
    split
    · exact List.nil_prefix
    · split
      · split
        · exact List.nil_prefix
        · exact (List.prefix_cons_inj c).mpr (stemChars_prefix (depth - 1) cs)
      · exact (List.prefix_cons_inj c).mpr (stemChars_prefix depth cs)

/-- **A group's name starts each member's name**, so typing it keeps all of them. -/
theorem stem_prefix (depth : Nat) (target : String) :
    (stem depth target).toList <+: target.toList := by
  simpa [stem] using stemChars_prefix depth target.toList

/-- A target's group at depth one is one part of its name: no separator, and no host. -/
theorem stemChars_one :
    ∀ (cs : List Char) (c : Char), c ∈ stemChars 1 cs → separator c = false ∧ c ≠ '@'
  | [], c, h => by simp [stemChars] at h
  | d :: cs, c, h => by
    unfold stemChars at h
    by_cases hat : d = '@'
    · simp [hat] at h
    · by_cases hsep : separator d = true
      · simp [hat, hsep] at h
      · simp only [hat, hsep, beq_iff_eq, ite_false, Bool.false_eq_true, List.mem_cons] at h
        rcases h with rfl | h
        · exact ⟨by simpa using hsep, hat⟩
        · exact stemChars_one cs c h

/-- The keys other than `k` are the keys not counted as `k`. -/
theorem count_add_length_filter_ne (k : String) :
    ∀ ks : List String, ks.count k + (ks.filter (· != k)).length = ks.length
  | [] => rfl
  | x :: xs => by
    have ih := count_add_length_filter_ne k xs
    by_cases h : x = k
    · subst h
      simp only [List.count_cons_self, List.filter_cons, bne_self_eq_false, Bool.false_eq_true,
        ite_false, List.length_cons]
      omega
    · simp only [List.count_cons_of_ne h, List.filter_cons, bne_iff_ne, ne_eq, h, not_false_eq_true,
        ite_true, List.length_cons]
      omega

/-- `groups_mem` for keys no longer than `bound`. -/
theorem groups_mem_le :
    ∀ (bound : Nat) (keys : List String) (k : String) (n : Nat),
      keys.length ≤ bound → (k, n) ∈ groups keys → k ∈ keys
  | _, [], k, n, _, h => by simp [groups] at h
  | 0, _ :: _, _, _, hb, _ => by simp at hb
  | bound + 1, k₀ :: ks, k, n, hb, h => by
    rw [groups] at h
    rcases List.mem_cons.mp h with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      simp [heq.1]
    · have hle : (ks.filter (· != k₀)).length ≤ bound :=
        Nat.le_trans (List.length_filter_le _ _) (by simpa using hb)
      exact List.mem_cons_of_mem _ (List.mem_filter.mp (groups_mem_le bound _ k n hle hmem)).1

/-- A key a group names is one of the keys. -/
theorem groups_mem (keys : List String) (k : String) (n : Nat) (h : (k, n) ∈ groups keys) :
    k ∈ keys := groups_mem_le keys.length keys k n (Nat.le_refl _) h

/-- `groups_count` for keys no longer than `bound`. -/
theorem groups_count_le :
    ∀ (bound : Nat) (keys : List String) (k : String) (n : Nat),
      keys.length ≤ bound → (k, n) ∈ groups keys → n = keys.count k
  | _, [], k, n, _, h => by simp [groups] at h
  | 0, _ :: _, _, _, hb, _ => by simp at hb
  | bound + 1, k₀ :: ks, k, n, hb, h => by
    rw [groups] at h
    rcases List.mem_cons.mp h with heq | hmem
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      simp
    · have hle : (ks.filter (· != k₀)).length ≤ bound :=
        Nat.le_trans (List.length_filter_le _ _) (by simpa using hb)
      have hk := List.mem_filter.mp (groups_mem _ k n hmem)
      have hne : k ≠ k₀ := by simpa using hk.2
      rw [groups_count_le bound _ k n hle hmem, List.count_cons_of_ne (Ne.symm hne)]
      exact List.count_filter (by simpa using hne)

/-- **Group counts are exact**: each group counts every occurrence of its key. -/
theorem groups_count (keys : List String) (k : String) (n : Nat) (h : (k, n) ∈ groups keys) :
    n = keys.count k := groups_count_le keys.length keys k n (Nat.le_refl _) h

/-- `groups_sum` for keys no longer than `bound`. -/
theorem groups_sum_le :
    ∀ (bound : Nat) (keys : List String),
      keys.length ≤ bound → ((groups keys).map (·.2)).sum = keys.length
  | _, [], _ => by simp [groups]
  | 0, _ :: _, hb => by simp at hb
  | bound + 1, k :: ks, hb => by
    have hle : (ks.filter (· != k)).length ≤ bound :=
      Nat.le_trans (List.length_filter_le _ _) (by simpa using hb)
    rw [groups]
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    rw [groups_sum_le bound _ hle]
    have := count_add_length_filter_ne k ks
    omega

/-- **Group counts add up** to the keys they sum up. -/
theorem groups_sum (keys : List String) : ((groups keys).map (·.2)).sum = keys.length :=
  groups_sum_le keys.length keys (Nat.le_refl _)

/-- Grouping at a depth helps a summary exactly when it makes at most `maxGroups` groups, and
fewer groups than targets. -/
theorem useful_iff (depth : Nat) (targets : List String) :
    useful depth targets = true ↔
      (groups (targets.map (stem depth))).length ≤ maxGroups ∧
        (groups (targets.map (stem depth))).length < targets.length := by
  simp [useful]

/-- What `chooseDepth` knows after looking at the depths `seen`: a best depth so far helps a
summary, with no larger a largest group than any other such depth seen, and there is none so far
only when no depth seen helps one. -/
def Best (targets : List String) (seen : List Nat) (best : Option Nat) : Prop :=
  (∀ b,
      best = some b →
        useful b targets = true ∧
          ∀ d ∈ seen, useful d targets = true → largest b targets ≤ largest d targets) ∧
    (best = none → ∀ d ∈ seen, useful d targets = false)

/-- Looking at one more depth keeps what `chooseDepth` knows true of the depths seen. -/
theorem better_best (targets : List String) (seen : List Nat) (best : Option Nat) (depth : Nat)
    (h : Best targets seen best) : Best targets (seen ++ [depth]) (better targets best depth) := by
  obtain ⟨hsome, hnone⟩ := h
  unfold better
  by_cases hr : useful depth targets = true
  · simp only [hr, ite_true]
    cases best with
    | none =>
      have hno := hnone rfl
      refine ⟨fun b hb => ?_, fun h => by cases h⟩
      cases hb
      refine ⟨hr, fun d hd hrd => ?_⟩
      rcases List.mem_append.mp hd with hd | hd
      · simp [hno d hd] at hrd
      · simp only [List.mem_singleton] at hd
        simp [hd]
    | some b =>
      obtain ⟨hrb, hb⟩ := hsome b rfl
      by_cases hle : largest depth targets ≤ largest b targets
      · simp only [hle, ite_true]
        refine ⟨fun b' hb' => ?_, fun h => by cases h⟩
        cases hb'
        refine ⟨hr, fun d hd hrd => ?_⟩
        rcases List.mem_append.mp hd with hd | hd
        · exact Nat.le_trans hle (hb d hd hrd)
        · simp only [List.mem_singleton] at hd
          simp [hd]
      · simp only [hle, ite_false]
        refine ⟨fun b' hb' => ?_, fun h => by cases h⟩
        cases hb'
        refine ⟨hrb, fun d hd hrd => ?_⟩
        rcases List.mem_append.mp hd with hd | hd
        · exact hb d hd hrd
        · simp only [List.mem_singleton] at hd
          subst hd
          exact Nat.le_of_lt (Nat.lt_of_not_le hle)
  · have hf : useful depth targets = false := by simpa using hr
    simp only [hf, Bool.false_eq_true, ite_false]
    refine ⟨fun b hb => ?_, fun h d hd => ?_⟩
    · obtain ⟨hrb, hbest⟩ := hsome b hb
      refine ⟨hrb, fun d hd hrd => ?_⟩
      rcases List.mem_append.mp hd with hd | hd
      · exact hbest d hd hrd
      · simp only [List.mem_singleton] at hd
        subst hd
        simp [hf] at hrd
    · rcases List.mem_append.mp hd with hd | hd
      · exact hnone h d hd
      · simp only [List.mem_singleton] at hd
        subst hd
        exact hf

/-- Looking at depths in turn keeps what `chooseDepth` knows true of every depth seen. -/
theorem foldl_better_best (targets : List String) :
    ∀ (ds seen : List Nat) (best : Option Nat),
      Best targets seen best → Best targets (seen ++ ds) (ds.foldl (better targets) best)
  | [], seen, best, h => by simpa using h
  | d :: ds, seen, best, h => by
    have :=
      foldl_better_best targets ds (seen ++ [d]) (better targets best d)
        (better_best targets seen best d h)
    simpa using this

/-- What `chooseDepth` knows of all the depths a summary may cut names at. -/
theorem chooseDepth_knows (targets : List String) : Best targets depths (chooseDepth targets) := by
  have hstart : Best targets [] none := ⟨fun b hb => (by cases hb), fun _ d hd => (by cases hd)⟩
  simpa [chooseDepth] using foldl_better_best targets depths [] none hstart

/-- **The most even split**: the depth `chooseDepth` picks helps a summary, and no other depth
that helps one has a smaller largest group. Looking at one more depth keeps this true
(`better`). -/
theorem chooseDepth_best (targets : List String) (depth : Nat)
    (h : chooseDepth targets = some depth) :
    useful depth targets = true ∧
      ∀ other ∈ depths,
        useful other targets = true →
          largest depth targets ≤ largest other targets := (chooseDepth_knows targets).1 depth h

/-- `chooseDepth` picks no depth only when no depth helps a summary. -/
theorem chooseDepth_none (targets : List String) (h : chooseDepth targets = none) :
    ∀ depth ∈ depths, useful depth targets = false := (chooseDepth_knows targets).2 h

/-- Looking at one more depth that does not help a summary keeps the best so far. -/
theorem better_useless (targets : List String) (best : Option Nat) (depth : Nat)
    (h : useful depth targets = false) : better targets best depth = best := by simp [better, h]

/-- **What a view leaves out adds up**: the groups it names count every row it leaves out, or
it names none. -/
theorem hidden_adds_up (targets : List String) :
    (hidden targets).2 = [] ∨ (((hidden targets).2).map (·.2)).sum = (hidden targets).1 := by
  unfold hidden
  cases chooseDepth targets with
  | none =>
    left; rfl
  | some depth =>
    right; simp [groups_sum]

/-- The statuses that ask for someone, by name: `⚑`, `⣿`, `✗` and `?`. -/
theorem mem_attention (st : Status) :
    st ∈ Status.attention ↔ st = .asks ∨ st = .wantsYou ∨ st = .exitedBad ∨ st = .unknown := by
  simp [Status.attention]

end Linger.Display.View
