module

import all Linger.Display.CoreCode.View
import all Linger.Display.CoreCode.Status
import all Init.Data.Repr

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

/-- A quiet session's place is a working one's… -/
theorem place_idle : place .idle = place .working := rfl

/-- …as is a paused one's. -/
theorem place_paused : place .paused = place .working := rfl

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
    ⟨[Status.asks, .exitedBad, .errored, .unknown, .wantsYou].flatMap fun st =>
        rows.filter fun x => place (status x) == st,
      [Status.working, .resumable, .exitedOk].flatMap fun st =>
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
    rcases hst with rfl | rfl | rfl | rfl | rfl <;> simp [Status.attention]
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
    ⟨[Status.asks, .exitedBad, .errored, .unknown, .wantsYou, .working].flatMap fun st =>
        rows.filter fun x => place (status x) == st,
      [Status.resumable, .exitedOk].flatMap fun st => rows.filter fun x => place (status x) == st,
      ?_, ?_, ?_⟩
  · rw [← List.flatMap_append]
    rfl
  · intro x hx
    simp only [List.mem_flatMap, List.mem_filter, beq_iff_eq] at hx
    obtain ⟨st, hst, _, heq⟩ := hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hst
    revert heq
    cases status x <;> rcases hst with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [place, done]
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
    ¬(status y = .asks ∨
        status y = .errored ∨
        status y = .wantsYou ∨ status y = .working ∨ status y = .paused ∨ status y = .idle) := by
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
          ((status x = .working ∨ status x = .paused ∨ status x = .idle) ∧
            (status' x = .working ∨ status' x = .paused ∨ status' x = .idle))) :
    sort status rows = sort status' rows := by
  have hp : ∀ x ∈ rows, place (status x) = place (status' x) := by
    intro x hx
    rcases h x hx with heq | ⟨h1, h2⟩
    · rw [heq]
    · rcases h1 with h1 | h1 | h1 <;> rcases h2 with h2 | h2 | h2 <;>
        simp only [h1, h2, place_idle, place_paused]
  unfold sort
  congr 1
  funext st
  exact List.filter_congr fun x hx => by rw [hp x hx]

/-- A status's place has its keys: a quiet session's are a printing one's. -/
theorem keys_place (st : Status) :
    needs (place st) = needs st ∧ lifecycle (place st) = lifecycle st := by cases st <;> decide

/-- **A view is ordered by two keys**: what needs you to act, then where the session is in its
life, running, saved, then ended, and rows with the same keys in the order they came in, so by
any order the rows were listed in, as names as people read them (`before_total`). -/
theorem sort_two_keys {α : Type} (status : α → Status) (earlier : α → α → Prop) (rows : List α)
    (listed : rows.Pairwise earlier) :
    (sort status rows).Pairwise fun a b =>
      needs (status a) < needs (status b) ∨
        needs (status a) = needs (status b) ∧
          (lifecycle (status a) < lifecycle (status b) ∨
            lifecycle (status a) = lifecycle (status b) ∧ earlier a b) := by
  have ranked :
    order.Pairwise fun a b =>
      needs a < needs b ∨ needs a = needs b ∧ lifecycle a < lifecycle b := by
    decide
  have keys :
    ∀ x st,
      place (status x) = st →
        needs (status x) = needs st ∧ lifecycle (status x) = lifecycle st := by
    intro x st h
    have := keys_place (status x)
    rw [h] at this
    exact ⟨this.1.symm, this.2.symm⟩
  unfold sort
  rw [List.pairwise_flatMap]
  refine ⟨fun st _ => ?_, ranked.imp fun {a b} hab => ?_⟩
  · refine (listed.sublist List.filter_sublist).imp_of_mem fun {x y} hx hy hxy => ?_
    simp only [List.mem_filter, beq_iff_eq] at hx hy
    obtain ⟨nx, lx⟩ := keys x st hx.2
    obtain ⟨ny, ly⟩ := keys y st hy.2
    exact Or.inr ⟨by omega, Or.inr ⟨by omega, hxy⟩⟩
  · intro x hx y hy
    simp only [List.mem_filter, beq_iff_eq] at hx hy
    obtain ⟨nx, lx⟩ := keys x a hx.2
    obtain ⟨ny, ly⟩ := keys y b hy.2
    rcases hab with h | ⟨h, h'⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, Or.inl (by omega)⟩

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

/-- The statuses that ask for someone, by name: `⚑`, `⣿`, `✗`, `!` and `?`. -/
theorem mem_attention (st : Status) :
    st ∈ Status.attention ↔
      st = .asks ∨ st = .wantsYou ∨ st = .exitedBad ∨ st = .errored ∨ st = .unknown := by
  simp [Status.attention]

/-! ## Names as people read them -/

/-- A name's runs, back from what they compare by. -/
def decode : List Nat → List Char
  | [] => []
  | n :: rest =>
    if n = 0x30 then
      ((rest.drop 2).take (rest.getD 1 0)).map Char.ofNat ++
        decode ((rest.drop 2).drop (rest.getD 1 0))
    else Char.ofNat n :: decode rest
termination_by l => l.length
decreasing_by
  all_goals simp only [List.length_drop, List.length_cons]
  all_goals omega

/-- A run as `runs` cuts it: one character that is not a digit, or digits. -/
def Run (r : List Char) : Prop :=
  (∃ c, r = [c] ∧ c.isDigit = false) ∨ (r ≠ [] ∧ ∀ c ∈ r, c.isDigit = true)

theorem runs_run (cs : List Char) : ∀ r ∈ runs cs, Run r := by
  induction cs using runs.induct with
  | case1 => simp [runs]
  | case2 c cs digit ih =>
    intro r hr
    rw [runs] at hr
    simp only [digit, ↓reduceIte] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · refine Or.inr ⟨by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact digit
      · exact List.all_eq_true.mp (List.all_takeWhile (p := Char.isDigit) (l := cs)) x hx
    · exact ih r hr
  | case3 c cs digit ih =>
    intro r hr
    rw [runs] at hr
    simp only [digit] at hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact Or.inl ⟨c, rfl, by simpa using digit⟩
    · exact ih r hr

theorem runs_flatten (cs : List Char) : (runs cs).flatten = cs := by
  induction cs using runs.induct with
  | case1 => simp [runs]
  | case2 c cs digit ih =>
    rw [runs]
    simp [digit, ih]
  | case3 c cs digit ih =>
    rw [runs]
    simp [digit, ih]

theorem decode_other (n : Nat) (rest : List Nat) (h : n ≠ 0x30) :
    decode (n :: rest) = Char.ofNat n :: decode rest := by
  rw [decode]
  simp [h]

theorem decode_digits (v len : Nat) (more : List Nat) :
    decode (0x30 :: v :: len :: more) =
      (more.take len).map Char.ofNat ++ decode (more.drop len) := by
  rw [decode]
  simp

theorem decode_code (r : List Char) (run : Run r) (rest : List Nat) :
    decode (code r ++ rest) = r ++ decode rest := by
  rcases run with ⟨c, rfl, digit⟩ | ⟨nonempty, digits⟩
  · have hc : c.toNat ≠ 0x30 := by
      intro h
      have : c = '0' := Char.toNat_inj.mp h
      simp [this] at digit
    simp only [code, List.head?_cons, Option.any_some, digit, Bool.false_eq_true, ↓reduceIte,
      List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [decode_other _ _ hc, Char.ofNat_toNat]
  · obtain ⟨c, cs, rfl⟩ := List.exists_cons_of_ne_nil nonempty
    have hc : c.isDigit = true := digits c (by simp)
    simp only [code, List.head?_cons, Option.any_some, hc, ite_true, List.cons_append]
    rw [decode_digits]
    simp [Function.comp_def]

theorem decode_runs (rs : List (List Char)) (h : ∀ r ∈ rs, Run r) :
    decode (rs.flatMap code) = rs.flatten := by
  induction rs with
  | nil => simp [decode]
  | cons r rs
    ih =>
    rw [List.flatMap_cons, decode_code r (h r (by simp)), ih fun r hr => h r (by simp [hr])]
    simp

theorem key_inj {a b : String} (h : key a = key b) : a = b := by
  have ha := decode_runs (runs a.toList) (runs_run a.toList)
  have hb := decode_runs (runs b.toList) (runs_run b.toList)
  rw [runs_flatten] at ha hb
  unfold key at h
  rw [h] at ha
  exact String.toList_inj.mp (ha.symm.trans hb)

/-- **Natural order is a total order**: no name comes before itself, it is transitive, and of two
different names one comes before the other. -/
theorem before_total (a b c : String) :
    before a a = false ∧
      (before a b = true → before b c = true → before a c = true) ∧
      (a ≠ b → before a b = true ∨ before b a = true) := by
  refine ⟨by simp [before, List.lt_irrefl], ?_, ?_⟩
  · simp only [before, decide_eq_true_eq]
    exact List.lt_trans
  · intro hne
    simp only [before, decide_eq_true_eq]
    rcases List.le_total (key a) (key b) with h | h
    · rcases (List.le_iff_lt_or_eq.mp h) with h | h
      · exact Or.inl h
      · exact absurd (key_inj h) hne
    · rcases (List.le_iff_lt_or_eq.mp h) with h | h
      · exact Or.inr h
      · exact absurd (key_inj h).symm hne

theorem takeWhile_dropWhile_stop (cs x : List Char) (h : ∃ a ∈ cs, a.isDigit = false) :
    (cs ++ x).takeWhile Char.isDigit = cs.takeWhile Char.isDigit ∧
      (cs ++ x).dropWhile Char.isDigit = cs.dropWhile Char.isDigit ++ x := by
  induction cs with
  | nil => simp at h
  | cons c cs ih =>
    by_cases hc : c.isDigit = true
    · have h' : ∃ a ∈ cs, a.isDigit = false := by
        obtain ⟨a, ha, hd⟩ := h
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [hc] at hd
        · exact ⟨a, ha, hd⟩
      obtain ⟨h1, h2⟩ := ih h'
      simp [hc, h1, h2]
    · simp [hc]

theorem runs_append (p x : List Char) (hp : ∀ c, p.getLast? = some c → c.isDigit = false) :
    runs (p ++ x) = runs p ++ runs x := by
  induction p using runs.induct with
  | case1 => simp [runs]
  | case2 c cs digit
    ih =>
    have stop : ∃ a ∈ cs, a.isDigit = false := by
      cases hcs : cs.getLast? with
      | none =>
        have : cs = [] := List.getLast?_eq_none_iff.mp hcs
        subst this
        simp [hp c (by simp)] at digit
      | some l => exact ⟨l, List.mem_of_getLast? hcs, hp l (by simp [List.getLast?_cons, hcs])⟩
    obtain ⟨h1, h2⟩ := takeWhile_dropWhile_stop cs x stop
    have hsuffix := List.dropWhile_suffix (l := cs) Char.isDigit
    obtain ⟨pre, hpre⟩ := hsuffix
    have hnil : cs.dropWhile Char.isDigit ≠ [] := by
      intro he
      obtain ⟨a, ha, hd⟩ := stop
      have := List.any_dropWhile (l := cs) (p := Char.isDigit)
      rw [he] at this
      have hall : cs.all Char.isDigit = false := by
        cases hh : cs.all Char.isDigit
        · rfl
        · exact absurd (List.all_eq_true.mp hh a ha) (by simp [hd])
      simp [hall] at this
    have hlast : ∀ l, (cs.dropWhile Char.isDigit).getLast? = some l → l.isDigit = false := by
      intro l hl
      apply hp l
      rw [List.getLast?_cons, ← hpre, List.getLast?_append, hl]
      simp
    have unfolded :
      runs (c :: cs) = (c :: cs.takeWhile Char.isDigit) :: runs (cs.dropWhile Char.isDigit) := by
      rw [runs]
      simp [digit]
    rw [List.cons_append, runs]
    simp only [digit, ↓reduceIte, h1, h2, ih hlast, unfolded]
    simp
  | case3 c cs digit
    ih =>
    have hcs : ∀ l, cs.getLast? = some l → l.isDigit = false := by
      intro l hl
      apply hp l
      simp [List.getLast?_cons, hl]
    have unfolded : runs (c :: cs) = [c] :: runs cs := by
      rw [runs]
      simp [digit]
    rw [List.cons_append, runs]
    simp only [digit, ih hcs, unfolded]
    simp

theorem runs_digits (d q : List Char) (nonempty : d ≠ []) (digits : ∀ c ∈ d, c.isDigit = true)
    (hq : ∀ c, q.head? = some c → c.isDigit = false) : runs (d ++ q) = d :: runs q := by
  obtain ⟨c, ds, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  have hc : c.isDigit = true := digits c (by simp)
  have hds : ∀ a ∈ ds, a.isDigit = true := fun a ha => digits a (by simp [ha])
  have htake : q.takeWhile Char.isDigit = [] := by
    cases q with
    | nil => rfl
    | cons a as => simp [hq a rfl]
  have hdrop : q.dropWhile Char.isDigit = q := by
    cases q with
    | nil => rfl
    | cons a as => simp [hq a rfl]
  rw [List.cons_append, runs]
  simp [hc, List.takeWhile_append_of_pos hds, List.dropWhile_append_of_pos hds, htake, hdrop]

theorem value_toDigits (n : Nat) : value (Nat.toDigits 10 n) = n := by
  induction n using Nat.strongRecOn with
  | ind n
    ih =>
    have digit : ∀ k, k < 10 → (Nat.digitChar k).toNat - 48 = k := by
      intro k hk
      rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
      all_goals
        first
        | omega
        | (simp [Nat.digitChar]; rfl)
        | simp [Nat.digitChar]
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · simp [value, digit n (by assumption)]
    · rename_i h
      simp only [value, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
      rw [ih (n / 10) (by omega), digit (n % 10) (Nat.mod_lt _ (by decide))]
      omega

/-- **Names that differ only in one number are ordered by it**: `p{n}q` comes before `p{m}q`
when `n < m`, whatever `p` and `q` say around the number. -/
theorem before_number (p q : String) (n m : Nat) (h : n < m)
    (hp : ∀ c, p.toList.getLast? = some c → c.isDigit = false)
    (hq : ∀ c, q.toList.head? = some c → c.isDigit = false) :
    before (p ++ toString n ++ q) (p ++ toString m ++ q) = true := by
  have shape (k : Nat) :
    key (p ++ toString k ++ q) = key p ++ code (Nat.toDigits 10 k) ++ key q := by
    have digits : ∀ c ∈ Nat.toDigits 10 k, c.isDigit = true := fun c hc =>
      Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
    simp only [key, String.toList_append, Nat.toString_eq_repr, Nat.toList_repr]
    rw [List.append_assoc, runs_append _ _ hp, runs_digits _ _ Nat.toDigits_ne_nil digits hq]
    simp
  have head (k : Nat) : (Nat.toDigits 10 k).head?.any Char.isDigit = true := by
    cases hd : Nat.toDigits 10 k with
    | nil => exact absurd hd Nat.toDigits_ne_nil
    | cons c cs =>
      simp [Nat.isDigit_of_mem_toDigits (b := 10) (n := k) (c := c) (by decide) (by decide)
            (by
              rw [hd]; simp)]
  simp only [before, decide_eq_true_eq, shape, List.append_assoc]
  apply List.append_left_lt
  simp only [code, head, ite_true, value_toDigits, List.cons_append]
  exact List.cons_lt_cons_iff.mpr (Or.inr ⟨rfl, List.cons_lt_cons_iff.mpr (Or.inl h)⟩)

end Linger.Display.View
