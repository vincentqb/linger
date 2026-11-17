module

-- The proofs unfold the status definitions, whose bodies only `import all` exposes.
import all Linger.Display.CoreCode.Status

/-! # The statuses partition the observation space, each column by its own sources

A legend is a claim, and it can be wrong in three ways: two rows that differ
could show the same glyphs (not exclusive), a row could match no glyph (not
covering), or a glyph could be unreachable (a lie in the legend). This file
rules out all three, for each column. `classify_iff`, the first headline of the status rule in
`Challenge.lean`, states the partition.

The legend predicates `Attention.Is` and `State.Is`, in `Linger/Display/CoreSpec.lean`, are the
columns as *described in the legend*, written independently of `classify`'s cascade — that
independence is the point. If they were the cascade's guards with the earlier branches negated,
cover and disjointness would be tautologies and the theorems would say nothing. As
written, `classify_sound` is a real claim: the cascade computes the description.
-/

namespace Linger.Display.Status

/-- The attention cascade agrees exactly with the attention legend. -/
theorem attentionOf_iff (o : Obs) (a : Attention) : attentionOf o = a ↔ a.Is o := by
  cases a <;> simp only [Attention.Is] <;> grind [attentionOf]

/-- The state cascade agrees exactly with the state legend. -/
theorem stateOf_iff (o : Obs) (s : State) : stateOf o = s ↔ s.Is o := by
  cases s <;> simp only [State.Is] <;> grind (splits := 16) [stateOf]

/-- The classifier agrees exactly with the independent legend predicates. -/
theorem classify_iff (o : Obs) (s : Status) : classify o = s ↔ Is s o := by
  obtain ⟨a, st⟩ := s
  rw [Is, ← attentionOf_iff, ← stateOf_iff]
  simp [classify]

/-- **Cover.** Every observation is in some status — no row can fail to be
described. -/
theorem cover (o : Obs) : ∃ s, Is s o := ⟨classify o, (classify_iff o _).mp rfl⟩

/-- **Disjoint.** No observation is in two statuses — two rows showing the
same glyphs really are in the same status. -/
theorem disjoint (o : Obs) (s t : Status) (hs : Is s o) (ht : Is t o) : s = t :=
  ((classify_iff o s).mpr hs).symm.trans ((classify_iff o t).mpr ht)

/-- **Sound.** The cascade computes the legend: what `classify` returns is
the status the row is actually in. This is the claim that would break if a
guard were mis-ordered. -/
theorem classify_sound (o : Obs) : Is (classify o) o := (classify_iff o _).mp rfl

/-- A running session whose daemon answered shows `⚑` exactly when it asks, whatever else it
shows. -/
theorem classify_running_asks (progress : Option Terminal.Mediation.Progress)
    (running unseen asks : Bool) :
    (classify { progress, running, unseen, asks }).attention = .asked ↔ asks = true := by
  cases asks <;> cases unseen <;> simp [classify, attentionOf]

/-- **Complete.** `classify` is the *only* function agreeing with the
legend, so the cascade is not one choice among several. Cover + disjoint +
sound, combined. -/
theorem classify_unique (o : Obs) (s : Status) (h : Is s o) : classify o = s :=
  (classify_iff o s).mpr h

/-- **Attention reads its own sources alone**: two observations that agree on the asks and the
new lines show one attention, whatever their state. -/
theorem attention_independent (o o' : Obs) (asks : o.asks = o'.asks)
    (unseen : o.unseen = o'.unseen) : (classify o).attention = (classify o').attention := by
  simp [classify, attentionOf, asks, unseen]

/-- **The state reads its own sources alone**: two observations that agree on the answer, the
daemon, the ending, the declared progress and the shell's marks show one state, whatever their
attention. -/
theorem state_independent (o o' : Obs) (known : o.known = o'.known)
    (daemonUp : o.daemonUp = o'.daemonUp) (exit : o.exit = o'.exit)
    (progress : o.progress = o'.progress) (running : o.running = o'.running) :
    (classify o).state = (classify o').state := by
  simp [classify, stateOf, known, daemonUp, exit, progress, running]

/-! ## Every glyph is reachable, and no two share one -/

/-- **Every pair is a status**: each attention with each state is produced by some observation,
so a session that rang while it works shows `⚑ ⣷`. -/
theorem reachable (a : Attention) (s : State) : ∃ o : Obs, classify o = ⟨a, s⟩ := by
  have ha : ∃ asks unseen, attentionOf { asks, unseen } = a := by
    cases a
    · exact ⟨true, false, rfl⟩
    · exact ⟨false, true, rfl⟩
    · exact ⟨false, false, rfl⟩
  obtain ⟨asks, unseen, ha⟩ := ha
  have hs :
    ∃ known daemonUp exit progress running,
      stateOf { known, daemonUp, exit, progress, running } = s := by
    cases s
    · exact ⟨false, true, none, none, false, rfl⟩
    · exact ⟨true, true, some 1, none, false, rfl⟩
    · exact ⟨true, true, some 0, none, false, rfl⟩
    · exact ⟨true, false, none, none, false, rfl⟩
    · exact ⟨true, true, none, some .error, false, rfl⟩
    · exact ⟨true, true, none, none, true, rfl⟩
    · exact ⟨true, true, none, some .paused, false, rfl⟩
    · exact ⟨true, true, none, none, false, rfl⟩
  obtain ⟨known, daemonUp, exit, progress, running, hs⟩ := hs
  refine ⟨{ known, daemonUp, exit, progress, running, unseen, asks }, ?_⟩
  simp only [classify, Status.mk.injEq]
  exact
    ⟨by
      rw [← ha]; rfl, by
      rw [← hs]; rfl⟩

/-- **No glyph collision.** Distinct states get distinct glyphs — the design
rule "share a glyph only when the action is the same" made concrete, so a
future merge has to delete a state rather than quietly overload a symbol. -/
theorem icon_injective (s t : State) (h : icon s = icon t) : s = t := by
  cases s <;> cases t <;> simp_all [icon]

/-- Distinct attentions get distinct marks. -/
theorem mark_injective (a b : Attention) (h : mark a = mark b) : a = b := by
  cases a <;> cases b <;> simp_all [mark]

/-- No mark is a state's glyph, so the two columns never read alike. -/
theorem mark_ne_icon (a : Attention) (s : State) : mark a ≠ icon s := by
  cases a <;> cases s <;> decide

/-- **The legend tells each glyph once**: `linger help` gives an `Attention` block, one line for
each mark, which begins with it, then a `State` block, one line for each state's glyph. -/
theorem legend_blocks :
    ∃ marks states,
      legend = "Attention" :: marks ++ "State" :: states ∧
        (∀ a : Attention,
          a ≠ .none → (marks.map fun line => line.toList.head?).count (some (mark a)) = 1) ∧
        (∀ line ∈ marks, ∃ a : Attention, a ≠ .none ∧ line.toList.head? = some (mark a)) ∧
        (∀ st, (states.map fun line => line.toList.head?).count (some (icon st)) = 1) ∧
        ∀ line ∈ states, ∃ st, line.toList.head? = some (icon st) := by
  refine
    ⟨counted.map (fun a => s!"{mark a}  {heard a}"),
      legendOrder.map fun st => s!"{icon st}  {seen st}", rfl, ?_, ?_, ?_, ?_⟩
  · intro a ha
    cases a <;> simp_all [counted, mark]
  · intro line h
    simp only [counted, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with h | h <;> subst h
    · exact ⟨.asked, by decide, by simp [mark]⟩
    · exact ⟨.unread, by decide, by simp [mark]⟩
  · intro st
    cases st <;> simp [legendOrder, icon]
  · intro line h
    simp only [legendOrder, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at h
    rcases h with h | h | h | h | h | h | h | h <;> subst h
    · exact ⟨.errored, by simp [icon]⟩
    · exact ⟨.working, by simp [icon]⟩
    · exact ⟨.paused, by simp [icon]⟩
    · exact ⟨.idle, by simp [icon]⟩
    · exact ⟨.exitedOk, by simp [icon]⟩
    · exact ⟨.exitedBad, by simp [icon]⟩
    · exact ⟨.resumable, by simp [icon]⟩
    · exact ⟨.unknown, by simp [icon]⟩

/-- Porcelain names carry no separator or newline, so a row stays one
unambiguous record — the invariant that makes tab-separated output safe
without an escaping pass. -/
theorem name_clean (s : State) : ∀ c ∈ (name s).toList, c ≠ '\t' ∧ c ≠ '\n' := by
  cases s <;> simp [name]

/-- The same for attention's porcelain names. -/
theorem attentionName_clean (a : Attention) :
    ∀ c ∈ (attentionName a).toList, c ≠ '\t' ∧ c ≠ '\n' := by cases a <;> simp [attentionName]

/-- `ofName` is a left inverse of `name`, so the human column and the
porcelain column can never disagree about a row. -/
theorem ofName_name (s : State) : ofName (name s) = s := by cases s <;> rfl

/-- `ofAttentionName` is a left inverse of `attentionName`. -/
theorem ofAttentionName_attentionName (a : Attention) : ofAttentionName (attentionName a) = a := by
  cases a <;> rfl

/-- The same for the porcelain names, which recipes parse. -/
theorem name_injective (s t : State) (h : name s = name t) : s = t := by
  simpa only [ofName_name] using congrArg ofName h

/-- The complete style vocabulary contains standard foreground SGRs only; its
quiet style adds dim and explicitly selects the default foreground. -/
theorem style_palette (s : State) :
    Linger.Display.Status.style s ∈ [[36], [33], [32], [31], [2, 39]] := by cases s <;> decide

/-- Positive counts appear once in attention order, independent of input order. -/
theorem attentionCounts_exact (attentions : List Attention) :
    Linger.Display.Status.attentionCounts attentions =
      (if attentions.count .asked = 0 then [] else [(.asked, attentions.count .asked)]) ++
        (if attentions.count .unread = 0 then [] else [(.unread, attentions.count .unread)]) := by
  simp only [attentionCounts, counted, List.filterMap_cons, List.filterMap_nil]
  split <;> split <;> simp_all

/-- Neither zero counts nor a blank attention can occur in an attention group. -/
theorem attentionCounts_mem (attentions : List Attention) (a : Attention) (n : Nat) :
    (a, n) ∈ Linger.Display.Status.attentionCounts attentions ↔
      a ∈ counted ∧ n = attentions.count a ∧ n ≠ 0 := by
  simp only [attentionCounts, List.mem_filterMap]
  constructor
  · rintro ⟨st, hm, he⟩
    split at he
    · contradiction
    · simp only [Option.some.injEq, Prod.mk.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      exact ⟨hm, rfl, by simpa using ‹¬(attentions.count st == 0) = true›⟩
  · rintro ⟨hm, rfl, hn⟩
    exact ⟨a, hm, by simp [hn]⟩

/-- The public string is precisely the positive-count attention groups with their
canonical marks, separated by one space. -/
theorem summary_exact (attentions : List Attention) :
    Linger.Display.Status.summary attentions =
      String.intercalate " "
        ((if attentions.count .asked = 0 then []
          else [(toString (attentions.count .asked)).push (mark .asked)]) ++
          (if attentions.count .unread = 0 then []
          else [(toString (attentions.count .unread)).push (mark .unread)])) := by
  rw [summary, attentionCounts_exact]
  split <;> split <;> simp_all

/-- With no attention counts, the summary has no placeholder or separator. -/
theorem summary_omits_zero (attentions : List Attention) (ha : attentions.count .asked = 0)
    (hu : attentions.count .unread = 0) : Linger.Display.Status.summary attentions = "" := by
  simp [summary_exact, ha, hu]

theorem summary_token_clean (attentions : List Attention) (a : Attention) (n : Nat)
    (h : (a, n) ∈ attentionCounts attentions) :
    ∀ c ∈ ((toString n).push (mark a)).toList, c.isDigit = true ∨ c ∈ ['⚑', '∙'] := by
  intro c hc
  simp only [String.toList_push, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · left
    rw [Nat.toString_eq_repr, Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  · right
    have hs := ((attentionCounts_mem attentions a n).mp h).1
    simp only [counted, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> decide

/-- Summary text contains only decimal digits, spaces and attention marks.
This is stronger than absence of newline or terminal escapes. -/
theorem summary_alphabet (attentions : List Attention) :
    ∀ c ∈ (Linger.Display.Status.summary attentions).toList,
      c.isDigit = true ∨ c ∈ [' ', '⚑', '∙'] := by
  have joinClean (strings : List String)
    (hs : ∀ text ∈ strings, ∀ c ∈ text.toList, c.isDigit = true ∨ c ∈ [' ', '⚑', '∙']) :
    ∀ c ∈ (String.intercalate " " strings).toList, c.isDigit = true ∨ c ∈ [' ', '⚑', '∙'] := by
    induction strings with
    | nil => simp
    | cons text rest ih =>
      cases rest with
      | nil => simpa using hs text (by simp)
      | cons next tail =>
        intro c hc
        simp only [String.intercalate_cons_cons, String.toList_append, List.mem_append] at hc
        rcases hc with (hc | hc) | hc
        · exact hs text (by simp) c hc
        · have space : (" " : String).toList = [' '] := by decide
          rw [space, List.mem_singleton] at hc
          subst c
          exact Or.inr (by simp)
        · exact ih (fun value hm => hs value (by simp [hm])) c hc
  apply joinClean
  intro text ht c hc
  obtain ⟨⟨a, n⟩, hm, rfl⟩ := List.mem_map.mp ht
  rcases summary_token_clean attentions a n hm c hc with hd | hi
  · exact Or.inl hd
  · exact Or.inr (by simp_all)

/-- A prompt or title can embed the summary verbatim: no controls, DEL or C1. -/
theorem summary_printable (attentions : List Attention) :
    ∀ c ∈ (Linger.Display.Status.summary attentions).toList,
      32 ≤ c.toNat ∧ (c.toNat < 127 ∨ 160 ≤ c.toNat) := by
  intro c hc
  rcases summary_alphabet attentions c hc with hd | hi
  · have := Char.isDigit_iff_toNat.mp hd
    change 48 ≤ c.toNat ∧ c.toNat ≤ 57 at this
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl <;> decide

/-! ## The legend `linger help` prints -/

/-- The legend lists every state: no session can show a glyph `linger help` does not explain. -/
theorem legendOrder_complete (s : State) : s ∈ legendOrder := by cases s <;> simp [legendOrder]

/-- …each once. -/
theorem legendOrder_nodup : legendOrder.Nodup := by decide

/-- Distinct states are described in distinct words, as they are shown with distinct glyphs
(`icon_injective`). -/
theorem seen_injective (s t : State) (h : seen s = seen t) : s = t := by
  cases s <;> cases t <;>
    first
    | rfl
    | exact absurd h (by decide)

/-- Titles and `ls --summary` count an attention exactly when it has a mark. -/
theorem attention_counted (attentions : List Attention) (a : Attention) :
    (∃ n, (a, n) ∈ attentionCounts attentions) ↔ a ≠ .none ∧ attentions.count a ≠ 0 := by
  have hc : a ∈ counted ↔ a ≠ .none := by cases a <;> simp [counted]
  constructor
  · rintro ⟨n, h⟩
    obtain ⟨hs, rfl, hn⟩ := (attentionCounts_mem attentions a n).mp h
    exact ⟨hc.mp hs, hn⟩
  · rintro ⟨hs, hn⟩
    exact ⟨_, (attentionCounts_mem attentions a _).mpr ⟨hc.mpr hs, rfl, hn⟩⟩

end Linger.Display.Status
