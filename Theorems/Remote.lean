module

public import Linger.Core.Remote
import all Linger.Core.Remote
import Theorems.Name

public section

/-! # §Remote — trusting a remote listing without trusting the remote

`parse` is total by construction (`filterMap` over `foldl`-split
lines — no partiality to prove). The load-bearing theorems: every name
in the result is `Valid` (§Name carries through, so remote data cannot
build a path outside the socket dir or smuggle bytes into ssh argv),
and display fields are scrubbed of control characters (nothing a
remote returns can inject escape sequences into the local listing).
-/

namespace Linger.Core.Remote

open Linger.Core.Name

/-- Every parsed row's name is sanitized-valid, whatever the remote
sent. -/
theorem parse_names_valid (out : String) : ∀ r ∈ parse out, Valid r.name := by
  intro r hr
  unfold parse at hr
  obtain ⟨rec, -, hparse⟩ := List.mem_filterMap.mp hr
  unfold parseRecord at hparse
  dsimp only at hparse
  split at hparse
  · exact absurd hparse (by simp)
  · rename_i kv heq
    simp only [Option.some.injEq] at hparse
    subst hparse
    exact sanitize_valid _

/-- Scrubbed strings carry no control bytes (C0, DEL — the ANSI
introducers). -/
theorem scrub_no_ctl (s : String) : ∀ c ∈ (scrub s).toList, c.toNat ≥ 0x20 ∧ c.toNat ≠ 0x7F := by
  intro c hc
  unfold scrub at hc
  rw [String.toList_ofList] at hc
  have := (List.mem_filter.mp hc).2
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  omega

/-- Parsed display fields are scrubbed. -/
theorem parse_cmd_scrubbed (out : String) :
    ∀ r ∈ parse out, ∀ c ∈ r.cmd.toList, c.toNat ≥ 0x20 ∧ c.toNat ≠ 0x7F := by
  intro r hr
  unfold parse at hr
  obtain ⟨rec, -, hparse⟩ := List.mem_filterMap.mp hr
  unfold parseRecord at hparse
  dsimp only at hparse
  split at hparse
  · exact absurd hparse (by simp)
  · simp only [Option.some.injEq] at hparse
    subst hparse
    exact scrub_no_ctl _

/-- §Remote (dup guard): a validated host list is duplicate-free, so no
host is ever queried twice and no duplicate row can reach the listing.
This is the enforcement the `-r` flag / remotes file rely on. -/
theorem checkHosts_ok_nodup {hosts l : List String} (h : checkHosts hosts = .ok l) : l.Nodup := by
  unfold checkHosts at h
  split at h
  · simp at h
  · rename_i hnd
    split at h
    · simp at h
    · simp only [Except.ok.injEq] at h
      subst h
      simpa using hnd

/-- A list with no dirty host is one where `hostClean` holds of every entry. The
walk and the predicate agree, which is what lets the theorem below be about the
*bytes* rather than about `firstDirtyHost`. -/
theorem firstDirtyHost_none {hosts : List String} (h : firstDirtyHost hosts = none) :
    ∀ x ∈ hosts, hostClean x = true := by
  induction hosts with
  | nil =>
    intro x hx; exact absurd hx (by simp)
  | cons a t ih =>
    unfold firstDirtyHost at h
    split at h
    · rename_i hc
      intro x hx
      rcases List.mem_cons.mp hx with he | ht
      · subst he; exact hc
      · exact ih h x ht
    · exact absurd h (by simp)

/-- **§Remote (argv guard): a validated host carries no control byte.** The host
string is handed to `ssh` as argv *and* printed into the listing, so a C0 control or
DEL in it is refused at the boundary rather than scrubbed on the way out — scrubbing
would silently connect somewhere the user did not name. With
`checkHosts_ok_nodup` this is the whole contract `-r` and the remotes file rely on. -/
theorem checkHosts_ok_clean {hosts l : List String} (h : checkHosts hosts = .ok l) :
    ∀ x ∈ l, ∀ c ∈ x.toList, c.toNat ≥ 0x20 ∧ c.toNat ≠ 0x7F := by
  unfold checkHosts at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i hdirty
      simp only [Except.ok.injEq] at h
      subst h
      intro x hx c hc
      have hcl : hostClean x = true := firstDirtyHost_none hdirty x hx
      unfold hostClean at hcl
      have := List.all_eq_true.mp hcl c hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact this

/-! ## Records: every group the splitter emits is a real record

`parse` `filterMap`s `parseRecord` over `records`' output, so an empty group would mean a run
of blank lines had manufactured a record slot. A group is appended only under `¬cur.isEmpty`
and `reverse` preserves that, so the invariant holds — and it is the one a consumer needs.

Deliberately *not* stated: `(records lines).flatten = lines`. It is **false** — blank lines
are dropped. The true version is `= lines.filter (¬·.trimAscii.isEmpty)`, which is strictly
stronger and needs a `done.flatten ++ cur.reverse` invariant; it earns its keep only when a
caller wants line-level fidelity, and none does. -/

private theorem foldl_records_ne_nil :
    ∀ (lines : List String) (done : List (List String)) (cur : List String),
      (∀ g ∈ done, g ≠ []) →
        ∀
          g ∈
            (lines.foldl
                (fun (acc : List (List String) × List String) l =>
                  if l.trimAscii.isEmpty then
                    (if acc.2.isEmpty then acc.1 else acc.1 ++ [acc.2.reverse], [])
                  else (acc.1, l :: acc.2))
                (done, cur)).1,
          g ≠ []
  | [], _, _, hd => by simpa using hd
  | l :: t, done, cur, hd => by
    simp only [List.foldl_cons]
    split
    · split
      · exact foldl_records_ne_nil t _ _ hd
      · rename_i hne
        refine foldl_records_ne_nil t _ _ ?_
        intro g hg
        rcases List.mem_append.mp hg with h1 | h2
        · exact hd g h1
        · rw [List.mem_singleton] at h2
          subst h2
          simpa using hne
    · exact foldl_records_ne_nil t _ _ hd

/-- **No record is empty.** A blank-line run cannot manufacture a slot for `parseRecord`. -/
theorem records_ne_nil (lines : List String) : ∀ g ∈ records lines, g ≠ [] := by
  intro g hg
  unfold records at hg
  dsimp only at hg
  split at hg
  · exact foldl_records_ne_nil lines [] [] (by simp) g hg
  · rcases List.mem_append.mp hg with h1 | h2
    · exact foldl_records_ne_nil lines [] [] (by simp) g h1
    · rename_i hne
      rw [List.mem_singleton] at h2
      subst h2
      simpa using hne

/-- **§Name at the record level.** Whatever a remote host sent, a parsed row's name has been
through `sanitize` — so it is safe to interpolate into a socket path. `parse_names_valid` is
this plus `mem_filterMap`; stating it here is what makes the guarantee a property of the
record parser rather than of the listing walk. -/
theorem parseRecord_name_valid {lines : List String} {r : RemoteRow}
    (h : parseRecord lines = some r) : Valid r.name := by
  unfold parseRecord at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i kv heq
    simp only [Option.some.injEq] at h
    subst h
    exact sanitize_valid _

/-! ## The duplicate report

`checkHosts` rejects on `¬hosts.Nodup` but fills its message from `firstDupHost`. If the two
could disagree the refusal would read `remote host '' listed more than once`, so what needs
proving is that the walk and `Nodup` agree exactly — not that the walk is the gate. -/

/-- The walk finds nothing only on a duplicate-free list. -/
theorem firstDupHost_none {hosts : List String} (h : firstDupHost hosts = none) : hosts.Nodup := by
  induction hosts with
  | nil => exact List.nodup_nil
  | cons a t ih =>
    unfold firstDupHost at h
    split at h
    · exact absurd h (by simp)
    · rename_i hc
      exact List.nodup_cons.mpr ⟨fun hm => hc (List.contains_iff_mem.mpr hm), ih h⟩

/-- …and it finds nothing on every duplicate-free list. -/
theorem firstDupHost_none_of_nodup {hosts : List String} (h : hosts.Nodup) :
    firstDupHost hosts = none := by
  induction hosts with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨ha, ht⟩ := List.nodup_cons.mp h
    show (if t.contains a then some a else firstDupHost t) = none
    split
    · rename_i hc
      exact absurd (List.contains_iff_mem.mp hc) ha
    · exact ih ht

/-- **So the refusal always names an offender.** This is the claim the message depends on:
`checkHosts` decided on `Nodup`, and this says `firstDupHost` cannot come back empty once
that decision has gone against the caller. -/
theorem firstDupHost_isSome_of_not_nodup {hosts : List String} (h : ¬hosts.Nodup) :
    (firstDupHost hosts).isSome := by
  cases hd : firstDupHost hosts with
  | none => exact absurd (firstDupHost_none hd) h
  | some _ => rfl

end Linger.Core.Remote
