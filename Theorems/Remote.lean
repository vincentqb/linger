import Linger.Core.Remote
import Theorems.Name

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

end Linger.Core.Remote
