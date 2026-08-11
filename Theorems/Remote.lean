import Zmx.Core.Remote
import Theorems.Name
/-! # §Remote — trusting a remote listing without trusting the remote

`parse` is total by construction (`filterMap` over `foldl`-split
lines — no partiality to prove). The load-bearing theorems: every name
in the result is `Valid` (§Name carries through, so remote data cannot
build a path outside the socket dir or smuggle bytes into ssh argv),
and display fields are scrubbed of control characters (nothing a
remote returns can inject escape sequences into the TUI frame).
-/

namespace Zmx.Core.Remote

open Zmx.Core.Name

/-- Every parsed row's name is sanitized-valid, whatever the remote
sent. -/
theorem parse_names_valid (out : String) :
    ∀ r ∈ parse out, Valid r.name := by
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
theorem scrub_no_ctl (s : String) :
    ∀ c ∈ (scrub s).toList, c.toNat ≥ 0x20 ∧ c.toNat ≠ 0x7F := by
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

end Zmx.Core.Remote
