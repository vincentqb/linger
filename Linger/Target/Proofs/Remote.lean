module

public import Linger.Target.CoreCode.Remote
public import Linger.Target.CoreSpec
import all Linger.Target.CoreCode.Remote
import Linger.Target.Proofs.Name

public section

/-! # Remote targets, the transport's argv and the remotes file

A target splits at its first `@` into a name, accepted without rewriting, and a host kept verbatim,
with the grammar commands and interactive creation share; a host's `serve` runs with exactly its
transport's command and `linger serve`; a remotes line that is only a host reaches it with ssh; and
`checkHosts` refuses a host list with a duplicate or a control character, which the headline
`checkHosts_ok_iff` (`Challenge.lean`, part 3) rests on.
-/

namespace Linger.Target.Remote

open Linger.Target.Name

/-- Scrubbed strings carry no C0/C1 controls or DEL. -/
theorem scrub_no_ctl (s : String) :
    ∀ c ∈ (scrub s).toList, c.toNat ≥ 32 ∧ (c.toNat < 127 ∨ c.toNat ≥ 160) := by
  intro c hc
  unfold scrub at hc
  rw [String.toList_ofList] at hc
  simpa only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] using (List.mem_filter.mp hc).2

/-- Commands and interactive creation use exactly the same target grammar. -/
theorem targetValid_iff (target : String) :
    targetValid target = true ↔
      target ≠ "" ∧
        Accepted ((target.splitOn "@").headD "") ∧
        (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
        ((target.splitOn "@").tail = [] ∨
          String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  have accepted (name : String) : (accept name).isSome = true ↔ Accepted name := by
    cases h : accept name with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      intro u
      have := (accept_eq_some_iff name name).mpr ⟨rfl, u⟩
      rw [h] at this
      cases this
    | some r =>
      simp only [Option.isSome_some, true_iff]
      exact ((accept_eq_some_iff name r).mp h).2
  simp [targetValid, hostClean, accepted, and_assoc]

/-- Parsing preserves the exact name and complete host suffix; no fuzzy lookup
or name repair occurs at this boundary. -/
theorem parseTarget_exact (target : String) (result : Target) :
    parseTarget target = some result ↔
      targetValid target = true ∧
        result.name = (target.splitOn "@").headD "" ∧
        result.host =
          (if (target.splitOn "@").tail.isEmpty then none
          else some (String.intercalate "@" (target.splitOn "@").tail)) := by
  cases result
  simp only [parseTarget]
  split
  · rename_i valid
    simp only [valid, true_and, Option.some.injEq, Target.mk.injEq]
    exact and_congr eq_comm eq_comm
  · simp_all

theorem parseTarget_name_valid {target : String} {result : Target}
    (h : parseTarget target = some result) : Accepted result.name := by
  obtain ⟨valid, name, _⟩ := (parseTarget_exact target result).mp h
  rw [name]
  exact ((targetValid_iff target).mp valid).2.1

/-! ## Target operands

`attach` and `capture` read their target with `targetArgs`, after their options: `--` places any
name, and a name that starts with `-` only after it. -/

/-- **A name after `--` reads back as itself**, and everything after it stays the command's. -/
theorem targetArgs_separated (name : String) (rest : List String) :
    targetArgs ("--" :: name :: rest) = some (name, rest) := by simp [targetArgs]

/-- No arguments name no target. -/
theorem targetArgs_nil : targetArgs [] = none := by simp [targetArgs]

/-- **A bare option-like name is no operand.** Without `--`, a name starting with `-`
is refused, so the round trip needs the separator; `--` itself reads the next word. -/
theorem targetArgs_option (name : String) (rest : List String) (option : name.startsWith "-" = true)
    (separator : name ≠ "--") : targetArgs (name :: rest) = none := by
  simp [targetArgs, option, separator]

/-- **No bare name starting with `-` reads back as itself**, `--` included: such a
target follows `--`. -/
theorem targetArgs_option_ne (name : String) (rest : List String)
    (option : name.startsWith "-" = true) : targetArgs (name :: rest) ≠ some (name, rest) := by
  by_cases separator : name = "--"
  · subst separator
    rcases rest with _ | ⟨word, words⟩
    · simp [targetArgs]
    · simp only [targetArgs, ne_eq, Option.some.injEq, Prod.mk.injEq, not_and]
      exact fun _ same => List.cons_ne_self word words same.symm
  · rw [targetArgs_option name rest option separator]
    exact nofun

/-! ## Transports

A host's `serve` runs with its transport's command and then `linger serve`, and nothing else; a line
that names only a host reaches it with ssh. -/

/-- **A host's `serve` runs with exactly its transport's command and `linger serve`.** -/
theorem argv_eq (transport : Transport) :
    argv transport = transport.command ++ ["linger", "serve"] := by simp only [argv]

/-- A line's words after its host name no command: ssh reaches it. -/
theorem transportOf_nil (host : String) : transportOf host [] = ssh host := by simp [transportOf]

/-- **A host's line still means what it meant.** A line whose one word is a host, as every line of
the file was before lines named commands, reaches that host with ssh. -/
theorem configLine_host {line host : String} (only : lineWords line = [host])
    (named : host.startsWith "#" = false) : configLine line = some (host, ssh host) := by
  simp [configLine, only, named, transportOf_nil]

/-! ## The duplicate report

The diagnostic walk is also the validation gate. Its agreement with `Nodup`
establishes both refusal of duplicates and acceptance of duplicate-free lists. -/

/-- The diagnostic walk is a complete decision for duplicate freedom. -/
theorem firstDupHost_none_iff (hosts : List String) : firstDupHost hosts = none ↔ hosts.Nodup := by
  induction hosts with
  | nil => simp [firstDupHost]
  | cons a t ih =>
    simp only [firstDupHost, List.nodup_cons]
    split <;> simp_all

/-- The walk finds nothing only on a duplicate-free list. -/
theorem firstDupHost_none {hosts : List String} (h : firstDupHost hosts = none) : hosts.Nodup :=
  (firstDupHost_none_iff hosts).mp h

/-- Every duplicate list produces an offender for the refusal message. -/
theorem firstDupHost_isSome_of_not_nodup {hosts : List String} (h : ¬hosts.Nodup) :
    (firstDupHost hosts).isSome := by
  cases hd : firstDupHost hosts with
  | none => exact absurd (firstDupHost_none hd) h
  | some _ => rfl

/-- Validation accepts every clean, unique host list and returns it unchanged,
including its order. It cannot silently rewrite, drop or duplicate a host. -/
theorem checkHosts_ok_iff (hosts result : List String) :
    checkHosts hosts = .ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, hostClean x = true := by
  have hclean : hosts.find? (!hostClean ·) = none ↔ ∀ x ∈ hosts, hostClean x = true := by
    simp [List.find?_eq_none]
  rw [← firstDupHost_none_iff, ← hclean]
  cases hd : firstDupHost hosts <;> cases hc : hosts.find? (!hostClean ·) <;>
    simp [checkHosts, hd, hc, eq_comm]

end Linger.Target.Remote
