module

public import Linger.Core.Remote
public import Linger.Core.Name
import all Linger.Core.Remote
import Theorems.Name

public section

/-! # §Remote — trusting a remote listing without trusting the remote

`parse` is total by construction (`filterMap` over `splitOnP`-split
lines — no partiality to prove). The load-bearing theorems: every name
in the result is `Valid` (§Name carries through, so remote data cannot
build a path outside the socket dir or smuggle bytes into ssh argv),
and display fields are scrubbed of control characters (nothing a
remote returns can inject escape sequences into the local listing).
-/

namespace Linger.Core.Remote

open Linger.Core.Name

/-- Parsed names are valid; an invalid peer name cannot become a different target. -/
theorem parseRecord_name_valid {lines : List String} {r : RemoteRow}
    (h : parseRecord lines = some r) : Valid r.name := by
  unfold parseRecord at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i raw heq
    cases hc : check raw with
    | none => simp [hc] at h
    | some name =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
      subst r
      obtain ⟨rfl, valid⟩ := (check_eq_some_iff raw name).mp hc
      exact valid

/-- Every parsed row's name is valid, whatever the remote
sent. -/
theorem parse_names_valid (out : String) : ∀ r ∈ parse out, Valid r.name := by
  intro r hr
  obtain ⟨rec, -, hparse⟩ := List.mem_filterMap.mp hr
  exact parseRecord_name_valid hparse

/-- Scrubbed strings carry no C0/C1 controls or DEL. -/
theorem scrub_no_ctl (s : String) :
    ∀ c ∈ (scrub s).toList, c.toNat ≥ 32 ∧ (c.toNat < 127 ∨ c.toNat ≥ 160) := by
  intro c hc
  unfold scrub at hc
  rw [String.toList_ofList] at hc
  simpa only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] using (List.mem_filter.mp hc).2

/-- Parsed display fields are scrubbed. -/
theorem parse_cmd_scrubbed (out : String) :
    ∀ r ∈ parse out, ∀ c ∈ r.cmd.toList, c.toNat ≥ 32 ∧ (c.toNat < 127 ∨ c.toNat ≥ 160) := by
  intro r hr
  unfold parse at hr
  obtain ⟨rec, -, h⟩ := List.mem_filterMap.mp hr
  unfold parseRecord at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i raw heq
    cases hc : check raw with
    | none => simp [hc] at h
    | some name =>
      simp only [hc, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
      subst r
      exact scrub_no_ctl _

/-- Commands and interactive creation use exactly the same target grammar. -/
theorem targetValid_iff (target : String) :
    targetValid target = true ↔
      target ≠ "" ∧
        Valid ((target.splitOn "@").headD "") ∧
        (∀ char ∈ target.toList, 32 ≤ char.toNat ∧ (char.toNat < 127 ∨ 160 ≤ char.toNat)) ∧
        ((target.splitOn "@").tail = [] ∨
          String.intercalate "@" (target.splitOn "@").tail ≠ "") := by
  simp [targetValid, hostClean, sanitize_eq_self_iff, and_assoc]

/-- Parsing preserves the exact name and complete SSH suffix; no fuzzy lookup
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
    (h : parseTarget target = some result) : Valid result.name := by
  obtain ⟨valid, name, _⟩ := (parseTarget_exact target result).mp h
  rw [name]
  exact ((targetValid_iff target).mp valid).2.1

/-! ## The literal subset of POSIX shell syntax

Inside single quotes, every character is literal. The sequence `'\''` emits
one quote and resumes the quoted region. A command consists only of these
words separated by spaces; there are no expansions or operators. This models
the shell syntax, not the SSH implementation. OS argument strings exclude NUL.
-/

namespace Shell

/-- Read a single-quoted region through its closing quote. -/
def quoted : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c == '\'' then
      match rest with
      | '\\' :: '\'' :: '\'' :: more => do
        let (text, tail) ← quoted more
        some ('\'' :: text, tail)
      | _ => some ([], rest)
    else do
      let (text, tail) ← quoted rest
      some (c :: text, tail)

/-- A word must start with a quote; unquoted shell syntax is outside the model. -/
def word : List Char → Option (List Char × List Char)
  | '\'' :: rest => quoted rest
  | _ => none

/-- A complete command contains only literal words and their separators. -/
inductive Words : List Char → List (List Char) → Prop where
  | last {source text} (read : word source = some (text, [])) : Words source [text]
  |
  next {source text tail rest} (read : word source = some (text, ' ' :: tail))
    (more : Words tail rest) : Words source (text :: rest)

theorem words_unique {source left right} (hl : Words source left) (hr : Words source right) :
    left = right := by
  induction hl generalizing right with
  | last read =>
    cases hr with
    | last other => simpa [read] using other
    | next other _ => simp [read] at other
  | next read more ih =>
    cases hr with
    | last other => simp [read] at other
    | next other
      rest =>
      simp only [read, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, true_and] at other
      obtain ⟨rfl, rfl⟩ := other
      exact congrArg (_ :: ·) (ih rest)

private theorem quoted_payload (chars tail : List Char)
    (boundary : tail = [] ∨ ∃ rest, tail = ' ' :: rest) :
    quoted
        (chars.flatMap (fun c => if c == '\'' then ['\'', '\\', '\'', '\''] else [c]) ++
          '\'' :: tail) =
      some (chars, tail) := by
  simp only [beq_iff_eq]
  induction chars with
  | nil => rcases boundary with rfl | ⟨rest, rfl⟩ <;> simp [quoted]
  | cons c chars ih =>
    by_cases quote : c = '\''
    · subst c
      simp [quoted, ih]
    · simp only [List.flatMap_cons, quote, ↓reduceIte, List.cons_append]
      rw [quoted.eq_def]
      simp [quote, ih]

end Shell

/-- Quoting round-trips every argument, including empty strings and shell syntax. -/
theorem shellQuote_roundtrip (s : String) (tail : List Char)
    (boundary : tail = [] ∨ ∃ rest, tail = ' ' :: rest) :
    Shell.word ((shellQuote s).toList ++ tail) = some (s.toList, tail) := by
  simpa [shellQuote, Shell.word, List.append_assoc] using
    Shell.quoted_payload s.toList tail boundary

private theorem quoted_words (words : List String) (nonempty : words ≠ []) :
    Shell.Words (String.intercalate " " (words.map shellQuote)).toList
      (words.map String.toList) := by
  induction words with
  | nil => contradiction
  | cons first rest ih =>
    cases rest with
    | nil =>
      apply Shell.Words.last
      simpa using shellQuote_roundtrip first [] (Or.inl rfl)
    | cons second rest =>
      apply Shell.Words.next
      · simpa [String.intercalate_cons_cons, String.toList_append] using
          shellQuote_roundtrip first
            (' ' :: (String.intercalate " " ((second :: rest).map shellQuote)).toList)
            (Or.inr ⟨_, rfl⟩)
      · simpa only [String.toList_intercalate, List.map_map, List.map_cons,
          show " ".toList = [' '] from rfl] using ih (by simp)

/-- The remote command parses as exactly `linger`, the verb and every supplied
word, with no additional shell action. -/
theorem command_argv (verb : String) (words : List String) :
    Shell.Words (command verb words).toList (("linger" :: verb :: words).map String.toList) :=
  quoted_words _ (by simp)

/-! ## Target operands

`attach` and `capture` read their target with `targetArgs`, after their options.
Every such argv linger builds for itself, locally or for a remote linger, places
the target with `targetOperands`; `command_argv` carries the words across SSH. -/

/-- **The operand round trip.** `targetArgs` reads `targetOperands name` back as
exactly `name`, and leaves everything after it to the command. -/
theorem targetArgs_targetOperands (name : String) (rest : List String) :
    targetArgs (targetOperands name ++ rest) = some (name, rest) := by
  unfold targetOperands
  by_cases option : name.startsWith "-" = true
  · simp [option, targetArgs]
  · have separator : name ≠ "--" := by
      rintro rfl
      exact option (by simp)
    simp [option, targetArgs, separator]

/-- **A bare option-like name is no operand.** Without `--`, a name starting with `-`
is refused, so the round trip needs the separator; `--` itself reads the next word. -/
theorem targetArgs_option (name : String) (rest : List String) (option : name.startsWith "-" = true)
    (separator : name ≠ "--") : targetArgs (name :: rest) = none := by
  simp [targetArgs, option, separator]

/-- **No bare name starting with `-` reads back as itself**, `--` included: such a
target needs `targetOperands`. -/
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

/-- The first-offender search succeeds exactly when every host is clean. -/
theorem firstDirtyHost_none_iff (hosts : List String) :
    firstDirtyHost hosts = none ↔ ∀ x ∈ hosts, hostClean x = true := by
  simp [firstDirtyHost, List.find?_eq_none]

/-- Validation accepts every clean, unique host list and returns it unchanged,
including its order. It cannot silently rewrite, drop or duplicate a host. -/
theorem checkHosts_ok_iff (hosts result : List String) :
    checkHosts hosts = .ok result ↔
      result = hosts ∧ hosts.Nodup ∧ ∀ x ∈ hosts, hostClean x = true := by
  rw [← firstDupHost_none_iff, ← firstDirtyHost_none_iff]
  cases hd : firstDupHost hosts <;> cases hc : firstDirtyHost hosts <;>
    simp [checkHosts, hd, hc, eq_comm]

/-- §Remote (dup guard): a validated host list is duplicate-free, so no
host is ever queried twice and no duplicate row can reach the listing.
This is the enforcement the `-r` flag / remotes file rely on. -/
theorem checkHosts_ok_nodup {hosts l : List String} (h : checkHosts hosts = .ok l) : l.Nodup := by
  obtain ⟨rfl, unique, _⟩ := (checkHosts_ok_iff hosts l).mp h
  exact unique

/-- **§Remote (argv guard): a validated host carries no control byte.** The host
string is handed to `ssh` as argv *and* printed into the listing, so a C0/C1 control or
DEL in it is refused at the boundary rather than scrubbed on the way out — scrubbing
would silently connect somewhere the user did not name. With
`checkHosts_ok_nodup` this is the whole contract `-r` and the remotes file rely on. -/
theorem checkHosts_ok_clean {hosts l : List String} (h : checkHosts hosts = .ok l) :
    ∀ x ∈ l, ∀ c ∈ x.toList, c.toNat ≥ 32 ∧ (c.toNat < 127 ∨ c.toNat ≥ 160) := by
  obtain ⟨rfl, _, clean⟩ := (checkHosts_ok_iff hosts l).mp h
  simpa [hostClean] using clean

/-! ## Records: every group the splitter emits is a real record -/

/-- **No record is empty.** A blank-line run cannot manufacture a slot for `parseRecord`. -/
theorem records_ne_nil (lines : List String) : ∀ g ∈ records lines, g ≠ [] := by
  intro g hg
  simpa [records] using (List.mem_filter.mp hg).2

end Linger.Core.Remote
