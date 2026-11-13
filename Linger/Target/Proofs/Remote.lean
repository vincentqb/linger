module

public import Linger.Target.CoreCode.Remote
public import Linger.Target.CoreSpec
public import Linger.Target.WorldSpec
import all Linger.Target.CoreCode.Remote
import Linger.Target.Proofs.Name

public section

/-! # Trusting a remote listing without trusting the remote

`parse` is total by construction (`filterMap` over `splitOnP`-split
lines — no partiality to prove). The load-bearing theorems: every name
in the result is `Valid` (name validation carries through, so remote data cannot
build a path outside the socket dir or smuggle bytes into a transport's argv),
and display fields are scrubbed of control characters (nothing a
remote returns can inject escape sequences into the local listing).
The later sections prove what the headlines `command_exact`, `transport_exact`,
`targetArgs_targetOperands` and `checkHosts_ok_iff` (`Challenge.lean`, part 3) rest on.
-/

namespace Linger.Target.Remote

open Linger.Target.Name

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
    (h : parseTarget target = some result) : Valid result.name := by
  obtain ⟨valid, name, _⟩ := (parseTarget_exact target result).mp h
  rw [name]
  exact ((targetValid_iff target).mp valid).2.1

/-! ## Encoded command lines

`command` spells the verb and every word in plain words, so a shell that passes plain words on
(`Shell.Literal`) hands the remote linger exactly the encoded words, and `decode` reads them back.
The decoder takes no other spelling: an encoded word decodes only to the word that encodes to it.
-/

theorem digitValue_hexDigit : ∀ n, n < 16 → digitValue (hexDigit n) = some n := by decide

theorem plainChar_hexDigit : ∀ n, n < 16 → Shell.plainChar (hexDigit n) = true := by decide

/-- A character `digitValue` reads is the digit `hexDigit` writes for its value. -/
theorem hexDigit_digitValue {c : Char} {n : Nat} (read : digitValue c = some n) :
    n < 16 ∧ hexDigit n = c := by
  unfold digitValue at read
  by_cases digit : '0' ≤ c ∧ c ≤ '9'
  · simp only [digit, and_self, ↓reduceIte, Option.some.injEq] at read
    subst read
    have low : 48 ≤ c.toNat := digit.1
    have high : c.toNat ≤ 57 := digit.2
    have back : 48 + (c.toNat - 48) = c.toNat := by omega
    refine ⟨by omega, ?_⟩
    simp only [hexDigit, show c.toNat - 48 < 10 by omega, ↓reduceIte, back, Char.ofNat_toNat]
  · by_cases letter : 'a' ≤ c ∧ c ≤ 'f'
    · simp only [digit, letter, and_self, ↓reduceIte, Option.some.injEq] at read
      subst read
      have low : 97 ≤ c.toNat := letter.1
      have high : c.toNat ≤ 102 := letter.2
      have back : 87 + (c.toNat - 87) = c.toNat := by omega
      refine ⟨by omega, ?_⟩
      simp only [hexDigit, show ¬c.toNat - 87 < 10 by omega, ↓reduceIte, back, Char.ofNat_toNat]
    · simp [digit, letter] at read

theorem unhex_hexChars (bytes done : List UInt8) :
    unhex (hexChars bytes) done = some (done.reverse ++ bytes) := by
  induction bytes generalizing done with
  | nil => simp [hexChars, unhex]
  | cons b bytes
    ih =>
    have high : b.toNat / 16 < 16 := by
      have := b.toNat_lt; omega
    have low : b.toNat % 16 < 16 := Nat.mod_lt _ (by decide)
    have byte : UInt8.ofNat (16 * (b.toNat / 16) + b.toNat % 16) = b := by
      rw [Nat.div_add_mod]
      exact UInt8.ofNat_toNat
    simp only [hexChars, List.flatMap_cons, List.cons_append, List.nil_append] at ih ⊢
    simp [unhex, digitValue_hexDigit _ high, digitValue_hexDigit _ low, byte, ih]

/-- Digits `unhex` reads are the digits `hexChars` writes for the bytes it reads. -/
theorem unhex_eq_some {digits : List Char} {done out : List UInt8}
    (read : unhex digits done = some out) :
    ∃ bytes, digits = hexChars bytes ∧ out = done.reverse ++ bytes := by
  induction digits, done using unhex.induct with
  | case1 done =>
    simp only [unhex, Option.some.injEq] at read
    exact ⟨[], rfl, by simp [read]⟩
  | case2 high low rest done h l readHigh readLow
    ih =>
    simp only [unhex, readHigh, readLow] at read
    obtain ⟨bytes, rfl, rfl⟩ := ih read
    obtain ⟨hBound, hDigit⟩ := hexDigit_digitValue readHigh
    obtain ⟨lBound, lDigit⟩ := hexDigit_digitValue readLow
    have value : (UInt8.ofNat (16 * h + l)).toNat = 16 * h + l := by
      simp only [UInt8.toNat_ofNat']
      omega
    refine ⟨UInt8.ofNat (16 * h + l) :: bytes, ?_, by simp⟩
    simp only [hexChars, List.flatMap_cons, value, List.cons_append, List.nil_append]
    rw [show (16 * h + l) / 16 = h by omega, show (16 * h + l) % 16 = l by omega, hDigit, lDigit]
  | case3 high low rest done notBoth =>
    simp only [unhex] at read
    simp at read
  | case4 c done => simp [unhex] at read

/-- The UTF-8 bytes `fromUTF8?` reads are the bytes of the string it returns. -/
private theorem fromUTF8?_eq_some {bytes : List UInt8} {word : String}
    (read : String.fromUTF8? (ByteArray.mk bytes.toArray) = some word) :
    word.toUTF8.data.toList = bytes := by
  unfold String.fromUTF8? at read
  split at read
  · simp only [Option.some.injEq] at read
    subst read
    simp [String.fromUTF8, String.toUTF8_eq_toByteArray]
  · simp at read

theorem decodeWord_encodeWord (word : String) : decodeWord (encodeWord word) = some word := by
  simp only [decodeWord, encodeWord, String.toList_ofList, unhex_hexChars, List.reverse_nil,
    List.nil_append, Option.bind_some, Array.toArray_toList]
  show String.fromUTF8? word.toUTF8 = some word
  simp only [String.fromUTF8?, String.toUTF8_eq_toByteArray, word.isValidUTF8, dite_true]
  rfl

/-- **One spelling.** An encoded word decodes to a word exactly when it is that word's encoding:
the decoder reads back every word the encoder writes, and nothing else. -/
theorem decodeWord_eq_some_iff (encoded word : String) :
    decodeWord encoded = some word ↔ encoded = encodeWord word := by
  constructor
  · intro read
    unfold decodeWord at read
    split at read
    · rename_i digits spelled
      cases bytesRead : unhex digits [] with
      | none => simp [bytesRead] at read
      | some bytes =>
        simp only [bytesRead, Option.bind_some] at read
        obtain ⟨written, rfl, same⟩ := unhex_eq_some bytesRead
        simp only [List.reverse_nil, List.nil_append] at same
        subst same
        rw [← String.toList_inj, spelled, encodeWord, String.toList_ofList, fromUTF8?_eq_some read]
    · simp at read
  · rintro rfl
    exact decodeWord_encodeWord word

theorem decode_map_encodeWord (words : List String) :
    decode (words.map encodeWord) = some words := by
  induction words with
  | nil => rfl
  | cons w ws
    ih =>
    simp only [decode, List.map_cons, List.mapM_cons, decodeWord_encodeWord] at ih ⊢
    simp [ih]

theorem plain_encodeWord (word : String) : Shell.plain (encodeWord word) = true := by
  simp only [Shell.plain, encodeWord, String.toList_ofList, Bool.and_eq_true, List.all_eq_true]
  refine ⟨by decide, ?_⟩
  intro c member
  simp only [hexChars, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at member
  obtain ⟨b, -, rfl | rfl⟩ := member
  · exact
      plainChar_hexDigit _
        (by
          have := b.toNat_lt; omega)
  · exact plainChar_hexDigit _ (Nat.mod_lt _ (by decide))

theorem plain_marker : Shell.plain marker = true := by decide

/-- **The marker is no session's name**, so a linger that reads the command line without
decoding it cannot take it for one. -/
theorem marker_invalid : ¬Valid marker := by
  unfold Valid
  decide

/-- **What the remote shell passes on.** Through a shell that passes plain words on, the remote
linger receives `marker` and the verb and words, encoded. -/
theorem command_split (split : String → List String) (literal : Shell.Literal split) (verb : String)
    (words : List String) :
    split (command verb words) = "linger" :: marker :: (verb :: words).map encodeWord := by
  apply literal
  intro word member
  simp only [List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨original, -, rfl⟩
  · exact plain_marker
  · exact plain_encodeWord original

/-- **What goes in comes out.** Through any shell that passes plain words on, the remote linger
receives `marker` and words that decode to exactly the verb and words the local one sent. -/
theorem command_decode (split : String → List String) (literal : Shell.Literal split)
    (verb : String) (words : List String) :
    ∃ encoded,
      split (command verb words) = "linger" :: marker :: encoded ∧
        decode encoded = some (verb :: words) :=
  ⟨_, command_split split literal verb words, decode_map_encodeWord _⟩

/-! ## A shell that reads backslashes inside quotes, as fish does

`Shell.Literal` says nothing about quotes, so a shell may read them its own way and still keep
it. `fishSplit` reads a line as fish does, as far as single quotes and backslashes go: an
unquoted space ends a word, a single quote opens or closes a quoted region, inside one a
backslash before a quote or a backslash is dropped, and outside one a backslash makes the next
character literal. POSIX quoting writes a quote in a word as `'\''`, which fish reads as a quote
inside the quoted region, so the region does not close where POSIX quoting meant it to. -/

/-- The words fish reads from `line`, given whether a quoted region is open and the word read so
far, as far as single quotes and backslashes go. -/
def fishRead : List Char → Bool → List Char → List (List Char)
  | [], _, word => [word]
  | ' ' :: rest, false, word => word :: fishRead rest false []
  | '\'' :: rest, quoted, word => fishRead rest (!quoted) word
  | '\\' :: next :: rest, quoted, word =>
    if quoted = false ∨ next = '\'' ∨ next = '\\' then fishRead rest quoted (word ++ [next])
    else fishRead (next :: rest) quoted (word ++ ['\\'])
  | c :: rest, quoted, word => fishRead rest quoted (word ++ [c])

/-- The words fish passes a program for a line, read as `fishRead` does. -/
def fishSplit (line : String) : List String := (fishRead line.toList false []).map String.ofList

private theorem fishRead_word (word rest : List Char) (quoted : Bool) (read : List Char)
    (safe : ∀ c ∈ word, c ≠ ' ' ∧ c ≠ '\'' ∧ c ≠ '\\') :
    fishRead (word ++ rest) quoted read = fishRead rest quoted (read ++ word) := by
  induction word generalizing read with
  | nil => simp
  | cons c word ih =>
    obtain ⟨space, quote, backslash⟩ := safe c (by simp)
    have step :
      fishRead (c :: (word ++ rest)) quoted read =
        fishRead (word ++ rest) quoted (read ++ [c]) := by
      rw [fishRead.eq_def]
      split <;> simp_all
    rw [List.cons_append, step, ih (read ++ [c]) (fun d member => safe d (by simp [member]))]
    simp

private theorem plain_safe {word : String} (isPlain : Shell.plain word = true) :
    ∀ c ∈ word.toList, c ≠ ' ' ∧ c ≠ '\'' ∧ c ≠ '\\' := by
  intro c member
  unfold Shell.plain at isPlain
  split at isPlain
  · rename_i first rest spelled
    rw [spelled] at member
    simp only [Bool.and_eq_true, List.all_eq_true] at isPlain
    rcases List.mem_cons.mp member with rfl | inRest
    · revert isPlain
      simp only [decide_eq_true_eq, and_imp]
      intro _ _ _
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp_all
    · have plainChar := isPlain.2 c inRest
      simp only [Shell.plainChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        beq_iff_eq] at plainChar
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> simp_all
  · simp at isPlain

private theorem fishRead_plain (words : List String) (allPlain : ∀ w ∈ words, Shell.plain w = true)
    (nonempty : words ≠ []) :
    fishRead ([' '].intercalate (words.map String.toList)) false [] = words.map String.toList := by
  induction words with
  | nil => contradiction
  | cons word words ih =>
    cases words with
    | nil =>
      have := fishRead_word word.toList [] false [] (plain_safe (allPlain word (by simp)))
      simp_all [fishRead]
    | cons next
      more =>
      have step :=
        fishRead_word word.toList (' ' :: [' '].intercalate ((next :: more).map String.toList))
          false [] (plain_safe (allPlain word (by simp)))
      have rest := ih (fun w member => allPlain w (by simp_all)) (by simp)
      simp only [List.map_cons, List.intercalate_cons_cons, List.append_assoc,
        List.singleton_append] at step rest ⊢
      rw [step]
      simp only [fishRead, List.nil_append]
      rw [rest]

/-- **fish keeps the world claim**: it passes plain words on. -/
theorem fishSplit_literal : Shell.Literal fishSplit := by
  intro words allPlain
  have withName : ∀ w ∈ "linger" :: words, Shell.plain w = true := by
    intro w member
    rcases List.mem_cons.mp member with rfl | inWords
    · decide
    · exact allPlain w inWords
  simp only [fishSplit, String.toList_intercalate, show " ".toList = [' '] from rfl]
  rw [fishRead_plain _ withName (by simp)]
  simp [List.map_map]

/-- **…and misreads POSIX quoting.** POSIX quoting of `send \'` reaches a program, through fish,
as `send ''`: the backslash is gone, and the quote that POSIX quoting escaped closed the quoted
region instead, so what followed it would be read as shell syntax. -/
theorem fishSplit_quoted :
    fishSplit
        (String.intercalate " "
          (["linger", "send", "\\'"].map fun word =>
            String.ofList
              ('\'' ::
                  word.toList.flatMap
                    (fun c => if c = '\'' then ['\'', '\\', '\'', '\''] else [c]) ++
                ['\'']))) =
      ["linger", "send", "''"] := by
  simp only [fishSplit, String.toList_intercalate, List.map_cons, List.map_nil,
    String.toList_ofList]
  decide

/-! ## Target operands

`attach` and `capture` read their target with `targetArgs`, after their options.
Every such argv linger builds for itself, locally or for a remote linger, places
the target with `targetOperands`; `command_decode` carries the words across SSH. -/

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

/-- No arguments name no target. -/
theorem targetArgs_nil : targetArgs [] = none := by simp [targetArgs]

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

/-! ## Transports

`targetArgv` runs the host's attach command for an attach and its query command for every other
verb, then `commandWords`: `linger` and plain words, which a transport hands on as they are
(`Transport.Delivers`), and which ssh joins into the line `command` spells. -/

/-- Joined by spaces, as ssh joins its command's words, `commandWords` is `command`. -/
theorem intercalate_commandWords (verb : String) (words : List String) :
    String.intercalate " " (commandWords verb words) = command verb words := by
  simp only [commandWords, command]

/-- After `linger`, every word linger runs is plain, so every shell and transport passes it on. -/
theorem plain_commandWords (verb : String) (words : List String) :
    ∀ word ∈ (commandWords verb words).tail, Shell.plain word = true := by
  intro word member
  simp only [commandWords, List.tail_cons, List.mem_cons, List.mem_map] at member
  rcases member with rfl | ⟨original, -, rfl⟩
  · exact plain_marker
  · exact plain_encodeWord original

/-- The argv of a verb on a host's session: the host's attach command for an attach and its query
command otherwise, then `linger`, the marker and the encoded verb, options, target operands and
arguments. -/
theorem targetArgv_eq (transport : Transport) (verb : String) (options : List String)
    (name : String) (args : List String) :
    targetArgv transport verb options name args =
      (if verb = "attach" then transport.attach else transport.query) ++
        "linger" ::
          marker ::
          (verb :: options ++
                (if verb = "attach" ∨ verb = "capture" then targetOperands name else [name]) ++
                args).map
            encodeWord := by
  simp [targetArgv, argv, operands, commandWords]

/-- A line's words after its host name no command: ssh reaches it. -/
theorem transportOf_nil (host : String) : transportOf host [] = .ok (ssh host) := by
  simp [transportOf]

/-- **A host's line still means what it meant.** A line whose one word is a host, as every line of
the file was before lines named commands, reaches that host with ssh. -/
theorem configLine_host {line host : String} (only : lineWords line = [host])
    (named : host.startsWith "#" = false) : configLine line = some (.ok (host, ssh host)) := by
  simp [configLine, only, named, transportOf_nil, Except.map]

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
