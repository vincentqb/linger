module

import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Commands

/-! # The command table

Each operation has exactly one command and each command one spelling: the table lists the
operations once each, in `Op.all`'s order, a word names the row whose word it is, help lists
every row once in table order, and a usage error quotes its command's own row. -/

namespace Linger.App.Commands

/-- `Op.all` lists every operation, -/
theorem mem_all (op : Op) : op ∈ Op.all := by cases op <;> decide

/-- …once. -/
theorem all_nodup : Op.all.Nodup := by decide

/-- **One row per operation**: the table's operations are `Op.all`, in order. -/
theorem table_ops : table.map (·.op) = Op.all := by decide

/-- No two commands share a word. -/
theorem words_nodup : (table.map (·.word)).Nodup := by decide

/-- The command table is not empty. -/
theorem table_ne_nil : table ≠ [] := by decide

/-- The removed words are not none. -/
theorem retired_ne_nil : retired ≠ [] := by decide

/-- A command's usage error: its word, then its arguments when it takes any. -/
theorem usageLine_eq (command : Command) :
    usageLine command =
      if command.args.isEmpty then s!"usage: linger {command.word}"
      else s!"usage: linger {command.word} {command.args}" := rfl

/-- A removed command's words name no command. -/
theorem retired_free : ∀ entry ∈ retired, lookup entry.1 = none := by decide

/-- Every command answers to its word. -/
theorem lookup_word : ∀ command ∈ table, lookup command.word = some command := by decide

/-- A word names only the row whose word it is. -/
theorem lookup_mem {word : String} {command : Command} (found : lookup word = some command) :
    command ∈ table ∧ command.word = word := by
  unfold lookup at found
  exact ⟨List.mem_of_find?_eq_some found, by simpa using List.find?_some found⟩

/-- Two rows of one operation are one row. -/
theorem op_inj : ∀ a ∈ table, ∀ b ∈ table, a.op = b.op → a = b := by decide

/-- **Every operation has a command**: some word names it. -/
theorem complete (op : Op) : ∃ word, (lookup word).map (·.op) = some op := by
  obtain ⟨command, member, rfl⟩ : ∃ command ∈ table, command.op = op := by cases op <;> decide
  exact ⟨command.word, by simp [lookup_word command member]⟩

/-- **One spelling per operation**: exactly one word names each operation, so no command is
another's alias and the parse from words to operations is one to one. -/
theorem one_spelling (op : Op) :
    ∃ word,
      (lookup word).map (·.op) = some op ∧
        ∀ other, (lookup other).map (·.op) = some op → other = word := by
  obtain ⟨command, member, rfl⟩ : ∃ command ∈ table, command.op = op := by cases op <;> decide
  refine ⟨command.word, by simp [lookup_word command member], ?_⟩
  intro word named
  cases found : lookup word with
  | none => simp [found] at named
  | some other =>
    simp only [found, Option.map_some, Option.some.injEq] at named
    obtain ⟨otherMember, rfl⟩ := lookup_mem found
    rw [op_inj _ otherMember _ member named]

/-- **Help lists every command once**, in table order, -/
theorem helpLines_eq : helpLines = table.map helpLine := rfl

/-- …joined one per line, -/
theorem helpText_eq : helpText = String.intercalate "\n" helpLines := rfl

/-- …each line its command's word, then a space. -/
theorem helpLine_word (command : Command) : ∃ rest, helpLine command = command.word ++ " " ++ rest :=
  ⟨_, rfl⟩

/-- **A usage error quotes its command's own row**: its word and the arguments help shows. -/
theorem usageLine_args (command : Command) (h : command.args.isEmpty = false) :
    usageLine command = s!"usage: linger {command.word} {command.args}" := by simp [usageLine, h]

end Linger.App.Commands
