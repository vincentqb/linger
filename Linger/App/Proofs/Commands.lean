module

import all Linger.App.Spec
import all Linger.App.Commands

/-! # The command table

Each word names one command, every command is found by each of its words, help lists every
command once in table order, and a usage error quotes its command's own row. -/

namespace Linger.App.Commands

/-- **One word, one command**: no two commands, and no command and another's spelling, share a
word. -/
theorem words_nodup : words.Nodup := by decide

/-- The command table is not empty. -/
theorem table_ne_nil : table ≠ [] := by decide

/-- The removed words are not none. -/
theorem retired_ne_nil : retired ≠ [] := by decide

/-- No two commands share a word, spelled over the table. -/
theorem table_words_nodup : (table.flatMap fun command => command.word :: command.aliases).Nodup :=
  words_nodup

/-- A command's usage error: its word, then its arguments when it takes any. -/
theorem usageLine_eq (command : Command) :
    usageLine command =
      if command.args.isEmpty then s!"usage: linger {command.word}"
      else s!"usage: linger {command.word} {command.args}" := rfl

/-- A removed command's words name no command. -/
theorem retired_free : ∀ entry ∈ retired, lookup entry.1 = none := by decide

/-- Every command answers to its word, -/
theorem lookup_word : ∀ command ∈ table, lookup command.word = some command := by decide

/-- …and to each of its other spellings. -/
theorem lookup_alias : ∀ command ∈ table, ∀ word ∈ command.aliases, lookup word = some command := by
  decide

/-- **Help lists every command once**, in table order, -/
theorem helpLines_eq : helpLines = table.map helpLine := rfl

/-- …joined one per line. -/
theorem helpText_eq : helpText = String.intercalate "\n" helpLines := rfl

/-- A command's help line is its word and arguments, padded to `summaryColumn` with at least two
spaces, then its summary. -/
theorem helpLine_eq (command : Command) :
    helpLine command =
      let synopsis :=
        if command.args.isEmpty then command.word else s!"{command.word} {command.args}"
      synopsis.pushn ' ' (max 2 (summaryColumn - synopsis.length)) ++ command.summary := rfl

/-- **A usage error quotes its command's own row**: its word and the arguments help shows. -/
theorem usageLine_args (command : Command) (h : command.args.isEmpty = false) :
    usageLine command = s!"usage: linger {command.word} {command.args}" := by simp [usageLine, h]

end Linger.App.Commands
