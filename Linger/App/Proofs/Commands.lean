module

import all Linger.App.Commands

/-! # The command table

Each word names one command, every command is found by each of its words, help lists every
command once in table order, and a usage error quotes its command's own row. -/

namespace Linger.App.Commands

/-- **One word, one command**: no two commands, and no command and another's spelling, share a
word. -/
theorem words_nodup : words.Nodup := by decide

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
