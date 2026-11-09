module

public section

/-! # Linger.App.Commands — the command table

**One command table.** Every command the CLI accepts is one row here: the word that names it, its
other spellings, the arguments it takes and what it does. `linger help` prints the table
(`helpText`), a usage error quotes its command's row (`usageLine`), and no two commands share a
word (`words_nodup`), so each word means one command. -/

namespace Linger.App.Commands

/-- One row of the command table. -/
structure Command where
  /-- The word that names the command. -/
  word : String
  /-- Its other spellings, each a word no other command uses. -/
  aliases : List String := []
  /-- The arguments it takes, as help and its usage error show them. -/
  args : String
  /-- What it does, in a few words. -/
  summary : String
  deriving Repr, DecidableEq

/-- The command table, in the order `linger help` lists it. -/
def table : List Command :=
  [{ word := "attach", aliases := ["a"], args := "[--read-only] [name] [command...]",
     summary := "Choose, create or attach to a session" },
    { word := "ls", aliases := ["list", "l"], args := "[-r [hosts]] [--summary|--porcelain]",
      summary := "List sessions or attention counts" },
    { word := "tmux", args := "<command> [SAVE]", summary := "Saved tmux panes; see tmux help" },
    { word := "run", aliases := ["r"], args := "<name> <command...>",
      summary := "Deprecated: type into a shell; use start, send" },
    { word := "start", args := "<name> <program> [args...]",
      summary := "Start a program, exactly, in a new session" },
    { word := "resume", args := "<name>",
      summary := "Run a saved or ended session's program again" },
    { word := "send", aliases := ["s"], args := "<name> <text...|->",
      summary := "Send raw input; - reads stdin" },
    { word := "detach", aliases := ["d"], args := "<name>",
      summary := "Detach all clients from a session" },
    { word := "kill", aliases := ["k"], args := "<name>",
      summary := "End a session, or discard a saved or ended one" },
    { word := "info", aliases := ["i"], args := "<name>", summary := "Print session details" },
    { word := "capture", aliases := ["c"], args := "[--history] <name>",
      summary := "Print the live or saved screen" },
    { word := "resize", args := "<name> <cols> <rows>", summary := "Resize a detached session" },
    { word := "wait", aliases := ["w"], args := "[--timeout SECONDS] <name>...",
      summary := "Wait for programs to end; 124 on timeout" },
    { word := "get", aliases := ["g"], args := "<name>", summary := "Print session labels" },
    { word := "set", args := "<name> <k=v>...", summary := "Set labels" },
    { word := "unset", aliases := ["un"], args := "<name> <key>...", summary := "Remove labels" },
    { word := "clear", aliases := ["cl"], args := "<name>", summary := "Remove all labels" },
    { word := "version", aliases := ["v"], args := "", summary := "Print version and state paths" },
    { word := "help", aliases := ["h", "--help", "-h"], args := "", summary := "Show commands" }]

/-- Every word a command answers to: each command's word, then its other spellings. -/
def words : List String := table.flatMap fun command => command.word :: command.aliases

/-- The command a word names, if any. -/
def lookup (word : String) : Option Command :=
  table.find? fun command => command.word == word || command.aliases.contains word

/-- The column help starts each summary at. -/
def summaryColumn : Nat := 42

/-- A command's line in `linger help`: its word and arguments, then its summary from
`summaryColumn` on, at least two spaces after them. -/
def helpLine (command : Command) : String :=
  let synopsis := if command.args.isEmpty then command.word else s!"{command.word} {command.args}"
  synopsis.pushn ' ' (max 2 (summaryColumn - synopsis.length)) ++ command.summary

/-- What `linger help` lists first: one line per command, in table order. -/
def helpLines : List String := table.map helpLine

/-- `helpLines`, one per line. -/
def helpText : String := String.intercalate "\n" helpLines

/-- The usage error a command with the wrong arguments prints: its own row's arguments. -/
def usageLine (command : Command) : String :=
  if command.args.isEmpty then s!"usage: linger {command.word}"
  else s!"usage: linger {command.word} {command.args}"

end Linger.App.Commands
