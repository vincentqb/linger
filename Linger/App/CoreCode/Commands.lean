module

public import Linger.App.CoreSpec

public section

/-! # Linger.App.Commands — the command table

**One command table, one command per operation.** Every command the CLI accepts is one row here:
the word that names it, its only spelling, the operation it performs, the arguments it takes and
what it does. The session CLI dispatches a command line through `lookup` to its row's `Op`, so a
word no row has names no command. Each operation of the session model has exactly one row, in
the order of `Op.all`, so each has exactly one spelling and no command is another's alias.
`linger --help` prints the table (`helpText`), and a usage error quotes its command's row
(`usageLine`). A word no row has is a usage error like any other.
`--help` and `--version` are the program's options, spelled as every program spells them, and
no operation of a session. -/

namespace Linger.App.Commands

/-- The command table, in the order `linger --help` lists it: one row for each `Op`. -/
def table : List Command :=
  [{ word := "attach", op := .attach, args := "[--read-only] [name] [command...]",
     summary := "Choose, create or attach to a session" },
    { word := "ls", op := .list, args := "[-r [hosts] | name...] [--porcelain]",
      summary := "List sessions and tmux panes; or --summary, --resurrect" },
    { word := "start", op := .start, args := "<name> <program> [args...]",
      summary := "Start a program, exactly, in a new session" },
    { word := "resume", op := .resume, args := "<name>",
      summary := "Run a saved or ended session's program again" },
    { word := "send", op := .send, args := "<name> <text...|->",
      summary := "Send raw input; - reads stdin" },
    { word := "detach", op := .detach, args := "<name>",
      summary := "Detach all clients from a session" },
    { word := "kill", op := .kill, args := "<name>",
      summary := "End a session, or discard a saved one or tmux pane" },
    { word := "rename", op := .rename, args := "<name> <new-name>",
      summary := "Give a session a new name" },
    { word := "capture", op := .capture, args := "[--history] <name>",
      summary := "Print the live or saved screen" },
    { word := "resize", op := .resize, args := "<name> <cols> <rows>",
      summary := "Resize a detached session" },
    { word := "wait", op := .wait, args := "<name>...", summary := "Wait for programs to end" },
    { word := "upgrade", op := .upgrade, args := "[name...]",
      summary := "Move live sessions onto this linger; programs keep running" },
    { word := "serve", op := .serve, args := "",
      summary := "Answer JSON-RPC 2.0 on stdin and stdout, a message a line" }]

/-- The option that explains the command line. -/
def helpOption : String := "--help"

/-- The option that prints linger's version and the state paths. -/
def versionOption : String := "--version"

/-- The command a word names, if any: the row whose word it is. -/
def lookup (word : String) : Option Command := table.find? fun command => command.word == word

/-- The column help starts each summary at. -/
def summaryColumn : Nat := 42

/-- A command's line in `linger --help`: its word and arguments, then its summary from
`summaryColumn` on, at least two spaces after them. -/
def helpLine (command : Command) : String :=
  command.word ++ " " ++
    (command.args.pushn ' '
        (max 2 (summaryColumn - (command.word.length + 1 + command.args.length))) ++
      command.summary)

/-- What `linger --help` lists first: one line per command, in table order. -/
def helpLines : List String := table.map helpLine

/-- `helpLines`, one per line. -/
def helpText : String := String.intercalate "\n" helpLines

/-- The usage error a command with the wrong arguments prints: its own row's arguments. -/
def usageLine (command : Command) : String :=
  if command.args.isEmpty then s!"usage: linger {command.word}"
  else s!"usage: linger {command.word} {command.args}"

end Linger.App.Commands
