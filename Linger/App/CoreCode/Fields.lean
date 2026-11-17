module

public import Linger.App.CoreSpec
public import Linger.Display.CoreSpec

public section

/-! # Linger.App.Fields — every field of a session's record, its kind, its owner and its role

**Fields are human or machine, each with one owner.** A human field is shown in rows as clean
text; a machine field is exact, never shown in a human row, and only `--porcelain` gives it. Each
field has one writer: the user, through exactly one command, the session's program, through what
it writes and what the operating system reports of its terminal, or linger (`fields_owned`). The
program's fields a listing reports are readings of what the session keeps of it (`Session.Owned`),
which only their sources change (`step_owned`). The name is the one field the user owns, which
`rename` writes: it says what the session is. A description an older linger saved is linger's to
keep, read only, and shows where the program's title would while the program sets none. -/

namespace Linger.App.Fields

/-- The fields of a session's record listings report, each once. -/
def table : List Field :=
  [{ key := "name", kind := .human, owner := .user .rename,
     role := "what the user calls the session" },
    { key := "title", kind := .human, owner := .program,
      role := "what the program calls its window" },
    { key := "notice", kind := .human, owner := .program,
      role := "the program's last notification since a look" },
    { key := "lastcmd", kind := .human, owner := .program,
      role := "the shell's last command since a look" },
    { key := "lastexit", kind := .human, owner := .program,
      role := "how the shell's last command ended" },
    { key := "status", kind := .human, owner := .linger, role := "what linger saw of the session" },
    { key := "state", kind := .human, owner := .linger,
      role := "whether the session runs or is saved" },
    { key := "saved", kind := .human, owner := .linger,
      role := "the signal that saved the session" },
    { key := "signal", kind := .human, owner := .linger,
      role := "the signal that killed the program" },
    { key := "outcome", kind := .human, owner := .linger,
      role := "that linger did not see the end" },
    { key := "exit", kind := .human, owner := .linger, role := "the program's exit status" },
    { key := "cmd", kind := .human, owner := .linger, role := "the command the session runs" },
    { key := "source", kind := .human, owner := .linger,
      role := "the source a saved pane came from" },
    { key := "description", kind := .human, owner := .linger,
      role := "the caption an older linger saved" },
    { key := "fg", kind := .human, owner := .program, role := "the program in the foreground" },
    { key := "fgdir", kind := .human, owner := .program,
      role := "the foreground program's directory" },
    { key := "idle", kind := .human, owner := .linger,
      role := "how long the program has been quiet" },
    { key := "clients", kind := .human, owner := .linger, role := "who watches the session" },
    { key := "pid", kind := .machine, owner := .linger, role := "the program's process" },
    { key := "fgpid", kind := .machine, owner := .program,
      role := "the foreground program's process" },
    { key := "login", kind := .machine, owner := .linger,
      role := "whether the foreground program is the login shell" },
    { key := "protocol", kind := .machine, owner := .linger,
      role := "the protocol level the daemon speaks" }]

end Linger.App.Fields
