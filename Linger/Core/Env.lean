module

public section

/-! # Linger.Core.Env — what an environment value means

The runtime reads each variable once and passes the result here, so what an
unset or empty value means is a pure decision with a theorem
(`Theorems/Env.lean`). The suites run the program with both.
-/

namespace Linger.Core.Env

/-- The program a session starts without a command: `$SHELL`, or `sh` when SHELL is
unset or empty, since an empty word names no program. -/
def shellOf (value : Option String) : String :=
  match value with
  | some shell => if shell.isEmpty then "sh" else shell
  | none => "sh"

/-- The remote hosts file, `$HOME/.config/linger/remotes`. An unset or empty HOME
configures none: a fallback such as world-writable `/tmp` would let another
account choose the hosts. -/
def remotesFile (home : Option String) : Option String :=
  match home with
  | some dir => if dir.isEmpty then none else some (dir ++ "/.config/linger/remotes")
  | none => none

/-- Whether the detach key detaches. A read-only view forwards no input and raw mode
clears ISIG, so the key is its only exit; `LINGER_NO_DETACH_KEY`, set to any value,
disables it for writable attach only. -/
def detachEnabled (readOnly : Bool) (flag : Option String) : Bool := readOnly || flag.isNone

end Linger.Core.Env
