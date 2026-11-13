module

public section

/-! # What session names and remote commands are judged by

A valid session name is nonempty, at most `maxLen` characters, made only of `okChar`s, and does
not begin with a dot, so it cannot name a path outside the socket directory.

A remote command is the line SSH hands to the login shell of the remote account, which may be
any shell, each with its own quoting. A plain word starts with a lowercase ASCII letter and goes
on with lowercase letters, digits and colons, which no shell expands, quotes, escapes or splits
at, and the world claim `Shell.Literal` (`Linger.Target.WorldSpec`) says that every shell passes
`linger` and then plain words, one space apart, to `linger` as exactly those words. `marker`
opens an encoded command line; holding a colon, it is no valid session name. Bodies are exposed:
each definition here is its own specification. -/

namespace Linger.Target.Name

/-- Characters a name may contain: ASCII alphanumerics plus `-_.+`.
`@` is deliberately excluded — it is reserved as the `name@host`
remote-target delimiter, so a name never collides with that syntax. -/
@[expose] def okChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '+'

/-- The longest valid name, in characters. -/
@[expose] def maxLen : Nat := 80

/-- A valid session name, over the character list so proofs stay in list-land. -/
@[expose] def Valid (s : String) : Prop :=
  s.toList.length > 0 ∧
    s.toList.length ≤ maxLen ∧ (∀ c ∈ s.toList, okChar c) ∧ s.toList.head? ≠ some '.'

end Linger.Target.Name

namespace Linger.Target.Remote

/-- A host fit to hand to `ssh` argv: no C0 or C1 control character and no DEL. Not
`Name.sanitize`, which would be wrong twice over: `@` is not an `okChar`, so it would destroy a
legitimate `user@host` target, and silently rewriting a host means connecting somewhere the user
did not ask for. -/
@[expose] def hostClean (h : String) : Bool :=
  h.toList.all (fun c => c.toNat ≥ 32 && (c.toNat < 127 || c.toNat ≥ 160))

/-- The word that opens an encoded command line: `linger argv:hex`, then the command's words,
each encoded as plain words. A colon is no `Name.okChar`, so no session has it for a name, and no
command does either: a linger that does not decode its command line refuses this one as a usage
error rather than acting on it. -/
@[expose] def marker : String := "argv:hex"

end Linger.Target.Remote

namespace Linger.Target.Remote.Shell

/-- A character a plain word may go on with: a lowercase ASCII letter, a digit or a colon. -/
@[expose] def plainChar (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9') || c == ':'

/-- A word every shell reads as itself: a lowercase ASCII letter, then `plainChar`s. None of them
is a quote, an escape, a separator or a character any shell expands, and the letter first makes
the word no number, option, assignment or path. -/
@[expose] def plain (word : String) : Bool :=
  match word.toList with
  | first :: rest => ('a' ≤ first && first ≤ 'z') && rest.all plainChar
  | [] => false

end Linger.Target.Remote.Shell
