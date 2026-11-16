module

public section

/-! # What session names and remote commands are judged by

A session's name is clean text (`Usable`): it is not empty or all spaces, holds no control
character, and no `@`, which marks a host, does not start with `-`, which reads as an option, and
takes at most `maxBytes` bytes. Spaces and any printable Unicode are names' too, since a session's
files are keyed by its ID, never by its name. A key, a name that can be its session's own ID as
every name an older linger kept was, is nonempty, at most `maxLen` characters, made only of
`okChar`s, and does not begin with a dot (`Valid`), so it cannot name a path outside the socket
directory; a command takes either (`Accepted`), so every name an older linger kept stays reachable,
and a new name is clean text.

A remote command runs through a transport, a command that runs linger elsewhere: ssh, which hands
its command line to the login shell of the remote account, or a command such as `docker exec`
that runs its words as they are. A `Transport` is the command for an attach, which gives the far
end a terminal, and the one for every other command. A shell may be any shell, each with its own
quoting. A plain word starts with a lowercase ASCII letter and goes on with lowercase letters,
digits and colons, which no shell expands, quotes, escapes or splits at, and the world claim
`Shell.Literal` (`Linger.Target.WorldSpec`) says that every shell passes `linger` and then plain
words, one space apart, to `linger` as exactly those words; `Transport.Delivers` says that a
transport runs a `linger` with exactly the plain words after it, or nothing. `marker` opens an
encoded command line; holding a colon, it is no valid session name. Bodies are exposed: each
definition here is its own specification. -/

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

/-- A character a name may hold: any but a control character, C0, DEL or C1, and `@`, which marks
a host. -/
@[expose] def textChar (c : Char) : Bool :=
  !(c.toNat < 0x20 || c.toNat == 0x7F || (0x80 ≤ c.toNat && c.toNat < 0xA0)) && c != '@'

/-- The most bytes a name takes in UTF-8, so that its entry in the names directory, which spells a
name that is no key in hexadecimal, stays within a file name's 255 bytes. -/
@[expose] def maxBytes : Nat := 120

/-- A name a session can have: not empty or all spaces, at most `maxBytes` bytes, made of
`textChar`s, and not starting with `-`. -/
@[expose] def Usable (s : String) : Prop :=
  s.toList.any (· != ' ') = true ∧
    s.toUTF8.size ≤ maxBytes ∧ (∀ c ∈ s.toList, textChar c = true) ∧ s.toList.head? ≠ some '-'

/-- A name a command takes: clean text (`Usable`), or a key an older linger kept (`Valid`), which
may start with `-` and so follows `--`, so that every session an older linger named stays
reachable by its name. A new name is clean text. -/
@[expose] def Accepted (s : String) : Prop := Usable s ∨ Valid s

/-- A wrong acceptance: the one before names were clean text, which takes only a key, so a name
with a space or a letter beyond ASCII is refused. The headline that a name round-trips through
every command is shown to reject it. -/
@[expose] def keyed (s : String) : Option String :=
  if s.toList.length > 0 && s.toList.length ≤ maxLen && s.toList.all okChar &&
      s.toList.head? != some '.' then
    some s
  else none

end Linger.Target.Name

namespace Linger.Target.Remote

/-- A host fit to hand to a transport's argv: no C0 or C1 control character and no DEL. Not
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

/-- How linger reaches a host: the command that runs linger there for an attach, which gives the
far end a terminal, and the one for every other command. Each is the words a command line holds
before `linger`, and what they do is the transport's. -/
structure Transport where
  /-- The command that runs linger there for every command but an attach. -/
  query : List String
  /-- The command that runs linger there for an attach, with a terminal at the far end. -/
  attach : List String
  deriving DecidableEq, Repr, Inhabited

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
