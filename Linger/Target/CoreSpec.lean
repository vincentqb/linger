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

A remote command runs through a transport, a command that runs linger elsewhere: ssh, or a
command such as `docker exec`. Every remote command runs `linger serve` there, through the host's
`Transport`, and speaks JSON-RPC to it on the command's standard input and output, so no word of
the command reaches a shell: the world claim `Transport.Delivers` (`Linger.Target.WorldSpec`) says
that a transport carries the bytes either way exactly, or runs nothing. Bodies are exposed: each
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

/-- How linger reaches a host: the command that runs linger there, as the words a command line
holds before `linger`, and what it does is the transport's. -/
structure Transport where
  /-- The command that runs linger there. -/
  command : List String
  deriving DecidableEq, Repr, Inhabited

end Linger.Target.Remote
