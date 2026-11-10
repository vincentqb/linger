module

public section

/-! # What session names and remote commands are judged by

A valid session name is nonempty, at most `maxLen` characters, made only of `okChar`s, and does
not begin with a dot, so it cannot name a path outside the socket directory.

The literal subset of POSIX shell syntax. Inside single quotes, every character is literal.
The sequence `'\''` emits one quote and resumes the quoted region. A command consists only of
these words separated by spaces; there are no expansions or operators. This models the shell
syntax, not the SSH implementation. OS argument strings exclude NUL. Bodies are exposed: each
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

end Linger.Target.Name

namespace Linger.Target.Remote

/-- A host fit to hand to `ssh` argv: no C0 or C1 control character and no DEL. Not
`Name.sanitize`, which would be wrong twice over: `@` is not an `okChar`, so it would destroy a
legitimate `user@host` target, and silently rewriting a host means connecting somewhere the user
did not ask for. -/
@[expose] def hostClean (h : String) : Bool :=
  h.toList.all (fun c => c.toNat ≥ 32 && (c.toNat < 127 || c.toNat ≥ 160))

end Linger.Target.Remote

namespace Linger.Target.Remote.Shell

/-- Read a single-quoted region through its closing quote. -/
@[expose]
def quoted : List Char → Option (List Char × List Char)
  | [] => none
  | c :: rest =>
    if c == '\'' then
      match rest with
      | '\\' :: '\'' :: '\'' :: more => do
        let (text, tail) ← quoted more
        some ('\'' :: text, tail)
      | _ => some ([], rest)
    else do
      let (text, tail) ← quoted rest
      some (c :: text, tail)

/-- A word must start with a quote; unquoted shell syntax is outside the model. -/
@[expose]
def word : List Char → Option (List Char × List Char)
  | '\'' :: rest => quoted rest
  | _ => none

/-- A complete command contains only literal words and their separators. -/
inductive Words : List Char → List (List Char) → Prop where
  /-- The source is one word and nothing after it. -/
  | last {source text} (read : word source = some (text, [])) : Words source [text]
  /-- A word, one space, and the words of the rest. -/
  |
  next {source text tail rest} (read : word source = some (text, ' ' :: tail))
    (more : Words tail rest) : Words source (text :: rest)

end Linger.Target.Remote.Shell
