module

public section

/-! # The shell syntax remote commands are judged by

The literal subset of POSIX shell syntax. Inside single quotes, every character is literal.
The sequence `'\''` emits one quote and resumes the quoted region. A command consists only of
these words separated by spaces; there are no expansions or operators. This models the shell
syntax, not the SSH implementation. OS argument strings exclude NUL. Bodies are exposed: each
definition here is its own specification. -/

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
