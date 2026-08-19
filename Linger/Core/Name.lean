/-! # Linger.Core.Name — session names that cannot escape their directory

A session name becomes a socket path (`<dir>/<name>.sock`) and a
checkpoint path. §Name (THEOREMS.md): a sanitized name contains no
path separator, no NUL, no leading dot, is nonempty and short — so the
composed path stays inside the directory for ANY input string, local
or arriving from a remote listing.
-/

namespace Linger.Core.Name

/-- Characters a name may contain: ASCII alphanumerics plus `-_.+`.
`@` is deliberately excluded — it is reserved as the `name@host`
remote-attach delimiter, so a name never collides with that syntax.
Everything else (slashes, NULs, spaces, controls, unicode, `@`) is
mapped away by `sanitize`. -/
def okChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == '+'

def maxLen : Nat := 80

/-- Total sanitizer: bad characters become `_`, a leading dot becomes
`_` (no hidden files, no `.`/`..`), overlong names truncate, the empty
name becomes `"_"`. Valid names pass through unchanged. -/
def sanitize (s : String) : String :=
  let mapped := s.toList.take maxLen |>.map (fun c => if okChar c then c else '_')
  String.ofList <|
    match mapped with
    | [] => ['_']
    | c :: rest => (if c == '.' then '_' else c) :: rest

/-- The §Name predicate, over the character list so proofs stay in
list-land. -/
def Valid (s : String) : Prop :=
  s.toList.length > 0 ∧ s.toList.length ≤ maxLen ∧
  (∀ c ∈ s.toList, okChar c) ∧ s.toList.head? ≠ some '.'

end Linger.Core.Name
