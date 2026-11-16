module

import Linger.Target.CoreSpec

public section

/-! # Linger.Target.Name — session names as clean text, and the keys among them

A session name is clean text (`Usable`, in `Linger/Target/CoreSpec.lean`), which commands and
remote listings accept as it is (`accept`). A key, a name that is also its session's ID and so
becomes a socket path (`<dir>/<name>.sock`) and a checkpoint path, is in canonical form
(`Valid`, `check`), so it cannot escape its directory. Validation never rewrites the requested
identity.
-/

namespace Linger.Target.Name

/-- Creation name offered by an empty interactive query. -/
def defaultName : String := "main"

/-- Total sanitizer: bad characters become `_`, a leading dot becomes
`_` (no hidden files, no `.`/`..`), overlong names truncate, the empty
name becomes `"_"`. Valid names pass through unchanged. -/
def sanitize (s : String) : String :=
  let mapped := s.toList.take maxLen |>.map (fun c => if okChar c then c else '_')
  String.ofList <|
    match mapped with
    | [] => ['_']
    | c :: rest => (if c == '.' then '_' else c) :: rest

/-- Accept an exact key, a name that can be its session's own ID. Validation must never select a
different name. -/
def check (s : String) : Option String := if sanitize s == s then some s else none

/-- Whether `s` is a name a session can have (`Usable`). -/
def usable (s : String) : Bool :=
  s.toList.any (· != ' ') && decide (s.utf8ByteSize ≤ maxBytes) && s.toList.all textChar &&
    s.toList.head? != some '-'

/-- Accept an exact session name: clean text (`Usable`), or a key an older linger kept
(`Accepted`). Validation must never select a different name. -/
def accept (s : String) : Option String := if usable s || (check s).isSome then some s else none

/-- A name as a title shows it: each character a name may not hold, but `@`, as `_`. -/
def shown (s : String) : String :=
  String.ofList (s.toList.map fun c => if textChar c || c == '@' then c else '_')

end Linger.Target.Name
