module

import Linger.Target.Spec

public section

/-! # Linger.Target.Name — session names that cannot escape their directory

A session name becomes a socket path (`<dir>/<name>.sock`) and a
checkpoint path. Commands and remote listings accept only names already
in canonical form (`Valid`, in `Linger/Target/Spec.lean`). Validation never rewrites the
requested identity.
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

/-- Accept an exact session name. Validation must never select a different name. -/
def check (s : String) : Option String := if sanitize s == s then some s else none

end Linger.Target.Name
