module

public import Linger.App.CoreSpec
public import ExactJSON.Derive
meta import ExactJSON.Derive

@[expose] public section

/-! # Linger.App.Serve — the codecs of `serve`'s typed values

Every typed value `serve` writes or reads, a method's params, a result, an update and who a party
is, is written and read by the codecs ExactJSON derives (`ExactJSON.ToValue`,
`ExactJSON.FromValue`): an object of its members by increasing key, each of its type, an optional
member left out when absent; reading takes exactly what writing writes, so a member a type does not
define, a member of another type and `null` for one left out are refused. A session's record is
ExactJSON's dictionary of fields, and an id and a colour have codecs of their own
(`Linger.App.CoreSpec`). That each codec writes the object `Linger.App.CoreSpec` states of its type
is proved in `Linger.App.Proofs.Codec`. -/

namespace Linger.App.Serve

open ExactJSON

deriving instance ToValue, FromValue for NoParams

deriving instance ToValue, FromValue for Named

deriving instance ToValue, FromValue for Listed

deriving instance ToValue, FromValue for Attaching

deriving instance ToValue, FromValue for Starting

deriving instance ToValue, FromValue for Sending

deriving instance ToValue, FromValue for Renaming

deriving instance ToValue, FromValue for Capturing

deriving instance ToValue, FromValue for Resizing

deriving instance ToValue, FromValue for Subscription

deriving instance ToValue, FromValue for Keys

deriving instance ToValue, FromValue for Sized

deriving instance ToValue, FromValue for Info

deriving instance ToValue, FromValue for Initialize

deriving instance ToValue, FromValue for Style

deriving instance ToValue, FromValue for Numbered

deriving instance ToValue, FromValue for Scrolled

deriving instance ToValue, FromValue for Cursor

deriving instance ToValue, FromValue for Shows

deriving instance ToValue, FromValue for Result

deriving instance ToValue, FromValue for Changed

deriving instance ToValue, FromValue for ScreenChanged

deriving instance ToValue, FromValue for HistoryChanged

deriving instance ToValue, FromValue for Output

deriving instance ToValue, FromValue for Abilities

deriving instance ToValue, FromValue for Welcome

/-- **A value read exactly as a type writes it**: what the type's codec reads of it, when writing
that writes the value back, as ExactJSON's `decode` reads a text; none otherwise. -/
def exactly {α : Type} [ToValue α] [FromValue α] (value : Value) : Option α :=
  match fromValue? value with
  | .ok a => if toValue a == value then some a else none
  | .error _ => none

end Linger.App.Serve
