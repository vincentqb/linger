import Linger.Core.Listing
/-! # Listing tests — the human row is safe and forgery-proof

`Theorems/Listing.lean` proves `humanRow`/`humanListing` carry no control byte
for *any* `info`. These fixtures pin concrete hostile input — the shape a remote
peer or a crafted checkpoint filename could produce — and, in the `before`
example, show that the previous `String`-interpolated row *did* leak, so the
channel is documented as closed rather than merely gone. `native_decide` is
allowed here (it is banned only in `Theorems/`). -/

namespace Linger.Core.Listing.Tests

open Linger.Core.Listing

/-- A reply carrying an ESC (SGR red), a TAB and a newline in its values, plus a
label with an ESC — the injection a hostile porcelain or a crafted checkpoint
name could attempt. -/
def hostile : List (String × String) :=
  [("name", "x"), ("status", "idle"), ("pid", "1"),
   ("cmd", "vi\x1b[31m\tm\ny"), ("label.a", "b\x1bc"), ("clients", "2")]

/-- No ESC, TAB, DEL or newline survives into the rendered row. -/
example : (humanRow 8 hostile).count 0x1B = 0 := by native_decide
example : (humanRow 8 hostile).count 0x09 = 0 := by native_decide
example : (humanRow 8 hostile).count 0x0A = 0 := by native_decide
example : (humanRow 8 hostile).count 0x7F = 0 := by native_decide

/-- The scrub is a *replacement*, not a deletion: the control bytes became
U+FFFD (0xEF 0xBF 0xBD), so the row still shows something happened. -/
example : (humanRow 8 hostile).contains 0xEF = true := by native_decide

/-- One line per row: a `cmd`/label/name with an embedded newline cannot forge a
listing row. Two hostile rows → exactly two line terminators. -/
example : (humanListing [hostile, hostile]).count 0x0A = 2 := by native_decide

/-- The empty state is its own single line. -/
example : (humanListing []).count 0x0A = 1 := by native_decide

/-- **The channel that was open before.** The old row was a `String`
interpolation of the raw values; on this same reply it carried the ESC straight
to the terminal. Pinned so the regression is documented, not merely absent. -/
example :
    (s!"{Linger.Core.Status.icon (Linger.Core.Status.ofName "idle")} \
      {(hostile.lookup "name").getD ""}\t{(hostile.lookup "cmd").getD ""}").toUTF8.toList.count 0x1B
      = 1 := by native_decide

end Linger.Core.Listing.Tests
