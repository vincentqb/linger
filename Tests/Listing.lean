import Linger.Core.Listing

/-! # Listing tests — the human row is safe and forgery-proof

`Theorems/Listing.lean` proves `humanRow` and `terminalListing false` carry no
control byte for *any* `info`. These fixtures pin concrete hostile input — the shape a remote
peer or a crafted checkpoint filename could produce. -/

namespace Linger.Core.Listing.Tests

open Linger.Core.Listing

/-- A reply carrying an ESC (SGR red), a TAB and a newline in its values, plus a
label with an ESC — the injection a hostile porcelain or a crafted checkpoint
name could attempt. -/
def hostile : List (String × String) :=
  [("name", "x"), ("status", "idle"), ("pid", "1"), ("cmd", "vi\x1b[31m\tm\ny"),
    ("label.a", "b\x1bc"), ("clients", "2")]

-- C1 metadata is text too; selectors and listings must not emit a CSI codepoint.
example :
    !(String.fromUTF8!
            (ByteArray.mk (humanRow 1 [("name", "x"), ("cmd", "vi\u009b31m")]).toArray)).contains
        '\u009b' := by
  native_decide

/-- The scrub is a *replacement*, not a deletion: the control bytes became
U+FFFD (0xEF 0xBF 0xBD), so the row still shows something happened. -/
example : (humanRow 8 hostile).contains 0xEF = true := by native_decide

/-- One line per row: a `cmd`/label/name with an embedded newline cannot forge a
listing row. Two hostile rows → exactly two line terminators. -/
example : (terminalListing false [hostile, hostile]).count 0x0A = 2 := by native_decide

/-- The empty state is its own single line. -/
example : (terminalListing false []).count 0x0A = 1 := by native_decide

example :
    terminalListing true [[("name", "work"), ("status", "working"), ("cmd", "vim")]] =
      "\x1b[36m⣷\x1b[0m work vim\n".toUTF8.toList := by
  native_decide

example :
    terminalListing true [[("name", "saved"), ("status", "resumable"), ("state", "resumable")]] =
      "\x1b[2;39m~\x1b[0m saved (resumable)\n".toUTF8.toList := by
  native_decide

example :
    (terminalListing true [hostile]).count 0x1B = 2 ∧
      (terminalListing true [hostile]).count 0x0A = 1 := by
  native_decide

example : (rowPieces 5 hostile).map (·.status) = [some Linger.Core.Status.Status.idle, none] := by
  native_decide

example : nameWidth [[("name", "a")], [("name", "work@host")]] = 9 := by native_decide

open Linger.Core.Status in
example :
    [.working, .wantsYou, .unknown, .exitedOk, .exitedBad, .idle, .resumable].map style =
      ["\x1b[36m", "\x1b[33m", "\x1b[33m", "\x1b[32m", "\x1b[31m", "\x1b[2;39m", "\x1b[2;39m"] := by
  native_decide

open Linger.Core.Status in
example :
    summary [.working, .exitedBad, .wantsYou, .idle, .wantsYou, .exitedOk, .resumable] =
      "2⣿ 1!" := by
  native_decide

open Linger.Core.Status in
example : summary [.unknown, .exitedBad, .wantsYou, .unknown] = "1⣿ 1! 2?" := by native_decide

open Linger.Core.Status in
example : summary [.idle, .working, .exitedOk, .resumable] = "" := by native_decide

open Linger.Core.Status in
example : summary (List.replicate 12 .unknown) = "12?" := by native_decide

open Linger.Core.Status in
example :
    attentionCounts [.unknown, .exitedBad, .wantsYou, .unknown] =
      [(.wantsYou, 1), (.exitedBad, 1), (.unknown, 2)] := by
  native_decide

end Linger.Core.Listing.Tests
