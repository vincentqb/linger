module

import Linger.Display.CoreCode.Listing
import all Linger.Display.CoreCode.Status
import Terminal.CoreCode.Vt
meta import Linger.Display.CoreCode.Listing
meta import Terminal.CoreCode.Vt

/-! # Listing tests — the human row is safe and forgery-proof

`Linger/Display/Proofs/Listing.lean` proves `humanRow` and `terminalListing false` carry no
control byte for *any* `info`. These fixtures pin concrete hostile input — the shape a remote
peer or a crafted checkpoint filename could produce. -/

namespace Linger.Display.Listing.Tests

/-- A reply carrying an ESC (SGR red), a TAB and a newline in its values, plus a
label with an ESC — the injection a hostile porcelain or a crafted checkpoint
name could attempt. -/
def hostile : List (String × String) :=
  [("name", "x"), ("status", "idle"), ("pid", "1"), ("cmd", "vi\x1b[31m\tm\ny"),
    ("fg", "vi\x1b[31m\tm\ny"), ("description", "b\x1bc"), ("clients", "2")]

-- C1 metadata is text too; selectors and listings must not emit a CSI codepoint.
example :
    !(String.fromUTF8!
            (ByteArray.mk (humanRow {} [("name", "x"), ("cmd", "vi\u009b31m")]).toArray)).contains
        '\u009b' := by
  native_decide

/-- The scrub is a *replacement*, not a deletion: the control bytes became
U+FFFD (0xEF 0xBF 0xBD), so the row still shows something happened. -/
example : (humanRow (layoutOf [hostile]) hostile).contains 0xEF = true := by native_decide

/-- One line per row: a `cmd`/label/name with an embedded newline cannot forge a
listing row. Two hostile rows → exactly two line terminators. -/
example : (terminalListing false none [hostile, hostile]).count 0x0A = 2 := by native_decide

/-- The empty state is its own single line. -/
example : (terminalListing false none []).count 0x0A = 1 := by native_decide

example :
    terminalListing true none [[("name", "work"), ("status", "working"), ("cmd", "vim")]] =
      "  \x1b[36m⣷\x1b[0m work vim\n".toUTF8.toList := by
  native_decide

example :
    terminalListing true none
        [[("name", "saved"), ("status", "resumable"), ("state", "resumable")]] =
      "  \x1b[2;39m~\x1b[0m saved (resumable)\n".toUTF8.toList := by
  native_decide

example :
    (terminalListing true none [hostile]).count 0x1B = 2 ∧
      (terminalListing true none [hostile]).count 0x0A = 1 := by
  native_decide

example : (rowPieces {} hostile).map (·.style) = [none, none, some [2, 39], none] := by
  native_decide

example : (layoutOf [[("name", "a")], [("name", "work@host")]]).nameCol = 9 := by native_decide

/-- A row alone in its view, laid out by itself. -/
def alone (width : Option Nat) (info : List (String × String)) : List Char :=
  rowText width (layoutOf [info]) info

/-- A shell session as a daemon reports it: its login shell runs `vim` in the foreground. -/
def present : List (String × String) :=
  [("name", "work"), ("pid", "10"), ("cmd", "/bin/zsh"), ("status", "idle"), ("login", "true"),
    ("fg", "vim notes.md"), ("fgpid", "22"), ("fgdir", "/home/u/src"), ("idle", "400"),
    ("clients", "1"), ("label.owner", "me")]

-- The row shows the foreground program, its directory, how long ago it printed and its watcher,
-- and neither the pid, the start command nor another field.
example :
    String.ofList (alone none (atHome "/home/u" present)) =
      "  ⣀ work vim notes.md  ~/src  6m  +1" := by
  native_decide

-- The title outranks a description an older linger saved, which shows while the program sets
-- none, and the caption outranks the program it names: `vim` is in the title.
example :
    String.ofList (alone none (present ++ [("title", "notes.md - VIM - vim")])) =
        "  ⣀ work notes.md - VIM - vim  /home/u/src  6m  +1" ∧
      String.ofList (alone none (("description", "fixing the parser") :: present)) =
        "  ⣀ work fixing the parser  vim notes.md  /home/u/src  6m  +1" ∧
      String.ofList
          (alone none (("description", "fixing the parser") :: present ++ [("title", "t")])) =
        "  ⣀ work t  vim notes.md  /home/u/src  6m  +1" := by
  native_decide

-- A login shell at its prompt shows no program, and a title that holds its directory hides it.
example :
    String.ofList
          (alone none
            [("name", "work"), ("pid", "10"), ("status", "idle"), ("login", "true"),
              ("fg", "/bin/zsh"), ("fgpid", "10"), ("fgdir", "/home/u/src"), ("idle", "5")]) =
        "  ⣀ work /home/u/src  5s" ∧
      String.ofList
          (alone none
            [("name", "work"), ("pid", "10"), ("status", "idle"), ("login", "true"),
              ("fg", "/bin/zsh"), ("fgpid", "10"), ("fgdir", "/home/u/src"),
              ("title", "u@host: /home/u/src")]) =
        "  ⣀ work u@host: /home/u/src" := by
  native_decide

-- A program started as the session's command shows, though it is the session's own process.
example :
    String.ofList
        (alone none
          [("name", "work"), ("pid", "10"), ("status", "working"), ("fg", "sleep 100"),
            ("fgpid", "10"), ("fgdir", "/tmp")]) =
      "  ⣷ work sleep 100  /tmp" := by
  native_decide

-- A narrow terminal cuts the fields from the right, and never the glyph or the name.
example :
    String.ofList (alone (some 22) present) = "  ⣀ work vim notes.md…" ∧
      String.ofList (alone (some 3) present) = "  ⣀ work" := by
  native_decide

example : tilde "/home/u" "/home/u" = "~" ∧ tilde "/home/u" "/home/user" = "/home/user" := by
  native_decide

open Linger.Display.Status in
example :
    [.working, .unknown, .exitedOk, .exitedBad, .errored, .idle, .resumable].map style =
      [[36], [33], [32], [31], [31], [2, 39], [2, 39]] := by
  decide

-- A session that rang while it works shows both, each in its column, each styled alone.
example :
    String.ofList (alone none [("name", "w"), ("attention", "asked"), ("status", "working")]) =
        "⚑ ⣷ w" ∧
      String.ofList (alone none [("name", "w"), ("attention", "unread"), ("status", "idle")]) =
        "∙ ⣀ w" ∧
      terminalListing true none [[("name", "w"), ("attention", "asked"), ("status", "working")]] =
        "\x1b[33m⚑\x1b[0m \x1b[36m⣷\x1b[0m w\n".toUTF8.toList := by
  native_decide

-- Each style's sequence keeps the bytes the listing always wrote.
example :
    [[36], [2, 39], [0]].map sgr = ["\x1b[36m", "\x1b[2;39m", "\x1b[0m"].map (·.toUTF8.toList) := by
  native_decide

open Linger.Display.Status in
example : summary [.none, .unread, .asked, .unread, .none] = "1⚑ 2∙" := by native_decide

open Linger.Display.Status in
example : summary [.none, .none] = "" := by native_decide

open Linger.Display.Status in
example : summary (List.replicate 12 .unread) = "12∙" := by native_decide

open Linger.Display.Status in
example : attentionCounts [.unread, .none, .asked, .unread] = [(.asked, 1), (.unread, 2)] := by
  native_decide

-- A daemon older than the field `running` meant by `unseen` any output since the look, so its
-- `unseen` shows no unread mark; a current daemon's `unseen` is unread lines.
example :
    (rowStatus (.live [("pid", "1"), ("cmd", "sh"), ("unseen", "true")])).attention = .none ∧
      (rowStatus
            (.live
              [("pid", "1"), ("cmd", "sh"), ("running", "false"), ("unseen", "true")])).attention =
        .unread := by
  native_decide
