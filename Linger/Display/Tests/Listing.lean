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
    ("fg", "vi\x1b[31m\tm\ny"), ("label.description", "b\x1bc"), ("clients", "2")]

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
      "\x1b[36m⣷\x1b[0m work vim\n".toUTF8.toList := by
  native_decide

example :
    terminalListing true none
        [[("name", "saved"), ("status", "resumable"), ("state", "resumable")]] =
      "\x1b[2;39m~\x1b[0m saved (resumable)\n".toUTF8.toList := by
  native_decide

example :
    (terminalListing true none [hostile]).count 0x1B = 2 ∧
      (terminalListing true none [hostile]).count 0x0A = 1 := by
  native_decide

example :
    (rowPieces {} hostile).map (·.status) = [some Linger.Display.Status.Status.idle, none] := by
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
-- and neither the pid, the start command nor another label.
example :
    String.ofList (alone none (atHome "/home/u" present)) =
      "⣀ work vim notes.md  ~/src  6m  +1" := by
  native_decide

-- The description outranks the title, which outranks nothing it names: `vim` is in the title.
example :
    String.ofList (alone none (present ++ [("title", "notes.md - VIM - vim")])) =
        "⣀ work notes.md - VIM - vim  /home/u/src  6m  +1" ∧
      String.ofList
          (alone none (("label.description", "fixing the parser") :: present ++ [("title", "t")])) =
        "⣀ work fixing the parser  vim notes.md  /home/u/src  6m  +1" := by
  native_decide

-- A login shell at its prompt shows no program, and a title that holds its directory hides it.
example :
    String.ofList
          (alone none
            [("name", "work"), ("pid", "10"), ("status", "idle"), ("login", "true"),
              ("fg", "/bin/zsh"), ("fgpid", "10"), ("fgdir", "/home/u/src"), ("idle", "5")]) =
        "⣀ work /home/u/src  5s" ∧
      String.ofList
          (alone none
            [("name", "work"), ("pid", "10"), ("status", "idle"), ("login", "true"),
              ("fg", "/bin/zsh"), ("fgpid", "10"), ("fgdir", "/home/u/src"),
              ("title", "u@host: /home/u/src")]) =
        "⣀ work u@host: /home/u/src" := by
  native_decide

-- A program started as the session's command shows, though it is the session's own process.
example :
    String.ofList
        (alone none
          [("name", "work"), ("pid", "10"), ("status", "working"), ("fg", "sleep 100"),
            ("fgpid", "10"), ("fgdir", "/tmp")]) =
      "⣷ work sleep 100  /tmp" := by
  native_decide

-- A narrow terminal cuts the fields from the right, and never the glyph or the name.
example :
    String.ofList (alone (some 20) present) = "⣀ work vim notes.md…" ∧
      String.ofList (alone (some 3) present) = "⣀ work" := by
  native_decide

example : tilde "/home/u" "/home/u" = "~" ∧ tilde "/home/u" "/home/user" = "/home/user" := by
  native_decide

open Linger.Display.Status in
example :
    [.asks, .working, .wantsYou, .unknown, .exitedOk, .exitedBad, .idle, .resumable].map style =
      [[33], [36], [33], [33], [32], [31], [2, 39], [2, 39]] := by
  decide

-- Each style's sequence keeps the bytes the listing always wrote.
example :
    [[36], [2, 39], [0]].map sgr = ["\x1b[36m", "\x1b[2;39m", "\x1b[0m"].map (·.toUTF8.toList) := by
  native_decide

open Linger.Display.Status in
example :
    summary [.working, .exitedBad, .wantsYou, .idle, .wantsYou, .exitedOk, .resumable] =
      "2⣿ 1✗" := by
  native_decide

open Linger.Display.Status in
example : summary [.unknown, .exitedBad, .wantsYou, .unknown] = "1⣿ 1✗ 2?" := by native_decide

open Linger.Display.Status in
example : summary [.unknown, .asks, .wantsYou, .asks] = "2⚑ 1⣿ 1?" := by native_decide

open Linger.Display.Status in
example : summary [.idle, .working, .exitedOk, .resumable] = "" := by native_decide

open Linger.Display.Status in
example : summary (List.replicate 12 .unknown) = "12?" := by native_decide

open Linger.Display.Status in
example :
    attentionCounts [.unknown, .exitedBad, .wantsYou, .unknown, .asks] =
      [(.asks, 1), (.wantsYou, 1), (.exitedBad, 1), (.unknown, 2)] := by
  native_decide

-- Every glyph, `⚑` and `✗` among them, takes one column in the toolkit's width table.
open Linger.Display.Status in
example :
    [Status.unknown, .exitedBad, .exitedOk, .resumable, .asks, .wantsYou, .working, .idle].all
        (fun s => Terminal.Vt.charWidth (icon s) == 1) =
      true := by
  native_decide

/-- A session whose program asked, with the text of its notification, as a daemon reports it. -/
def asking : List (String × String) :=
  [("name", "agent"), ("pid", "10"), ("status", "asks-you"), ("login", "true"),
    ("label.description", "fix parser"), ("notice", "edit src/Foo.lean?"), ("fg", "claude"),
    ("fgpid", "22"), ("fgdir", "/home/u/src"), ("idle", "120")]

-- While it asks, the row shows the notification's text right after the caption; once it no longer
-- asks, the text is gone.
example :
    String.ofList (alone none (atHome "/home/u" asking)) =
        "⚑ agent fix parser  edit src/Foo.lean?  claude  ~/src  2m" ∧
      String.ofList
          (alone none
            (atHome "/home/u"
              (asking.map fun (k, v) => if k == "status" then (k, "idle") else (k, v)))) =
        "⣀ agent fix parser  claude  ~/src  2m" := by
  native_decide

/-- A shell at its prompt whose last command ended while nobody looked, as a daemon reports it. -/
def ended : List (String × String) :=
  [("name", "build"), ("pid", "10"), ("status", "wants-you"), ("login", "true"),
    ("label.description", "fix parser"), ("lastcmd", "make test"), ("lastexit", "2"), ("fg", "zsh"),
    ("fgpid", "10"), ("fgdir", "/home/u/src"), ("idle", "5")]

-- The row shows how the command ended right after the caption, its line and its status, or the
-- line alone when the shell gave no status, and the status alone when no line reads.
example :
    String.ofList (alone none (atHome "/home/u" ended)) =
        "⣿ build fix parser  make test: exit 2  ~/src  5s" ∧
      String.ofList (alone none (ended.filter (·.1 != "lastexit"))) =
        "⣿ build fix parser  make test: ended  /home/u/src  5s" ∧
      String.ofList (alone none (ended.filter (·.1 != "lastcmd"))) =
        "⣿ build fix parser  exit 2  /home/u/src  5s" := by
  native_decide

-- One field, one column: rows of different names and captions, one with wide characters, start
-- each field at the same display column.
example :
    let rows :=
      [[("name", "a"), ("status", "idle"), ("label.description", "漢字"), ("fg", "vim"),
          ("pid", "1")],
        [("name", "longer"), ("status", "idle"), ("label.description", "abcdefgh"), ("fg", "vi"),
          ("pid", "1")]]
    rows.map (fun r => String.ofList (rowText none (layoutOf rows) r)) =
      ["⣀ a      漢字      vim", "⣀ longer abcdefgh  vi"] := by
  native_decide

end Linger.Display.Listing.Tests
