import Zmx.Core.Tui
/-! # TUI state-machine tests — keystrokes in, effects out -/

namespace Zmx.Core.Tui.Tests

open Zmx.Core.Tui

def rows0 : List Row :=
  [{ name := "alpha" }, { name := "beta" }, { name := "gamma", state := .resumable }]

def st0 : State := (step {} (.rowsUpdated rows0)).1

def keys (st : State) (ks : List Key) : State × List Effect :=
  ks.foldl (fun (acc : State × List Effect) k =>
    let (s, effs) := step acc.1 (.key k)
    (s, acc.2 ++ effs)) (st, [])

/-- Fuzzy filter: subsequence, case-insensitive. -/
example : (fuzzy "ba" "beta" && fuzzy "GM" "gamma" && !fuzzy "x" "beta") = true := by
  native_decide

/-- Enter on a selection attaches it. -/
example : ((keys st0 [.enter]).2 == [.attach "alpha" .local]) = true := by native_decide

/-- Down-down-enter attaches the third row. -/
example : ((keys st0 [.down, .down, .enter]).2.getLast?
    == some (.attach "gamma" .local)) = true := by native_decide

/-- Typing filters; enter attaches the match, not the first row. -/
example : ((keys st0 [.char 'b', .char 't', .enter]).2.getLast?
    == some (.attach "beta" .local)) = true := by native_decide

/-- A query with no match + enter creates (name sanitized). -/
example : ((keys st0 [.char 'n', .char 'e', .char 'w', .char '/', .char 'x',
    .enter]).2.getLast? == some (.create "new_x")) = true := by native_decide

/-- Selection never escapes the filtered list (§Bound(tui), concrete). -/
example : ((keys st0 [.down, .down, .down, .down, .down]).1.sel == 2
    && (keys st0 [.char 'b', .char 'e', .down, .down]).1.sel == 0) = true := by
  native_decide

/-- Kill needs a confirming second C-x. -/
example : ((keys st0 [.ctrlX]).2 == []
    && (keys st0 [.ctrlX, .ctrlX]).2 == [.kill "alpha" .local, .refresh]) = true := by
  native_decide

/-- Any movement disarms the pending kill (a preview fetch may fire;
what must not is a kill). -/
example : (((keys st0 [.ctrlX, .down, .ctrlX]).2.all
    (fun e => match e with | .kill _ _ => false | _ => true))) = true := by native_decide

/-- Esc quits. -/
example : ((keys st0 [.esc]).2 == [.quit]) = true := by native_decide

/-- A stale preview (selection moved on) is rejected. -/
example : ((step st0 (.previewUpdated "beta" .local ["x"])).1.previewFor
    == none) = true := by native_decide

end Zmx.Core.Tui.Tests


namespace Row
/-! §Row: a row's identity comes from the socket filename, never from
the daemon's reply. -/

open Zmx.Core.Tui

/-- A silent daemon (empty reply) still gets its real name. -/
example : ((rowOfInfo "work" []).name == "work"
    && (rowOfInfo "work" []).cmd == "") = true := by native_decide

/-- Fields are carried when the reply has them. -/
example : ((rowOfInfo "work" [("pid", "42"), ("cmd", "vim"), ("label.env", "dev")])
    == { name := "work", state := .live, pid := "42", cmd := "vim",
         labels := [("env", "dev")] }) = true := by native_decide

/-- A reply claiming another identity cannot rename the row. -/
example : ((rowOfInfo "mine" [("name", "yours")]).name == "mine") = true := by
  native_decide

/-- A path-ish socket name is sanitized like any other name. -/
example : ((rowOfInfo "../etc" []).name == "_._etc") = true := by native_decide

/-- Control bytes in the reply never reach the rendered row. -/
example : ((rowOfInfo "x" [("cmd", "vi\x1b[31mm\x07")]).cmd == "vi[31mm") = true := by
  native_decide

end Row
