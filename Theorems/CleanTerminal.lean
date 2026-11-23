module

public import Linger.Display.CoreCode.Alert
public import Linger.Display.CoreCode.Listing
public import Linger.Selector.CoreCode.Picker
public import Linger.Os.CoreCode.Env
public import Linger.Session.CoreCode
public import Linger.Session.CoreSpec
public import Terminal.CoreCode.Render
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
public import Terminal.CoreCode.Title
import all Linger.App.Proofs.Api
import all Linger.App.Proofs.Capture
import all Linger.App.Proofs.Commands
import all Linger.App.Proofs.Entry
import all Linger.App.Proofs.Kill
import all Linger.App.Proofs.Recovery
import all Linger.App.Proofs.Serve
import all Linger.App.Proofs.Screen
import all Linger.App.Proofs.Wait
import Linger.Display.Proofs.Clean
import all Linger.App.Proofs.Fields
import all Linger.App.Proofs.Owned
import all Linger.Display.Proofs.Alert
import all Linger.Display.Proofs.Listing
import all Linger.Display.Proofs.Status
import all Linger.Display.Proofs.View
import all Linger.Import.Proofs.Resurrect
import Linger.Selector.Proofs.Frame
import all Linger.Selector.Proofs.Picker
import all Linger.Selector.Proofs.Fetch
import all Linger.Display.Proofs.Title
import all Linger.Os.Proofs.Answer
import all Linger.Os.Proofs.Env
import all Os.Proofs.Wait
import Linger.Target.Proofs.Name
import Linger.Target.Proofs.Remote
import all Linger.Session.Proofs.Buf
import all Linger.Session.Proofs.Offloop
import all Linger.Session.Proofs.Present
import all Linger.Session.Proofs.Checkpoint
import all Linger.Session.Proofs.Handoff
import all Linger.Session.Proofs.Claim
import all Linger.Session.Proofs.Names
import all Linger.Session.Proofs.Driver
import all Linger.Session.Proofs.Record
import all Linger.Session.Proofs.Session
import all Linger.Session.Proofs.Start
import all Linger.Session.Proofs.Wire
public import Linger.Session.CoreCode.Record
public import Linger.Session.CoreCode.Wire
import all Terminal.CoreCode.Vt
import all Terminal.Proofs.Vt
import all Terminal.Proofs.Vt.History
import all Terminal.Proofs.Vt.Renderable
import all Terminal.Proofs.Render.Grid
import all Terminal.Proofs.Render.History
import all Terminal.Proofs.Render.PendingWrap
import all Terminal.Proofs.Render.Scrollback
import all Terminal.Proofs.Render.Sticky
import all Terminal.Proofs.Replay
import all Terminal.Proofs.Vt.State

/-! # Part 8 of `Challenge.lean`, clean terminal: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem infoText_text (s : State) :
    ∃ cs : List Char,
      Session.infoText s = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\t' ∨
            c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  obtain ⟨cs, text, safe⟩ := Session.infoText_text s
  refine ⟨cs, ?_, safe⟩
  rw [text]
  exact congrArg (cs.flatMap ·) (funext Render.utf8_eq_utf8EncodeChar)

theorem infoText_text_rejects_escape :
    ¬∀ (s : State),
        ∃ cs : List Char,
          (fun (_ : State) => ([0x1B] : List UInt8)) s = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\t' ∨
                c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  intro h
  obtain ⟨cs, text, safe⟩ := h (State.boot (Vt.Vt.init 1 1) [] [])
  have escape : (0x1B : UInt8) ∈ cs.flatMap String.utf8EncodeChar := by
    rw [← text]
    exact List.mem_singleton_self _
  obtain ⟨c, member, byte⟩ := List.mem_flatMap.mp escape
  rcases safe c member with tab | newline | ⟨printable, notDel, -⟩
  · subst tab
    revert byte
    decide
  · subst newline
    revert byte
    decide
  · rw [← Render.utf8_eq_utf8EncodeChar] at byte
    exact absurd (Render.utf8_no_ctl c printable notDel _ byte).1 (by decide)

theorem writes_clean :
    (∀ withColor width rows, Display.Clean (Display.Listing.terminalListing withColor width rows)) ∧
      (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
        Display.Clean
          (Selector.Picker.frame state snapshot statusOf loaded withColor savedTmux remoteAge cols
            rows)) ∧
      (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
        ∀
          row ∈
            Selector.Picker.frameRows state snapshot statusOf loaded withColor savedTmux remoteAge
              cols rows,
          Display.Clean row) ∧
      (∀ before after : List (List UInt8),
        (∀ row ∈ after, Display.Clean row) → Display.Clean (Selector.Picker.update before after)) ∧
      Display.Clean Selector.Picker.enterAnsi ∧
      Display.Clean Selector.Picker.exitAnsi ∧
      (∀ title, Display.Clean (Terminal.Title.ansi title)) ∧
      (∀ v title, Display.Clean (Terminal.Title.update v title)) ∧
      (∀ v, Display.Clean (Terminal.Render.screenText v)) ∧
      (∀ v, Display.Clean (Terminal.Render.history v)) ∧
      (∀ s, Display.Clean (Session.infoText s)) ∧
      (∀ name notice, Display.Clean (Display.Alert.notification name notice)) ∧
      Display.Clean Terminal.Render.leaveAnsi := by
  have info (s : State) : Display.Clean (Session.infoText s) := by
    obtain ⟨cs, text, safe⟩ := infoText_text s
    rw [text]
    exact
      Display.clean_text fun c hc =>
        (safe c hc).elim (fun tab => .inr (.inr tab)) fun rest =>
          rest.elim (fun newline => .inr (.inl newline)) .inl
  exact
    ⟨Display.terminalListing_clean, Selector.Picker.frame_clean, Selector.Picker.frameRows_clean,
      Selector.Picker.update_clean, Selector.Picker.enterAnsi_clean, Selector.Picker.exitAnsi_clean,
      Display.title_ansi_clean, Display.title_update_clean, Display.screenText_clean,
      Display.history_clean, info, Display.Alert.notification_clean, Display.leaveAnsi_clean⟩

theorem writes_clean_rejects_reset :
    ¬((∀ withColor width rows,
          Display.Clean
            ((fun (_ : Bool) (_ : Option Nat) (_ : List (List (String × String))) =>
                ([0x1B, 0x63] : List UInt8))
              withColor width rows)) ∧
        (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
          Display.Clean
            (Selector.Picker.frame state snapshot statusOf loaded withColor savedTmux remoteAge cols
              rows)) ∧
        (∀ state snapshot statusOf loaded withColor savedTmux remoteAge cols rows,
          ∀
            row ∈
              Selector.Picker.frameRows state snapshot statusOf loaded withColor savedTmux remoteAge
                cols rows,
            Display.Clean row) ∧
        (∀ before after : List (List UInt8),
          (∀ row ∈ after, Display.Clean row) →
            Display.Clean (Selector.Picker.update before after)) ∧
        Display.Clean Selector.Picker.enterAnsi ∧
        Display.Clean Selector.Picker.exitAnsi ∧
        (∀ title, Display.Clean (Terminal.Title.ansi title)) ∧
        (∀ v title, Display.Clean (Terminal.Title.update v title)) ∧
        (∀ v, Display.Clean (Terminal.Render.screenText v)) ∧
        (∀ v, Display.Clean (Terminal.Render.history v)) ∧
        (∀ s, Display.Clean (Session.infoText s)) ∧
        (∀ name notice, Display.Clean (Display.Alert.notification name notice)) ∧
        Display.Clean Terminal.Render.leaveAnsi) :=
  fun h => Display.not_clean_reset (h.1 true none [])

theorem withColor_iff (terminal : Bool) (noColor term : Option String) :
    Os.Env.withColor terminal noColor term = true ↔
      terminal = true ∧
        (noColor = none ∨ noColor = some "") ∧
        ∃ name, term = some name ∧ name ≠ "" ∧ name ≠ "dumb" :=
  Os.Env.withColor_iff terminal noColor term

theorem withColor_iff_rejects_presence :
    ¬∀ (terminal : Bool) (noColor term : Option String),
        (fun (terminal : Bool) (noColor : Option String) (_ : Option String) =>
                terminal && noColor.isNone)
              terminal noColor term =
            true ↔
          terminal = true ∧
            (noColor = none ∨ noColor = some "") ∧
            ∃ name, term = some name ∧ name ≠ "" ∧ name ≠ "dumb" := by
  intro h
  have colors :=
    (h true (some "") (some "xterm")).mpr ⟨rfl, .inr rfl, "xterm", rfl, by simp, by simp⟩
  exact absurd colors (by decide)

end Linger
