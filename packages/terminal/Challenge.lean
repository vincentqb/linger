module

public import Terminal.CoreSpec
meta import SoftwareChallenge

/-! # Headline theorems of the terminal toolkit

What the VT toolkit must do for the program that keeps a terminal: a live terminal keeps its
shape and its history, feeding inert bytes changes nothing, a control sequence's count is capped,
a repaint streams in bounded chunks and restores its terminal on the receiver, screen text has no
control characters, and the handback sequence leaves a terminal canonical: its modes the
default record, the terminal's own cursor shape among them (`leave_canonical_all`). The theorems
are stated over the toolkit's parts, declared below as holes: `sorry` here, which the package's
code supplies, and `Terminal.Solution` proves the same statements of them.

A repaint, streamed at any positive budget, restores its terminal on the receiver as far as the
receiver can show it (`replay_restores`, as `Vt.Restores` says). Any receiver, such as a watcher
of another size, gets the terminal's pen and every mode, the cursor's shape among them, the mouse
mode when it is one a program sets, and is left between control sequences and characters; one as
tall as the terminal also gets the scroll region, the character sets, the shift state and which
screen is current, when DECSTBM could have set that region. A live receiver of a live terminal's size shows each row and
the cursor too, and, when the terminal sits between control sequences and characters as well,
no later output tells the two apart, so the receiver also holds what the emulator reads and no
accessor shows, such as the deferred wrap, the tab ruler, the cursor DECSC saved and the main
screen the alternate one stashes, its rows among them. When
`Render.sbRows` picks any history rows, the newest that fit the repaint's budget for history, the
receiver's history is those rows (`replay_history`). Not claimed of a repaint: more than that of
a receiver of another size, or of a terminal or receiver no session holds; older history; the
window title, which it scrubs of C0 controls and DEL and a receiver may cut short; the mouse mode
once later output arrives, or at all when it is other than off, 1000, 1002 and 1003, which only a
decoded checkpoint holds; the bell, which stays the receiver's; and what later output shows of a
terminal repainted inside a control sequence or a character, whose partial one the receiver does
not hold. -/

public section

open Terminal

def Terminal.Vt.Vt : Type := sorry

def Terminal.Vt.Vt.init : (cols rows : Nat) → Vt.Vt := sorry

def Terminal.Vt.Vt.feed : Vt.Vt → List UInt8 → Vt.Vt := sorry

def Terminal.Vt.Vt.resize : Vt.Vt → (cols rows : Nat) → Vt.Vt := sorry

def Terminal.Vt.Vt.quiesce : Vt.Vt → Vt.Vt := sorry

def Terminal.Vt.Vt.Decodable : Vt.Vt → Prop := sorry

def Terminal.Vt.Vt.colCount : Vt.Vt → Nat := sorry

def Terminal.Vt.Vt.rowCount : Vt.Vt → Nat := sorry

def Terminal.Vt.Vt.getRow : Vt.Vt → Nat → Vt.Row := sorry

def Terminal.Vt.Vt.cursorPos : Vt.Vt → Nat × Nat := sorry

def Terminal.Vt.Vt.getModes : Vt.Vt → Vt.Modes := sorry

def Terminal.Vt.Vt.getPen : Vt.Vt → Vt.Pen := sorry

def Terminal.Vt.Vt.scrollback : Vt.Vt → List Vt.Row := sorry

def Terminal.Vt.stick : Vt.Vt → Vt.Sticky := sorry

def Terminal.Vt.Vt.windowTitle : Vt.Vt → String := sorry

def Terminal.Vt.Vt.atBoundary : Vt.Vt → Bool := sorry

def Terminal.Vt.sbCap : Nat := sorry

def Terminal.Vt.Vt.repeatAtMost : Vt.Vt → (cap count : Nat) → (Vt.Vt → Vt.Vt) → Vt.Vt := sorry

def Terminal.Render.sbRows : Vt.Vt → Array Vt.Row := sorry

def Terminal.Render.screenText : Vt.Vt → Render.Bytes := sorry

def Terminal.Render.history : Vt.Vt → Render.Bytes := sorry

def Terminal.Render.leaveAnsi : Render.Bytes := sorry

def Terminal.Replay.Plan : Type := sorry

def Terminal.Replay.start : Vt.Vt → Replay.Plan := sorry

def Terminal.Replay.next :
    (budget : Nat) → Replay.Plan → Option (Render.Bytes × Replay.Plan) := sorry

namespace Terminal

theorem replay_restores (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        Vt.Restores (Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable)
          Vt.Vt.feed Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
          Vt.Vt.getModes Vt.stick Vt.Vt.atBoundary v w (w.feed bytes) := by
  sorry

@[kills replay_restores]
theorem replay_restores_rejects_resaved :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            ∃ bytes,
              Replay.Emits Replay.next budget
                  ((fun (v : Vt.Vt) => Replay.start (v.feed [0x1B, 0x37])) v) bytes ∧
                Vt.Restores
                  (Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable)
                  Vt.Vt.feed Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
                  Vt.Vt.getModes Vt.stick Vt.Vt.atBoundary v w (w.feed bytes) := by
  sorry

theorem replay_history (budget : Nat) (positive : 0 < budget) (v w : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v)
    (hw : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w)
    (hcols : w.colCount = v.colCount) (hrows : w.rowCount = v.rowCount)
    (retained : (Render.sbRows v).isEmpty = false) :
    ∃ bytes,
      Replay.Emits Replay.next budget (Replay.start v) bytes ∧
        (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  sorry

@[kills replay_history]
theorem replay_history_rejects_silence :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v w : Vt.Vt),
            Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
              Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w →
              w.colCount = v.colCount →
              w.rowCount = v.rowCount →
              (Render.sbRows v).isEmpty = false →
              ∃ bytes,
                Replay.Emits (fun _ _ => none) budget (Replay.start v) bytes ∧
                  (w.feed bytes).scrollback = (Render.sbRows v).toList := by
  sorry

theorem history_grows (v : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) :
    (∀ bytes : List UInt8,
        v.atBoundary = true →
          Vt.mayErase bytes = false →
          ∃ added, (v.feed bytes).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added)) ∧
      ∀ cols rows : Nat,
        ∃ added,
          (v.resize cols rows).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added) ∧
            ((Vt.stick v).alt = false →
              added = (List.range (v.rowCount - (v.resize cols rows).rowCount)).map v.getRow) := by
  sorry

@[kills history_grows]
theorem history_grows_rejects_lost :
    ¬∀ (v : Vt.Vt),
        Vt.Live Vt.Vt.init (fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) Vt.Vt.resize
            Vt.Vt.quiesce Vt.Vt.Decodable v →
          (∀ bytes : List UInt8,
              v.atBoundary = true →
                Vt.mayErase bytes = false →
                ∃ added,
                  ((fun (_ : Vt.Vt) (_ : List UInt8) => Vt.Vt.init 1 1) v bytes).scrollback =
                    Vt.newest Vt.sbCap (v.scrollback ++ added)) ∧
            ∀ cols rows : Nat,
              ∃ added,
                (v.resize cols rows).scrollback = Vt.newest Vt.sbCap (v.scrollback ++ added) ∧
                  ((Vt.stick v).alt = false →
                    added =
                      (List.range (v.rowCount - (v.resize cols rows).rowCount)).map v.getRow) := by
  sorry

theorem live_shape (v : Vt.Vt)
    (hv : Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) :
    1 ≤ v.colCount ∧
      v.colCount ≤ 1000 ∧
      1 ≤ v.rowCount ∧
      v.rowCount ≤ 1000 ∧
      (∀ y < v.rowCount, (v.getRow y).size = v.colCount) ∧
      v.cursorPos.1 < v.colCount ∧ v.cursorPos.2 < v.rowCount ∧ v.scrollback.length ≤ Vt.sbCap := by
  sorry

@[kills live_shape]
theorem live_shape_rejects_empty :
    ¬∀ (v : Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
          1 ≤ v.colCount ∧
            v.colCount ≤ 1000 ∧
            1 ≤ v.rowCount ∧
            v.rowCount ≤ 1000 ∧
            (∀ y < v.rowCount,
              ((fun (_ : Vt.Vt) (_ : Nat) => (#[] : Vt.Row)) v y).size = v.colCount) ∧
            v.cursorPos.1 < v.colCount ∧
            v.cursorPos.2 < v.rowCount ∧ v.scrollback.length ≤ Vt.sbCap := by
  sorry

theorem feed_inert (v : Vt.Vt) (bytes : List UInt8) (between : v.atBoundary = true)
    (inert : ∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) :
    v.feed bytes = v := by sorry

@[kills feed_inert]
theorem feed_inert_rejects_print :
    ¬∀ (v : Vt.Vt) (bytes : List UInt8),
        v.atBoundary = true →
          (∀ b ∈ bytes, b = 0x7F ∨ b < 0x07 ∨ 0x0F < b ∧ b < 0x20 ∧ b ≠ 0x1B) →
          (fun (v : Vt.Vt) (bytes : List UInt8) =>
                v.feed (bytes.map fun b => if b = 0x7F then 0x3F else b))
              v bytes =
            v := by
  sorry

theorem repeatAtMost_eq_repeat (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt) :
    v.repeatAtMost cap count f = Nat.repeat f (min count cap) v := by sorry

@[kills repeatAtMost_eq_repeat]
theorem repeatAtMost_eq_repeat_rejects_uncapped :
    ¬∀ (v : Vt.Vt) (cap count : Nat) (f : Vt.Vt → Vt.Vt),
        (fun (v : Vt.Vt) (_ count : Nat) (f : Vt.Vt → Vt.Vt) => Nat.repeat f count v) v cap count
            f =
          Nat.repeat f (min count cap) v := by
  sorry

theorem next_bounded {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes}
    (h : Replay.next budget p = some (bytes, q)) : bytes.length ≤ budget := by sorry

@[kills next_bounded]
theorem next_bounded_rejects_overrun :
    ¬∀ {budget : Nat} {p q : Replay.Plan} {bytes : Render.Bytes},
        Replay.overrun budget p = some (bytes, q) → bytes.length ≤ budget := by
  sorry

theorem screenText_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.screenText v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

@[kills screenText_text]
theorem screenText_text_rejects_escape :
    ¬∀ (v : Vt.Vt),
        ∃ cs : List Char,
          Render.escape v = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

theorem history_text (v : Vt.Vt) :
    ∃ cs : List Char,
      Render.history v = cs.flatMap String.utf8EncodeChar ∧
        ∀ c ∈ cs,
          c = '\n' ∨ (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

@[kills history_text]
theorem history_text_rejects_escape :
    ¬∀ (v : Vt.Vt),
        ∃ cs : List Char,
          Render.escape v = cs.flatMap String.utf8EncodeChar ∧
            ∀ c ∈ cs,
              c = '\n' ∨
                (0x20 ≤ c.toNat ∧ c.toNat ≠ 0x7F ∧ ¬(0x80 ≤ c.toNat ∧ c.toNat < 0xA0)) := by
  sorry

theorem leave_canonical_all (w : Vt.Vt) (h2 : 2 ≤ w.rowCount) :
    (w.feed Render.leaveAnsi).atBoundary = true ∧
      (w.feed Render.leaveAnsi).getModes = ({} : Vt.Modes) ∧
      Vt.stick (w.feed Render.leaveAnsi) =
        { rows := w.rowCount, top := 0, bot := w.rowCount - 1, g0 := false, g1 := false,
          so := false, alt := false } ∧
      (w.feed Render.leaveAnsi).getPen = ({} : Vt.Pen) ∧
      (w.feed Render.leaveAnsi).windowTitle = "" := by
  sorry

@[kills leave_canonical_all]
theorem leave_canonical_all_rejects_escape :
    ¬∀ (w : Vt.Vt),
        2 ≤ w.rowCount →
          (w.feed ([0x1B] : Render.Bytes)).atBoundary = true ∧
            (w.feed ([0x1B] : Render.Bytes)).getModes = ({} : Vt.Modes) ∧
            Vt.stick (w.feed ([0x1B] : Render.Bytes)) =
              { rows := w.rowCount, top := 0, bot := w.rowCount - 1, g0 := false, g1 := false,
                so := false, alt := false } ∧
            (w.feed ([0x1B] : Render.Bytes)).getPen = ({} : Vt.Pen) ∧
            (w.feed ([0x1B] : Render.Bytes)).windowTitle = "" := by
  sorry

end Terminal
