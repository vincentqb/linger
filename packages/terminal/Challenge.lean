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
receiver's history is those rows (`replay_history`). A repaint, at any budget, is one
synchronized update: it opens with `CSI ? 2026 h`, closes with `CSI ? 2026 l` and holds neither
inside (`replay_synchronized`), so a terminal that knows DEC mode 2026 shows it whole. Not claimed
of a repaint: more than that of a receiver of another size, or of a terminal or receiver no session holds; older history; the
window title, which it scrubs of C0 controls and DEL and a receiver may cut short; the mouse mode
once later output arrives, or at all when it is other than off, 1000, 1002 and 1003, which only a
decoded checkpoint holds; the bell, which stays the receiver's; and what later output shows of a
terminal repainted inside a control sequence or a character, whose partial one the receiver does
not hold.

The emulator does what the standards say each of a small set of sequences does (`vt_conforms`):
`Vt.Ref` is a reference model of an abstract screen, its cells, cursor and deferred wrap, pen,
modes, scroll region, tab stops, saved cursor, stashed main screen, title and bell, written from
ECMA-48, xterm's `ctlseqs` and the VT510 manual, and `Vt.Ref.Seq` its sequences: printing ASCII
with autowrap and the deferred wrap, CR, LF, BS, HT, BEL, CUU, CUD, CUF, CUB, CUP, CHA, VPA, ED and
EL 0 to 2, IL, DL, ICH, DCH, ECH, SGR's reset, bold, faint, italic, underline, inverse and 8, 256 and
24-bit colours, DECSTBM, IND and RI, DECSC and DECRC, DECSET and DECRST 25, 7, 1049, 2004 and 2026,
and OSC 0 and 2 titles. Some reading of every terminal as a reference screen shows what the
terminal's accessors show, and feeding any sequence of the set, as a program writes it, to a live
terminal between control sequences and characters changes that reading exactly as the reference
says. Where linger departs from xterm the reference says so: 1049 homes the cursor and makes the
whole screen the region, and BS and the erases keep a deferred wrap, as tmux does. What linger
keeps or skips outside the set changes nothing a terminal shows (`vt_keeps`): DECSCUSR sets the
cursor's shape alone, which a repaint replays, and sixel images, APC strings such as kitty's
graphics and OSC 8 hyperlinks are skipped. Not claimed of the reference: a terminal with a wide
character or a combining mark on its screen, insert mode, DEC line drawing, a parameter above
65535, an SGR of more than 16 parameters, a title past an OSC payload's 2048 bytes, a sequence that
starts inside another or a character, a sequence outside the set, and the history, which
`history_grows` covers.

What a program's output tells is decided byte by byte, over any stream of whole tokens
(`Stream.Token`): printable ASCII characters, C0 controls other than ESC, control sequences, OSC
strings ended by BEL or ST, DCS, SOS, PM and APC strings and escape sequences. The window title
changes only as OSC 0 and OSC 2 set it and RIS resets it (`title_source`, killed by an emulator
that takes OSC 1, the icon name, for the title). The mediator feeds the terminal every byte, and
the stream asks for someone exactly when it holds BEL as a control or an OSC that posts a desktop
notification, OSC 9 but not its ConEmu sub-commands such as `9;4` progress, or OSC 777 `notify`,
and the notification's text is the last one's (`asks_exact`, killed by a mediator that hears the
BEL ending a string as a bell and by one that hears `9;4` as a notification). Not claimed of the
streams: an OSC whose payload exceeds the 253 bytes the mediator classifies, a string or sequence
cut short, a C0 control inside a sequence, and a CSI with an intermediate byte. -/

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

def Terminal.Mediation.feed :
    Vt.Vt → Mediation.Scan → Render.Bytes → Mediation.Result Vt.Vt := sorry

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

theorem replay_synchronized (budget : Nat) (positive : 0 < budget) (v : Vt.Vt)
    (bytes : Render.Bytes) (emits : Replay.Emits Replay.next budget (Replay.start v) bytes) :
    ∃ body,
      bytes = Render.syncBegin ++ body ++ Render.syncEnd ∧
        ¬Render.syncBegin <:+: body ∧ ¬Render.syncEnd <:+: body := by
  sorry

@[kills replay_synchronized]
theorem replay_synchronized_rejects_bare :
    ¬∀ (budget : Nat),
        0 < budget →
          ∀ (v : Vt.Vt),
            ∀ (bytes : Render.Bytes),
              Replay.Emits Replay.next budget (Replay.unbracketed Replay.start Replay.next v)
                  bytes →
                ∃ body,
                  bytes = Render.syncBegin ++ body ++ Render.syncEnd ∧
                    ¬Render.syncBegin <:+: body ∧ ¬Render.syncEnd <:+: body := by
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

theorem vt_conforms :
    ∃ screen : Vt.Vt → Vt.Ref.Screen,
      (∀ v,
          Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
            Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
        ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
          Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
            v.atBoundary = true →
            Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
            s.Ok → Vt.Ref.Same (screen (v.feed s.bytes)) (Vt.Ref.Seq.apply (screen v) s) := by
  sorry

@[kills vt_conforms]
theorem vt_conforms_rejects_elWhole :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.elWhole Vt.Vt.feed) Vt.Vt.resize Vt.Vt.quiesce
                Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.elWhole Vt.Vt.feed) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  sorry

@[kills vt_conforms]
theorem vt_conforms_rejects_cupFromZero :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.cupFromZero Vt.Vt.feed) Vt.Vt.resize Vt.Vt.quiesce
                Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.cupFromZero Vt.Vt.feed) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  sorry

@[kills vt_conforms]
theorem vt_conforms_rejects_eagerWrap :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.eagerWrap Vt.Vt.feed Vt.Vt.colCount Vt.Vt.cursorPos)
                Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same
                (screen ((Vt.Ref.eagerWrap Vt.Vt.feed Vt.Vt.colCount Vt.Vt.cursorPos) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  sorry

@[kills vt_conforms]
theorem vt_conforms_rejects_resetKeepsBold :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.resetKeepsBold Vt.Vt.feed Vt.Vt.getPen) Vt.Vt.resize
                Vt.Vt.quiesce Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.resetKeepsBold Vt.Vt.feed Vt.Vt.getPen) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  sorry

@[kills vt_conforms]
theorem vt_conforms_rejects_ilKeepsColumn :
    ¬∃ screen : Vt.Vt → Vt.Ref.Screen,
        (∀ v,
            Vt.Ref.Reads Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.cursorPos Vt.Vt.getPen
              Vt.Vt.getModes Vt.stick Vt.Vt.windowTitle v (screen v)) ∧
          ∀ (v : Vt.Vt) (s : Vt.Ref.Seq),
            Vt.Live Vt.Vt.init (Vt.Ref.ilKeepsColumn Vt.Vt.feed Vt.Vt.cursorPos) Vt.Vt.resize
                Vt.Vt.quiesce Vt.Vt.Decodable v →
              v.atBoundary = true →
              Vt.Ref.Plain Vt.Vt.colCount Vt.Vt.rowCount Vt.Vt.getRow Vt.Vt.getModes Vt.stick v →
              s.Ok →
              Vt.Ref.Same (screen ((Vt.Ref.ilKeepsColumn Vt.Vt.feed Vt.Vt.cursorPos) v s.bytes))
                (Vt.Ref.Seq.apply (screen v) s) := by
  sorry

theorem vt_keeps (v : Vt.Vt) (k : Vt.Ref.Kept) (between : v.atBoundary = true) (ok : k.Ok) :
    (∀ y, (v.feed k.bytes).getRow y = v.getRow y) ∧
      (v.feed k.bytes).cursorPos = v.cursorPos ∧
      (v.feed k.bytes).getPen = v.getPen ∧
      (v.feed k.bytes).getModes = Vt.Ref.Kept.modes v.getModes k ∧
      Vt.stick (v.feed k.bytes) = Vt.stick v ∧
      (v.feed k.bytes).windowTitle = v.windowTitle ∧ (v.feed k.bytes).atBoundary = true := by
  sorry

@[kills vt_keeps]
theorem vt_keeps_rejects_unescaped :
    ¬∀ (v : Vt.Vt) (k : Vt.Ref.Kept),
        v.atBoundary = true →
          k.Ok →
          (∀ y, ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).getRow y = v.getRow y) ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).cursorPos = v.cursorPos ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).getPen = v.getPen ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).getModes = Vt.Ref.Kept.modes v.getModes k ∧
            Vt.stick ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes) = Vt.stick v ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).windowTitle = v.windowTitle ∧
            ((Vt.Ref.unescaped Vt.Vt.feed) v k.bytes).atBoundary = true := by
  sorry

theorem title_source (v : Vt.Vt) (ts : List Stream.Token) (between : v.atBoundary = true)
    (ok : ∀ t ∈ ts, t.Ok) :
    (v.feed (ts.flatMap Stream.Token.bytes)).windowTitle =
        ts.foldl Stream.Token.retitle v.windowTitle ∧
      (v.feed (ts.flatMap Stream.Token.bytes)).atBoundary = true := by
  sorry

@[kills title_source]
theorem title_source_rejects_icon :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        v.atBoundary = true →
          (∀ t ∈ ts, t.Ok) →
          ((Stream.iconAsTitle Vt.Vt.feed) v (ts.flatMap Stream.Token.bytes)).windowTitle =
              ts.foldl Stream.Token.retitle v.windowTitle ∧
            ((Stream.iconAsTitle Vt.Vt.feed) v (ts.flatMap Stream.Token.bytes)).atBoundary =
              true := by
  sorry

theorem asks_exact (v : Vt.Vt) (ts : List Stream.Token) (ok : ∀ t ∈ ts, t.Ok) :
    (Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).vt =
        v.feed (ts.flatMap Stream.Token.bytes) ∧
      (Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).asks = ts.any Stream.Token.asks ∧
      (Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).notice = Stream.notice ts := by
  sorry

@[kills asks_exact]
theorem asks_exact_rejects_ending :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        (∀ t ∈ ts, t.Ok) →
          ((Stream.endingRings Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).vt =
              v.feed (ts.flatMap Stream.Token.bytes) ∧
            ((Stream.endingRings Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).asks =
              ts.any Stream.Token.asks ∧
            ((Stream.endingRings Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).notice =
              Stream.notice ts := by
  sorry

@[kills asks_exact]
theorem asks_exact_rejects_progress :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        (∀ t ∈ ts, t.Ok) →
          ((Stream.progressAsks Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).vt =
              v.feed (ts.flatMap Stream.Token.bytes) ∧
            ((Stream.progressAsks Mediation.feed) v .ground (ts.flatMap Stream.Token.bytes)).asks =
              ts.any Stream.Token.asks ∧
            ((Stream.progressAsks Mediation.feed) v .ground
                  (ts.flatMap Stream.Token.bytes)).notice =
              Stream.notice ts := by
  sorry

end Terminal
