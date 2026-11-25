module

public import Terminal.CoreSpec
meta import SoftwareChallenge

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

@[witness replay_history]
theorem replay_history_applies :
    ∃ (budget : Nat) (_ : 0 < budget) (v : Vt.Vt) (w : Vt.Vt) (_ :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v) (_ :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable w) (_ :
      w.colCount = v.colCount) (_ : w.rowCount = v.rowCount),
      (Render.sbRows v).isEmpty = false := by
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

@[witness replay_synchronized]
theorem replay_synchronized_applies :
    ∃ (budget : Nat) (_ : 0 < budget) (v : Vt.Vt) (bytes : Render.Bytes),
      Replay.Emits Replay.next budget (Replay.start v) bytes := by
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

@[witness history_grows]
theorem history_grows_applies :
    ∃ (v : Vt.Vt), Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v := by
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

@[witness live_shape]
theorem live_shape_applies :
    ∃ (v : Vt.Vt), Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce Vt.Vt.Decodable v := by
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

@[witness feed_inert]
theorem feed_inert_applies : ∃ (v : Vt.Vt) (_ : List UInt8), v.atBoundary = true := by sorry

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

@[witness next_bounded]
theorem next_bounded_applies :
    ∃ (budget : Nat) (p : Replay.Plan) (q : Replay.Plan) (bytes : Render.Bytes),
      Replay.next budget p = some (bytes, q) := by
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

@[witness leave_canonical_all]
theorem leave_canonical_all_applies : ∃ (w : Vt.Vt), 2 ≤ w.rowCount := by sorry

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

@[witness vt_keeps]
theorem vt_keeps_applies : ∃ (v : Vt.Vt) (_ : Vt.Ref.Kept), v.atBoundary = true := by sorry

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

@[witness title_source]
theorem title_source_applies : ∃ (v : Vt.Vt) (_ : List Stream.Token), v.atBoundary = true := by
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

theorem progress_source (v : Vt.Vt) (ts : List Stream.Token) (ok : ∀ t ∈ ts, t.Ok)
    (p : Option Mediation.Progress) :
    ((Mediation.feed v .ground (ts.flatMap Stream.Token.bytes)).progress).getD p =
      ts.foldl Stream.Token.reprogress p := by
  sorry

@[kills progress_source]
theorem progress_source_rejects_title :
    ¬∀ (v : Vt.Vt) (ts : List Stream.Token),
        (∀ t ∈ ts, t.Ok) →
          ∀ (p : Option Mediation.Progress),
            (((Stream.titleProgress Vt.Vt.windowTitle Mediation.feed) v .ground
                      (ts.flatMap Stream.Token.bytes)).progress).getD
                p =
              ts.foldl Stream.Token.reprogress p := by
  sorry

end Terminal
