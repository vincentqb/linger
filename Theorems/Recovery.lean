module

public import Linger.App.CoreCode.Recovery
public import Linger.Import.CoreCode.Resurrect
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Checkpoint
public import Linger.Session.CoreCode.Handoff
public import Os.WorldSpec
public import Linger.Session.CoreSpec
public import Terminal.CoreCode.Replay
public import Terminal.CoreSpec
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

/-! # Part 7 of `Challenge.lean`, recovery: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem handoff_carries (s : State) (w : Handoff.World)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) s.terminal)
    (quiet : s.terminal.quiesce = s.terminal) : Handoff.decode (Handoff.encode s w) = some (s, w) :=
  Handoff.decode_encode s w (Checkpoint.live_of_decoded h) quiet

/-- A world a daemon could hand over, for the kills. -/
private def someWorld : Handoff.World :=
  { listenFd := 0, ptyFd := 0, childPid := 0, signals := (0, 0), locks := [], conns := [],
    ptyIn := [], login := false, asker := 0 }

private theorem init_quiet : (Vt.Vt.init 1 1).quiesce = Vt.Vt.init 1 1 := Vt.quiesce_of_quiet rfl

theorem handoff_carries_rejects_rebuilt :
    ¬∀ (s : State) (w : Handoff.World),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded Checkpoint.loadBytes) s.terminal →
          s.terminal.quiesce = s.terminal →
          Handoff.decode
              ((fun (s : State) (w : Handoff.World) =>
                  Handoff.encode (State.boot s.terminal s.fieldList []) w)
                s w) =
            some (s, w) := by
  intro h
  have carried := h (State.boot (Vt.Vt.init 1 1) [] [("k", "v")]) someWorld (.init 1 1) init_quiet
  rw [Handoff.decode_encode _ _ (.init 1 1) init_quiet] at carried
  simp [State.boot, State.terminal, State.fieldList] at carried

theorem upgrade_keeps (exec : Nat → List Nat → List Nat → Nat × List Nat × List Nat)
    (keeps : Os.Exec.Keeps exec) (pid : Nat) (w : Handoff.World) :
    (exec pid [w.childPid] (Handoff.kept w)).1 = pid ∧
      (exec pid [w.childPid] (Handoff.kept w)).2.1 = [w.childPid] ∧
      ∀ fd ∈ w.fds, fd ∈ (exec pid [w.childPid] (Handoff.kept w)).2.2 := by
  rw [keeps pid [w.childPid] (Handoff.kept w)]
  exact ⟨rfl, rfl, Handoff.fds_kept w⟩

theorem upgrade_keeps_rejects_unconnected :
    ¬∀ (exec : Nat → List Nat → List Nat → Nat × List Nat × List Nat),
        Os.Exec.Keeps exec →
          ∀ (pid : Nat) (w : Handoff.World),
            (exec pid [w.childPid] ((fun (w : Handoff.World) => [w.listenFd, w.ptyFd]) w)).1 = pid ∧
              (exec pid [w.childPid] ((fun (w : Handoff.World) => [w.listenFd, w.ptyFd]) w)).2.1 =
                [w.childPid] ∧
              ∀ fd ∈ w.fds,
                fd ∈
                  (exec pid [w.childPid]
                      ((fun (w : Handoff.World) => [w.listenFd, w.ptyFd]) w)).2.2 := by
  intro h
  -- an exec that keeps the socket and the pty, and closes a lock
  have kept :=
    (h (fun pid children kept => (pid, children, kept)) (fun _ _ _ => rfl) 0
          { listenFd := 3, ptyFd := 4, childPid := 1, signals := (5, 6), locks := [7], conns := [],
            ptyIn := [], login := false, asker := 0 }).2.2
      7 (by simp [Handoff.World.fds])
  simp at kept

theorem handoff_versioned (s : State) (w : Handoff.World) (v : Nat) (rest : List UInt8) :
    Handoff.version ∈ Handoff.formats ∧
      (Handoff.encode s w).take (Handoff.header Handoff.version).length =
        Handoff.header Handoff.version ∧
      (v ∉ Handoff.formats → v < 256 → Handoff.decode (Handoff.header v ++ rest) = none) :=
  ⟨by decide, Handoff.encode_header s w, Handoff.decode_unknown v rest⟩

theorem handoff_versioned_rejects_unread :
    ¬∀ (s : State) (w : Handoff.World) (v : Nat) (rest : List UInt8),
        Handoff.version ∈ Handoff.formats ∧
          (Handoff.encode s w).take (Handoff.header Handoff.version).length =
            Handoff.header Handoff.version ∧
          (v ∉ Handoff.formats →
            v < 256 →
            (fun (bytes : List UInt8) =>
                  Handoff.decode
                    (Handoff.header Handoff.version ++
                      bytes.drop (Handoff.header Handoff.version).length))
                (Handoff.header v ++ rest) =
              none) := by
  intro h
  let s := State.boot (Vt.Vt.init 1 1) [] []
  let rest := (Handoff.encode s someWorld).drop (Handoff.header Handoff.version).length
  have refused := (h s someWorld 200 rest).2.2 (by decide) (by decide)
  have dropped :
    (Handoff.header 200 ++ rest).drop (Handoff.header Handoff.version).length = rest := by
    simp [Handoff.header]
  have whole : Handoff.header Handoff.version ++ rest = Handoff.encode s someWorld := by
    simp [rest, Handoff.encode]
  dsimp only at refused
  rw [dropped, whole, Handoff.decode_encode _ _ (.init 1 1) init_quiet] at refused
  cases refused

theorem upgrade_probes (reported : Option (List Nat)) :
    Upgrade.proceeds reported = true ↔
      ∃ formats, reported = some formats ∧ Handoff.version ∈ formats :=
  Upgrade.proceeds_iff reported

theorem upgrade_probes_rejects_unprobed :
    ¬∀ (reported : Option (List Nat)),
        (fun (_ : Option (List Nat)) => true) reported = true ↔
          ∃ formats, reported = some formats ∧ Handoff.version ∈ formats := by
  intro h
  obtain ⟨_, none_some, _⟩ := (h none).1 rfl
  cases none_some

theorem loadBytes_saveBytes_live (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
  Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)

theorem loadBytes_saveBytes_live_rejects_refusal :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt))) c.vt →
          (fun _ => none : ByteArray → Option (Checkpoint.Ckpt Vt.Vt)) (Checkpoint.saveBytes c) =
            some { c with vt := c.vt.quiesce } := by
  intro h
  cases h ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1)

theorem resume_restores (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt)
    (metaKv : List (String × String)) :
    (State.boot (bootVt ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
            (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
            metaKv).terminal =
        c.vt.quiesce ∧
      (State.boot (bootVt ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
            (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
            metaKv).fieldList =
        (c.fields.filter (recordField ·.1)).take maxFields := by
  have loaded :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some { c with vt := c.vt.quiesce } :=
    Checkpoint.loadBytes_saveBytes_live c (Checkpoint.live_of_decoded h)
  obtain ⟨_, restored, terminal, -, labels, -⟩ := Session.boot_observed c.vt.quiesce c.fields metaKv
  simp only [loaded, Option.map_some, Option.getD_some, restored]
  exact ⟨terminal, labels⟩

theorem resume_restores_rejects_fresh :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded Checkpoint.loadBytes) c.vt →
          ∀ (metaKv : List (String × String)),
            (State.boot
                    ((fun (_ : Option Vt.Vt) => Vt.Vt.init 1 1)
                      ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
                    (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
                    metaKv).terminal =
                c.vt.quiesce ∧
              (State.boot
                    ((fun (_ : Option Vt.Vt) => Vt.Vt.init 1 1)
                      ((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.vt)))
                    (((Checkpoint.loadBytes (Checkpoint.saveBytes c)).map (·.fields)).getD [])
                    metaKv).fieldList =
                (c.fields.filter (recordField ·.1)).take maxFields := by
  intro h
  have fresh := (h ⟨Vt.Vt.init 2 1, "", []⟩ (.init 2 1) []).1
  obtain ⟨-, -, terminal, -, -, -⟩ :=
    Session.boot_observed (Vt.Vt.init 1 1)
      (((Checkpoint.loadBytes (Checkpoint.saveBytes ⟨Vt.Vt.init 2 1, "", []⟩)).map (·.fields)).getD
        [])
      []
  rw [terminal] at fresh
  exact absurd (congrArg Vt.Vt.colCount fresh) (by decide +kernel)

theorem loadBytes_resave {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt}
    (h : Checkpoint.loadBytes b = some c) :
    Checkpoint.loadBytes (Checkpoint.saveBytes c) = some c := Checkpoint.loadBytes_resave h

theorem loadBytes_resave_rejects_fixed :
    ¬∀ {b : ByteArray} {c : Checkpoint.Ckpt Vt.Vt},
        Checkpoint.loadBytes b = some c →
          Checkpoint.loadBytes
              ((fun (_ : Checkpoint.Ckpt Vt.Vt) => Checkpoint.saveBytes ⟨Vt.Vt.init 1 1, "x", []⟩)
                c) =
            some c := by
  intro h
  have empty := loadBytes_saveBytes_live ⟨Vt.Vt.init 1 1, "", []⟩ (.init 1 1)
  have other := loadBytes_saveBytes_live ⟨Vt.Vt.init 1 1, "x", []⟩ (.init 1 1)
  have same := (h empty).symm.trans other
  exact absurd (congrArg (Option.map Checkpoint.Ckpt.cwd) same) (by decide)

theorem recovery_exact (create : Bool) (file : Option ByteArray) :
    App.Recovery.decide create file =
      (file.map fun bytes =>
            ((Checkpoint.loadBytes bytes).map App.Recovery.resume).getD (.refuse .notDone)).getD
        (if create then .fresh else .refuse .notFound) := App.Recovery.recovery_exact create file

theorem recovery_exact_rejects_missing :
    ¬∀ (create : Bool) (file : Option ByteArray),
        (fun (create : Bool) (file : Option ByteArray) =>
              ((file.bind Checkpoint.loadBytes).map App.Recovery.resume).getD
                (if create then App.Recovery.fresh else .refuse .notFound))
            create file =
          (file.map fun bytes =>
                ((Checkpoint.loadBytes bytes).map App.Recovery.resume).getD (.refuse .notDone)).getD
            (if create then .fresh else .refuse .notFound) := by
  intro h
  have empty : Checkpoint.loadBytes ByteArray.empty = none := rfl
  have taken := h true (some ByteArray.empty)
  simp [empty] at taken

theorem checkpoint_metadata (pane : Import.Resurrect.Pane) (contents : Option String) :
    (Import.Resurrect.checkpoint pane contents).cwd = pane.dir ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.command" =
        some pane.details.command ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.saved-command" =
        some pane.details.savedCommand ∧
      (Import.Resurrect.checkpoint pane contents).fields.lookup "tmux.capture" =
        some (if contents.isSome then "saved" else "none") :=
  Import.Resurrect.checkpoint_metadata pane contents

theorem checkpoint_metadata_rejects_blank :
    ¬∀ (pane : Import.Resurrect.Pane) (contents : Option String),
        ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                  (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                pane contents).cwd =
            pane.dir ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).fields.lookup
              "tmux.command" =
            some pane.details.command ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).fields.lookup
              "tmux.saved-command" =
            some pane.details.savedCommand ∧
          ((fun (_ : Import.Resurrect.Pane) (_ : Option String) =>
                    (⟨Vt.Vt.init 1 1, "", []⟩ : Checkpoint.Ckpt Vt.Vt))
                  pane contents).fields.lookup
              "tmux.capture" =
            some (if contents.isSome then "saved" else "none") := by
  intro h
  exact absurd (h { name := "a", dir := "x", line := 0 } none).1 (by decide)

theorem older_record_described (c : Checkpoint.Ckpt Vt.Vt)
    (h :
      Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
        (Checkpoint.Decoded Checkpoint.loadBytes) c.vt)
    (undescribed : c.fields.lookup "description" = none) (old : ByteArray)
    (format3 :
      old.data.toList =
        [0x4C, 0x4E, 0x47, 0x52, 3] ++ (Checkpoint.saveBytes c).data.toList.drop 5) :
    Checkpoint.loadBytes old =
      some
        { c with
          vt := c.vt.quiesce, fields := c.fields ++ Checkpoint.importDescription c.fields } := by
  rw [Checkpoint.loadBytes_format3 c (Checkpoint.live_of_decoded h) old format3]
  simp [Checkpoint.readFields, undescribed]

theorem older_record_described_rejects_stored :
    ¬∀ (c : Checkpoint.Ckpt Vt.Vt),
        Vt.Live Vt.Vt.init Vt.Vt.feed Vt.Vt.resize Vt.Vt.quiesce
            (Checkpoint.Decoded
              (fun (b : ByteArray) =>
                (Checkpoint.loadBytes b).map fun (c : Checkpoint.Ckpt Vt.Vt) =>
                  (⟨c.vt, c.cwd, c.fields.filter (·.1 != "description")⟩ : Checkpoint.Ckpt Vt.Vt)))
            c.vt →
          c.fields.lookup "description" = none →
          ∀ (old : ByteArray),
            old.data.toList =
                [0x4C, 0x4E, 0x47, 0x52, 3] ++ (Checkpoint.saveBytes c).data.toList.drop 5 →
              (fun (b : ByteArray) =>
                    (Checkpoint.loadBytes b).map fun (c : Checkpoint.Ckpt Vt.Vt) =>
                      (⟨c.vt, c.cwd, c.fields.filter (·.1 != "description")⟩ :
                        Checkpoint.Ckpt Vt.Vt))
                  old =
                some
                  { c with
                    vt := c.vt.quiesce,
                    fields := c.fields ++ Checkpoint.importDescription c.fields } := by
  intro h
  -- a reader that drops the description an older record reads with
  have k :=
    h ⟨Vt.Vt.init 1 1, "", [("tmux.window-title", "w")]⟩ (.init 1 1) (by simp)
      ⟨([0x4C, 0x4E, 0x47, 0x52, 3] ++
            (Checkpoint.saveBytes
                  ⟨Vt.Vt.init 1 1, "", [("tmux.window-title", "w")]⟩).data.toList.drop
              5).toArray⟩
      (by simp)
  simp only [] at k
  rw [older_record_described ⟨Vt.Vt.init 1 1, "", [("tmux.window-title", "w")]⟩ (.init 1 1)
      (by simp) _ (by simp)] at k
  simp [Checkpoint.importDescription] at k

end Linger
