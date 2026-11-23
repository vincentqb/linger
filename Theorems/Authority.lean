module

public import Linger.Display.CoreCode.Listing
public import Linger.Display.CoreCode.Status
public import Linger.Selector.CoreCode.Picker
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Claim
public import Linger.Session.CoreCode.Names
public import Os.WorldSpec
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
public import Linger.Target.CoreCode.Name
public import Linger.Target.CoreSpec
public import Terminal.CoreCode.Mediation
public import Terminal.CoreCode.Render
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
public import Linger.Session.CoreCode.Start
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

/-! # Part 2 of `Challenge.lean`, authority and attribution: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem one_owner (grant : Claim.State → Nat → Nat → Bool) (exclusive : Claim.Exclusive grant)
    {s : Claim.State} (reached : Claim.Reachable grant Claim.enters s) {a b resource : Nat}
    {left right : Claim.Lease} (ha : s.active a = some left) (hb : s.active b = some right)
    (leftUses : left.Uses resource) (rightUses : right.Uses resource) : a = b :=
  Claim.at_most_one_owner exclusive reached ha hb leftUses rightUses

theorem one_owner_rejects_socket :
    ¬∀ (grant : Claim.State → Nat → Nat → Bool),
        Claim.Exclusive grant →
          ∀ {s : Claim.State},
            Claim.Reachable grant (fun (socket _ : Bool) => socket) s →
              ∀ {a b resource : Nat} {left right : Claim.Lease},
                s.active a = some left →
                  s.active b = some right → left.Uses resource → right.Uses resource → a = b := by
  intro h
  -- the operating system grants every free lock, and only a free one
  let grant : Claim.State → Nat → Nat → Bool := fun s _ resource => s.locks resource == none
  have exclusive : Claim.Exclusive grant := fun s _ resource granted => by
    simpa [grant] using granted
  -- process 1 takes socket 1 and acts on lease (1, 3); process 2 takes socket 2 and checkpoint 3
  let s1 : Claim.State := { Claim.initial with locks := Claim.put Claim.initial.locks 1 (some 1) }
  let s2 : Claim.State := { s1 with active := Claim.put s1.active 1 (some ⟨1, 3⟩) }
  let s3 : Claim.State := { s2 with locks := Claim.put s2.locks 2 (some 2) }
  let s4 : Claim.State := { s3 with locks := Claim.put s3.locks 3 (some 2) }
  let s5 : Claim.State := { s4 with active := Claim.put s4.active 2 (some ⟨2, 3⟩) }
  have reached : Claim.Reachable grant (fun (socket _ : Bool) => socket) s5 :=
    ((((Claim.Reachable.initial.next (.acquire _ 1 1 rfl)).next (.enter _ 1 ⟨1, 3⟩ rfl rfl)).next
              (.acquire _ 2 2 rfl)).next
          (.acquire _ 2 3 rfl)).next
      (.enter _ 2 ⟨2, 3⟩ rfl rfl)
  have same := @h grant exclusive s5 reached 1 2 3 ⟨1, 3⟩ ⟨2, 3⟩ rfl rfl (.inr rfl) (.inr rfl)
  exact absurd same (by decide)

theorem names_one_to_one (t : Names.Table) (wf : Names.Wf t) (a b id : String) :
    (Names.resolve t a = some id → Names.resolve t b = some id → a = b) ∧
      (Names.resolve t a = some id ↔ Names.nameOf t id = some a) ∧
      Names.resolve [] a = Name.check a :=
  ⟨Names.resolve_injective wf, Names.resolve_iff_nameOf wf a id, Names.resolve_nil a⟩

theorem names_one_to_one_rejects_stale :
    ¬∀ (t : Names.Table),
        Names.Wf t →
          ∀ (a b id : String),
            (Names.resolveStale t a = some id → Names.resolveStale t b = some id → a = b) ∧
              (Names.resolveStale t a = some id ↔ Names.nameOf t id = some a) ∧
              Names.resolveStale [] a = Name.check a := by
  intro h
  -- `x` renamed `y`: the stale resolution still reaches it by `x`
  have wf : Names.Wf [("y", "x")] := by simp [Names.Wf]
  have := (h [("y", "x")] wf "x" "y" "x").1 (by decide) (by decide)
  exact absurd this (by decide)

theorem rename_moves (t : Names.Table) (wf : Names.Wf t) (old new id : String)
    (found : Names.resolve t old = some id) (free : t.lookup new = none) (other : old ≠ new) :
    Names.Wf (Names.rename t old new id) ∧
      Names.resolve (Names.rename t old new id) new = some id ∧
      Names.resolve (Names.rename t old new id) old ≠ some id ∧
      ∀ n, n ≠ old → n ≠ new → Names.resolve (Names.rename t old new id) n = Names.resolve t n :=
  Names.rename_moves wf found free other

theorem rename_moves_rejects_reid :
    ¬∀ (t : Names.Table),
        Names.Wf t →
          ∀ (old new id : String),
            Names.resolve t old = some id →
              t.lookup new = none →
              old ≠ new →
              Names.Wf (Names.renameReid t old new id) ∧
                Names.resolve (Names.renameReid t old new id) new = some id ∧
                Names.resolve (Names.renameReid t old new id) old ≠ some id ∧
                ∀ n,
                  n ≠ old →
                    n ≠ new →
                    Names.resolve (Names.renameReid t old new id) n = Names.resolve t n := by
  intro h
  have valid : Name.check "a" = some "a" :=
    (Name.check_eq_some_iff "a" "a").mpr
      ⟨rfl, by
        unfold Name.Valid; decide⟩
  have found : Names.resolve [] "a" = some "a" := by rw [Names.resolve_nil, valid]
  have moved := (h [] (by simp [Names.Wf]) "a" "b" "a" found (by decide) (by decide)).2.1
  have : Names.resolve (Names.renameReid [] "a" "b" "a") "b" = some "b" := by
    simp [Names.renameReid, Names.resolve]
  rw [this] at moved
  exact absurd moved (by decide)

theorem claim_fresh (t : Names.Table) (wf : Names.Wf t) (name id : String)
    (unnamed : Names.resolve t name = none) (fresh : Names.Fresh id) (unused : id ∉ t.map (·.2)) :
    Names.Wf (Names.claim t name id) ∧
      Names.resolve (Names.claim t name id) name = some id ∧
      ∀ n, n ≠ name → Names.resolve (Names.claim t name id) n = Names.resolve t n :=
  Names.claim_fresh wf unnamed fresh unused

theorem claim_fresh_rejects_self :
    ¬∀ (t : Names.Table),
        Names.Wf t →
          ∀ (name id : String),
            Names.resolve t name = none →
              Names.Fresh id →
              id ∉ t.map (·.2) →
              Names.Wf (Names.claimSelf t name id) ∧
                Names.resolve (Names.claimSelf t name id) name = some id ∧
                ∀ n,
                  n ≠ name → Names.resolve (Names.claimSelf t name id) n = Names.resolve t n := by
  intro h
  -- `n` renamed `x`, so `n` leads nowhere; a start that took `n` for the ID would share it
  have unnamed : Names.resolve [("x", "n")] "n" = none := by simp [Names.resolve, List.lookup_cons]
  have fresh : Names.Fresh ".a" := ⟨['a'], rfl, by simp, by decide⟩
  have := (h [("x", "n")] (by simp [Names.Wf]) "n" ".a" unnamed fresh (by decide)).2.1
  simp [Names.claimSelf, Names.resolve] at this

theorem nameOf_shown (t : Names.Table) (id name : String) (shown : Names.nameOf t id = some name) :
    (name, id) ∈ t ∨ Name.check id = some name := Names.nameOf_shown t id name shown

theorem nameOf_shown_rejects_bare :
    ¬∀ (t : Names.Table) (id name : String),
        Names.nameOfBare t id = some name → (name, id) ∈ t ∨ Name.check id = some name := by
  intro h
  rcases h [] ".a" ".a" rfl with mem | checked
  · simp at mem
  · have := ((Name.check_eq_some_iff ".a" ".a").mp checked).2
    exact absurd this.2.2.2 (by decide)

theorem rename_plan (valid oldHeld older newHeld : Bool) :
    (Names.Rename.plan valid oldHeld older newHeld = .move ↔
        valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = false) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .invalid ↔ valid = false) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .missing ↔
        valid = true ∧ oldHeld = false) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .taken ↔
        valid = true ∧ oldHeld = true ∧ newHeld = true) ∧
      (Names.Rename.plan valid oldHeld older newHeld = .refuse .older ↔
        valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = true) := by
  rw [Names.rename_plan_eq]
  cases valid <;> cases oldHeld <;> cases older <;> cases newHeld <;> simp

theorem rename_plan_rejects_move :
    ¬∀ (valid oldHeld older newHeld : Bool),
        ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld = .move ↔
            valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = false) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .invalid ↔
            valid = false) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .missing ↔
            valid = true ∧ oldHeld = false) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .taken ↔
            valid = true ∧ oldHeld = true ∧ newHeld = true) ∧
          ((fun (_ _ _ _ : Bool) => Names.Rename.Plan.move) valid oldHeld older newHeld =
              .refuse .older ↔
            valid = true ∧ oldHeld = true ∧ newHeld = false ∧ older = true) := by
  intro h
  cases ((h false true false false).1.mp rfl).1

theorem one_name
    (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat))
    (noReplace : Os.Place.NoReplace placed) (first second : Names.Op) (names : String → Option Nat)
    (src src' dst : String) (file : Nat) (named : names src = some file)
    {after : String → Option Nat}
    (placedFirst : (Names.call first).run placed names src dst = some after) :
    after dst = some file ∧ (Names.call second).run placed after src' dst = none :=
  Names.call_second_fails noReplace first second named placedFirst

theorem one_name_rejects_replace :
    ¬∀ (placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat)),
        Os.Place.NoReplace placed →
          ∀ (first second : Names.Op) (names : String → Option Nat) (src src' dst : String)
            (file : Nat),
            names src = some file →
              ∀ {after : String → Option Nat},
                ((fun (_ : Names.Op) => Names.Call.replace) first).run placed names src dst =
                    some after →
                  after dst = some file ∧
                    ((fun (_ : Names.Op) => Names.Call.replace) second).run placed after src' dst =
                      none := by
  intro h
  -- an operating system that places a name only where none is
  let placed : Bool → (String → Option Nat) → String → String → Option (String → Option Nat) :=
    fun rename names src dst =>
    if (names dst).isSome ∨ src = dst then none
    else
      some fun p =>
        if p = dst then names src
        else if p = src then (if rename then none else names src) else names p
  have noReplace : Os.Place.NoReplace placed := by
    intro rename names src dst
    refine ⟨fun taken => by simp [placed, taken], fun after placedOk => ?_⟩
    simp only [placed] at placedOk
    split at placedOk
    · cases placedOk
    · rename_i free
      cases placedOk
      have ne : src ≠ dst := fun e => free (Or.inr e)
      refine ⟨ne, by simp, by simp [ne], fun other h1 h2 => by simp [h1, h2]⟩
  have :=
    (@h placed noReplace .create .create (fun p => if p = "s" then some 0 else none) "s" "s" "d" 0
        (by simp)
        (fun p =>
          if p = "d" then (if "s" = "s" then some 0 else none)
          else if p = "s" then none else (if p = "s" then some 0 else none))
        rfl).2
  simp [Names.Call.run] at this

theorem step_fields_kept (s : State) (ev : Event) :
    (Session.step s ev).1.fieldList = s.fieldList := Session.step_fields_kept s ev

theorem step_fields_kept_rejects_reset :
    ¬∀ (s : State) (ev : Event),
        ((fun (s : State) (_ : Event) =>
                (State.boot s.terminal [] [], ([] : List (Effect Replay.Plan))))
              s ev).1.fieldList =
          s.fieldList := by
  intro h
  obtain ⟨-, -, -, -, labelled, -⟩ :=
    Session.boot_observed (Vt.Vt.init 1 1) [("description", "b")] []
  obtain ⟨-, -, -, -, emptied, -⟩ :=
    Session.boot_observed (State.boot (Vt.Vt.init 1 1) [("description", "b")] []).terminal [] []
  have kept := h (State.boot (Vt.Vt.init 1 1) [("description", "b")] []) (.tick 0)
  simp only at kept
  rw [emptied, labelled] at kept
  simp [maxFields, recordField] at kept

theorem infoFields_boot (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event) :
    ∃ rest,
      Session.infoFields (Session.trace Session.step (State.boot vt fields metadata) evs).1 =
        metadata ++ rest := by
  rw [Session.trace_step]
  exact Session.run_boot_infoFields vt fields metadata evs

theorem infoFields_boot_rejects_reboot :
    ¬∀ (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event),
        ∃ rest,
          Session.infoFields
              (Session.trace
                  (fun (_ : State) (_ : Event) =>
                    (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  (State.boot vt fields metadata) evs).1 =
            metadata ++ rest := by
  intro h
  obtain ⟨rest, named⟩ := h (Vt.Vt.init 1 1) [] [("name", "a")] [.tick 0]
  obtain ⟨tail, counted⟩ := Session.infoFields_metaKv (State.boot (Vt.Vt.init 1 1) [] [])
  have booted :
    (Session.trace
          (fun (_ : State) (_ : Event) =>
            (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
          (State.boot (Vt.Vt.init 1 1) [] [("name", "a")]) [.tick 0]).1 =
      State.boot (Vt.Vt.init 1 1) [] [] :=
    rfl
  rw [booted, counted, Session.boot_metaKv] at named
  simp at named

theorem step_terminal_sources (s : State) (ev : Event) :
    (∃ chunk, ev = .ptyOut chunk ∧ (Session.step s ev).1.terminal = s.terminal.feed chunk) ∨
      ∃ sizes : List (Nat × Nat),
        (Session.step s ev).1.terminal =
          sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal :=
  Session.step_vt_sources s ev

theorem step_terminal_sources_rejects_print :
    ¬∀ (s : State) (ev : Event),
        (∃ chunk,
            ev = .ptyOut chunk ∧
              ((fun (s : State) (_ : Event) =>
                      (State.boot (s.terminal.feed [0x41]) [] [], ([] : List (Effect Replay.Plan))))
                    s ev).1.terminal =
                s.terminal.feed chunk) ∨
          ∃ sizes : List (Nat × Nat),
            ((fun (s : State) (_ : Event) =>
                    (State.boot (s.terminal.feed [0x41]) [] [], ([] : List (Effect Replay.Plan))))
                  s ev).1.terminal =
              sizes.foldl (fun v (size : Nat × Nat) => v.resize size.1 size.2) s.terminal := by
  intro h
  obtain ⟨-, -, kept, -, -, -⟩ := Session.boot_observed (Vt.Vt.init 2 1) [] []
  obtain ⟨-, -, printed, -, -, -⟩ :=
    Session.boot_observed ((State.boot (Vt.Vt.init 2 1) [] []).terminal.feed [0x41]) [] []
  rcases h (State.boot (Vt.Vt.init 2 1) [] []) (.tick 0) with ⟨_, ticked, -⟩ | ⟨sizes, resized⟩
  · cases ticked
  · change
      (State.boot ((State.boot (Vt.Vt.init 2 1) [] []).terminal.feed [0x41]) [] []).terminal =
        _ at resized
    rw [printed, kept] at resized
    have moved : ((Vt.Vt.init 2 1).feed [0x41]).cursorPos = (1, 0) := by decide +kernel
    rw [resized, Session.foldl_resize_origin _ (by decide +kernel)] at moved
    simp at moved

theorem step_owned (s : State) (ev : Event) :
    (∀ chunk,
        ev = .ptyOut chunk →
          (Session.step s ev).1.owned =
            s.owned.hear (Mediation.feed s.terminal s.scanner chunk).vt.windowTitle
              (Mediation.feed s.terminal s.scanner chunk).asks
              (Mediation.feed s.terminal s.scanner chunk).notice
              (Mediation.feed s.terminal s.scanner chunk).progress
              (Mediation.feed s.terminal s.scanner chunk).marks (seenBy s.roster)) ∧
      (∀ o, ev = .observed o → (Session.step s ev).1.owned = s.owned.observe o) ∧
      (∀ d, ev = .notified d → (Session.step s ev).1.owned = s.owned.notify d) ∧
      (∀ id chunk,
        ev = .bytes id chunk →
          (Session.step s ev).1.owned = s.owned ∨
            (Session.step s ev).1.owned = s.owned.look ∧
              ∃ c, s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks) ∧
      (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
        ev = .bytes id chunk →
          s.client? id = some c →
          c.attached = false →
          c.decoder.feed chunk = (dec, [m]) →
          dec.errored = false → m.Looks → (Session.step s ev).1.owned = s.owned.look) ∧
      ((∀ chunk, ev ≠ .ptyOut chunk) →
        (∀ o, ev ≠ .observed o) →
        (∀ id chunk, ev ≠ .bytes id chunk) →
        (∀ d, ev ≠ .notified d) → (Session.step s ev).1.owned = s.owned) ∧
      ((Status.classify
              { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                asks := s.seen.asks }).attention =
          .asked ↔
        s.owned.asks = true) :=
  ⟨fun chunk hev => by
    subst hev
    exact Session.step_ptyOut_owned s chunk, fun o hev => by
    subst hev
    exact Session.step_observed_owned s o, fun d hev => by
    subst hev
    exact Session.step_notified_owned s d, fun id chunk hev => by
    subst hev
    exact Session.step_bytes_owned s id chunk,
    fun id chunk c dec m hev hc fresh read healthy looks => by
    subst hev
    exact Session.step_look_owned s id chunk hc fresh read healthy looks, fun out seen read heard =>
    Session.step_owned_kept s ev out seen read heard, Status.classify_running_asks _ _ _ _⟩

theorem step_owned_rejects_rung :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.hear (Mediation.feed s.terminal s.scanner chunk).vt.windowTitle
                  (Mediation.feed s.terminal s.scanner chunk).asks
                  (Mediation.feed s.terminal s.scanner chunk).notice
                  (Mediation.feed s.terminal s.scanner chunk).progress
                  (Mediation.feed s.terminal s.scanner chunk).marks (seenBy s.roster)) ∧
          (∀ o,
            ev = .observed o →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.observe o) ∧
          (∀ d,
            ev = .notified d →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.notify d) ∧
          (∀ id chunk,
            ev = .bytes id chunk →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                  s.owned ∨
                ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                    s.owned.look ∧
                  ∃ c, s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks) ∧
          (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
            ev = .bytes id chunk →
              s.client? id = some c →
              c.attached = false →
              c.decoder.feed chunk = (dec, [m]) →
              dec.errored = false →
              m.Looks →
              ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
                s.owned.look) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (∀ o, ev ≠ .observed o) →
            (∀ id chunk, ev ≠ .bytes id chunk) →
            (∀ d, ev ≠ .notified d) →
            ((fun (s : State) (_ : Event) => Session.step s (.ptyOut [0x07])) s ev).1.owned =
              s.owned) ∧
          ((Status.classify
                  { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                    asks := s.seen.asks }).attention =
              .asked ↔
            s.owned.asks = true) := by
  -- a session that rings the bell on a client's read asks, with no output and no look
  intro h
  rcases (h (State.boot (Vt.Vt.init 80 24) [] []) (.bytes 0 [])).2.2.2.1 0 [] rfl with kept |
    ⟨-, c, hc, -⟩
  · have := congrArg Owned.asks kept
    simp only at this
    rw [Session.rung_asks] at this
    cases this
  · cases hc

theorem step_owned_rejects_lumped :
    ¬∀ (s : State) (ev : Event),
        (∀ chunk,
            ev = .ptyOut chunk →
              (Session.step s ev).1.owned =
                s.owned.hear (Mediation.feed s.terminal s.scanner chunk).vt.windowTitle
                  (Mediation.feed s.terminal s.scanner chunk).asks
                  (Mediation.feed s.terminal s.scanner chunk).notice
                  (Mediation.feed s.terminal s.scanner chunk).progress
                  (Mediation.feed s.terminal s.scanner chunk).marks (seenBy s.roster)) ∧
          (∀ o, ev = .observed o → (Session.step s ev).1.owned = s.owned.observe o) ∧
          (∀ d, ev = .notified d → (Session.step s ev).1.owned = s.owned.notify d) ∧
          (∀ id chunk,
            ev = .bytes id chunk →
              (Session.step s ev).1.owned = s.owned ∨
                (Session.step s ev).1.owned = s.owned.look ∧
                  ∃ c, s.client? id = some c ∧ ∃ m ∈ (c.decoder.feed chunk).2, m.Looks) ∧
          (∀ (id : Nat) (chunk : List UInt8) (c : Client) (dec : Wire.Decoder) (m : Wire.Msg),
            ev = .bytes id chunk →
              s.client? id = some c →
              c.attached = false →
              c.decoder.feed chunk = (dec, [m]) →
              dec.errored = false → m.Looks → (Session.step s ev).1.owned = s.owned.look) ∧
          ((∀ chunk, ev ≠ .ptyOut chunk) →
            (∀ o, ev ≠ .observed o) →
            (∀ id chunk, ev ≠ .bytes id chunk) →
            (∀ d, ev ≠ .notified d) → (Session.step s ev).1.owned = s.owned) ∧
          ((Status.lumped Status.classify
                  { progress := s.seen.progress, running := s.seen.running, unseen := s.seen.unseen,
                    asks := s.seen.asks }).attention =
              .asked ↔
            s.owned.asks = true) := by
  -- today's rule lists a session whose program rang the bell by its output, never as asking
  intro h
  have heard :=
    ((h (Session.step (State.boot (Vt.Vt.init 80 24) [] []) (.ptyOut [0x07])).1
            (.tick 0)).2.2.2.2.2.2).mpr
      Session.rung_asks
  have never : ∀ o : Status.Obs, (Status.lumped Status.classify o).attention ≠ .asked :=
    fun o hasks => by
    unfold Status.lumped at hasks
    simp [Status.classify, Status.attentionOf] at hasks
    split at hasks <;> simp at hasks
  exact never _ heard

theorem notify_exact (received : Nat → List (List UInt8) → List (List UInt8))
    (whole : Os.Dgram.Whole received) (vt : Vt.Vt) (fields metadata : List (String × String))
    (evs : List Event) (sent : List (List UInt8)) (fits : ∀ d ∈ sent, d.length ≤ Notify.cap)
    (heard : Notify.heard evs = received Notify.cap sent) :
    (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned.ready =
        Notify.ready sent ∧
      (Session.trace Session.step (State.boot vt fields metadata) evs).1.owned.status =
        Notify.status sent := by
  have sent' : Notify.heard evs = sent := heard.trans (whole _ _ fits)
  obtain ⟨ready, status⟩ := Session.trace_notified (State.boot vt fields metadata) evs
  rw [ready, status, sent']
  exact ⟨rfl, Option.or_none⟩

theorem notify_exact_rejects_output :
    ¬∀ (received : Nat → List (List UInt8) → List (List UInt8)),
        Os.Dgram.Whole received →
          ∀ (vt : Vt.Vt) (fields metadata : List (String × String)) (evs : List Event)
            (sent : List (List UInt8)),
            (∀ d ∈ sent, d.length ≤ Notify.cap) →
              Notify.heard evs = received Notify.cap sent →
              (Session.trace (Session.outputNotifies Session.step) (State.boot vt fields metadata)
                      evs).1.owned.ready =
                  Notify.ready sent ∧
                (Session.trace (Session.outputNotifies Session.step) (State.boot vt fields metadata)
                      evs).1.owned.status =
                  Notify.status sent := by
  -- a session that reads its program's output as notifications is ready once it prints `READY=1`
  intro h
  have :=
    (h (fun _ sent => sent) (fun _ _ _ => rfl) (Vt.Vt.init 1 1) [] []
        [.ptyOut [0x52, 0x45, 0x41, 0x44, 0x59, 0x3D, 0x31]] [] (by simp) rfl).1
  rw [Session.outputNotifies_ready] at this
  cases this

theorem start_plan (live saved : Bool) :
    (Start.plan live saved = .take ↔ live = false ∧ saved = false) ∧
      (Start.plan live saved = .running ↔ live = true) ∧
      (Start.plan live saved = .saved ↔ live = false ∧ saved = true) := by
  rw [Start.plan_eq]
  cases live <;> cases saved <;> decide

theorem start_plan_rejects_take :
    ¬∀ (live saved : Bool),
        ((fun (_ _ : Bool) => Start.Plan.take) live saved = .take ↔ live = false ∧ saved = false) ∧
          ((fun (_ _ : Bool) => Start.Plan.take) live saved = .running ↔ live = true) ∧
          ((fun (_ _ : Bool) => Start.Plan.take) live saved = .saved ↔
            live = false ∧ saved = true) := by
  intro h
  cases ((h true false).1.mp rfl).1

theorem run_bytes_isolates (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat}
    (h : other ≠ id) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.client? other =
      s.client? other := by
  rw [Session.trace_step]
  exact Session.run_bytes_isolates s id chunks h

theorem run_bytes_isolates_rejects_reset :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {other : Nat},
        other ≠ id →
          (Session.trace
                  (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
                  s (chunks.map (Event.bytes id))).1.client?
              other =
            s.client? other := by
  intro h
  obtain ⟨joined, empty⟩ := Session.connected_client_witness
  have forgot :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 0 [[]] 1
      (by decide)
  have reset :
    (Session.trace
          (fun _ _ => (State.boot (Vt.Vt.init 1 1) [] [], ([] : List (Effect Replay.Plan))))
          (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1
          ([[]].map (Event.bytes 0))).1 =
      State.boot (Vt.Vt.init 1 1) [] [] :=
    rfl
  rw [reset, empty, joined] at forgot
  cases forgot

theorem run_readonly (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client}
    (hc : s.client? id = some c) (attached : c.attached = true) (watcher : c.mode = .readOnly) :
    (Session.trace Session.step s (chunks.map (Event.bytes id))).1.terminal = s.terminal ∧
      (Session.trace Session.step s (chunks.map (Event.bytes id))).1.fieldList = s.fieldList ∧
      ∀ eff ∈ (Session.trace Session.step s (chunks.map (Event.bytes id))).2,
        (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  rw [Session.trace_step]
  exact Session.run_readonly s id chunks hc attached watcher

theorem run_readonly_rejects_kill :
    ¬∀ (s : State) (id : Nat) (chunks : List (List UInt8)) {c : Client},
        (fun (_ : State) (i : Nat) =>
                some ({ id := i, attached := true, mode := .readOnly } : Client))
              s id =
            some c →
          c.attached = true →
          c.mode = .readOnly →
          (Session.trace (fun s _ => (s, ([.stopProgram] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.terminal =
              s.terminal ∧
            (Session.trace (fun s _ => (s, ([.stopProgram] : List (Effect Replay.Plan)))) s
                  (chunks.map (Event.bytes id))).1.fieldList =
              s.fieldList ∧
            ∀
              eff ∈
                (Session.trace (fun s _ => (s, ([.stopProgram] : List (Effect Replay.Plan)))) s
                    (chunks.map (Event.bytes id))).2,
              (∃ m, eff = .send id m) ∨ eff = .close id ∨ eff = .checkpoint := by
  intro h
  obtain ⟨-, -, effects⟩ :=
    @h (State.boot (Vt.Vt.init 1 1) [] []) 0 [[]] { id := 0, attached := true, mode := .readOnly }
      rfl rfl rfl
  rcases effects .stopProgram (by simp [Session.trace]) with ⟨_, sent⟩ | closed | saved
  · cases sent
  · cases closed
  · cases saved

theorem step_attach_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {mode : Mode} {cols rows : UInt32} (hc : s.client? id = some c)
    (fresh : c.attached = false) (read : c.decoder.feed chunk = (dec, [.attach mode cols rows]))
    (healthy : dec.errored = false) :
    ∃ c',
      (Session.step s (.bytes id chunk)).1.client? id = some c' ∧
        c'.attached = true ∧ c'.mode = mode :=
  Session.step_attach_mode s id chunk hc fresh read healthy

theorem step_attach_mode_rejects_unsized :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder} {mode : Mode}
        {cols rows : UInt32},
        (fun (s : State) (i : Nat) =>
                (s.client? i).map fun c =>
                  { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
              s id =
            some c →
          c.attached = false →
          c.decoder.feed chunk = (dec, [.attach mode cols rows]) →
          dec.errored = false →
          ∃ c',
            (fun (s : State) (i : Nat) =>
                    (s.client? i).map fun c =>
                      { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
                  (Session.step s (.bytes id chunk)).1 id =
                some c' ∧
              c'.attached = true ∧ c'.mode = mode := by
  intro h
  -- a writable attach from a terminal with no size: today's rule would make it read-only
  obtain ⟨joined, -⟩ := Session.connected_client_witness
  obtain ⟨c', seen, -, writable⟩ :=
    @h (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] []) [.connected 1]).1 1
      (Wire.encode (.attach .writable 0 0)) { id := 1 } {} .writable 0 0 (by simp [joined]) rfl
      (Session.feed_encode_fresh (.attach .writable 0 0) trivial) rfl
  dsimp only at seen
  rw [Session.step_attach_record joined rfl (Session.feed_encode_fresh _ trivial) rfl] at seen
  simp only [Option.map_some, Option.some.injEq] at seen
  rw [← seen] at writable
  simp at writable

theorem step_resize_mode (s : State) (id : Nat) (chunk : List UInt8) {c : Client}
    {dec : Wire.Decoder} {sizes : List (UInt32 × UInt32)} (hc : s.client? id = some c)
    (read : c.decoder.feed chunk = (dec, sizes.map fun size => .resize size.1 size.2))
    (healthy : dec.errored = false) :
    ((Session.step s (.bytes id chunk)).1.client? id).map (·.mode) = some c.mode :=
  Session.step_resize_mode s id chunk hc read healthy

theorem step_resize_mode_rejects_unsized :
    ¬∀ (s : State) (id : Nat) (chunk : List UInt8) {c : Client} {dec : Wire.Decoder}
        {sizes : List (UInt32 × UInt32)},
        (fun (s : State) (i : Nat) =>
                (s.client? i).map fun c =>
                  { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
              s id =
            some c →
          c.decoder.feed chunk = (dec, sizes.map fun size => .resize size.1 size.2) →
          dec.errored = false →
          ((fun (s : State) (i : Nat) =>
                    (s.client? i).map fun c =>
                      { c with mode := if c.cols = 0 ∨ c.rows = 0 then .readOnly else c.mode })
                  (Session.step s (.bytes id chunk)).1 id).map
              (·.mode) =
            some c.mode := by
  intro h
  -- a writable client at 80×24 whose terminal loses its size: today's rule would drop its typing
  have joined := Session.attached_client_witness
  have kept :=
    @h
      (Session.trace Session.step (State.boot (Vt.Vt.init 1 1) [] [])
          [.connected 1, .bytes 1 (Wire.encode (.attach .writable 80 24))]).1
      1 (Wire.encode (.resize 0 0)) { id := 1, attached := true, cols := 80, rows := 24 } {}
      [(0, 0)] (by simp [joined]) (Session.feed_encode_fresh (.resize 0 0) trivial) rfl
  dsimp only at kept
  rw [Session.step_resize_record joined rfl (Session.feed_encode_fresh (.resize 0 0) trivial)
      rfl] at kept
  simp at kept

theorem step_resizes_sized (s : State) (ev : Event) (cols rows : UInt32)
    (resized : Effect.resizePty cols rows ∈ (Session.step s ev).2) :
    0 < cols ∧
      0 < rows ∧
      ∃ id chunk c,
        ev = .bytes id chunk ∧
          s.client? id = some c ∧
          ∃ m ∈ (c.decoder.feed chunk).2,
            ∃ mode width height,
              (m = .attach mode width height ∨ m = .resize width height) ∧
                width ≠ 0 ∧
                height ≠ 0 ∧
                cols.toNat = Vt.clampDim width.toNat ∧ rows.toNat = Vt.clampDim height.toNat :=
  Session.step_resizes_sized s ev cols rows resized

theorem step_resizes_sized_rejects_zero :
    ¬∀ (s : State) (ev : Event) (cols rows : UInt32),
        Effect.resizePty cols rows ∈
            ((fun (s : State) (_ : Event) => (s, ([.resizePty 0 0] : List (Effect Replay.Plan)))) s
                ev).2 →
          0 < cols ∧
            0 < rows ∧
            ∃ id chunk c,
              ev = .bytes id chunk ∧
                s.client? id = some c ∧
                ∃ m ∈ (c.decoder.feed chunk).2,
                  ∃ mode width height,
                    (m = .attach mode width height ∨ m = .resize width height) ∧
                      width ≠ 0 ∧
                      height ≠ 0 ∧
                      cols.toNat = Vt.clampDim width.toNat ∧
                      rows.toNat = Vt.clampDim height.toNat := by
  intro h
  have zero := h (State.boot (Vt.Vt.init 1 1) [] []) (.tick 0) 0 0 (by simp)
  exact absurd zero.1 (by decide)

theorem rowFields_name (socketName : String) (info : List (String × String)) :
    (Listing.rowFields socketName info).lookup "name" = some socketName :=
  Listing.rowFields_name socketName info

theorem rowFields_name_rejects_reply :
    ¬∀ (socketName : String) (info : List (String × String)),
        ((fun (_ : String) (info : List (String × String)) => info) socketName info).lookup "name" =
          some socketName := by
  intro h
  exact absurd (h "s" []) (by simp)

theorem rowText_sources (width : Option Nat) (layout : Listing.Layout)
    (info info' : List (String × String))
    (h : ∀ key ∈ Listing.sources, info.lookup key = info'.lookup key) :
    Listing.rowText width layout info = Listing.rowText width layout info' :=
  Listing.rowText_sources width layout info info' h

theorem rowText_sources_rejects_every_field :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info info' : List (String × String)),
        (∀ key ∈ Listing.sources, info.lookup key = info'.lookup key) →
          (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                info.flatMap fun kv => kv.2.toList)
              width layout info =
            (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                info.flatMap fun kv => kv.2.toList)
              width layout info' := by
  intro h
  have := h none {} [("label.k", "a")] [("label.k", "b")] (by simp [Listing.sources, List.lookup])
  simp at this

theorem caption_precedence (info : List (String × String)) :
    ((info.lookup "title").getD "" ≠ "" → Listing.caption info = (info.lookup "title").getD "") ∧
      ((info.lookup "title").getD "" = "" →
        (info.lookup "status_text").getD "" ≠ "" →
        Listing.caption info = (info.lookup "status_text").getD "") ∧
      ((info.lookup "title").getD "" = "" →
        (info.lookup "status_text").getD "" = "" →
        Listing.caption info = (info.lookup "description").getD "") ∧
      (Listing.program info = "" ∨
        ¬(Listing.command (Listing.program info)).toList <:+: (Listing.caption info).toList) :=
  Listing.caption_precedence info

theorem caption_precedence_rejects_described :
    ¬∀ (info : List (String × String)),
        ((info.lookup "title").getD "" ≠ "" →
            (fun (info : List (String × String)) => (info.lookup "description").getD "") info =
              (info.lookup "title").getD "") ∧
          ((info.lookup "title").getD "" = "" →
            (info.lookup "status_text").getD "" ≠ "" →
            (fun (info : List (String × String)) => (info.lookup "description").getD "") info =
              (info.lookup "status_text").getD "") ∧
          ((info.lookup "title").getD "" = "" →
            (info.lookup "status_text").getD "" = "" →
            (fun (info : List (String × String)) => (info.lookup "description").getD "") info =
              (info.lookup "description").getD "") ∧
          (Listing.program info = "" ∨
            ¬(Listing.command (Listing.program info)).toList <:+:
                ((fun (info : List (String × String)) => (info.lookup "description").getD "")
                    info).toList) := by
  intro h
  have := (h [("description", "d"), ("title", "t")]).1 (by simp [List.lookup])
  simp [List.lookup] at this

theorem info_foreground (reported seen : UInt32 → Option Foreground)
    (foreground : Pty.Foreground reported seen) (s : State) (master : UInt32) (o : Observation)
    (read : o.foreground = reported master) {fg : Foreground} (found : reported master = some fg) :
    ∃ process,
      seen master = some process ∧
        ("fg", String.intercalate " " process.argv) ∈
          Session.infoFields (Session.step s (.observed o)).1 ∧
        ("fgpid", toString process.pid) ∈ Session.infoFields (Session.step s (.observed o)).1 ∧
        ("fgdir", process.dir) ∈ Session.infoFields (Session.step s (.observed o)).1 := by
  rw [found] at read
  exact ⟨fg, foreground master fg found, Session.infoFields_foreground s o read⟩

theorem info_foreground_rejects_unreported :
    ¬∀ (reported seen : UInt32 → Option Foreground),
        Pty.Foreground reported seen →
          ∀ (s : State) (master : UInt32) (o : Observation),
            o.foreground = reported master →
              ∀ {fg : Foreground},
                reported master = some fg →
                  ∃ process,
                    seen master = some process ∧
                      ("fg", String.intercalate " " process.argv) ∈
                        (fun (_ : State) => ([] : List (String × String)))
                          (Session.step s (.observed o)).1 ∧
                      ("fgpid", toString process.pid) ∈
                        (fun (_ : State) => ([] : List (String × String)))
                          (Session.step s (.observed o)).1 ∧
                      ("fgdir", process.dir) ∈
                        (fun (_ : State) => ([] : List (String × String)))
                          (Session.step s (.observed o)).1 := by
  intro h
  -- a report that leaves the foreground out
  have shell : Foreground := ⟨1, ["sh"], "/"⟩
  obtain ⟨_, -, missing, -⟩ :=
    h (fun _ => some shell) (fun _ => some shell) (fun _ _ found => found)
      (State.boot (Vt.Vt.init 1 1) [] []) 0
      { nowMs := 0, wallS := 0, login := false, foreground := some shell } rfl rfl
  simp at missing

theorem info_echo (reported set : UInt32 → Option Bool) (echo : Pty.Echo reported set) (s : State)
    (master : UInt32) (o : Observation) (read : o.echo = reported master) {on : Bool}
    (found : reported master = some on) :
    set master = some on ∧
      ("echo", toString on) ∈ Session.infoFields (Session.step s (.observed o)).1 := by
  rw [found] at read
  exact ⟨echo master on found, Session.infoFields_echo s o read⟩

theorem info_echo_rejects_unreported :
    ¬∀ (reported set : UInt32 → Option Bool),
        Pty.Echo reported set →
          ∀ (s : State) (master : UInt32) (o : Observation),
            o.echo = reported master →
              ∀ {on : Bool},
                reported master = some on →
                  set master = some on ∧
                    ("echo", toString on) ∈
                      (fun (_ : State) => ([] : List (String × String)))
                        (Session.step s (.observed o)).1 := by
  intro h
  -- a report that leaves the echo out
  obtain ⟨-, missing⟩ :=
    h (fun _ => some true) (fun _ => some true) (fun _ _ found => found)
      (State.boot (Vt.Vt.init 1 1) [] []) 0
      { nowMs := 0, wallS := 0, login := false, foreground := none, echo := some true } rfl rfl
  simp at missing

theorem rowText_fits (width : Option Nat) (layout : Listing.Layout)
    (info : List (String × String)) :
    (Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
          ' ' ::
          Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
          ' ' :: ((info.lookup "name").getD "").toList.map Terminal.Render.textChar <+:
        Listing.rowText width layout info) ∧
      ∀ w,
        width = some w →
          ((Listing.rowText width layout info).map Terminal.Vt.charWidth).sum ≤
            max w (4 + (((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum) := by
  refine ⟨Listing.rowText_head width layout info, fun w hw => ?_⟩
  subst hw
  exact Listing.rowText_width w layout info

theorem rowText_fits_rejects_overflow :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info : List (String × String)),
        (Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
              ' ' ::
              Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
              ' ' :: ((info.lookup "name").getD "").toList.map Terminal.Render.textChar <+:
            (fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                Status.mark (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
                  ' ' ::
                  Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
                  ' ' ::
                  (((info.lookup "name").getD "").toList.map Terminal.Render.textChar ++
                    ['…', '…', '…']))
              width layout info) ∧
          ∀ w,
            width = some w →
              (((fun (_ : Option Nat) (_ : Listing.Layout) (info : List (String × String)) =>
                          Status.mark
                              (Status.ofAttentionName ((info.lookup "attention").getD "")) ::
                            ' ' ::
                            Status.icon (Status.ofName ((info.lookup "status").getD "")) ::
                            ' ' ::
                            (((info.lookup "name").getD "").toList.map Terminal.Render.textChar ++
                              ['…', '…', '…']))
                        width layout info).map
                    Terminal.Vt.charWidth).sum ≤
                max w
                  (4 + (((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum) := by
  intro h
  have := (h (some 0) {} []).2 0 rfl
  exact absurd this (by decide)

theorem rowText_clean (width : Option Nat) (layout : Listing.Layout)
    (info : List (String × String)) :
    ∀ c ∈ Listing.rowText width layout info, Display.Printable c :=
  Listing.rowText_printable width layout info

theorem rowText_clean_rejects_escape :
    ¬∀ (width : Option Nat) (layout : Listing.Layout) (info : List (String × String)),
        ∀
          c ∈
            (fun (_ : Option Nat) (_ : Listing.Layout) (_ : List (String × String)) => ['\x1b'])
              width layout info,
          Display.Printable c := by
  intro h
  have := h none {} [] '\x1b' (by simp)
  simp [Display.Printable] at this

theorem columns_aligned (layout : Listing.Layout) (info : List (String × String)) :
    (∃ blanks : List Char,
        (∀ c ∈ blanks, c = ' ') ∧
          (Listing.columns layout info).flatten = Listing.rowText none layout info ++ blanks) ∧
      ((((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum ≤ layout.nameCol →
        (Listing.columns layout info).map (fun part => (part.map Terminal.Vt.charWidth).sum) =
          layout.spans) := Listing.columns_aligned layout info

theorem columns_aligned_rejects_join :
    ¬∀ (layout : Listing.Layout) (info : List (String × String)),
        (∃ blanks : List Char,
            (∀ c ∈ blanks, c = ' ') ∧
              ((fun (_ : Listing.Layout) (info : List (String × String)) =>
                      [(String.intercalate " " (info.map (·.2))).toList])
                    layout info).flatten =
                Listing.rowText none layout info ++ blanks) ∧
          ((((info.lookup "name").getD "").toList.map Terminal.Vt.charWidth).sum ≤ layout.nameCol →
            ((fun (_ : Listing.Layout) (info : List (String × String)) =>
                      [(String.intercalate " " (info.map (·.2))).toList])
                    layout info).map
                (fun part => (part.map Terminal.Vt.charWidth).sum) =
              layout.spans) := by
  intro h
  have := (h {} []).2 (by decide)
  simp [Listing.Layout.spans] at this

theorem cells_sources (i : Nat) (info info' : List (String × String))
    (h : ∀ key ∈ Listing.cellSources.getD i [], info.lookup key = info'.lookup key) :
    (Listing.cells info)[i]? = (Listing.cells info')[i]? := Listing.cells_sources i info info' h

theorem cells_sources_rejects_all :
    ¬∀ (i : Nat) (info info' : List (String × String)),
        (∀ key ∈ Listing.cellSources.getD i [], info.lookup key = info'.lookup key) →
          ((fun (info : List (String × String)) => [String.join (info.map (·.2))]) info)[i]? =
            ((fun (info : List (String × String)) => [String.join (info.map (·.2))])
                info')[i]? := by
  intro h
  have := h 0 [("x", "a")] [] (by decide)
  simp at this

theorem picker_attach_listed (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .attach target) : target ∈ s.candidates :=
  (Selector.Picker.step_attach_mem s key target h).1

theorem picker_attach_listed_rejects_fixed :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.attach "s") s
              key =
            .attach target →
          target ∈ s.candidates := by
  intro h
  exact absurd (h { candidates := [] } .accept "s" rfl) (by simp)

theorem picker_create_new (s : Selector.Picker.State) (key : Selector.Key) (target : String)
    (h : Selector.Picker.step s key = .create target) :
    target ∉ s.candidates ∧ target ≠ "" ∧ Name.Accepted ((target.splitOn "@").headD "") := by
  obtain ⟨-, absent, nonempty, valid, -⟩ := Selector.Picker.step_create_valid s key target h
  exact ⟨absent, nonempty, valid⟩

theorem picker_create_new_rejects_empty :
    ¬∀ (s : Selector.Picker.State) (key : Selector.Key) (target : String),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.create "") s
              key =
            .create target →
          target ∉ s.candidates ∧ target ≠ "" ∧ Name.Accepted ((target.splitOn "@").headD "") := by
  intro h
  exact absurd (h { candidates := [] } .accept "" rfl).2.1 (by simp)

theorem relist_keeps_rows (s : Selector.Picker.State) (resort : Bool) (ordered : List String)
    (descriptions : List (String × String)) :
    (Selector.Picker.relist s resort ordered descriptions).candidates =
        (if resort then ordered
        else
          s.candidates.filter (fun t => ordered.contains t) ++
            ordered.filter fun t => !s.candidates.contains t) ∧
      (Selector.Picker.relist s resort ordered descriptions).query = s.query ∧
      (Selector.Picker.relist s resort ordered descriptions).descriptions = descriptions :=
  Selector.Picker.relist_rows s resort ordered descriptions

theorem relist_keeps_rows_rejects_resort :
    ¬∀ (s : Selector.Picker.State) (resort : Bool) (ordered : List String)
        (descriptions : List (String × String)),
        ((fun (s : Selector.Picker.State) (_ : Bool) (ordered : List String)
                    (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions })
                s resort ordered descriptions).candidates =
            (if resort then ordered
            else
              s.candidates.filter (fun t => ordered.contains t) ++
                ordered.filter fun t => !s.candidates.contains t) ∧
          ((fun (s : Selector.Picker.State) (_ : Bool) (ordered : List String)
                    (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions })
                s resort ordered descriptions).query =
            s.query ∧
          ((fun (s : Selector.Picker.State) (_ : Bool) (ordered : List String)
                    (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions })
                s resort ordered descriptions).descriptions =
            descriptions := by
  intro h
  have kept := (h { candidates := ["a", "b"] } false ["b", "a"] []).1
  exact absurd kept (by decide)

theorem enter_returns (s : Selector.Picker.State) (shown : List String) (focus : Option String)
    (ordered : List String) (descriptions : List (String × String)) :
    (Selector.Picker.enter s shown focus ordered descriptions).candidates =
        shown.filter (fun t => ordered.contains t) ++ ordered.filter (fun t => !shown.contains t) ∧
      (Selector.Picker.enter s shown focus ordered descriptions).query = s.query ∧
      (∀ t,
        focus = some t →
          s.query = "" →
          t ∈ ordered →
          (Selector.Picker.enter s shown focus ordered
                  descriptions).candidates[(Selector.Picker.enter s shown focus ordered
                  descriptions).cursor]? =
            some t) ∧
      ((∀ t, focus = some t → s.query = "" → t ∉ ordered) →
        (Selector.Picker.enter s shown focus ordered descriptions).cursor = 0) :=
  Selector.Picker.enter_returns s shown focus ordered descriptions

theorem enter_returns_rejects_top :
    ¬∀ (s : Selector.Picker.State) (shown : List String) (focus : Option String)
        (ordered : List String) (descriptions : List (String × String)),
        ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                    (ordered : List String) (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions, cursor := 0 })
                s shown focus ordered descriptions).candidates =
            shown.filter (fun t => ordered.contains t) ++
              ordered.filter (fun t => !shown.contains t) ∧
          ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                    (ordered : List String) (descriptions : List (String × String)) =>
                  { s with
                    candidates := ordered, descriptions := descriptions, cursor := 0 })
                s shown focus ordered descriptions).query =
            s.query ∧
          (∀ t,
            focus = some t →
              s.query = "" →
              t ∈ ordered →
              ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                          (ordered : List String) (descriptions : List (String × String)) =>
                        { s with
                          candidates := ordered, descriptions := descriptions, cursor := 0 })
                      s shown focus ordered
                      descriptions).candidates[((fun (s : Selector.Picker.State) (_ : List String)
                          (_ : Option String) (ordered : List String)
                          (descriptions : List (String × String)) =>
                        { s with
                          candidates := ordered, descriptions := descriptions, cursor := 0 })
                      s shown focus ordered descriptions).cursor]? =
                some t) ∧
          ((∀ t, focus = some t → s.query = "" → t ∉ ordered) →
            ((fun (s : Selector.Picker.State) (_ : List String) (_ : Option String)
                      (ordered : List String) (descriptions : List (String × String)) =>
                    { s with
                      candidates := ordered, descriptions := descriptions, cursor := 0 })
                  s shown focus ordered descriptions).cursor =
              0) := by
  intro h
  have chosen := (h { candidates := [] } [] (some "b") ["a", "b"] []).2.2.1 "b" rfl rfl (by simp)
  exact absurd chosen (by decide)

theorem picker_eof_empty (s : Selector.Picker.State) :
    Selector.Picker.step s .deleteCharEof = if s.query = "" then .cancel else .stay s :=
  Selector.Picker.step_deleteCharEof s

theorem picker_eof_empty_rejects_cancel :
    ¬∀ (s : Selector.Picker.State),
        (fun (_ : Selector.Picker.State) (_ : Selector.Key) => Selector.Picker.Outcome.cancel) s
            .deleteCharEof =
          if s.query = "" then .cancel else .stay s := by
  intro h
  -- a Ctrl-D that cancelled whatever the query held would end a visit with a query typed
  have typed := h { candidates := [], query := "a" }
  simp at typed

theorem picker_moves_cycle (s : Selector.Picker.State) (n k : Nat)
    (rows : ∀ i, (∃ next, Selector.Picker.step { s with cursor := i } .accept = .stay next) ↔ n ≤ i)
    (row : s.cursor < n ∨ n = 0) :
    Selector.Picker.press Selector.Picker.step s (List.replicate k .down) =
        .stay (if n = 0 then s else { s with cursor := (s.cursor + k) % n }) ∧
      Selector.Picker.press Selector.Picker.step s (List.replicate k .up) =
        .stay (if n = 0 then s else { s with cursor := ((s.cursor - k : Int) % n).toNat }) :=
  Selector.Picker.moves_cycle s n k rows row

theorem picker_moves_cycle_rejects_clamped :
    ¬∀ (s : Selector.Picker.State) (n k : Nat),
        (∀ i,
            (∃ next,
                Selector.Picker.clamped Selector.Picker.step { s with cursor := i } .accept =
                  .stay next) ↔
              n ≤ i) →
          s.cursor < n ∨ n = 0 →
          Selector.Picker.press (Selector.Picker.clamped Selector.Picker.step) s
                (List.replicate k .down) =
              .stay (if n = 0 then s else { s with cursor := (s.cursor + k) % n }) ∧
            Selector.Picker.press (Selector.Picker.clamped Selector.Picker.step) s
                (List.replicate k .up) =
              .stay (if n = 0 then s else { s with cursor := ((s.cursor - k : Int) % n).toNat }) :=
  -- of two rows, the second selected, a clamped down stays there, where the cycle selects the first
  Selector.Picker.clamped_not_cycle

end Linger
