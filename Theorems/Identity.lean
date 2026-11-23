module

public import Linger.Session.CoreCode
public import Linger.Session.CoreSpec
public import Linger.Session.WorldSpec
public import Terminal.CoreCode.Mediation
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

/-! # Part 4 of `Challenge.lean`, program identity: the proofs of its headline theorems and their kills

`Challenge.lean` states them; each proof cites the component theorems it restates, and
`Theorems.Solution` gathers every part for `./lake comparator`. -/

public section

namespace Linger

open Linger.Display Linger.Session Linger.Target Terminal

theorem input_unrecorded (vt : Vt.Vt) (fields metadata : List (String × String))
    (evs evs' : List Event) (framed : ∀ ev ∈ evs, Framed Wire.encode ev)
    (typed : Typed Wire.encode evs evs') :
    (Session.trace Session.step (State.boot vt fields metadata) evs).1 =
        (Session.trace Session.step (State.boot vt fields metadata) evs').1 ∧
      (Session.trace Session.step (State.boot vt fields metadata) evs).2.map Effect.blind =
        (Session.trace Session.step (State.boot vt fields metadata) evs').2.map Effect.blind :=
  Session.trace_typed _ (Session.boot_whole vt fields metadata) evs evs' framed typed

theorem input_unrecorded_rejects_kept :
    ¬∀ (vt : Vt.Vt) (fields metadata : List (String × String)) (evs evs' : List Event),
        (∀ ev ∈ evs, Framed Wire.encode ev) →
          Typed Wire.encode evs evs' →
          (Session.trace
                  (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                    (Session.step s (.ptyOut chunk)).1)
                  (State.boot vt fields metadata) evs).1 =
              (Session.trace
                  (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                    (Session.step s (.ptyOut chunk)).1)
                  (State.boot vt fields metadata) evs').1 ∧
            (Session.trace
                    (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                      (Session.step s (.ptyOut chunk)).1)
                    (State.boot vt fields metadata) evs).2.map
                Effect.blind =
              (Session.trace
                    (Session.keepsInput Session.step fun (s : State) (chunk : List UInt8) =>
                      (Session.step s (.ptyOut chunk)).1)
                    (State.boot vt fields metadata) evs').2.map
                Effect.blind := by
  -- a session that keeps what a client typed in its terminal tells two typings apart
  intro h
  have fits : ∀ bytes : List UInt8, bytes.length ≤ 2 → ∀ m ∈ [Wire.Msg.input bytes], m.Fits := by
    intro bytes hb m hm
    simp only [List.mem_singleton] at hm
    subst hm
    simp only [Wire.Msg.Fits]
    exact Nat.le_trans hb (by decide)
  have typed :
    Typed Wire.encode [.connected 0, .bytes 0 ([Wire.Msg.input [0x41]].flatMap Wire.encode)]
      [.connected 0, .bytes 0 ([Wire.Msg.input [0x41, 0x41]].flatMap Wire.encode)] :=
    .same _ (.input 0 _ _ (fits [0x41] (by decide)) (fits [0x41, 0x41] (by decide)) rfl .nil)
  have framed :
    ∀ ev ∈ [Event.connected 0, .bytes 0 ([Wire.Msg.input [0x41]].flatMap Wire.encode)],
      Framed Wire.encode ev := by
    intro ev hev
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hev
    rcases hev with rfl | rfl
    · trivial
    · exact ⟨_, rfl, fits [0x41] (by decide)⟩
  have same :=
    congrArg (fun s => s.terminal.cursorPos) (h (Vt.Vt.init 10 1) [] [] _ _ framed typed).1
  rw [Session.keepsInput_terminal _ (by decide), Session.keepsInput_terminal _ (by decide)] at same
  revert same
  decide +kernel

theorem start_runs (inherited : String → Option String)
    (start :
      String →
        String → Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started)
    (runs : Spawn.Runs inherited start) (names : List String)
    (named : ∀ key, (inherited key).isSome → key ∈ names) (id notify dir shell : String)
    (argv : List String) {started : Spawn.Started}
    (ok :
      start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
          (Start.environment id notify names) Start.reset =
        some started) :
    started.argv = argv.headD shell :: argv.drop 1 ∧
      started.dir = dir ∧
      started.env "LINGER_SESSION" = some id ∧
      started.env "TERM" = some "xterm-256color" ∧
      started.env "COLORTERM" = some "truecolor" ∧
      started.env "TERM_PROGRAM" = some "linger" ∧
      started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
      started.env "NOTIFY_SOCKET" = some notify ∧
      ∀ key,
        key ∉
            ["LINGER_SESSION", "TERM", "COLORTERM", "TERM_PROGRAM", "TERM_PROGRAM_VERSION",
              "NOTIFY_SOCKET"] →
          started.env key = if Start.lingers key then none else inherited key := by
  obtain ⟨hargv, hdir, henv⟩ := runs _ _ _ _ _ _ ok
  rw [Start.programOf_exact] at hargv
  refine ⟨by simpa using hargv, hdir, ?_, ?_, ?_, ?_, ?_, ?_, fun key hkey => ?_⟩
  all_goals rw [henv, Start.environment_lookup _ _ _ _ _ (named _)]
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp
  · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hkey
    simp [hkey.1, hkey.2.1, hkey.2.2.1, hkey.2.2.2.1, hkey.2.2.2.2.1, hkey.2.2.2.2.2]

theorem start_runs_rejects_passing :
    ¬∀ (inherited : String → Option String)
        (start :
          String →
            String →
            Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started),
        Spawn.Runs inherited start →
          ∀ (names : List String),
            (∀ key, (inherited key).isSome → key ∈ names) →
              ∀ (id notify dir shell : String) (argv : List String) {started : Spawn.Started},
                start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
                      ((fun (id notify : String) (_ : List String) =>
                          Start.environment id notify [])
                        id notify names)
                      Start.reset =
                    some started →
                  started.argv = argv.headD shell :: argv.drop 1 ∧
                    started.dir = dir ∧
                    started.env "LINGER_SESSION" = some id ∧
                    started.env "TERM" = some "xterm-256color" ∧
                    started.env "COLORTERM" = some "truecolor" ∧
                    started.env "TERM_PROGRAM" = some "linger" ∧
                    started.env "TERM_PROGRAM_VERSION" = some Mediation.versionNumber ∧
                    started.env "NOTIFY_SOCKET" = some notify ∧
                    ∀ key,
                      key ∉
                          ["LINGER_SESSION", "TERM", "COLORTERM", "TERM_PROGRAM",
                            "TERM_PROGRAM_VERSION", "NOTIFY_SOCKET"] →
                        started.env key = if Start.lingers key then none else inherited key := by
  intro h
  -- a caller with `LINGER_DIR` set, which an environment that unsets nothing passes through
  let inherited := fun key : String => if key = "LINGER_DIR" then some "state" else none
  have runs :
    Spawn.Runs inherited fun dir prog args extra _ =>
      some
        { argv := prog :: args.toList, dir,
          env := fun key => (extra.reverse.lookup key).getD (inherited key),
          ignored := fun _ => false, blocked := fun _ => false, descriptor := fun _ => none } := by
    intro dir prog args extra reset started hs
    cases hs
    exact ⟨rfl, rfl, fun _ => rfl⟩
  have named : ∀ key, (inherited key).isSome → key ∈ ["LINGER_DIR"] := by
    intro key h
    by_cases dirKey : key = "LINGER_DIR"
    · simp [dirKey]
    · simp [inherited, dirKey] at h
  have passed :=
    (h _ _ runs ["LINGER_DIR"] named "x" "n" "" "sh" [] rfl).2.2.2.2.2.2.2.2 "LINGER_DIR"
      (by decide)
  simp [Start.lingers, Start.environment, Start.session, List.lookup, inherited] at passed

theorem start_clean
    (start :
      String →
        String → Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started)
    (clean : Spawn.Clean start) (name notify dir shell : String) (names argv : List String)
    {started : Spawn.Started}
    (ok :
      start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
          (Start.environment name notify names) Start.reset =
        some started) :
    (∀ sig, started.ignored sig = false) ∧
      (∀ sig, started.blocked sig = false) ∧
      ∀ fd, started.descriptor fd = if fd < 3 then some .terminal else none := by
  obtain ⟨terminal, ignored, blocked, closed⟩ := clean _ _ _ _ _ _ ok
  obtain ⟨dispositions, mask, descriptors⟩ := Start.reset_clean
  refine ⟨ignored dispositions, blocked mask, fun fd => ?_⟩
  by_cases low : fd < 3
  · rw [ite_eq_left low]
    exact terminal fd low
  · rw [ite_eq_right low]
    exact closed descriptors fd (Nat.le_of_not_lt low)

theorem start_clean_rejects_inherited :
    ¬∀
        (start :
          String →
            String →
            Array String → List (String × Option String) → Spawn.Reset → Option Spawn.Started),
        Spawn.Clean start →
          ∀ (name notify dir shell : String) (names argv : List String) {started : Spawn.Started},
            start dir (Start.programOf shell argv).1 (Start.programOf shell argv).2
                  (Start.environment name notify names)
                  ({ dispositions := false, mask := true, descriptors := true } : Spawn.Reset) =
                some started →
              (∀ sig, started.ignored sig = false) ∧
                (∀ sig, started.blocked sig = false) ∧
                ∀ fd, started.descriptor fd = if fd < 3 then some .terminal else none := by
  intro h
  -- a start that leaves every signal ignored unless it is asked to reset them
  have clean :
    Spawn.Clean fun _ _ _ _ reset =>
      some
        { argv := [], dir := "", env := fun _ => none, ignored := fun _ => !reset.dispositions,
          blocked := fun _ => false,
          descriptor := fun fd => if fd < 3 then some .terminal else none } := by
    intro dir prog args extra reset started hs
    cases hs
    refine ⟨fun fd low => ite_eq_left low, fun asked _ => by simp [asked], fun _ _ => rfl, ?_⟩
    exact fun _ fd high => ite_eq_right (Nat.not_lt_of_le high)
  exact absurd ((h _ clean "x" "n" "" "sh" [] [] rfl).1 2) (by simp)

end Linger
