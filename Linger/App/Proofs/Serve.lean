module

public import Linger.App.CoreCode.Serve
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Serve
import all Linger.App.CoreCode.Api
import all Linger.App.CoreCode.Commands
import all Linger.App.Proofs.Api

/-! # A connection: its requests are command lines, and its handshake comes first

A method's request is the request of its command line, of the method's operation, and its result
is the answer that command line exits with. Until the client says `initialized` a connection
writes nothing but errors and `initialize`'s result, which carries the version the client asked
for, and performs nothing; it answers or performs every request it hears, and sends no
notification. -/

namespace Linger.App.Serve

/-- **A method's request is its command line's.** -/
theorem parse_eq (method : String) (params : Json) :
    parse method params =
      (words method params).bind fun argv =>
        (Api.parse argv).bind fun request =>
          (input method params).map fun bytes => (request, bytes) := rfl

/-- Each method's command word names the method's operation. -/
theorem methods_words : ∀ e ∈ methods, (Commands.lookup e.2.2).map (·.op) = some e.2.1 := by decide

/-- **A method is one operation**: the request its params parse to is of its operation. -/
theorem parse_op {method : String} {params : Json} {request : Api.Request} {bytes : List UInt8}
    (parsed : parse method params = some (request, bytes)) :
    (methods.lookup method).map (·.1) = some request.op := by
  unfold parse words at parsed
  cases found : methods.lookup method with
  | none => simp [found] at parsed
  | some entry =>
    obtain ⟨op, word⟩ := entry
    simp only [found, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at parsed
    obtain ⟨argv, ⟨rest, _, rfl⟩, request', parsedArgv, bytes', _, same⟩ := parsed
    obtain ⟨rfl, -⟩ := Prod.mk.inj same
    have byWord := Api.parse_op parsedArgv
    obtain ⟨before, after, split, -⟩ := List.lookup_eq_some_iff.mp found
    have member : (method, op, word) ∈ methods := by simp [split]
    have named := methods_words _ member
    simp only [List.headD_cons] at byWord
    simp only [Option.map_some, Option.some.injEq]
    rw [named] at byWord
    exact Option.some.inj byWord

/-- **A result is the command line's answer**, by name and code, then what the request shows. -/
theorem result_eq (found : Api.Found) (members : List (String × Json)) :
    result found members =
      .obj
        (("answer", .str (answerName (Api.answer found))) ::
          ("code", .number (toString (Api.answer found).code)) :: members) := rfl

/-- A connection starts before its handshake. -/
theorem init_phase : State.init.phase = .fresh := rfl

/-- **Before it is ready, a connection writes nothing but errors and `initialize`'s result, and
performs nothing.** -/
theorem step_negotiating (s : State) (ev : Event) (notReady : ∀ version, s.phase ≠ .ready version) :
    ∀ e ∈ (step s ev).2, e.Negotiating := by
  obtain ⟨message⟩ := ev
  cases message with
  | invalid id unparsed => cases unparsed <;> simp [step, Effect.Negotiating]
  | notification method params =>
    simp only [step]
    split
    · split <;> simp
    · simp
  | request id method params =>
    simp only [step, request]
    split
    · split
      · split
        · intro e sent
          simp only [List.mem_singleton] at sent
          subst sent
          exact ⟨_, _, rfl⟩
        · simp [Effect.Negotiating]
      · simp [Effect.Negotiating]
    · simp [Effect.Negotiating, notInitialized]

/-- **A connection is ready only once the client said `initialized`** after `initialize` was
answered. -/
theorem step_ready (s : State) (ev : Event) (version : String)
    (ready : (step s ev).1.phase = .ready version) :
    s.phase = .ready version ∨
      s.phase = .negotiated version ∧
        ∃ params, ev = .received (.notification "initialized" params) := by
  obtain ⟨message⟩ := ev
  cases message with
  | invalid id unparsed => exact .inl ready
  | notification method params =>
    simp only [step] at ready
    split at ready
    · rename_i negotiated phase
      split at ready
      · rename_i initialized
        simp only [State.phase] at ready
        cases ready
        exact .inr ⟨phase, params, by rw [initialized]⟩
      · exact .inl ready
    · exact .inl ready
  | request id method params =>
    simp only [step, request] at ready
    split at ready
    · split at ready
      · split at ready
        · simp [State.phase] at ready
        · exact .inl ready
      · exact .inl ready
    · split at ready
      · split at ready
        · split at ready <;> exact .inl ready
        · exact .inl ready
      · exact .inl ready

/-- **`initialize`'s result goes only to `initialize`, with the version the client asked for**,
one `serve` speaks. -/
theorem step_welcome (s : State) (ev : Event) (id : Id) (version linger : String)
    (sent : Effect.send (.result id (welcome version linger)) ∈ (step s ev).2) :
    version ∈ versions ∧
      ∃ params,
        ev = .received (.request id "initialize" params) ∧
          params.member? "protocolVersion" = some (.str version) := by
  obtain ⟨message⟩ := ev
  cases message with
  | invalid id' unparsed => cases unparsed <;> simp [step] at sent
  | notification method params =>
    simp only [step] at sent
    split at sent
    · split at sent <;> simp at sent
    · simp at sent
  | request id' method params =>
    simp only [step, request] at sent
    split at sent
    · rename_i isInitialize
      split at sent
      · split at sent
        · rename_i chose
          simp only [List.mem_singleton, Effect.send.injEq, Outgoing.result.injEq, welcome,
            Json.obj.injEq, List.cons.injEq, Prod.mk.injEq, Json.str.injEq, true_and] at sent
          obtain ⟨rfl, rfl, -⟩ := sent
          unfold chosen at chose
          split at chose
          · rename_i asked
            split at chose
            · rename_i speaks
              cases chose
              exact ⟨speaks, params, by rw [isInitialize], asked⟩
            · simp at chose
          · simp at chose
        · simp at sent
      · simp at sent
    · split at sent
      · split at sent
        · split at sent <;> simp at sent
        · simp at sent
      · simp [notInitialized] at sent

/-- **Every request is answered or performed.** -/
theorem step_answers (s : State) (id : Id) (method : String) (params : Json) :
    ∃ e ∈ (step s (.received (.request id method params))).2, e.Answers id := by
  simp only [step, request]
  split
  · split
    · split <;> simp [Effect.Answers]
    · simp [Effect.Answers]
  · split
    · split
      · split <;> simp [Effect.Answers]
      · simp [Effect.Answers]
    · simp [Effect.Answers, notInitialized]

/-- A connection sends no notification. -/
theorem step_quiet (s : State) (ev : Event) :
    ∀ e ∈ (step s ev).2, ∀ method params, e ≠ .send (.notify method params) := by
  obtain ⟨message⟩ := ev
  cases message with
  | invalid id unparsed => cases unparsed <;> simp [step]
  | notification method params =>
    simp only [step]
    split
    · split <;> simp
    · simp
  | request id method params =>
    simp only [step, request]
    split
    · split
      · split <;> simp
      · simp
    · split
      · split
        · split <;> simp
        · simp
      · simp [notInitialized]

end Linger.App.Serve
