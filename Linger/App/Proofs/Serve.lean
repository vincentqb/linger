module

public import Linger.App.CoreCode.Serve
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Serve
import all Linger.App.CoreCode.Api
import all Linger.App.CoreCode.Commands
import all Linger.App.Proofs.Api

/-! # A connection: its requests are command lines, its handshake comes first, its table converges

A method's request is the request of its command line, of the method's operation, and its result
is the answer that command line exits with. Until the client says `initialized` a connection
writes nothing but errors and `initialize`'s result, which carries the version the client asked
for, and performs nothing; it answers or performs every request it hears. Its one notification,
`sessions/changed`, goes to the subscription open, which a `sessions/subscribe` opens and a
`sessions/unsubscribe` closes. A listing's records replace the latest it holds and send nothing;
each time the writer is free it sends what differs from what it last told the subscriber, which
brings the subscriber's view to the latest records. A log keeps the last entries, at most its
cap, and counts the rest. -/

namespace Linger.App.Serve

/-- **A method's request is its command line's.** -/
theorem parse_eq (method : String) (params : Json) :
    parse method params =
      (words method params).bind fun argv =>
        (Api.parse argv).bind fun request =>
          (input method params).map fun bytes => (request, bytes) := rfl

/-- Each method's command word names the method's operation. -/
theorem methods_words : ∀ e ∈ methods, (Commands.lookup e.2.2.1).map (·.op) = some e.2.1 := by
  decide

/-- **A method is one operation**: the request its params parse to is of its operation. -/
theorem parse_op {method : String} {params : Json} {request : Api.Request} {bytes : List UInt8}
    (parsed : parse method params = some (request, bytes)) :
    (methods.lookup method).map (·.1) = some request.op := by
  unfold parse words at parsed
  cases found : methods.lookup method with
  | none => simp [found] at parsed
  | some entry =>
    obtain ⟨op, word, shape⟩ := entry
    simp only [found, Option.bind_some, Option.bind_eq_some_iff, Option.map_eq_some_iff] at parsed
    obtain ⟨argv, ⟨rest, _, rfl⟩, request', parsedArgv, bytes', _, same⟩ := parsed
    obtain ⟨rfl, -⟩ := Prod.mk.inj same
    have byWord := Api.parse_op parsedArgv
    obtain ⟨before, after, split, -⟩ := List.lookup_eq_some_iff.mp found
    have member : (method, op, word, shape) ∈ methods := by simp [split]
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

/-- `sessions/subscribe` takes any params: it lists every session, as records. -/
theorem parse_subscribe (params : Json) :
    parse "sessions/subscribe" params = some (.list (.every true none), []) := by
  simp [parse, words, input, operands, methods]
  rfl

/-- An id as JSON reads back as the id. -/
theorem Id.of_json (id : Id) : Id.of id.json = some id := by cases id <;> rfl

/-- No result is `initialize`'s: a result begins with its answer, `initialize`'s with its version. -/
theorem result_ne_welcome (found : Api.Found) (members : List (String × Json))
    (version linger : String) : result found members ≠ welcome version linger := by
  simp [result, answerMembers, welcome]

/-! ## Watches held -/

/-- A watch set or dropped, or one more asked for, leaves the rest of a connection as it was. -/
theorem setWatch_eq (s : State) (id : Id) (w : Watch) :
    ∃ ws, s.setWatch id w = { s with watches := ws } := ⟨_, rfl⟩

/-- A watch dropped leaves the rest of a connection as it was. -/
theorem dropWatch_eq (s : State) (id : Id) : ∃ ws, s.dropWatch id = { s with watches := ws } :=
  ⟨_, rfl⟩

/-- Looking up a key among pairs, one of which is set to a value under its key. -/
theorem lookup_set {β : Type} (id : Id) (w : β) :
    ∀ (pairs : List (Id × β)) (key : Id),
      (pairs.map fun entry => if entry.1 = id then (id, w) else entry).lookup key =
        if key = id then (pairs.lookup key).map fun _ => w else pairs.lookup key
  | [], key => by simp [List.lookup]
  | (k, v) :: rest, key => by
    have ih := lookup_set id w rest key
    simp only [List.map_cons]
    by_cases asked : key = k
    · subst asked
      by_cases here : key = id
      · subst here
        simp [List.lookup_cons_self]
      · simp [List.lookup_cons_self, here]
    · have other : (key == k) = false := beq_eq_false_iff_ne.mpr asked
      by_cases here : k = id
      · subst here
        have : (key == k) = false := other
        simp only [↓reduceIte, List.lookup_cons, this]
        exact ih
      · simp only [here, ↓reduceIte, List.lookup_cons, other]
        exact ih

/-- Looking up a key among pairs less those under one key. -/
theorem lookup_drop {β : Type} (id : Id) :
    ∀ (pairs : List (Id × β)) (key : Id),
      (pairs.filter fun entry => entry.1 != id).lookup key =
        if key = id then none else pairs.lookup key
  | [], key => by simp [List.lookup]
  | (k, v) :: rest, key => by
    have ih := lookup_drop id rest key
    simp only [List.filter_cons]
    by_cases here : k = id
    · subst here
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      rw [ih]
      by_cases asked : key = k
      · simp [asked]
      · have other : (key == k) = false := beq_eq_false_iff_ne.mpr asked
        simp [asked, List.lookup_cons, other]
    · have keep : (k != id) = true := by simpa using here
      simp only [keep, ↓reduceIte]
      by_cases asked : key = k
      · subst asked
        simp [List.lookup_cons_self, here]
      · have other : (key == k) = false := beq_eq_false_iff_ne.mpr asked
        simp only [List.lookup_cons, other]
        exact ih

/-- What a connection holds for a watch once one is set: the watch, where it held one, and for
every other id what it held. -/
theorem setWatch_watching (s : State) (id : Id) (w : Watch) (key : Id) :
    (s.setWatch id w).watching key =
      if key = id then (s.watching key).map fun _ => w else s.watching key :=
  lookup_set id w s.watches key

/-- What a connection holds once a watch is dropped: none for it, and for every other id what it
held. -/
theorem dropWatch_watching (s : State) (id : Id) (key : Id) :
    (s.dropWatch id).watching key = if key = id then none else s.watching key :=
  lookup_drop id s.watches key

/-- Looking up a key among pairs, one more appended. -/
theorem lookup_append_one {β : Type} (id : Id) (w : β) :
    ∀ (pairs : List (Id × β)) (key : Id),
      (pairs ++ [(id, w)]).lookup key = (pairs.lookup key).or (if key = id then some w else none)
  | [], key => by
    by_cases asked : key = id
    · subst asked
      simp [List.lookup_cons_self]
    · have other : (key == id) = false := beq_eq_false_iff_ne.mpr asked
      simp [List.lookup_cons, other, asked, List.lookup]
  | (k, v) :: rest, key => by
    have ih := lookup_append_one id w rest key
    by_cases asked : key = k
    · subst asked
      simp [List.lookup_cons_self]
    · have other : (key == k) = false := beq_eq_false_iff_ne.mpr asked
      simp only [List.cons_append, List.lookup_cons, other]
      exact ih

/-- A watch's look sets the watch it finds and nothing else. -/
theorem watched_eq (s : State) (id : Id) (screen : Screen) (left : Log Line) :
    ∃ ws, (watched s id screen left).1 = { s with watches := ws } := by
  unfold watched
  split
  all_goals
    first
    | exact setWatch_eq _ _ _
    | exact ⟨s.watches, rfl⟩

/-- A free writer's update of a watch sets the watch it finds and nothing else. -/
theorem flushed_eq (s : State) (id : Id) : ∃ ws, (flushed s id).1 = { s with watches := ws } := by
  unfold flushed
  split
  all_goals
    first
    | exact setWatch_eq _ _ _
    | exact ⟨s.watches, rfl⟩

/-- A watch's end drops the watch it finds and nothing else. -/
theorem unwatched_eq (s : State) (id : Id) (found : Api.Found) (said : Log String) :
    ∃ ws, (unwatched s id found said).1 = { s with watches := ws } := by
  unfold unwatched
  split
  all_goals
    first
    | exact dropWatch_eq _ _
    | exact ⟨s.watches, rfl⟩

/-- A watch's look holds a watch under an id exactly where the connection held one. -/
theorem watched_watching (s : State) (id : Id) (screen : Screen) (left : Log Line) (key : Id) :
    ((watched s id screen left).1.watching key).isSome = (s.watching key).isSome := by
  unfold watched
  split
  · rw [setWatch_watching]; split <;> simp
  · rw [setWatch_watching]; split <;> simp
  · rw [setWatch_watching]; split <;> simp
  · rw [setWatch_watching]; split <;> simp
  · rfl

/-- A free writer's update holds a watch under an id exactly where the connection held one. -/
theorem flushed_watching (s : State) (id : Id) (key : Id) :
    ((flushed s id).1.watching key).isSome = (s.watching key).isSome := by
  unfold flushed
  split
  · rw [setWatch_watching]; split <;> simp
  · rw [setWatch_watching]; split <;> simp
  · rfl

/-- A watch's end holds a watch under an id only where the connection held one. -/
theorem unwatched_watching (s : State) (id : Id) (found : Api.Found) (said : Log String) (key : Id)
    (held : ((unwatched s id found said).1.watching key).isSome) : (s.watching key).isSome := by
  unfold unwatched at held
  split at held
  all_goals
    first
    | exact held
    | ( rw [dropWatch_watching] at held
        split at held
        · simp at held
        · exact held)

/-! ## Requests -/

/-- `sessions/unsubscribe` leaves the handshake as it was. -/
theorem unsubscribe_stage (s : State) (id : Id) (params : Json) :
    (unsubscribe s id params).1.stage = s.stage := by
  unfold unsubscribe
  split
  · split
    · obtain ⟨ws, same⟩ :=
        dropWatch_eq
          (if s.subscription = some _ then
            { s with
              open? := none, toldRecords := none, latestRecords := none }
          else s)
          _
      rw [same]
      split <;> rfl
    · rfl
  · rfl

/-- A request performed leaves the handshake as it was. -/
theorem performs_stage (s : State) (id : Id) (method : String) (req : Api.Request)
    (bytes : List UInt8) : (performs s id method req bytes).1.stage = s.stage := by
  unfold performs
  split
  · rfl
  · split
    · split <;> rfl
    · rfl

/-- What a request does to the handshake: nothing, but an `initialize` before it, answered. -/
theorem request_stage (s : State) (id : Id) (method : String) (params : Json) :
    (request s id method params).1.stage = s.stage ∨
      ∃ version,
        s.stage = .fresh ∧
          method = "initialize" ∧ (request s id method params).1.stage = .negotiated version := by
  unfold request
  split
  · rename_i isInitialize
    split
    · rename_i fresh
      split
      · rename_i version _
        exact .inr ⟨version, fresh, isInitialize, rfl⟩
      · exact .inl rfl
    · exact .inl rfl
  · split
    · split
      · exact .inl (unsubscribe_stage s id params)
      · split
        · split
          · exact .inl (performs_stage _ _ _ _ _)
          · exact .inl rfl
        · exact .inl rfl
    · exact .inl rfl

/-- What an event does to the handshake: nothing, but an `initialize` before it, answered, and
then the client's `initialized`. -/
theorem step_stage (s : State) (ev : Event) :
    (step s ev).1.stage = s.stage ∨
      (∃ version id params,
        s.stage = .fresh ∧
          ev = .received (.request id "initialize" params) ∧
          (step s ev).1.stage = .negotiated version) ∨
      ∃ version params,
        s.stage = .negotiated version ∧
          ev = .received (.notification "initialized" params) ∧
          (step s ev).1.stage = .ready version := by
  cases ev with
  | received message =>
    cases message with
    | invalid id unparsed => exact .inl rfl
    | notification method params =>
      simp only [step]
      split
      · rename_i version negotiated
        split
        · rename_i initialized
          subst initialized
          exact .inr (.inr ⟨version, params, negotiated, rfl, rfl⟩)
        · exact .inl rfl
      · exact .inl rfl
    | request id method params =>
      simp only [step]
      rcases request_stage s id method params with same | ⟨version, fresh, rfl, negotiated⟩
      · exact .inl same
      · exact .inr (.inl ⟨version, id, params, fresh, rfl, negotiated⟩)
  | opened id records =>
    left
    simp only [step]
    split
    · split <;> rfl
    · rfl
  | sampled records =>
    left
    simp only [step]
    split
    · split <;> rfl
    · rfl
  | writable =>
    left
    simp only [step]
    split <;> rfl
  | watched id screen left =>
    left
    obtain ⟨ws, same⟩ := watched_eq s id screen left
    simp only [step, same]
  | flush id =>
    left
    obtain ⟨ws, same⟩ := flushed_eq s id
    simp only [step, same]
  | unwatched id found said =>
    left
    obtain ⟨ws, same⟩ := unwatched_eq s id found said
    simp only [step, same]

/-- **Before it is ready, a connection writes nothing but errors and `initialize`'s result, and
performs nothing.** -/
theorem step_negotiating (s : State) (ev : Event) (notReady : ∀ version, s.phase ≠ .ready version) :
    ∀ e ∈ (step s ev).2, e.Negotiating := by
  obtain ⟨stage, open?, told, latest, watches⟩ := s
  cases stage with
  | ready version => exact absurd rfl (notReady version)
  | fresh =>
    cases ev with
    | received message =>
      cases message with
      | invalid id unparsed => cases unparsed <;> simp [step, Effect.Negotiating]
      | notification method params => simp [step, State.phase]
      | request id method params =>
        simp only [step, request, State.phase]
        split
        · split
          · intro e sent
            simp only [List.mem_singleton] at sent
            subst sent
            exact ⟨_, _, rfl⟩
          · simp [Effect.Negotiating]
        · simp [Effect.Negotiating, notInitialized]
    | opened id records => simp [step, State.phase]
    | sampled records => simp [step, State.phase]
    | writable => simp [step, State.phase]
    | watched id screen left => simp [step, watched, State.phase]
    | flush id => simp [step, flushed, State.phase]
    | unwatched id found said => simp [step, unwatched, State.phase]
  | negotiated version =>
    cases ev with
    | received message =>
      cases message with
      | invalid id unparsed => cases unparsed <;> simp [step, Effect.Negotiating]
      | notification method params =>
        simp only [step, State.phase]
        split <;> simp
      | request id method params =>
        simp only [step, request, State.phase]
        split <;> simp [Effect.Negotiating, notInitialized]
    | opened id records => simp [step, State.phase]
    | sampled records => simp [step, State.phase]
    | writable => simp [step, State.phase]
    | watched id screen left => simp [step, watched, State.phase]
    | flush id => simp [step, flushed, State.phase]
    | unwatched id found said => simp [step, unwatched, State.phase]

/-- **A connection is ready only once the client said `initialized`** after `initialize` was
answered. -/
theorem step_ready (s : State) (ev : Event) (version : String)
    (ready : (step s ev).1.phase = .ready version) :
    s.phase = .ready version ∨
      s.phase = .negotiated version ∧
        ∃ params, ev = .received (.notification "initialized" params) := by
  simp only [State.phase] at ready ⊢
  rcases step_stage s ev with same | ⟨_, _, _, _, _, negotiated⟩ |
    ⟨version', params, was, heard, now⟩
  · exact .inl (same ▸ ready)
  · rw [negotiated] at ready
    cases ready
  · rw [now] at ready
    cases ready
    exact .inr ⟨was, params, heard⟩

/-- What `sessions/unsubscribe` sends: results, and errors. -/
theorem unsubscribe_sends (s : State) (id : Id) (params : Json) :
    ∀ e ∈ (unsubscribe s id params).2,
      (∃ key found members, e = .send (.result key (result found members))) ∨
        ∃ code message data, e = .send (.error (some id) code message data) := by
  unfold unsubscribe
  split
  · split
    · intro e sent
      simp only [List.mem_append, List.mem_singleton] at sent
      rcases sent with sent | sent
      · split at sent
        · simp only [List.mem_singleton] at sent
          exact .inl ⟨_, _, _, sent⟩
        · simp at sent
      · exact .inl ⟨_, _, _, sent⟩
    · simp
  · simp

/-- What a performed request sends: its result, or that it is performed. -/
theorem performs_sends (s : State) (id : Id) (method : String) (req : Api.Request)
    (bytes : List UInt8) :
    ∀ e ∈ (performs s id method req bytes).2,
      (∃ found members, e = .send (.result id (result found members))) ∨
        e = .perform id method req bytes := by
  unfold performs
  split
  · simp
  · split
    · split
      · simp
      · simp only [List.mem_singleton]
        intro e sent
        exact .inl ⟨_, _, sent⟩
    · simp

/-- What a watch's look sends: the result of the request that asked for it. -/
theorem watched_sends (s : State) (id : Id) (screen : Screen) (left : Log Line) :
    ∀ e ∈ (watched s id screen left).2,
      ∃ found members, e = .send (.result id (result found members)) := by
  unfold watched
  split
  all_goals simp only [List.mem_singleton, List.not_mem_nil, false_imp_iff, implies_true]
  all_goals
    intro e sent
    exact ⟨_, _, sent⟩

/-- **`initialize`'s result goes only to `initialize`, with the version the client asked for**,
one `serve` speaks. -/
theorem step_welcome (s : State) (ev : Event) (id : Id) (version linger : String)
    (sent : Effect.send (.result id (welcome version linger)) ∈ (step s ev).2) :
    version ∈ versions ∧
      ∃ params,
        ev = .received (.request id "initialize" params) ∧
          params.member? "protocolVersion" = some (.str version) := by
  cases ev with
  | received message =>
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
          · rcases unsubscribe_sends s id' params _ sent with ⟨_, found, members, same⟩ |
              ⟨_, _, _, same⟩
            · simp only [Effect.send.injEq, Outgoing.result.injEq] at same
              exact absurd same.2.symm (result_ne_welcome found members version linger)
            · simp at same
          · split at sent
            · split at sent
              · rcases performs_sends s id' method _ _ _ sent with ⟨found, members, same⟩ | same
                · simp only [Effect.send.injEq, Outgoing.result.injEq] at same
                  exact absurd same.2.symm (result_ne_welcome found members version linger)
                · simp at same
              · simp at sent
            · simp at sent
        · simp [notInitialized] at sent
  | opened id' records =>
    simp only [step] at sent
    split at sent
    · split at sent <;> simp at sent
    · simp at sent
  | sampled records =>
    simp only [step] at sent
    split at sent
    · split at sent <;> simp at sent
    · simp at sent
  | writable =>
    simp only [step] at sent
    split at sent
    · split at sent <;> simp at sent
    · simp at sent
  | watched id' screen left =>
    simp only [step] at sent
    obtain ⟨found, members, same⟩ := watched_sends s id' screen left _ sent
    simp only [Effect.send.injEq, Outgoing.result.injEq] at same
    exact absurd same.2.symm (result_ne_welcome found members version linger)
  | flush id' =>
    simp only [step, flushed] at sent
    split at sent
    · split at sent <;> simp at sent
    · split at sent <;> simp at sent
    · simp at sent
  | unwatched id' found said =>
    simp only [step, unwatched] at sent
    split at sent
    · simp only [List.mem_singleton, Effect.send.injEq, Outgoing.result.injEq] at sent
      exact absurd sent.2.symm (result_ne_welcome found _ version linger)
    · simp at sent
    · simp at sent
    · simp at sent

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
      · unfold unsubscribe
        split
        · split
          · exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl⟩
          · simp [Effect.Answers]
        · simp [Effect.Answers]
      · split
        · split
          · unfold performs
            split
            · simp [Effect.Answers]
            · split
              · split <;> simp [Effect.Answers]
              · simp [Effect.Answers]
          · simp [Effect.Answers]
        · simp [Effect.Answers]
    · simp [Effect.Answers, notInitialized]

/-- An update's params name the subscription they update. -/
theorem update_names (id : Id) (records : List Record) (gone : List String) :
    (update id records gone).member? "subscription" = some id.json := by simp [update, Json.member?]

/-- A screen's update names its subscription, with members after it or none. -/
theorem screen_update_names (id : Id) (u : Screen.Update) (more : List (String × Json)) :
    ((Screen.update id u).withMembers more).member? "subscription" = some id.json ∧
      (Screen.update id u).member? "subscription" = some id.json := by
  simp [Screen.update, Json.withMembers, Json.member?, List.lookup]

/-- A history's update names its subscription, with members after it or none. -/
theorem log_update_names (id : Id) (log : Log Line) (more : List (String × Json)) :
    ((Log.update id log).withMembers more).member? "subscription" = some id.json ∧
      (Log.update id log).member? "subscription" = some id.json := by
  simp [Log.update, Json.withMembers, Json.member?, List.lookup]

/-- **A connection's notifications name a subscription open**, of their kind: `sessions/changed`
the sessions table's, `session/screen/changed` a screen's and `session/history/changed` a
history's. -/
theorem step_notify_open (s : State) (ev : Event) :
    ∀ e ∈ (step s ev).2,
      ∀ method params,
        e = .send (.notify method params) →
          ∃ id,
            params.member? "subscription" = some id.json ∧
              (method = "sessions/changed" ∧ s.subscription = some id ∨
                method = "session/screen/changed" ∧
                  (∃ told latest, s.watching id = some (.screen told latest)) ∨
                method = "session/history/changed" ∧
                  ∃ pending, s.watching id = some (.history pending)) := by
  intro e sent method params notified
  subst notified
  cases ev with
  | received message =>
    cases message with
    | invalid id unparsed => cases unparsed <;> simp [step] at sent
    | notification method params =>
      simp only [step] at sent
      split at sent
      · split at sent <;> simp at sent
      · simp at sent
    | request id method' params' =>
      simp only [step, request] at sent
      split at sent
      · repeat' split at sent
        all_goals simp at sent
      · split at sent
        · split at sent
          · rcases unsubscribe_sends s id params' _ sent with ⟨_, _, _, same⟩ | ⟨_, _, _, same⟩
            all_goals simp at same
          · split at sent
            · split at sent
              · rcases performs_sends s id method' _ _ _ sent with ⟨_, _, same⟩ | same
                all_goals simp at same
              · simp at sent
            · simp at sent
        · simp [notInitialized] at sent
  | opened id records =>
    simp only [step] at sent
    split at sent
    · split at sent <;> simp at sent
    · simp at sent
  | sampled records =>
    simp only [step] at sent
    split at sent
    · split at sent <;> simp at sent
    · simp at sent
  | writable =>
    simp only [step] at sent
    split at sent
    · rename_i version id told latest _ subscribed _ _
      split at sent
      · simp at sent
      · simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
        obtain ⟨rfl, rfl⟩ := sent
        exact ⟨id, update_names _ _ _, .inl ⟨rfl, subscribed⟩⟩
    · simp at sent
  | watched id screen left =>
    simp only [step] at sent
    obtain ⟨_, _, same⟩ := watched_sends s id screen left _ sent
    simp at same
  | flush id =>
    simp only [step, flushed] at sent
    split at sent
    · rename_i version told latest _ holds
      split at sent
      · simp at sent
      · simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
        obtain ⟨rfl, rfl⟩ := sent
        exact ⟨id, (screen_update_names _ _ []).2, .inr (.inl ⟨rfl, told, latest, holds⟩)⟩
    · rename_i version pending _ holds
      split at sent
      · simp at sent
      · simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
        obtain ⟨rfl, rfl⟩ := sent
        exact ⟨id, (log_update_names _ _ []).2, .inr (.inr ⟨rfl, pending, holds⟩)⟩
    · simp at sent
  | unwatched id found said =>
    simp only [step, unwatched] at sent
    split at sent
    · simp at sent
    · rename_i version told latest _ holds
      simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
      obtain ⟨rfl, rfl⟩ := sent
      exact ⟨id, (screen_update_names _ _ _).1, .inr (.inl ⟨rfl, told, latest, holds⟩)⟩
    · rename_i version pending _ holds
      simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
      obtain ⟨rfl, rfl⟩ := sent
      exact ⟨id, (log_update_names _ _ _).1, .inr (.inr ⟨rfl, pending, holds⟩)⟩
    · simp at sent

/-- What `sessions/unsubscribe` does to the subscription: nothing, or closes it. -/
theorem unsubscribe_open (s : State) (id : Id) (params : Json) :
    (unsubscribe s id params).1.open? = s.open? ∨ (unsubscribe s id params).1.open? = none := by
  unfold unsubscribe
  split
  · split
    · obtain ⟨ws, same⟩ :=
        dropWatch_eq
          (if s.subscription = some _ then
            { s with
              open? := none, toldRecords := none, latestRecords := none }
          else s)
          _
      rw [same]
      split
      · exact .inr rfl
      · exact .inl rfl
    · exact .inl rfl
  · exact .inl rfl

/-- What a performed request does to the subscription: nothing, or opens one named by its id, a
`sessions/subscribe`. -/
theorem performs_open (s : State) (id : Id) (method : String) (req : Api.Request)
    (bytes : List UInt8) :
    (performs s id method req bytes).1.open? = s.open? ∨
      method = "sessions/subscribe" ∧ (performs s id method req bytes).1.open? = some id := by
  unfold performs
  split
  · rename_i subscribe
    exact .inr ⟨subscribe, rfl⟩
  · split
    · split <;> exact .inl rfl
    · exact .inl rfl

/-- What a request does to the subscription: nothing, closes it, or opens one named by its id, a
`sessions/subscribe` in a ready connection. -/
theorem request_open (s : State) (id : Id) (method : String) (params : Json) :
    (request s id method params).1.open? = s.open? ∨
      (request s id method params).1.open? = none ∨
      ∃ version,
        s.phase = .ready version ∧
          method = "sessions/subscribe" ∧ (request s id method params).1.open? = some id := by
  unfold request
  split
  · split
    · split <;> exact .inl rfl
    · exact .inl rfl
  · split
    · rename_i version ready
      split
      · rcases unsubscribe_open s id params with same | closed
        · exact .inl same
        · exact .inr (.inl closed)
      · split
        · split
          · rcases performs_open s id method _ _ with same | ⟨subscribe, now⟩
            · exact .inl same
            · exact .inr (.inr ⟨version, ready, subscribe, now⟩)
          · exact .inl rfl
        · exact .inl rfl
    · exact .inl rfl

/-- **A subscription opens only by its `sessions/subscribe`**, in a ready connection. -/
theorem step_opens (s : State) (ev : Event) (id : Id)
    (opened : (step s ev).1.subscription = some id) :
    s.subscription = some id ∨
      ∃ params version,
        s.phase = .ready version ∧ ev = .received (.request id "sessions/subscribe" params) := by
  simp only [State.subscription] at opened ⊢
  cases ev with
  | received message =>
    cases message with
    | invalid id' unparsed => exact .inl opened
    | notification method params =>
      simp only [step] at opened
      split at opened
      · split at opened <;> exact .inl opened
      · exact .inl opened
    | request id' method params =>
      simp only [step] at opened
      rcases request_open s id' method params with same | closed | ⟨version, ready, rfl, now⟩
      · exact .inl (same ▸ opened)
      · rw [closed] at opened
        cases opened
      · rw [now] at opened
        cases opened
        exact .inr ⟨params, version, ready, rfl⟩
  | opened id' records =>
    simp only [step] at opened
    split at opened
    · split at opened <;> exact .inl opened
    · exact .inl opened
  | sampled records =>
    simp only [step] at opened
    split at opened
    · split at opened <;> exact .inl opened
    · exact .inl opened
  | writable =>
    simp only [step] at opened
    split at opened <;> exact .inl opened
  | watched id' screen left =>
    obtain ⟨ws, same⟩ := watched_eq s id' screen left
    simp only [step, same] at opened
    exact .inl opened
  | flush id' =>
    obtain ⟨ws, same⟩ := flushed_eq s id'
    simp only [step, same] at opened
    exact .inl opened
  | unwatched id' found said =>
    obtain ⟨ws, same⟩ := unwatched_eq s id' found said
    simp only [step, same] at opened
    exact .inl opened

/-- **A `sessions/subscribe` in a ready connection opens its subscription**, named by its id. -/
theorem subscribe_opens (s : State) (id : Id) (params : Json) (version : String)
    (ready : s.phase = .ready version) :
    (step s (.received (.request id "sessions/subscribe" params))).1.subscription = some id := by
  simp [step, request, ready, parse_subscribe, methods, performs, State.subscription]

/-- **A `sessions/unsubscribe` of the subscription open closes it.** -/
theorem unsubscribe_closes (s : State) (id asked : Id) (params : Json) (version : String)
    (ready : s.phase = .ready version) (subscribed : s.subscription = some id)
    (names : params.member? "subscription" = some id.json) :
    (step s (.received (.request asked "sessions/unsubscribe" params))).1.subscription = none := by
  simp only [step, request, ready]
  simp only [unsubscribe, names, Option.bind_some, Id.of_json, subscribed, true_or, ↓reduceIte]
  obtain ⟨ws, same⟩ :=
    dropWatch_eq
      ({ s with
          open? := none, toldRecords := none, latestRecords := none } :
        State)
      id
  simp [same, State.subscription]

/-- What `sessions/unsubscribe` does to the watches: drops the one it names, or nothing. -/
theorem unsubscribe_watching (s : State) (id : Id) (params : Json) (key : Id)
    (held : ((unsubscribe s id params).1.watching key).isSome) : (s.watching key).isSome := by
  unfold unsubscribe at held
  split at held
  · split at held
    · rw [dropWatch_watching] at held
      split at held
      · simp at held
      · split at held <;> exact held
    · exact held
  · exact held

/-- What a performed request does to the watches: asks for one under its id, a watch's request, or
nothing. -/
theorem performs_watching (s : State) (id : Id) (method : String) (req : Api.Request)
    (bytes : List UInt8) (key : Id)
    (held : ((performs s id method req bytes).1.watching key).isSome) :
    (s.watching key).isSome ∨
      key = id ∧ (method = "session/screen" ∨ method = "session/history") := by
  unfold performs at held
  split at held
  · exact .inl held
  · split at held
    · rename_i watch
      split at held
      · simp only [State.watching, lookup_append_one] at held
        cases found : s.watches.lookup key with
        | some _ => exact .inl (by simp [State.watching, found])
        | none =>
          rw [found] at held
          by_cases same : key = id
          · exact .inr ⟨same, watch⟩
          · simp [same] at held
      · exact .inl held
    · exact .inl held

/-- What a request does to the watches: asks for one under its id, a watch's request in a ready
connection, drops one, or nothing. -/
theorem request_watching (s : State) (id : Id) (method : String) (params : Json) (key : Id)
    (held : ((request s id method params).1.watching key).isSome) :
    (s.watching key).isSome ∨
      ∃ version,
        s.phase = .ready version ∧
          key = id ∧ (method = "session/screen" ∨ method = "session/history") := by
  unfold request at held
  split at held
  · split at held
    · split at held
      · exact .inl held
      · exact .inl held
    · exact .inl held
  · split at held
    · rename_i version ready
      split at held
      · exact .inl (unsubscribe_watching s id params key held)
      · split at held
        · split at held
          · rcases performs_watching s id method _ _ key held with old | ⟨same, watch⟩
            · exact .inl old
            · exact .inr ⟨version, ready, same, watch⟩
          · exact .inl held
        · exact .inl held
    · exact .inl held

/-- **A watch opens only by its request**, `session/screen` or `session/history`, in a ready
connection. -/
theorem step_watch_opens (s : State) (ev : Event) (id : Id)
    (held : ((step s ev).1.watching id).isSome) :
    (s.watching id).isSome ∨
      ∃ params version,
        s.phase = .ready version ∧
          (ev = .received (.request id "session/screen" params) ∨
            ev = .received (.request id "session/history" params)) := by
  cases ev with
  | received message =>
    cases message with
    | invalid id' unparsed => exact .inl held
    | notification method params =>
      simp only [step] at held
      split at held
      · split at held <;> exact .inl held
      · exact .inl held
    | request id' method params =>
      simp only [step] at held
      rcases request_watching s id' method params id held with old | ⟨version, ready, rfl, watch⟩
      · exact .inl old
      · rcases watch with rfl | rfl
        · exact .inr ⟨params, version, ready, .inl rfl⟩
        · exact .inr ⟨params, version, ready, .inr rfl⟩
  | opened id' records =>
    simp only [step] at held
    split at held
    · split at held <;> exact .inl held
    · exact .inl held
  | sampled records =>
    simp only [step] at held
    split at held
    · split at held <;> exact .inl held
    · exact .inl held
  | writable =>
    simp only [step] at held
    split at held <;> exact .inl held
  | watched id' screen left =>
    simp only [step] at held
    rw [watched_watching] at held
    exact .inl held
  | flush id' =>
    simp only [step] at held
    rw [flushed_watching] at held
    exact .inl held
  | unwatched id' found said =>
    simp only [step] at held
    exact .inl (unwatched_watching s id' found said id held)

/-- **A `sessions/unsubscribe` of a watch closes it.** -/
theorem unsubscribe_closes_watch (s : State) (id asked : Id) (params : Json) (version : String)
    (ready : s.phase = .ready version) (held : (s.watching id).isSome)
    (names : params.member? "subscription" = some id.json) :
    (step s (.received (.request asked "sessions/unsubscribe" params))).1.watching id = none := by
  simp only [step, request, ready]
  simp only [unsubscribe, names, Option.bind_some, Id.of_json, held, or_true, ↓reduceIte]
  simp [dropWatch_watching]

/-- **What a free writer sends the subscriber**: `sessions/changed`, exactly when the latest
records differ from what it last told the subscriber, with the records that differ and the keys
that went; then it has told the latest. -/
theorem step_writable (s : State) (version : String) (id : Id) (told latest : List Record)
    (ready : s.phase = .ready version) (subscribed : s.subscription = some id)
    (was : s.told = some told) (now : s.latest = some latest) :
    (step s .writable).2 =
        (if changes told latest = [] ∧ removed told latest = [] then []
        else
          [.send
              (.notify "sessions/changed"
                (update id (changes told latest) (removed told latest)))]) ∧
      (step s .writable).1.subscription = some id ∧
      (step s .writable).1.told = some latest ∧ (step s .writable).1.latest = some latest := by
  obtain ⟨stage, open?, toldRecords, latestRecords, watches⟩ := s
  simp only [State.phase, State.subscription, State.told, State.latest] at ready subscribed was now
  subst ready subscribed was now
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The subscription's own listing is the table its subscriber first holds.** -/
theorem step_opened (s : State) (version : String) (id : Id) (records : List Record)
    (ready : s.phase = .ready version) (subscribed : s.subscription = some id) :
    (step s (.opened id records)).2 = [] ∧
      (step s (.opened id records)).1.told = some records ∧
      (step s (.opened id records)).1.latest = some records := by
  simp [step, ready, subscribed, State.told, State.latest]

/-- **A later listing sends nothing and replaces the latest records**, keeping what the
subscriber was told. -/
theorem step_sampled (s : State) (version : String) (id : Id) (told records : List Record)
    (ready : s.phase = .ready version) (subscribed : s.subscription = some id)
    (was : s.told = some told) :
    (step s (.sampled records)).2 = [] ∧
      (step s (.sampled records)).1.subscription = some id ∧
      (step s (.sampled records)).1.told = some told ∧
      (step s (.sampled records)).1.latest = some records := by
  obtain ⟨stage, open?, toldRecords, latestRecords, watches⟩ := s
  simp only [State.phase, State.subscription, State.told] at ready subscribed was
  subst ready subscribed was
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## A watch's table and log -/

/-- **A screen's first look answers its request with the screen**, which its subscriber then
holds. -/
theorem watched_screen_opens (s : State) (version : String) (id : Id) (screen : Screen)
    (left : Log Line) (ready : s.phase = .ready version)
    (asked : s.watching id = some (.asked false)) :
    (step s (.watched id screen left)).2 = [.send (.result id (result .done screen.members))] ∧
      (step s (.watched id screen left)).1.watching id = some (.screen screen screen) := by
  refine ⟨?_, ?_⟩ <;> simp [step, watched, ready, asked, setWatch_watching]

/-- **A screen's later look sends nothing and replaces its latest screen**, keeping what its
subscriber was told. -/
theorem watched_screen (s : State) (version : String) (id : Id) (told latest screen : Screen)
    (left : Log Line) (ready : s.phase = .ready version)
    (holds : s.watching id = some (.screen told latest)) :
    (step s (.watched id screen left)).2 = [] ∧
      (step s (.watched id screen left)).1.watching id = some (.screen told screen) := by
  refine ⟨?_, ?_⟩ <;> simp [step, watched, ready, holds, setWatch_watching]

/-- **What a free writer sends a screen's subscriber**: its changes, exactly when the latest look
differs from what the subscriber was told; then it has told the latest. -/
theorem flush_screen (s : State) (version : String) (id : Id) (told latest : Screen)
    (ready : s.phase = .ready version) (holds : s.watching id = some (.screen told latest)) :
    (step s (.flush id)).2 =
        (if told = latest then []
        else
          [.send
              (.notify "session/screen/changed" (Screen.update id (Screen.changes told latest)))]) ∧
      (step s (.flush id)).1.watching id = some (.screen latest latest) := by
  refine ⟨?_, ?_⟩ <;> simp [step, flushed, ready, holds, setWatch_watching]

/-- **A history's first look answers its request**, and keeps the lines that left since. -/
theorem watched_history_opens (s : State) (version : String) (id : Id) (screen : Screen)
    (left : Log Line) (ready : s.phase = .ready version)
    (asked : s.watching id = some (.asked true)) :
    (step s (.watched id screen left)).2 = [.send (.result id (result .done []))] ∧
      (step s (.watched id screen left)).1.watching id =
        some (.history (Log.append historyCap {} left)) := by
  refine ⟨?_, ?_⟩ <;> simp [step, watched, ready, asked, setWatch_watching]

/-- **A history's later look sends nothing and adds the lines that left to its log.** -/
theorem watched_history (s : State) (version : String) (id : Id) (pending : Log Line)
    (screen : Screen) (left : Log Line) (ready : s.phase = .ready version)
    (holds : s.watching id = some (.history pending)) :
    (step s (.watched id screen left)).2 = [] ∧
      (step s (.watched id screen left)).1.watching id =
        some (.history (Log.append historyCap pending left)) := by
  refine ⟨?_, ?_⟩ <;> simp [step, watched, ready, holds, setWatch_watching]

/-- **What a free writer sends a history's subscriber**: its log since the last update, when it
holds a line or a drop; then it holds none. -/
theorem flush_history (s : State) (version : String) (id : Id) (pending : Log Line)
    (ready : s.phase = .ready version) (holds : s.watching id = some (.history pending)) :
    (step s (.flush id)).2 =
        (if pending.tail = [] ∧ pending.dropped = 0 then []
        else [.send (.notify "session/history/changed" (Log.update id pending))]) ∧
      (step s (.flush id)).1.watching id = some (.history {}) := by
  refine ⟨?_, ?_⟩ <;> simp [step, flushed, ready, holds, setWatch_watching]

/-- The first record under a key that a filter keeps, of records no two of which share a key:
the first under it, if the filter keeps it. -/
theorem find_filter_keyed (keep : Record → Bool) (key : String) :
    ∀ (records : List Record),
      (records.map Record.key).Nodup →
        (records.filter keep).find? (·.key == key) = (records.find? (·.key == key)).filter keep
  | [], _ => rfl
  | record :: rest, keyed => by
    simp only [List.map_cons, List.nodup_cons] at keyed
    obtain ⟨fresh, keyed⟩ := keyed
    have ih := find_filter_keyed keep key rest keyed
    by_cases here : record.key = key
    · have later : rest.find? (·.key == key) = none := by
        rw [List.find?_eq_none]
        intro other member same
        apply fresh
        exact
          List.mem_map.mpr
            ⟨other, member, by
              simp at same; rw [same, here]⟩
      rw [later] at ih
      by_cases kept : keep record = true
      · simp [kept, here, Option.filter]
      · simp [kept, here, ih, Option.filter]
    · by_cases kept : keep record = true
      · simp [kept, here, ih]
      · simp [kept, here, ih]

/-- **An update brings a view to the latest records**: applying the records that differ from
`told` and the keys that went gives, under every key, the latest record, read without the clock,
when no two latest records share a key. -/
theorem View.converges (told latest : List Record) (keyed : (latest.map Record.key).Nodup)
    (key : String) :
    (View.apply (View.of told) (changes told latest) (removed told latest) key).map Record.reading =
      (View.of latest key).map Record.reading := by
  unfold View.apply View.of changes
  rw [find_filter_keyed _ key latest keyed]
  split
  · rename_i gone
    have none : latest.find? (·.key == key) = none := by
      simp only [removed, List.contains_iff_mem, List.mem_filter, Bool.not_eq_true',
        List.any_eq_false] at gone
      rw [List.find?_eq_none]
      intro record member same
      exact absurd same (by simpa using gone.2 record member)
    rw [none]
  · rename_i gone
    cases found : latest.find? (·.key == key) with
    | none =>
      have untold : told.find? (·.key == key) = none := by
        rw [List.find?_eq_none]
        intro record member same
        apply gone
        simp only [removed, List.contains_iff_mem, List.mem_filter, List.mem_map, Bool.not_eq_true',
          List.any_eq_false]
        refine ⟨⟨record, member, by simpa using same⟩, fun other inLatest hit => ?_⟩
        rw [List.find?_eq_none] at found
        exact found other inLatest hit
      simp [untold]
    | some
      latestRecord =>
      have sameKey : latestRecord.key = key := by simpa using List.find?_some found
      by_cases differs :
        ((told.find? (·.key == latestRecord.key)).map Record.reading != some latestRecord.reading) =
          true
      · simp [Option.filter, differs]
      · simp only [Option.filter, differs, Bool.false_eq_true, ↓reduceIte, Option.none_or]
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at differs
        rw [sameKey] at differs
        rw [differs]
        rfl

/-- Pushing onto a log within its cap: its tail with the entry, less the first when it held as
many as its cap already, which it counts. -/
theorem Log.push_fits {α : Type} (cap : Nat) (log : Log α) (entry : α)
    (fits : log.tail.length ≤ cap) :
    (Log.push cap log entry).tail = (log.tail ++ [entry]).drop (log.tail.length + 1 - cap) ∧
      (Log.push cap log entry).dropped = log.dropped + (log.tail.length + 1 - cap) := by
  unfold Log.push
  split
  · rename_i room
    simp only [List.length_append, List.length_singleton] at room
    simp [Nat.sub_eq_zero_of_le room]
  · rename_i full
    simp only [List.length_append, List.length_singleton] at full
    have one : log.tail.length + 1 - cap = 1 := by omega
    simp [one]

/-- **A log keeps the last entries, at most its cap, and counts the ones before them.** -/
theorem Log.fold_push {α : Type} (cap : Nat) :
    ∀ (entries : List α) (log : Log α),
      log.tail.length ≤ cap →
        (entries.foldl (Log.push cap) log).tail =
            (log.tail ++ entries).drop ((log.tail ++ entries).length - cap) ∧
          (entries.foldl (Log.push cap) log).dropped =
            log.dropped + ((log.tail ++ entries).length - cap)
  | [], log, fits => by simp [Nat.sub_eq_zero_of_le fits]
  | entry :: rest, log, fits => by
    obtain ⟨tail, dropped⟩ := Log.push_fits cap log entry fits
    have fits' : (Log.push cap log entry).tail.length ≤ cap := by
      rw [tail, List.length_drop, List.length_append, List.length_singleton]
      omega
    obtain ⟨ih₁, ih₂⟩ := Log.fold_push cap rest (Log.push cap log entry) fits'
    have pushed :
      (Log.push cap log entry).tail ++ rest =
        (log.tail ++ entry :: rest).drop (log.tail.length + 1 - cap) := by
      rw [tail, show log.tail ++ entry :: rest = (log.tail ++ [entry]) ++ rest by simp,
        List.drop_append_of_le_length (l₁ := log.tail ++ [entry])
          (by
            rw [List.length_append, List.length_singleton]; omega)]
    have size :
      ((Log.push cap log entry).tail ++ rest).length =
        log.tail.length + 1 + rest.length - (log.tail.length + 1 - cap) := by
      rw [pushed, List.length_drop, List.length_append, List.length_cons]
      omega
    simp only [List.foldl_cons]
    refine ⟨?_, ?_⟩
    · rw [ih₁, pushed, List.drop_drop, ← pushed, size, List.length_append, List.length_cons]
      congr 1
      omega
    · rw [ih₂, dropped, size, List.length_append, List.length_cons]
      omega

end Linger.App.Serve
