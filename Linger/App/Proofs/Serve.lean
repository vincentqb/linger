module

public import Linger.App.CoreSpec
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Serve
import all Linger.App.CoreCode.Api
import all Linger.App.CoreCode.Commands
import all Linger.App.Proofs.Api
import all Linger.App.CoreCode.Codec
public import Linger.App.Proofs.Codec

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

open ExactJSON (Value toValue)

/-- **A method's request is its command line's.** -/
theorem parse_eq (method : String) (params : Value) :
    parse method params =
      (Call.read method params).bind fun call =>
        (Api.parse call.words).bind fun request =>
          call.input.map fun bytes => (request, bytes) := rfl

/-- Each method's command word names the method's operation. -/
theorem methods_words : ∀ e ∈ methods, (Commands.lookup e.2.2.1).map (·.op) = some e.2.1 := by
  decide

/-- A call's params read as the call they write. -/
theorem Call.read_params (call : Call) : Call.read call.method call.params = some call := by
  cases call <;> simp only [Call.read, Call.method, Call.params] <;> simp <;>
    first
    | exact (exactly_iff _ _).mpr (toValue_attaching _)
    | exact (exactly_iff _ _).mpr (toValue_capturing _)
    | exact (exactly_iff _ _).mpr (toValue_listed _)
    | exact (exactly_iff _ _).mpr (toValue_named _)
    | exact (exactly_iff _ _).mpr (toValue_noParams _)
    | exact (exactly_iff _ _).mpr (toValue_renaming _)
    | exact (exactly_iff _ _).mpr (toValue_resizing _)
    | exact (exactly_iff _ _).mpr (toValue_sending _)
    | exact (exactly_iff _ _).mpr (toValue_starting _)
    | exact ⟨_, (exactly_iff _ _).mpr (toValue_noParams _)⟩

/-- What a call is read from: its method, and exactly its params. -/
theorem Call.read_eq {method : String} {params : Value} {call : Call}
    (read : Call.read method params = some call) : call.method = method ∧ call.params = params := by
  unfold Call.read at read
  by_cases h0 : method = "sessions/list"
  · subst h0
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_listed p).symm⟩
  simp only [h0, ↓reduceIte] at read
  by_cases h1 : method = "sessions/subscribe"
  · subst h1
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_noParams p).symm⟩
  simp only [h1, ↓reduceIte] at read
  by_cases h2 : method = "session/screen"
  · subst h2
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_named p).symm⟩
  simp only [h2, ↓reduceIte] at read
  by_cases h3 : method = "session/history"
  · subst h3
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_named p).symm⟩
  simp only [h3, ↓reduceIte] at read
  by_cases h4 : method = "session/attach"
  · subst h4
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_attaching p).symm⟩
  simp only [h4, ↓reduceIte] at read
  by_cases h5 : method = "session/start"
  · subst h5
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_starting p).symm⟩
  simp only [h5, ↓reduceIte] at read
  by_cases h6 : method = "session/resume"
  · subst h6
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_named p).symm⟩
  simp only [h6, ↓reduceIte] at read
  by_cases h7 : method = "session/send"
  · subst h7
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_sending p).symm⟩
  simp only [h7, ↓reduceIte] at read
  by_cases h8 : method = "session/detach"
  · subst h8
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_named p).symm⟩
  simp only [h8, ↓reduceIte] at read
  by_cases h9 : method = "session/kill"
  · subst h9
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_named p).symm⟩
  simp only [h9, ↓reduceIte] at read
  by_cases h10 : method = "session/rename"
  · subst h10
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_renaming p).symm⟩
  simp only [h10, ↓reduceIte] at read
  by_cases h11 : method = "session/capture"
  · subst h11
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_capturing p).symm⟩
  simp only [h11, ↓reduceIte] at read
  by_cases h12 : method = "session/resize"
  · subst h12
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_resizing p).symm⟩
  simp only [h12, ↓reduceIte] at read
  by_cases h13 : method = "session/wait"
  · subst h13
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_named p).symm⟩
  simp only [h13, ↓reduceIte] at read
  by_cases h14 : method = "session/upgrade"
  · subst h14
    simp only [↓reduceIte] at read
    obtain ⟨p, exact, rfl⟩ := Option.map_eq_some_iff.mp read
    exact ⟨rfl, ((exactly_iff params p).mp exact) ▸ (toValue_named p).symm⟩
  simp only [h14, ↓reduceIte] at read
  cases read

/-- **A method's params are exactly a call's**: they read as a call just when it is a call of the
method whose params they are. -/
theorem Call.read_iff (method : String) (params : Value) (call : Call) :
    Call.read method params = some call ↔ call.method = method ∧ call.params = params := by
  constructor
  · exact Call.read_eq
  · rintro ⟨rfl, rfl⟩
    exact Call.read_params call

/-- **A method's request is its params' call's command line's**: it reads just when the params are
exactly those of a call of the method whose command line reads as the request, with the call's
standard input. -/
theorem parse_iff (method : String) (params : Value) (request : Api.Request) (bytes : List UInt8) :
    parse method params = some (request, bytes) ↔
      ∃ call : Call,
        call.method = method ∧
          call.params = params ∧ Api.parse call.words = some request ∧ call.input = some bytes := by
  constructor
  · intro parsed
    simp only [parse, Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at parsed
    obtain ⟨call, read, request', parsedWords, bytes', input, rfl, rfl⟩ := parsed
    obtain ⟨methodIs, paramsAre⟩ := Call.read_eq read
    exact ⟨call, methodIs, paramsAre, parsedWords, input⟩
  · rintro ⟨call, rfl, rfl, parsedWords, input⟩
    simp [parse, Call.read_params, parsedWords, input]

/-- The method a call names is one `methods` lists, with its command word. -/
theorem Call.words_head (call : Call) :
    ∃ op shape, methods.lookup call.method = some (op, call.words.headD "", shape) := by
  cases call <;> exact ⟨_, _, rfl⟩

/-- **A method is one operation**: the request its params parse to is of its operation. -/
theorem parse_op {method : String} {params : Value} {request : Api.Request} {bytes : List UInt8}
    (parsed : parse method params = some (request, bytes)) :
    (methods.lookup method).map (·.1) = some request.op := by
  obtain ⟨call, rfl, -, parsedWords, -⟩ := (parse_iff method params request bytes).mp parsed
  obtain ⟨op, shape, found⟩ := Call.words_head call
  have byWord := Api.parse_op parsedWords
  obtain ⟨before, after, split, -⟩ := List.lookup_eq_some_iff.mp found
  have member : (call.method, op, call.words.headD "", shape) ∈ methods := by simp [split]
  have named := methods_words _ member
  simp only [found, Option.map_some, Option.some.injEq]
  simp only at named
  rw [named] at byWord
  exact Option.some.inj byWord

/-- **A result is the command line's answer**, by name and code, then what the request shows. -/
theorem result_eq (found : Api.Found) (shows : Shows) :
    result found shows =
      Result.json
        { toShows := shows, answer := answerName (Api.answer found),
          code := (Api.answer found).code.toNat } := toValue_result _

/-- **A line that is not canonical JSON is no message**, with ExactJSON's reason. -/
theorem decode_uncanonical {line reason : String}
    (refused : ExactJSON.Value.parse line = .error reason) :
    decode line = .invalid none (some reason) := by simp [decode, refused]

/-- **A line that is not canonical JSON is answered -32700**, its `data` the usage answer and the
reader's reason, and changes nothing. -/
theorem step_uncanonical (s : State) (reason : String) :
    step s (.received (.invalid none (some reason))) =
      (s,
        [.send
            (.error none (-32700) "parse error"
              (Result.json
                { answer := answerName .usage, code := (Os.Answer.code .usage).toNat,
                  reason? := some reason }))]) := by
  simp only [step, refusal, answered, toValue_result]

/-- A connection starts before its handshake. -/
theorem init_phase : State.init.phase = .fresh := rfl

/-- `sessions/subscribe` takes no params: it lists every session, as records. -/
theorem parse_subscribe :
    parse "sessions/subscribe" (NoParams.json {}) = some (.list (.every true none), []) := by
  rw [show NoParams.json {} = Call.params (.subscribe {}) from rfl]
  simp only [parse, show "sessions/subscribe" = Call.method (.subscribe {}) from rfl,
    Call.read_params]
  rfl

/-- An id as JSON reads back as the id. -/
theorem Id.of_json (id : Id) : Id.of id.json = some id := by cases id <;> rfl

/-- No result is `initialize`'s: a result begins with its answer, `initialize`'s with its
capabilities. -/
theorem result_ne_welcome (found : Api.Found) (shows : Shows) (version linger : String) :
    result found shows ≠ welcome version linger := by
  rw [result_eq]
  simp [Result.json, welcome, Welcome.json]

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

/-- A read of an attach's connection sets or drops the attach and nothing else. -/
theorem streamed_eq (s : State) (id : Id) (dec : Session.Wire.Decoder)
    (pending bytes : List UInt8) :
    ∃ ws, (streamed s id dec pending bytes).1 = { s with watches := ws } := by
  simp only [streamed]
  split
  · exact dropWatch_eq _ _
  · split
    · exact dropWatch_eq _ _
    · exact setWatch_eq _ _ _

/-- A read of an attach's connection, as a connection takes it, sets or drops the attach and
nothing else. -/
theorem readAttach_eq (s : State) (id : Id) (bytes : List UInt8) :
    ∃ ws, (readAttach s id bytes).1 = { s with watches := ws } := by
  unfold readAttach
  split
  · exact streamed_eq _ _ _ _ _
  · exact streamed_eq _ _ _ _ _
  · exact ⟨s.watches, rfl⟩

/-- A read of an attach's connection holds a watch under an id only where the connection held
one. -/
theorem streamed_watching (s : State) (id : Id) (dec : Session.Wire.Decoder)
    (pending bytes : List UInt8) (key : Id)
    (held : ((streamed s id dec pending bytes).1.watching key).isSome) :
    (s.watching key).isSome := by
  simp only [streamed] at held
  split at held
  · rw [dropWatch_watching] at held
    split at held
    · simp at held
    · exact held
  · split at held
    · rw [dropWatch_watching] at held
      split at held
      · simp at held
      · exact held
    · rw [setWatch_watching] at held
      split at held
      · simpa using held
      · exact held

/-- A read of an attach's connection, as a connection takes it, holds a watch under an id only
where the connection held one. -/
theorem read_watching (s : State) (id : Id) (bytes : List UInt8) (key : Id)
    (held : ((readAttach s id bytes).1.watching key).isSome) : (s.watching key).isSome := by
  unfold readAttach at held
  split at held
  · exact streamed_watching s id {} [] bytes key held
  · exact streamed_watching s id _ _ bytes key held
  · exact held

/-! ## Requests -/

/-- `sessions/unsubscribe` leaves the handshake as it was. -/
theorem unsubscribe_stage (s : State) (id : Id) (params : Value) :
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

/-- A request of an attach's conversation drops the attach, or nothing, and changes nothing
else. -/
theorem converse_eq (s : State) (id : Id) (method : String) (params : Value) :
    ∃ ws, (converse s id method params).1 = { s with watches := ws } := by
  unfold converse
  split
  · exact ⟨s.watches, rfl⟩
  · split
    · split
      · exact dropWatch_eq _ _
      · exact ⟨s.watches, rfl⟩
    · split
      · exact dropWatch_eq _ _
      · exact ⟨s.watches, rfl⟩
    · exact ⟨s.watches, rfl⟩

/-- What a request does to the handshake: nothing, but an `initialize` before it, answered. -/
theorem request_stage (s : State) (id : Id) (method : String) (params : Value) :
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
      · rename_i asked _
        split
        · exact .inr ⟨asked.protocolVersion, fresh, isInitialize, rfl⟩
        · exact .inl rfl
      · exact .inl rfl
    · exact .inl rfl
  · split
    · split
      · exact .inl (unsubscribe_stage s id params)
      · split
        · obtain ⟨ws, same⟩ := converse_eq s id method params
          exact .inl (by rw [same])
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
  | read id bytes =>
    left
    obtain ⟨ws, same⟩ := readAttach_eq s id bytes
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
          · split
            · intro e sent
              simp only [List.mem_singleton] at sent
              subst sent
              exact ⟨_, _, toValue_welcome _⟩
            · simp [Effect.Negotiating]
          · simp [Effect.Negotiating]
        · simp [Effect.Negotiating, notInitialized]
    | opened id records => simp [step, State.phase]
    | sampled records => simp [step, State.phase]
    | writable => simp [step, State.phase]
    | watched id screen left => simp [step, watched, State.phase]
    | flush id => simp [step, flushed, State.phase]
    | unwatched id found said => simp [step, unwatched, State.phase]
    | read id bytes => simp [step, readAttach, State.phase]
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
    | read id bytes => simp [step, readAttach, State.phase]

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
theorem unsubscribe_sends (s : State) (id : Id) (params : Value) :
    ∀ e ∈ (unsubscribe s id params).2,
      (∃ key found shows, e = .send (.result key (result found shows))) ∨
        ∃ code message data, e = .send (.error (some id) code message data) := by
  unfold unsubscribe
  split
  · split
    · intro e sent
      simp only [List.mem_append, List.mem_singleton] at sent
      rcases sent with sent | sent
      · split at sent
        all_goals
          first
          | ( simp only [List.mem_singleton] at sent
              exact .inl ⟨_, _, _, sent⟩)
          | simp at sent
      · exact .inl ⟨_, _, _, sent⟩
    · simp
  · simp

/-- What a request of an attach's conversation sends: results, errors, and the messages it relays
to the attach its params name, an attach open. -/
theorem converse_sends (s : State) (id : Id) (method : String) (params : Value) :
    ∀ e ∈ (converse s id method params).2,
      (∃ key found shows, e = .send (.result key (result found shows))) ∨
        (∃ code message data, e = .send (.error (some id) code message data)) ∨
        ∃ key messages decoder pending,
          e = .relay key messages ∧ s.watching key = some (.stream decoder pending) := by
  unfold converse
  split
  · simp
  · rename_i key _ _
    split
    · split
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro e (sent | sent) <;> exact .inl ⟨_, _, _, sent⟩
      · simp
    · rename_i decoder pending holds
      split
      · simp only [List.mem_singleton]
        intro e sent
        exact .inl ⟨_, _, _, sent⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro e (sent | sent)
        · exact .inr (.inr ⟨key, _, decoder, pending, sent, holds⟩)
        · exact .inl ⟨_, _, _, sent⟩
    · simp

/-- What a performed request sends: its result, or that it is performed. -/
theorem performs_sends (s : State) (id : Id) (method : String) (req : Api.Request)
    (bytes : List UInt8) :
    ∀ e ∈ (performs s id method req bytes).2,
      (∃ found shows, e = .send (.result id (result found shows))) ∨
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
      ∃ found shows, e = .send (.result id (result found shows)) := by
  unfold watched
  split
  all_goals simp only [List.mem_singleton, List.not_mem_nil, false_imp_iff, implies_true]
  all_goals
    intro e sent
    exact ⟨_, _, sent⟩

/-- An update of an attach's stream names its subscription, closed or not. -/
theorem output_update_names (id : Id) (bytes : List UInt8) (closed : Option Result) :
    member? "subscription" (Output.update id bytes closed) = some id.json := by
  cases closed <;> simp [Output.update, toValue_output, Output.json, member?, optional, List.lookup]

/-- What a read of an attach's connection sends: the stream's updates, each naming the attach. -/
theorem streamed_sends (s : State) (id : Id) (dec : Session.Wire.Decoder)
    (pending bytes : List UInt8) :
    ∀ e ∈ (streamed s id dec pending bytes).2,
      ∃ params,
        e = .send (.notify "session/output" params) ∧
          member? "subscription" params = some id.json := by
  simp only [streamed]
  split
  · simp only [List.mem_singleton]
    intro e sent
    exact ⟨_, sent, output_update_names _ _ _⟩
  · split
    · simp only [List.mem_singleton]
      intro e sent
      exact ⟨_, sent, output_update_names _ _ _⟩
    · simp

/-- What a read of an attach's connection, as a connection takes it, sends: the first answers the
attach's request `done`, and each sends the stream's updates, each naming the attach. -/
theorem read_sends (s : State) (id : Id) (bytes : List UInt8) :
    ∀ e ∈ (readAttach s id bytes).2,
      e = .send (.result id (result .done {})) ∨
        ∃ params,
          e = .send (.notify "session/output" params) ∧
            member? "subscription" params = some id.json := by
  unfold readAttach
  split
  · simp only [List.mem_cons]
    rintro e (sent | sent)
    · exact .inl sent
    · exact .inr (streamed_sends s id {} [] bytes e sent)
  · intro e sent
    exact .inr (streamed_sends s id _ _ bytes e sent)
  · simp

/-- A read of an attach's connection sends something only for an attach the connection holds. -/
theorem read_holds (s : State) (id : Id) (bytes : List UInt8)
    (sends : (readAttach s id bytes).2 ≠ []) :
    s.watching id = some .attaching ∨
      ∃ decoder pending, s.watching id = some (.stream decoder pending) := by
  unfold readAttach at sends
  split at sends
  · rename_i holds
    exact .inl holds
  · rename_i decoder pending _ holds
    exact .inr ⟨decoder, pending, holds⟩
  · simp at sends

/-- The welcome of one version is no other version's. -/
theorem welcome_version {version version' linger linger' : String}
    (same : (Welcome.of version linger).json = welcome version' linger') : version = version' := by
  simp [welcome, Welcome.json, Welcome.of] at same
  exact same.1

/-- **`initialize`'s result goes only to `initialize`, with the version the client asked for**,
one `serve` speaks. -/
theorem step_welcome (s : State) (ev : Event) (id : Id) (version linger : String)
    (sent : Effect.send (.result id (welcome version linger)) ∈ (step s ev).2) :
    version ∈ versions ∧
      ∃ params : Initialize,
        ev = .received (.request id "initialize" params.json) ∧
          params.protocolVersion = version := by
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
          · rename_i asked exact
            split at sent
            · rename_i speaks
              simp only [List.mem_singleton, Effect.send.injEq, Outgoing.result.injEq] at sent
              obtain ⟨rfl, same⟩ := sent
              rw [toValue_welcome] at same
              obtain rfl := welcome_version same
              refine ⟨speaks, asked, ?_, rfl⟩
              rw [isInitialize, ← toValue_initialize, (exactly_iff params asked).mp exact]
            · simp at sent
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
            · rcases converse_sends s id' method params _ sent with ⟨_, found, members, same⟩ |
                ⟨_, _, _, same⟩ | ⟨_, _, _, _, same, -⟩
              · simp only [Effect.send.injEq, Outgoing.result.injEq] at same
                exact absurd same.2.symm (result_ne_welcome found members version linger)
              · simp at same
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
    · split at sent <;> simp at sent
    · simp at sent
  | unwatched id' found said =>
    simp only [step, unwatched] at sent
    split at sent
    all_goals
      first
      | ( simp only [List.mem_singleton, Effect.send.injEq, Outgoing.result.injEq] at sent
          exact absurd sent.2.symm (result_ne_welcome found _ version linger))
      | simp at sent
  | read id' bytes =>
    simp only [step] at sent
    rcases read_sends s id' bytes _ sent with same | ⟨_, same, -⟩
    · simp only [Effect.send.injEq, Outgoing.result.injEq] at same
      exact absurd same.2.symm (result_ne_welcome .done {} version linger)
    · simp at same

/-- **A request of an attach's conversation is answered.** -/
theorem converse_answers (s : State) (id : Id) (method : String) (params : Value) :
    ∃ e ∈ (converse s id method params).2, e.Answers id := by
  unfold converse
  split
  · simp [Effect.Answers]
  · split
    · split
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩
      · simp [Effect.Answers]
    · split
      · simp [Effect.Answers]
      · exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩
    · simp [Effect.Answers]

/-- **Every request is answered or performed.** -/
theorem step_answers (s : State) (id : Id) (method : String) (params : Value) :
    ∃ e ∈ (step s (.received (.request id method params))).2, e.Answers id := by
  simp only [step, request]
  split
  · split
    · split
      · split <;> simp [Effect.Answers]
      · simp [Effect.Answers]
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
        · exact converse_answers s id method params
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

/-- The sessions table's update is the one the spec states. -/
theorem changed_eq (id : Id) (records : List Record) (gone : List String) :
    changed id records gone = update id records gone := toValue_changed _

/-- A screen's update, until its last, is the one the spec states. -/
theorem Screen.changed_eq (id : Id) (u : Screen.Update) : Screen.changed id u = Screen.update id u :=
  toValue_screenChanged _

/-- A history's update, until its last, is the one the spec states. -/
theorem Log.changed_eq (id : Id) (log : Log Line) : Log.changed id log = Log.update id log :=
  toValue_historyChanged _

/-- An update's params name the subscription they update. -/
theorem update_names (id : Id) (records : List Record) (gone : List String) :
    member? "subscription" (changed id records gone) = some id.json := by
  simp [changed_eq, update, Changed.json, member?, List.lookup]

/-- A screen's update names its subscription, closed or not. -/
theorem screen_update_names (id : Id) (u : Screen.Update) (closed : Option Result) :
    member? "subscription" (Screen.changed id u closed) = some id.json := by
  simp only [Screen.changed, toValue_screenChanged, ScreenChanged.json, member?, optional]
  cases closed <;> cases u.cursor <;> simp [List.lookup]

/-- A history's update names its subscription, closed or not. -/
theorem log_update_names (id : Id) (log : Log Line) (closed : Option Result) :
    member? "subscription" (Log.changed id log closed) = some id.json := by
  simp only [Log.changed, toValue_historyChanged, HistoryChanged.json, member?, optional]
  cases closed <;> simp [List.lookup]

/-- **A connection's notifications name a subscription open**, of their kind: `sessions/changed`
the sessions table's, `session/screen/changed` a screen's and `session/history/changed` a
history's. -/
theorem step_notify_open (s : State) (ev : Event) :
    ∀ e ∈ (step s ev).2,
      ∀ method params,
        e = .send (.notify method params) →
          ∃ id,
            member? "subscription" params = some id.json ∧
              (method = "sessions/changed" ∧ s.subscription = some id ∨
                method = "session/screen/changed" ∧
                  (∃ told latest, s.watching id = some (.screen told latest)) ∨
                method = "session/history/changed" ∧
                  (∃ pending, s.watching id = some (.history pending)) ∨
                method = "session/output" ∧
                  (s.watching id = some .attaching ∨
                    ∃ decoder pending, s.watching id = some (.stream decoder pending))) := by
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
            · rcases converse_sends s id method' params' _ sent with ⟨_, _, _, same⟩ |
                ⟨_, _, _, same⟩ | ⟨_, _, _, _, same, -⟩
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
        exact ⟨id, (screen_update_names _ _ _), .inr (.inl ⟨rfl, told, latest, holds⟩)⟩
    · rename_i version pending _ holds
      split at sent
      · simp at sent
      · simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
        obtain ⟨rfl, rfl⟩ := sent
        exact ⟨id, (log_update_names _ _ _), .inr (.inr (.inl ⟨rfl, pending, holds⟩))⟩
    · rename_i version decoder pending _ holds
      split at sent
      · simp at sent
      · simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
        obtain ⟨rfl, rfl⟩ := sent
        exact
          ⟨id, (output_update_names _ _ _),
            .inr (.inr (.inr ⟨rfl, .inr ⟨decoder, pending, holds⟩⟩))⟩
    · simp at sent
  | unwatched id found said =>
    simp only [step, unwatched] at sent
    split at sent
    · simp at sent
    · simp at sent
    · rename_i version decoder pending _ holds
      simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
      obtain ⟨rfl, rfl⟩ := sent
      exact
        ⟨id, (output_update_names _ _ _),
          .inr (.inr (.inr ⟨rfl, .inr ⟨decoder, pending, holds⟩⟩))⟩
    · rename_i version told latest _ holds
      simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
      obtain ⟨rfl, rfl⟩ := sent
      exact ⟨id, (screen_update_names _ _ _), .inr (.inl ⟨rfl, told, latest, holds⟩)⟩
    · rename_i version pending _ holds
      simp only [List.mem_singleton, Effect.send.injEq, Outgoing.notify.injEq] at sent
      obtain ⟨rfl, rfl⟩ := sent
      exact ⟨id, (log_update_names _ _ _), .inr (.inr (.inl ⟨rfl, pending, holds⟩))⟩
    · simp at sent
  | read id bytes =>
    simp only [step] at sent
    rcases read_sends s id bytes _ sent with same | ⟨params', same, names⟩
    · simp at same
    · simp only [Effect.send.injEq, Outgoing.notify.injEq] at same
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨id, names, .inr (.inr (.inr ⟨rfl, read_holds s id bytes (List.ne_nil_of_mem sent)⟩))⟩

/-- What `sessions/unsubscribe` does to the subscription: nothing, or closes it. -/
theorem unsubscribe_open (s : State) (id : Id) (params : Value) :
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
theorem request_open (s : State) (id : Id) (method : String) (params : Value) :
    (request s id method params).1.open? = s.open? ∨
      (request s id method params).1.open? = none ∨
      ∃ version,
        s.phase = .ready version ∧
          method = "sessions/subscribe" ∧ (request s id method params).1.open? = some id := by
  unfold request
  split
  · split
    · split
      · split <;> exact .inl rfl
      · exact .inl rfl
    · exact .inl rfl
  · split
    · rename_i version ready
      split
      · rcases unsubscribe_open s id params with same | closed
        · exact .inl same
        · exact .inr (.inl closed)
      · split
        · obtain ⟨ws, same⟩ := converse_eq s id method params
          exact .inl (by rw [same])
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
  | read id' bytes =>
    obtain ⟨ws, same⟩ := readAttach_eq s id' bytes
    simp only [step, same] at opened
    exact .inl opened

/-- `sessions/subscribe` is no request of an attach's conversation. -/
theorem converses_subscribe (params : Value) : converses "sessions/subscribe" params = false := by
  simp [converses]

/-- `sessions/unsubscribe` is no request of an attach's conversation. -/
theorem converses_unsubscribe (params : Value) :
    converses "sessions/unsubscribe" params = false := by simp [converses]

/-- **A `sessions/subscribe` in a ready connection opens its subscription**, named by its id. -/
theorem subscribe_opens (s : State) (id : Id) (version : String)
    (ready : s.phase = .ready version) :
    (step s (.received (.request id "sessions/subscribe" (NoParams.json {})))).1.subscription =
      some id := by
  simp [step, request, ready, converses_subscribe, parse_subscribe, methods, performs,
    State.subscription]

/-- The params that name a subscription read as it. -/
theorem exactly_subscription (id : Id) :
    (exactly (Subscription.json ⟨id⟩) : Option Subscription) = some ⟨id⟩ :=
  (exactly_iff _ _).mpr (toValue_subscription _)

/-- **A `sessions/unsubscribe` of the subscription open closes it.** -/
theorem unsubscribe_closes (s : State) (id asked : Id) (version : String)
    (ready : s.phase = .ready version) (subscribed : s.subscription = some id) :
    (step s (.received (.request asked "sessions/unsubscribe" (Subscription.json ⟨id⟩)))).1.subscription =
      none := by
  simp only [step, request, ready]
  simp only [unsubscribe, exactly_subscription, subscribed, true_or, ↓reduceIte]
  obtain ⟨ws, same⟩ :=
    dropWatch_eq
      ({ s with
          open? := none, toldRecords := none, latestRecords := none } :
        State)
      id
  simp [same, State.subscription]

/-- What `sessions/unsubscribe` does to the watches: drops the one it names, or nothing. -/
theorem unsubscribe_watching (s : State) (id : Id) (params : Value) (key : Id)
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

/-- What a request of an attach's conversation does to the watches: drops the attach it names, or
nothing. -/
theorem converse_watching (s : State) (id : Id) (method : String) (params : Value) (key : Id)
    (held : ((converse s id method params).1.watching key).isSome) : (s.watching key).isSome := by
  unfold converse at held
  split at held
  · exact held
  · split at held
    · split at held
      · rw [dropWatch_watching] at held
        split at held
        · simp at held
        · exact held
      · exact held
    · split at held
      · rw [dropWatch_watching] at held
        split at held
        · simp at held
        · exact held
      · exact held
    · exact held

/-- What a performed request does to the watches: asks for one under its id, a watch's request, or
nothing. -/
theorem performs_watching (s : State) (id : Id) (method : String) (req : Api.Request)
    (bytes : List UInt8) (key : Id)
    (held : ((performs s id method req bytes).1.watching key).isSome) :
    (s.watching key).isSome ∨
      key = id ∧
        (method = "session/screen" ∨ method = "session/history" ∨ method = "session/attach") := by
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
theorem request_watching (s : State) (id : Id) (method : String) (params : Value) (key : Id)
    (held : ((request s id method params).1.watching key).isSome) :
    (s.watching key).isSome ∨
      ∃ version,
        s.phase = .ready version ∧
          key = id ∧
          (method = "session/screen" ∨ method = "session/history" ∨ method = "session/attach") := by
  unfold request at held
  split at held
  · split at held
    · split at held
      · split at held <;> exact .inl held
      · exact .inl held
    · exact .inl held
  · split at held
    · rename_i version ready
      split at held
      · exact .inl (unsubscribe_watching s id params key held)
      · split at held
        · exact .inl (converse_watching s id method params key held)
        · split at held
          · split at held
            · rcases performs_watching s id method _ _ key held with old | ⟨same, watch⟩
              · exact .inl old
              · exact .inr ⟨version, ready, same, watch⟩
            · exact .inl held
          · exact .inl held
    · exact .inl held

/-- **A watch opens only by its request**, `session/screen`, `session/history` or
`session/attach`, in a ready connection. -/
theorem step_watch_opens (s : State) (ev : Event) (id : Id)
    (held : ((step s ev).1.watching id).isSome) :
    (s.watching id).isSome ∨
      ∃ params version,
        s.phase = .ready version ∧
          (ev = .received (.request id "session/screen" params) ∨
            ev = .received (.request id "session/history" params) ∨
            ev = .received (.request id "session/attach" params)) := by
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
      · rcases watch with rfl | rfl | rfl
        · exact .inr ⟨params, version, ready, .inl rfl⟩
        · exact .inr ⟨params, version, ready, .inr (.inl rfl)⟩
        · exact .inr ⟨params, version, ready, .inr (.inr rfl)⟩
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
  | read id' bytes =>
    simp only [step] at held
    exact .inl (read_watching s id' bytes id held)

/-- **A `sessions/unsubscribe` of a watch closes it.** -/
theorem unsubscribe_closes_watch (s : State) (id asked : Id) (version : String)
    (ready : s.phase = .ready version) (held : (s.watching id).isSome) :
    (step s (.received (.request asked "sessions/unsubscribe" (Subscription.json ⟨id⟩)))).1.watching
        id =
      none := by
  simp only [step, request, ready]
  simp only [unsubscribe, exactly_subscription, held, or_true, ↓reduceIte]
  simp [dropWatch_watching]

/-- **A connection relays messages only to an attach open.** -/
theorem step_relays_open (s : State) (ev : Event) :
    ∀ e ∈ (step s ev).2,
      ∀ id messages,
        e = .relay id messages →
          ∃ decoder pending, s.watching id = some (.stream decoder pending) := by
  intro e sent id messages relayed
  subst relayed
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
      · repeat' split at sent
        all_goals simp at sent
      · split at sent
        · split at sent
          · rcases unsubscribe_sends s id' params _ sent with ⟨_, _, _, same⟩ | ⟨_, _, _, same⟩
            all_goals simp at same
          · split at sent
            · rcases converse_sends s id' method params _ sent with ⟨_, _, _, same⟩ |
                ⟨_, _, _, same⟩ | ⟨key, messages', decoder, pending, same, holds⟩
              · simp at same
              · simp at same
              · simp only [Effect.relay.injEq] at same
                obtain ⟨rfl, rfl⟩ := same
                exact ⟨decoder, pending, holds⟩
            · split at sent
              · split at sent
                · rcases performs_sends s id' method _ _ _ sent with ⟨_, _, same⟩ | same
                  all_goals simp at same
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
    obtain ⟨_, _, same⟩ := watched_sends s id' screen left _ sent
    simp at same
  | flush id' =>
    simp only [step, flushed] at sent
    split at sent
    all_goals
      first
      | (split at sent <;> simp at sent)
      | simp at sent
  | unwatched id' found said =>
    simp only [step, unwatched] at sent
    split at sent
    all_goals simp at sent
  | read id' bytes =>
    simp only [step] at sent
    rcases read_sends s id' bytes _ sent with same | ⟨_, same, -⟩
    all_goals simp at same

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
  exact ⟨by simp only [step, changed_eq]; rfl, rfl, rfl, rfl⟩

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
    (step s (.watched id screen left)).2 = [.send (.result id (result .done screen.shows))] ∧
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
  refine ⟨?_, ?_⟩ <;> simp [step, flushed, ready, holds, setWatch_watching, Screen.changed_eq]

/-- **A history's first look answers its request**, and keeps the lines that left since. -/
theorem watched_history_opens (s : State) (version : String) (id : Id) (screen : Screen)
    (left : Log Line) (ready : s.phase = .ready version)
    (asked : s.watching id = some (.asked true)) :
    (step s (.watched id screen left)).2 = [.send (.result id (result .done {}))] ∧
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
  refine ⟨?_, ?_⟩ <;> simp [step, flushed, ready, holds, setWatch_watching, Log.changed_eq]

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

/-! ## Params a method does not take -/

/-- **A request whose params are no call of its method is refused as invalid**, with linger's
usage answer, and changes nothing: params with a member the method does not define among them. -/
theorem step_refuses_params (s : State) (version : String) (id : Id) (method : String)
    (params : Value) (ready : s.phase = .ready version)
    (listed : (methods.lookup method).isSome = true)
    (plain :
      ¬(method = "session/resize" ∨ method = "session/detach") ∨
        member? "subscription" params = none)
    (undefined : ∀ call : Call, call.method = method → call.params ≠ params) :
    step s (.received (.request id method params)) =
      (s,
        [.send
            (.error (some id) (-32602) "invalid params"
              (Result.json
                { answer := answerName .usage, code := (Os.Answer.code .usage).toNat }))]) := by
  have notInitialize : method ≠ "initialize" := by
    rintro rfl
    simp [methods] at listed
  have notUnsubscribe : method ≠ "sessions/unsubscribe" := by
    rintro rfl
    simp [methods] at listed
  have notInput : method ≠ "session/input" := by
    rintro rfl
    simp [methods] at listed
  have plainRequest : converses method params = false := by
    unfold converses
    rcases plain with neither | none
    · simp only [not_or] at neither
      simp [notInput, neither.1, neither.2]
    · simp [notInput, none]
  have noCall : Call.read method params = none := by
    cases read : Call.read method params with
    | none => rfl
    | some call => exact absurd (Call.read_eq read).2 (undefined call (Call.read_eq read).1)
  have noParse : parse method params = none := by simp [parse, noCall]
  simp only [step, request, notInitialize, ↓reduceIte, ready, notUnsubscribe, plainRequest,
    Bool.false_eq_true, listed, noParse]
  simp only [refusal, answered, toValue_result]

end Linger.App.Serve
