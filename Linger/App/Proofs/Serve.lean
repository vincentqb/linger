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

/-- The result of a request that did what was asked is no `initialize` result. -/
theorem result_done_ne_welcome (version linger : String) :
    result .done [] ≠ welcome version linger := by simp [result, answerMembers, welcome]

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
      · split <;> exact .inl rfl
      · split
        · split
          · split <;> exact .inl rfl
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

/-- **Before it is ready, a connection writes nothing but errors and `initialize`'s result, and
performs nothing.** -/
theorem step_negotiating (s : State) (ev : Event) (notReady : ∀ version, s.phase ≠ .ready version) :
    ∀ e ∈ (step s ev).2, e.Negotiating := by
  obtain ⟨stage, open?, told, latest⟩ := s
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
          · split at sent
            · simp only [List.mem_singleton, Effect.send.injEq, Outgoing.result.injEq] at sent
              exact absurd sent.2.symm (result_done_ne_welcome version linger)
            · simp at sent
          · split at sent
            · split at sent <;> simp at sent
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
      · split
        · split <;> simp [Effect.Answers]
        · simp [Effect.Answers]
    · simp [Effect.Answers, notInitialized]

/-- **A connection's one notification, `sessions/changed`, names the subscription open.** -/
theorem step_notify_open (s : State) (ev : Event) :
    ∀ e ∈ (step s ev).2,
      ∀ method params,
        e = .send (.notify method params) →
          method = "sessions/changed" ∧
            ∃ id, s.subscription = some id ∧ params.member? "subscription" = some id.json := by
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
      repeat' split at sent
      all_goals simp [notInitialized] at sent
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
        exact ⟨rfl, id, subscribed, by simp [update, Json.member?]⟩
    · simp at sent

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
      · split
        · exact .inr (.inl rfl)
        · exact .inl rfl
      · split
        · split
          · split
            · rename_i subscribe
              exact .inr (.inr ⟨version, ready, subscribe, rfl⟩)
            · exact .inl rfl
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

/-- **A `sessions/subscribe` in a ready connection opens its subscription**, named by its id. -/
theorem subscribe_opens (s : State) (id : Id) (params : Json) (version : String)
    (ready : s.phase = .ready version) :
    (step s (.received (.request id "sessions/subscribe" params))).1.subscription = some id := by
  simp [step, request, ready, parse_subscribe, methods, State.subscription]

/-- **A `sessions/unsubscribe` of the subscription open closes it.** -/
theorem unsubscribe_closes (s : State) (id asked : Id) (params : Json) (version : String)
    (ready : s.phase = .ready version) (subscribed : s.subscription = some id)
    (names : params.member? "subscription" = some id.json) :
    (step s (.received (.request asked "sessions/unsubscribe" params))).1.subscription = none := by
  simp only [step, request, ready]
  rw [subscribed]
  simp [names, Id.of_json, State.subscription]

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
  obtain ⟨stage, open?, toldRecords, latestRecords⟩ := s
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
  obtain ⟨stage, open?, toldRecords, latestRecords⟩ := s
  simp only [State.phase, State.subscription, State.told] at ready subscribed was
  subst ready subscribed was
  exact ⟨rfl, rfl, rfl, rfl⟩

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
