module

public import Linger.App.CoreSpec
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Serve
import all Linger.Os.CoreCode.Answer
import all Linger.App.CoreCode.Api
import all Linger.App.CoreCode.Commands
import all Linger.App.CoreCode.Base64
import all Linger.App.CoreCode.Codec
public import Linger.App.Proofs.Codec
import Linger.Display.Proofs.Record
import all Linger.App.Proofs.Stream
import all Linger.App.Proofs.Serve
import all Linger.Session.Proofs.Wire
import all Linger.Session.CoreCode.Wire
import all Linger.Target.CoreCode.Remote
import Std.Data.String.ToNat

/-! # A remote host through `serve`: its answer is what it answered

A host's messages read as an answer exactly when it shook hands and answered the call with it, by
name and code, and as a refusal exactly when it refused `serve` with a usage answer; an answer's
name and code read back as exactly that answer; and a host's rows are its records whose names a
target takes, in order, each named `name@host`. -/

namespace Linger.App.Serve

open ExactJSON (Value toValue)

/-- **Whether a host shook hands is `Remote.Shook`.** -/
theorem Remote.shook_iff (messages : List Value) :
    Remote.shook messages = true ↔ Remote.Shook messages := by
  unfold Remote.shook Remote.Shook
  cases answered : Remote.answerOf messages 1 "result" with
  | none => simp
  | some result =>
    simp only [Option.bind_some, Option.some.injEq]
    cases read : (exactly result : Option Welcome) with
    | none =>
      simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
      intro welcome same _
      rw [same, (exactly_iff _ welcome).mpr (toValue_welcome welcome)] at read
      cases read
    | some welcome =>
      have written := (exactly_iff result welcome).mp read
      rw [toValue_welcome] at written
      constructor
      · intro speaks
        exact ⟨welcome, written.symm, by simpa [versions] using speaks⟩
      · rintro ⟨other, same, speaks⟩
        have : other = welcome := by
          rw [same, (exactly_iff _ other).mpr (toValue_welcome other)] at read
          exact Option.some.inj read
        subst this
        simpa [versions] using speaks

/-- **Whether a host refused `serve` with a usage answer is `Remote.Usage`.** -/
theorem Remote.usage_iff (messages : List Value) (status : UInt32) :
    Remote.usage messages status = true ↔ Remote.Usage messages status := by
  unfold Remote.usage Remote.Usage Remote.refusedUsage
  rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, Remote.shook_iff, Bool.or_eq_true,
    beq_iff_eq]
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  cases answered : Remote.answerOf messages 1 "error" with
  | none => simp
  | some error =>
    cases data : member? "data" error with
    | none => simp [data]
    | some value =>
      simp only [Option.bind_some, data]
      split <;> simp_all

/-- The code of a signal's answer is 128 plus the signal's number. -/
theorem signal_code (signal : UInt8) : (128 + signal.toUInt32).toNat = 128 + signal.toNat := by
  have small := signal.toNat_lt
  simp only [UInt32.toNat_add, UInt8.toNat_toUInt32]
  rw [show (128 : UInt32).toNat = 128 from rfl]
  omega

/-- **An answer's name and code read back as exactly that answer.** -/
theorem answerNamed_answerName (answer : Os.Answer) :
    answerNamed (answerName answer) answer.code.toNat = some answer := by
  cases answer with
  | stopped signal =>
    have small := signal.toNat_lt
    simp only [Linger.Os.Answer.code, signal_code]
    simp only [answerNamed, show 128 ≤ 128 + signal.toNat by omega,
      show 128 + signal.toNat < 384 by omega, and_self, ↓reduceIte,
      show 128 + signal.toNat < 4294967296 by omega, List.cons_append, List.nil_append,
      List.find?_cons]
    simp [answerName, Linger.Os.Answer.code, UInt8.ofNat_toNat,
      Nat.mod_eq_of_lt (show 128 + signal.toNat < 4294967296 by omega)]
  | saved signal =>
    have small := signal.toNat_lt
    simp only [Linger.Os.Answer.code, signal_code]
    simp only [answerNamed, show 128 ≤ 128 + signal.toNat by omega,
      show 128 + signal.toNat < 384 by omega, and_self, ↓reduceIte,
      show 128 + signal.toNat < 4294967296 by omega, List.cons_append, List.nil_append,
      List.find?_cons]
    simp [answerName, Linger.Os.Answer.code, UInt8.ofNat_toNat,
      Nat.mod_eq_of_lt (show 128 + signal.toNat < 4294967296 by omega)]
  | program status =>
    have small := status.toNat_lt
    simp only [Linger.Os.Answer.code]
    unfold answerNamed
    rw [List.find?_append, List.find?_append]
    have own :
      ([.done, .notDone, .usage, .timedOut, .failed, .cannotRun, .notFound, .cancelled] :
              List Os.Answer).find?
          (fun answer => answerName answer == "program" && answer.code.toNat == status.toNat) =
        none := by
      simp [answerName]
    have signals :
      ((if 128 ≤ status.toNat ∧ status.toNat < 384 then
                [Os.Answer.stopped (status.toNat - 128).toUInt8,
                  .saved (status.toNat - 128).toUInt8]
              else []) :
              List Os.Answer).find?
          (fun answer => answerName answer == "program" && answer.code.toNat == status.toNat) =
        none := by
      split <;> simp [answerName]
    simp only [answerName] at own signals ⊢
    rw [own, signals]
    simp [small, UInt32.ofNat_toNat, Nat.toUInt32, Linger.Os.Answer.code]
  | _ => rfl

/-- An answer `answerNamed` reads has the name and the code it was read of. -/
theorem answerNamed_eq_some {name : String} {code : Nat} {answer : Os.Answer}
    (read : answerNamed name code = some answer) :
    answerName answer = name ∧ answer.code.toNat = code := by
  unfold answerNamed at read
  have found := List.find?_some read
  simpa using found

/-- **An answer and what it shows read back as exactly a result that gives them**: one whose
`answer` and `code` are its name and code, and which shows what it shows. -/
theorem Remote.answerIn_eq_some (value : Value) (answer : Os.Answer) (shows : Shows) :
    Remote.answerIn value = some (answer, shows) ↔
      ∃ result : Result,
        value = result.json ∧
          result.answer = answerName answer ∧
          result.code = answer.code.toNat ∧ result.toShows = shows := by
  unfold Remote.answerIn
  constructor
  · intro read
    simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff, Prod.mk.injEq] at read
    obtain ⟨result, exact, found, named, rfl, rfl⟩ := read
    obtain ⟨nameIs, codeIs⟩ := answerNamed_eq_some named
    refine ⟨result, ?_, nameIs.symm, codeIs.symm, rfl⟩
    rw [← toValue_result, (exactly_iff value result).mp exact]
  · rintro ⟨result, rfl, named, coded, rfl⟩
    rw [show (exactly result.json : Option Result) = some result from
        (exactly_iff _ _).mpr (toValue_result result)]
    simp only [Option.bind_some, named, coded, answerNamed_answerName, Option.map_some]

/-- **A host's answer reads as an answer exactly when it shook hands and answered the call with
it.** -/
theorem Remote.heard_answered (messages : List Value) (status : UInt32) (answer : Os.Answer)
    (shows : Shows) :
    Remote.heard messages status = .answered answer shows ↔
      Remote.Shook messages ∧ Remote.Answered Linger.Os.Answer.code messages answer shows := by
  have bound :
    (Remote.callAnswer messages).bind Remote.answerIn = some (answer, shows) ↔
      ∃ result : Result,
        Remote.callAnswer messages = some result.json ∧
          result.answer = answerName answer ∧
          result.code = answer.code.toNat ∧ result.toShows = shows := by
    cases Remote.callAnswer messages with
    | none => simp
    | some value => simp only [Option.bind_some, Remote.answerIn_eq_some, Option.some.injEq]
  rw [← Remote.shook_iff]
  unfold Remote.Answered
  rw [show
      (Remote.answerOf messages 2 "result").or
          ((Remote.answerOf messages 2 "error").bind (member? "data")) =
        Remote.callAnswer messages
      from rfl,
    ← bound]
  unfold Remote.heard
  by_cases shook : Remote.shook messages = true
  · simp only [shook, ↓reduceIte, true_and]
    cases (Remote.callAnswer messages).bind Remote.answerIn with
    | none => simp
    | some pair =>
      obtain ⟨a, ms⟩ := pair
      simp [eq_comm]
  · simp only [shook, Bool.false_eq_true, ↓reduceIte, false_and, iff_false]
    split <;> simp

/-- **A host's answer reads as a refusal exactly when it refused `serve` with a usage answer.** -/
theorem Remote.heard_refused (messages : List Value) (status : UInt32) :
    Remote.heard messages status = .refused ↔ Remote.Usage messages status := by
  rw [← Remote.usage_iff]
  unfold Remote.heard
  split
  · rename_i shook
    have notUsage : Remote.usage messages status = false := by simp [Remote.usage, shook]
    rw [notUsage]
    split <;> simp
  · rename_i notShook
    split <;> simp_all

/-! ## A remote request is its host's -/

/-- `sessions/list`'s params read as its call. -/
theorem read_list (p : Listed) : Call.read "sessions/list" p.json = some (.list p) :=
  Call.read_params (.list p)

/-- `sessions/subscribe`'s params read as its call. -/
theorem read_subscribe (p : NoParams) : Call.read "sessions/subscribe" p.json = some (.subscribe p) := Call.read_params (.subscribe p)

/-- `session/screen`'s params read as its call. -/
theorem read_screen (p : Named) : Call.read "session/screen" p.json = some (.screen p) := Call.read_params (.screen p)

/-- `session/history`'s params read as its call. -/
theorem read_history (p : Named) : Call.read "session/history" p.json = some (.history p) := Call.read_params (.history p)

/-- `session/attach`'s params read as its call. -/
theorem read_attach (p : Attaching) : Call.read "session/attach" p.json = some (.attach p) := Call.read_params (.attach p)

/-- `session/start`'s params read as its call. -/
theorem read_start (p : Starting) : Call.read "session/start" p.json = some (.start p) := Call.read_params (.start p)

/-- `session/resume`'s params read as its call. -/
theorem read_resume (p : Named) : Call.read "session/resume" p.json = some (.resume p) := Call.read_params (.resume p)

/-- `session/send`'s params read as its call. -/
theorem read_send (p : Sending) : Call.read "session/send" p.json = some (.send p) := Call.read_params (.send p)

/-- `session/detach`'s params read as its call. -/
theorem read_detach (p : Named) : Call.read "session/detach" p.json = some (.detach p) := Call.read_params (.detach p)

/-- `session/kill`'s params read as its call. -/
theorem read_kill (p : Named) : Call.read "session/kill" p.json = some (.kill p) := Call.read_params (.kill p)

/-- `session/rename`'s params read as its call. -/
theorem read_rename (p : Renaming) : Call.read "session/rename" p.json = some (.rename p) := Call.read_params (.rename p)

/-- `session/capture`'s params read as its call. -/
theorem read_capture (p : Capturing) : Call.read "session/capture" p.json = some (.capture p) := Call.read_params (.capture p)

/-- `session/resize`'s params read as its call. -/
theorem read_resize (p : Resizing) : Call.read "session/resize" p.json = some (.resize p) := Call.read_params (.resize p)

/-- `session/wait`'s params read as its call. -/
theorem read_wait (p : Named) : Call.read "session/wait" p.json = some (.wait p) := Call.read_params (.wait p)

/-- `session/upgrade`'s params read as its call. -/
theorem read_upgrade (p : Named) : Call.read "session/upgrade" p.json = some (.upgrade p) := Call.read_params (.upgrade p)

/-- A method's params that read as a call parse as the call's command line, with its input. -/
theorem parse_read {method : String} {params : Value} {call : Call}
    (read : Call.read method params = some call) :
    parse method params = (Api.parse call.words).bind fun request => call.input.map ((request, ·)) := by
  simp [parse, read]

attribute [local simp] Remote.named Remote.attaching List.lookup Api.parse Commands.lookup
  Commands.table Api.parseOp Call.words Call.operands Call.input Call.method Remote.call
  Remote.asked Api.flagged Linger.Target.Remote.targetArgs toValue_named toValue_listed
  toValue_attaching toValue_starting toValue_sending toValue_renaming toValue_capturing
  toValue_resizing

/-- **The host reads linger's call as exactly the request it performs for the session.** -/
theorem Remote.call_parse (request : Api.Request) (name : String) (input : List UInt8) :
    (Remote.call request name input).bind (fun called => parse called.1 called.2) =
      Remote.asked request name input := by
  cases request with
  | kill t => simp (config := { decide := true }) [parse_read (read_kill _), methods]
  | detach t => simp (config := { decide := true }) [parse_read (read_detach _), methods]
  | resume t => simp (config := { decide := true }) [parse_read (read_resume _), methods]
  | upgrade ts => simp (config := { decide := true }) [parse_read (read_upgrade _), methods]
  | rename t new => simp (config := { decide := true }) [parse_read (read_rename _), methods]
  | serve => simp
  | wait ts =>
    simp (config := { decide := true }) [parse_read (read_wait _), methods]; split <;> simp_all
  | start t program args => simp (config := { decide := true }) [parse_read (read_start _), methods]
  | capture history t =>
    cases history <;> simp (config := { decide := true }) [parse_read (read_capture _), methods]
  | list view =>
    cases view <;>
      simp (config := { decide := true }) [parse_read (read_list _), methods, Api.parseView,
        Api.parseLs, Api.parseLs.go]
  | resize t cols
    rows =>
    simp (config := { decide := true }) [parse_read (read_resize _), methods, Api.parseSize,
      Nat.toNat?_repr]
    by_cases c : Terminal.Vt.clampDim cols = cols <;>
      by_cases r : Terminal.Vt.clampDim rows = rows <;>
      simp [c, r]
  | send t input =>
    cases input <;>
      simp (config := { decide := true }) [parse_read (read_send _), methods, Base64.decode_encode]
  | attach readOnly t command =>
    cases readOnly <;> cases command <;>
      simp (config := { decide := true }) [parse_read (read_attach _), methods]

/-- **A host's rows are its records whose names a target takes, each named `name@host`.** -/
theorem Remote.rows_keys (host : String) (records : List Record) :
    (Remote.rows host records).map Record.key =
      (records.filter fun record => Linger.Target.Name.accept record.key == some record.key).map
        fun record => record.key ++ "@" ++ host := by
  simp only [Remote.rows, Remote.row, List.map_map, Function.comp_def]
  congr 1
  funext record
  simp only [Record.key, List.cons_append]
  exact Linger.Display.Listing.ofRow_key _ _

/-- **What a remote command finds answers as its host answered.** -/
theorem Remote.found_answer (answer : Os.Answer) (shows : Shows) :
    Api.answer (Remote.found answer shows) = answer := by
  unfold Remote.found
  split
  · rename_i ending _
    split
    · rename_i same
      simp [Api.answer, Api.Found.answer, same]
    · simp [Api.answer, Api.Found.answer]
  · simp [Api.answer, Api.Found.answer]

/-- **What a remote command says of its host's answer is each line the host said, as the
host's.** -/
theorem Remote.said_eq (host : String) (shows : Shows) :
    Remote.said host shows =
      (shows.said?.getD []).map fun text =>
        Linger.Target.Remote.scrub host ++ ": " ++ Linger.Target.Remote.scrub text := rfl

/-! ## A remote attach -/

/-- An attach client writes nothing of a message that ends the attach, nor of what follows it. -/
theorem shown_ends {m : Session.Wire.Msg} (ends : m.ends = true) (rest : List Session.Wire.Msg) :
    Session.Wire.shown (m :: rest) = [] := by
  cases m <;> simp_all [Session.Wire.shown, Session.Wire.Msg.ends]

/-- The message that ends an attach as `closed` says ends it, and fits a frame. -/
theorem ending_ends (closed : Value) :
    (Remote.ending closed).ends = true ∧ (Remote.ending closed).Fits := by
  unfold Remote.ending
  split
  · simp [Session.Wire.Msg.ends, Session.Wire.Msg.Fits]
  · simp [Session.Wire.Msg.ends, Session.Wire.Msg.Fits]
  · refine ⟨rfl, ?_⟩
    simp only [Session.Wire.Msg.Fits, Session.Wire.maxPayload, Remote.endedText]
    decide

/-- **What linger relays of an update that carries bytes**: their frames, then, when it carries
`closed`, the message that ends the attach. -/
theorem relay_output {id : Id} {bytes : List UInt8} {update : Value}
    (carried : Carries id bytes update) :
    Remote.relay id (Remote.output update) =
      Remote.outputFrames bytes ++
        match member? "closed" update with
        | some closed => [Remote.ending closed]
        | none => [] := by
  obtain ⟨named, text, data, decoded⟩ := carried
  have method : member? "method" (Remote.output update) = some (.string "session/output") := rfl
  have params : member? "params" (Remote.output update) = some update := rfl
  simp only [Remote.relay, method, params, named, Option.bind_some, Id.of_json, ↓reduceIte, data,
    decoded, Option.getD_some]
  rfl

/-- **A remote attach shows exactly the bytes the host's `session/attach` sends, and sends exactly
the keys typed.** -/
theorem Remote.relays (id : Id) (stream : List (Value × List UInt8)) (typed : List UInt8) :
    Remote.Relays Remote.relay Remote.keys id stream typed := by
  refine ⟨?_, ?_, ?_⟩
  · induction stream with
    | nil => simp [Session.Wire.shown]
    | cons first rest ih =>
      intro carried closedLast
      have relayed := relay_output (carried first (by simp))
      cases rest with
      | nil =>
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, relayed, List.map_cons,
          List.map_nil, List.flatten_cons, List.flatten_nil]
        constructor
        · intro m member
          rw [List.mem_append] at member
          rcases member with frame | closedPart
          · exact outputFrames_fit _ m frame
          · split at closedPart
            · simp only [List.mem_singleton] at closedPart
              exact closedPart ▸ (ending_ends _).2
            · cases closedPart
        · rw [shown_outputFrames]
          split
          · simp [shown_ends (ending_ends _).1]
          · simp [Session.Wire.shown]
      | cons second
        more =>
        have opened : member? "closed" first.1 = none := closedLast first (by simp)
        obtain ⟨fits, shows⟩ :=
          ih (fun update member => carried update (List.mem_cons_of_mem _ member))
            (fun update member =>
              closedLast update
                (by
                  rw [List.dropLast_cons_of_ne_nil (by simp)]
                  exact List.mem_cons_of_mem _ member))
        rw [opened] at relayed
        simp only [List.append_nil] at relayed
        constructor
        · intro m member
          rw [List.flatMap_cons, relayed, List.mem_append] at member
          rcases member with frame | later
          · exact outputFrames_fit _ m frame
          · exact fits m later
        · rw [List.flatMap_cons, relayed, shown_outputFrames, shows]
          simp
  · intro params named closed
    obtain ⟨value, found⟩ := Option.isSome_iff_exists.mp closed
    have method : member? "method" (Remote.output params) = some (.string "session/output") := rfl
    have given : member? "params" (Remote.output params) = some params := rfl
    refine ⟨Remote.ending value, ?_, (ending_ends value).1⟩
    simp only [Remote.relay, method, given, named, Option.bind_some, Id.of_json, ↓reduceIte, found]
    simp
  · refine ⟨?_, Base64.encode typed, ?_, Base64.decode_encode typed⟩ <;>
      simp [Remote.keys, toValue_keys, Keys.json, member?, List.lookup]

/-- A relay that writes base64 undecoded shows its text, not the bytes it carries. -/
theorem Remote.relays_rejects_undecoded :
    ¬∀ (id : Id) (stream : List (Value × List UInt8)) (typed : List UInt8),
        Remote.Relays Remote.undecoded Remote.keys id stream typed := by
  intro h
  have carried : Carries (.number 2) [0] (Remote.keys (.number 2) [0]) :=
    (Remote.relays (.number 2) [] [0]).2.2
  have shown :=
    ((h (.number 2) [(Remote.keys (.number 2) [0], [0])] []).1
        (fun update member => by
          simp at member; subst member; exact carried)
        (by simp)).2
  simp [Remote.undecoded, Remote.keys, toValue_keys, Keys.json, Remote.output, member?,
    List.lookup, Base64.encode, Base64.encodeTo, Id.json, Session.Wire.shown] at shown

end Linger.App.Serve
