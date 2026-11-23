module

public import Linger.App.CoreSpec
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Serve
import all Linger.Os.CoreCode.Answer
import all Linger.App.CoreCode.Api
import all Linger.App.CoreCode.Commands
import all Linger.App.CoreCode.Json
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

/-- A member's text is `text` exactly when the member is the string `text`. -/
theorem text_eq_some (value : Option Json) (text : String) :
    value.bind Json.text? = some text ↔ value = some (.str text) := by
  cases value with
  | none => simp
  | some json => cases json <;> simp [Json.text?]

/-- **Whether a host shook hands is `Remote.Shook`.** -/
theorem Remote.shook_iff (messages : List Json) :
    Remote.shook messages = true ↔ Remote.Shook messages := by
  unfold Remote.shook Remote.Shook
  split
  · rename_i version found
    rw [Option.bind_assoc] at found
    cases answered : Remote.answerOf messages "1" "result" with
    | none => simp [answered] at found
    | some result =>
      simp only [answered, Option.bind_some] at found
      have member := (text_eq_some _ _).mp found
      simp [member, versions]
  · rename_i none
    rw [Option.bind_assoc] at none
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    intro result version answered member _
    simp [answered, member, Json.text?] at none

/-- **Whether a host refused `serve` with a usage answer is `Remote.Usage`.** -/
theorem Remote.usage_iff (messages : List Json) (status : UInt32) :
    Remote.usage messages status = true ↔ Remote.Usage messages status := by
  unfold Remote.usage Remote.Usage Remote.refusedUsage
  rw [Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, Remote.shook_iff, Bool.or_eq_true,
    beq_iff_eq, beq_iff_eq]
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  cases answered : Remote.answerOf messages "1" "error" with
  | none => simp
  | some error =>
    cases data : error.member? "data" with
    | none => simp [data]
    | some value => simp [data, text_eq_some]

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

/-- **An answer and members read back as exactly the object a result gives them as**: its name,
its code in decimal, then the members. -/
theorem Remote.answerIn_eq_some (value : Json) (answer : Os.Answer)
    (members : List (String × Json)) :
    Remote.answerIn value = some (answer, members) ↔
      value =
        .obj
          (("answer", .str (answerName answer)) ::
            ("code", .number (toString answer.code)) :: members) := by
  constructor
  · intro read
    unfold Remote.answerIn at read
    split at read
    · rename_i name code rest
      split at read
      · rename_i n parsed
        split at read
        · rename_i canonical
          simp only [Option.map_eq_some_iff, Prod.mk.injEq] at read
          obtain ⟨found, named, rfl, rfl⟩ := read
          obtain ⟨rfl, coded⟩ := answerNamed_eq_some named
          rw [← canonical, ← coded]
          rfl
        · simp at read
      · simp at read
    · simp at read
  · rintro rfl
    simp only [Remote.answerIn]
    rw [show toString answer.code = Nat.repr answer.code.toNat from rfl, Nat.toNat?_repr]
    simp [answerNamed_answerName]

/-- **A host's answer reads as an answer exactly when it shook hands and answered the call with
it.** -/
theorem Remote.heard_answered (messages : List Json) (status : UInt32) (answer : Os.Answer)
    (members : List (String × Json)) :
    Remote.heard messages status = .answered answer members ↔
      Remote.Shook messages ∧ Remote.Answered Linger.Os.Answer.code messages answer members := by
  have bound :
    (Remote.callAnswer messages).bind Remote.answerIn = some (answer, members) ↔
      Remote.callAnswer messages =
        some
          (.obj
            (("answer", .str (answerName answer)) ::
              ("code", .number (toString answer.code)) :: members)) := by
    cases Remote.callAnswer messages with
    | none => simp
    | some value => simp [Remote.answerIn_eq_some]
  rw [← Remote.shook_iff]
  unfold Remote.Answered
  rw [show
      (Remote.answerOf messages "2" "result").or
          ((Remote.answerOf messages "2" "error").bind (·.member? "data")) =
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
theorem Remote.heard_refused (messages : List Json) (status : UInt32) :
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

/-- A list of strings as JSON reads back as itself. -/
theorem texts_map_str (texts : List String) : Json.texts? (.arr (texts.map .str)) = some texts := by
  induction texts with
  | nil => rfl
  | cons text texts
    ih =>
    simp only [Json.texts?, List.map_cons, List.mapM_cons, Json.text?] at ih ⊢
    simp [ih]

theorem texts_cons (text : String) (rest : List Json) :
    Json.texts? (.arr (.str text :: rest)) = (Json.texts? (.arr rest)).map (text :: ·) := by
  simp only [Json.texts?, List.mapM_cons, Json.text?]
  cases rest.mapM Json.text? <;> rfl

theorem texts_one (text : String) : Json.texts? (.arr [.str text]) = some [text] := rfl

theorem nat_number (n : Nat) : Json.nat? (.number (toString n)) = some n := by
  have digits : (toString n).toList.all Char.isDigit = true := by
    simp only [List.all_eq_true]
    intro c member
    rw [Nat.toString_eq_repr, Nat.toList_repr] at member
    exact Nat.isDigit_of_mem_toDigits (b := 10) (by decide) (by decide) member
  simp only [Json.nat?, digits, ↓reduceIte]
  rw [show toString n = Nat.repr n from rfl, Nat.toNat?_repr]

theorem nat_repr (n : Nat) : Json.nat? (.number n.repr) = some n := nat_number n

attribute [local simp] Remote.named Json.need Json.opt Json.member? List.lookup Json.text?
  Json.flag? Api.parse Commands.lookup Commands.table Api.parseOp parse words operands input
  Remote.call Remote.asked Api.flagged Linger.Target.Remote.targetArgs

/-- **The host reads linger's call as exactly the request it performs for the session.** -/
theorem Remote.call_parse (request : Api.Request) (name : String) (input : List UInt8) :
    (Remote.call request name input).bind (fun called => parse called.1 called.2) =
      Remote.asked request name input := by
  cases request with
  | kill t => simp (config := { decide := true }) [methods]
  | detach t => simp (config := { decide := true }) [methods]
  | resume t => simp (config := { decide := true }) [methods]
  | upgrade ts => simp (config := { decide := true }) [methods]
  | rename t new => simp (config := { decide := true }) [methods]
  | serve => simp
  | wait ts =>
    simp (config := { decide := true }) [methods]; split <;> simp_all
  | start t program args => simp (config := { decide := true }) [methods, texts_map_str]
  | capture history t => cases history <;> simp (config := { decide := true }) [methods]
  | list view =>
    cases view <;>
      simp (config := { decide := true }) [methods, texts_one, Api.parseView, Api.parseLs,
        Api.parseLs.go]
  | resize t cols
    rows =>
    simp (config := { decide := true }) [methods, nat_repr, Api.parseSize, Nat.toNat?_repr]
    by_cases c : Terminal.Vt.clampDim cols = cols <;>
      by_cases r : Terminal.Vt.clampDim rows = rows <;>
      simp [c, r]
  | send t input =>
    cases input <;> simp (config := { decide := true }) [methods, Base64.decode_encode]
  | attach readOnly t command =>
    cases readOnly <;> cases command <;>
      simp (config := { decide := true }) [methods, texts_map_str, texts_cons]

/-- **A host's rows are its records whose names a target takes, each named `name@host`.** -/
theorem Remote.rows_keys (host : String) (records : List Record) :
    (Remote.rows host records).map Record.key =
      (records.filter fun record => Linger.Target.Name.accept record.key == some record.key).map
        fun record => record.key ++ "@" ++ host := by
  simp [Remote.rows, Remote.row, Record.key]

/-- **What a remote command finds answers as its host answered.** -/
theorem Remote.found_answer (answer : Os.Answer) (members : List (String × Json)) :
    Api.answer (Remote.found answer members) = answer := by
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
theorem Remote.said_eq (host : String) (members : List (String × Json)) :
    Remote.said host members =
      (((members.lookup "said").bind Json.texts?).getD []).map fun text =>
        Linger.Target.Remote.scrub host ++ ": " ++ Linger.Target.Remote.scrub text := rfl

/-! ## A remote attach -/

/-- An attach client writes all of the bytes output frames carry, then what follows. -/
theorem shown_outputFrames (bytes : List UInt8) (rest : List Session.Wire.Msg) :
    Session.Wire.shown (Remote.outputFrames bytes ++ rest) = bytes ++ Session.Wire.shown rest := by
  unfold Remote.outputFrames
  conv =>
    rhs; rw [← Session.Wire.inputChunks_flatten bytes]
  induction Session.Wire.inputChunks bytes with
  | nil => simp
  | cons chunk chunks ih => simp [Session.Wire.shown, ih]

/-- An attach client writes nothing of a message that ends the attach, nor of what follows it. -/
theorem shown_ends {m : Session.Wire.Msg} (ends : m.ends = true) (rest : List Session.Wire.Msg) :
    Session.Wire.shown (m :: rest) = [] := by
  cases m <;> simp_all [Session.Wire.shown, Session.Wire.Msg.ends]

/-- Output frames fit a frame. -/
theorem outputFrames_fit (bytes : List UInt8) : ∀ m ∈ Remote.outputFrames bytes, m.Fits := by
  intro m member
  simp only [Remote.outputFrames, List.mem_map] at member
  obtain ⟨chunk, inChunks, rfl⟩ := member
  have short := Session.Wire.inputChunks_length_le bytes chunk inChunks
  simp only [Session.Wire.Msg.Fits, Session.Wire.maxPayload]
  simp only [Session.Wire.inputChunk] at short
  omega

/-- The message that ends an attach as `closed` says ends it, and fits a frame. -/
theorem ending_ends (closed : Json) :
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
theorem relay_output {id : Id} {bytes : List UInt8} {update : Json}
    (carried : Carries id bytes update) :
    Remote.relay id (Remote.output update) =
      Remote.outputFrames bytes ++
        match update.member? "closed" with
        | some closed => [Remote.ending closed]
        | none => [] := by
  obtain ⟨named, text, data, decoded⟩ := carried
  have method : (Remote.output update).member? "method" = some (.str "session/output") := rfl
  have params : (Remote.output update).member? "params" = some update := rfl
  simp only [Remote.relay, method, params, named, Option.bind_some, Id.of_json, ↓reduceIte, data,
    decoded, Option.getD_some]
  rfl

/-- **A remote attach shows exactly the bytes the host's `session/attach` sends, and sends exactly
the keys typed.** -/
theorem Remote.shows (id : Id) (stream : List (Json × List UInt8)) (typed : List UInt8) :
    Remote.Shows Remote.relay Remote.keys id stream typed := by
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
        have opened : first.1.member? "closed" = none := closedLast first (by simp)
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
    have method : (Remote.output params).member? "method" = some (.str "session/output") := rfl
    have given : (Remote.output params).member? "params" = some params := rfl
    refine ⟨Remote.ending value, ?_, (ending_ends value).1⟩
    simp only [Remote.relay, method, given, named, Option.bind_some, Id.of_json, ↓reduceIte, found]
    simp
  · exact ⟨rfl, Base64.encode typed, rfl, Base64.decode_encode typed⟩

/-- A relay that writes base64 undecoded shows its text, not the bytes it carries. -/
theorem Remote.shows_rejects_undecoded :
    ¬∀ (id : Id) (stream : List (Json × List UInt8)) (typed : List UInt8),
        Remote.Shows Remote.undecoded Remote.keys id stream typed := by
  intro h
  have carried : Carries (.number "2") [0] (Remote.keys (.number "2") [0]) :=
    (Remote.shows (.number "2") [] [0]).2.2
  have shown :=
    ((h (.number "2") [(Remote.keys (.number "2") [0], [0])] []).1
        (fun update member => by
          simp at member; subst member; exact carried)
        (by simp)).2
  simp [Remote.undecoded, Remote.keys, Remote.output, Json.member?, List.lookup, Base64.encode,
    Base64.encodeTo, Id.json, Session.Wire.shown] at shown

end Linger.App.Serve
