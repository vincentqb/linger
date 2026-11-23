module

public import Linger.App.CoreSpec
import all Linger.App.CoreSpec
import all Linger.App.CoreCode.Serve

/-! # A remote host through `serve`: its rows are what its `sessions/list` returns

A host's answer reads as records exactly when it shook hands and its `sessions/list` returned
them, and as an older linger's exactly when it answered the handshake with a usage answer; its rows
are its records whose names a target takes, in order, each named `name@host`. -/

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

/-- **The records a host listed are `Remote.Lists`'s.** -/
theorem Remote.listed_iff (messages : List Json) (records : List Record) :
    Remote.listed messages = some records ↔ Remote.Lists messages records := by
  unfold Remote.listed Remote.Lists
  cases answered : Remote.answerOf messages "2" "result" with
  | none => simp
  | some
    result =>
    have cond :
      ((result.member? "answer").bind Json.text? == some "done") = true ↔
        result.member? "answer" = some (.str "done") := by
      rw [beq_iff_eq, text_eq_some]
    by_cases done : result.member? "answer" = some (.str "done")
    · simp only [cond.mpr done, ↓reduceIte]
      cases items : result.member? "records" with
      | none => simp [items, done]
      | some value => cases value <;> simp [items, done]
    · have refused : ((result.member? "answer").bind Json.text? == some "done") = false := by
        cases holds : ((result.member? "answer").bind Json.text? == some "done")
        · rfl
        · exact absurd (cond.mp holds) done
      simp [refused, done]

/-- **Whether a host answered the handshake with a usage answer is `Remote.Usage`.** -/
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

/-- **A host's answer reads as records exactly when it shook hands and listed them.** -/
theorem Remote.heard_listed (messages : List Json) (status : UInt32) (records : List Record) :
    Remote.heard messages status = .listed records ↔
      Remote.Shook messages ∧ Remote.Lists messages records := by
  rw [← Remote.shook_iff, ← Remote.listed_iff]
  unfold Remote.heard
  split
  · rename_i shook
    split
    · rename_i listed found
      simp [shook, found]
    · rename_i none
      simp [shook, none]
  · rename_i notShook
    split <;> simp [notShook]

/-- **A host's answer reads as an older linger's exactly when it answered the handshake with a
usage answer.** -/
theorem Remote.heard_older (messages : List Json) (status : UInt32) :
    Remote.heard messages status = .older ↔ Remote.Usage messages status := by
  rw [← Remote.usage_iff]
  unfold Remote.heard
  split
  · rename_i shook
    split <;> simp [Remote.usage, shook]
  · rename_i notShook
    split <;> simp_all

/-- **A host's rows are its records whose names a target takes, each named `name@host`.** -/
theorem Remote.rows_keys (host : String) (records : List Record) :
    (Remote.rows host records).map Record.key =
      (records.filter fun record => Linger.Target.Name.accept record.key == some record.key).map
        fun record => record.key ++ "@" ++ host := by
  simp [Remote.rows, Remote.row, Record.key]

end Linger.App.Serve
