module

public import Linger.App.CoreCode.Codec
public import ExactJSON.Lawful
public import ExactJSON.Solution
public import Linger.Display.Proofs.Record
meta import ExactJSON.Derive

@[expose] public section

/-! # The codecs of `serve`'s typed values are lawful and write what the spec states

Each typed value's codec reads back what it writes, as a valid value (`ExactJSON.LawfulValue`),
and writes the object `Linger.App.CoreSpec` states of its type; so a value is read exactly
(`exactly`) when it is the object some typed value writes. ExactJSON derives the lawfulness of a
type with an optional member; a type whose members are all required is lawful by the same
ExactJSON lemmas, given its reader. -/

namespace Linger.App.Serve

open ExactJSON ExactJSON.Derive

/-! ## Lawfulness -/

instance : LawfulValue Id where
  fromValue_toValue id := by cases id <;> rfl
  toValue_valid id := by cases id <;> rfl

instance : LawfulValue Hue where
  fromValue_toValue h := by cases h <;> simp [toValue, fromValue?, Hue.json]
  toValue_valid h := by cases h <;> rfl

deriving instance LawfulValue for NoParams

deriving instance LawfulValue for Listed

deriving instance LawfulValue for Attaching

deriving instance LawfulValue for Starting

deriving instance LawfulValue for Capturing

deriving instance LawfulValue for Info

deriving instance LawfulValue for Initialize

deriving instance LawfulValue for Style

instance : LawfulValue Named where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Named") (schema := [("name", false)]) (r :=
      (Rd.pure fun name => ({ name } : Named)).ap (req fromValue? "name")) (b := { name := p.name })
      (keysIncrease_cons keysIncreaseFrom_nil) (.req .nil)
      (.ap .pure (req_some (LawfulValue.fromValue_toValue p.name)))
  toValue_valid p :=
    valid_record (schema := [("name", false)]) (keysIncrease_cons keysIncreaseFrom_nil)
      (.some (LawfulValue.toValue_valid p.name) .nil)

instance : LawfulValue Sending where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Sending") (schema :=
      [("data", false), ("name", false)]) (r :=
      (((Rd.pure fun data name => ({ data, name } : Sending)).ap (req fromValue? "data")).ap
        (req fromValue? "name")))
      (b := { data := p.data, name := p.name })
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.req (.req .nil))
      (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.data)))
        (req_some (LawfulValue.fromValue_toValue p.name)))
  toValue_valid p :=
    valid_record (schema := [("data", false), ("name", false)])
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.some (LawfulValue.toValue_valid p.data) (.some (LawfulValue.toValue_valid p.name) .nil))

instance : LawfulValue Renaming where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Renaming") (schema :=
      [("name", false), ("new", false)]) (r :=
      (((Rd.pure fun name new => ({ name, new } : Renaming)).ap (req fromValue? "name")).ap
        (req fromValue? "new")))
      (b := { name := p.name, new := p.new })
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.req (.req .nil))
      (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.name)))
        (req_some (LawfulValue.fromValue_toValue p.new)))
  toValue_valid p :=
    valid_record (schema := [("name", false), ("new", false)])
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.some (LawfulValue.toValue_valid p.name) (.some (LawfulValue.toValue_valid p.new) .nil))

instance : LawfulValue Resizing where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Resizing") (schema :=
      [("cols", false), ("name", false), ("rows", false)]) (r :=
      ((((Rd.pure fun cols name rows => ({ cols, name, rows } : Resizing)).ap
                (req fromValue? "cols")).ap
            (req fromValue? "name")).ap
        (req fromValue? "rows")))
      (b := { cols := p.cols, name := p.name, rows := p.rows })
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.req (.req (.req .nil)))
      (.ap
        (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.cols)))
          (req_some (LawfulValue.fromValue_toValue p.name)))
        (req_some (LawfulValue.fromValue_toValue p.rows)))
  toValue_valid p :=
    valid_record (schema := [("cols", false), ("name", false), ("rows", false)])
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.some (LawfulValue.toValue_valid p.cols)
        (.some (LawfulValue.toValue_valid p.name) (.some (LawfulValue.toValue_valid p.rows) .nil)))

instance : LawfulValue Subscription where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Subscription") (schema :=
      [("subscription", false)]) (r :=
      ((Rd.pure fun subscription => ({ subscription } : Subscription)).ap
        (req fromValue? "subscription")))
      (b := { subscription := p.subscription }) (keysIncrease_cons keysIncreaseFrom_nil) (.req .nil)
      (.ap .pure (req_some (LawfulValue.fromValue_toValue p.subscription)))
  toValue_valid p :=
    valid_record (schema := [("subscription", false)]) (keysIncrease_cons keysIncreaseFrom_nil)
      (.some (LawfulValue.toValue_valid p.subscription) .nil)

instance : LawfulValue Keys where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Keys") (schema :=
      [("data", false), ("subscription", false)]) (r :=
      (((Rd.pure fun data subscription => ({ data, subscription } : Keys)).ap
            (req fromValue? "data")).ap
        (req fromValue? "subscription")))
      (b := { data := p.data, subscription := p.subscription })
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.req (.req .nil))
      (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.data)))
        (req_some (LawfulValue.fromValue_toValue p.subscription)))
  toValue_valid p :=
    valid_record (schema := [("data", false), ("subscription", false)])
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.some (LawfulValue.toValue_valid p.data)
        (.some (LawfulValue.toValue_valid p.subscription) .nil))

instance : LawfulValue Sized where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Sized") (schema :=
      [("cols", false), ("rows", false), ("subscription", false)]) (r :=
      ((((Rd.pure fun cols rows subscription => ({ cols, rows, subscription } : Sized)).ap
                (req fromValue? "cols")).ap
            (req fromValue? "rows")).ap
        (req fromValue? "subscription")))
      (b := { cols := p.cols, rows := p.rows, subscription := p.subscription })
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.req (.req (.req .nil)))
      (.ap
        (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.cols)))
          (req_some (LawfulValue.fromValue_toValue p.rows)))
        (req_some (LawfulValue.fromValue_toValue p.subscription)))
  toValue_valid p :=
    valid_record (schema := [("cols", false), ("rows", false), ("subscription", false)])
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.some (LawfulValue.toValue_valid p.cols)
        (.some (LawfulValue.toValue_valid p.rows)
          (.some (LawfulValue.toValue_valid p.subscription) .nil)))

instance : LawfulValue Numbered where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Numbered") (schema :=
      [("line", false), ("spans", false), ("text", false)]) (r :=
      ((((Rd.pure fun line spans text => ({ line, spans, text } : Numbered)).ap
                (req fromValue? "line")).ap
            (req fromValue? "spans")).ap
        (req fromValue? "text")))
      (b := { line := p.line, spans := p.spans, text := p.text })
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.req (.req (.req .nil)))
      (.ap
        (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.line)))
          (req_some (LawfulValue.fromValue_toValue p.spans)))
        (req_some (LawfulValue.fromValue_toValue p.text)))
  toValue_valid p :=
    valid_record (schema := [("line", false), ("spans", false), ("text", false)])
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.some (LawfulValue.toValue_valid p.line)
        (.some (LawfulValue.toValue_valid p.spans) (.some (LawfulValue.toValue_valid p.text) .nil)))

instance : LawfulValue Scrolled where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Scrolled") (schema :=
      [("spans", false), ("text", false)]) (r :=
      (((Rd.pure fun spans text => ({ spans, text } : Scrolled)).ap (req fromValue? "spans")).ap
        (req fromValue? "text")))
      (b := { spans := p.spans, text := p.text })
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.req (.req .nil))
      (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.spans)))
        (req_some (LawfulValue.fromValue_toValue p.text)))
  toValue_valid p :=
    valid_record (schema := [("spans", false), ("text", false)])
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.some (LawfulValue.toValue_valid p.spans) (.some (LawfulValue.toValue_valid p.text) .nil))

instance : LawfulValue Cursor where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Cursor") (schema :=
      [("visible", false), ("x", false), ("y", false)]) (r :=
      ((((Rd.pure fun visible x y => ({ visible, x, y } : Cursor)).ap (req fromValue? "visible")).ap
            (req fromValue? "x")).ap
        (req fromValue? "y")))
      (b := { visible := p.visible, x := p.x, y := p.y })
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.req (.req (.req .nil)))
      (.ap
        (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.visible)))
          (req_some (LawfulValue.fromValue_toValue p.x)))
        (req_some (LawfulValue.fromValue_toValue p.y)))
  toValue_valid p :=
    valid_record (schema := [("visible", false), ("x", false), ("y", false)])
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.some (LawfulValue.toValue_valid p.visible)
        (.some (LawfulValue.toValue_valid p.x) (.some (LawfulValue.toValue_valid p.y) .nil)))

instance : LawfulValue Abilities where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Abilities") (schema :=
      [("methods", false), ("notifications", false)]) (r :=
      (((Rd.pure fun methods notifications => ({ methods, notifications } : Abilities)).ap
            (req fromValue? "methods")).ap
        (req fromValue? "notifications")))
      (b := { methods := p.methods, notifications := p.notifications })
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.req (.req .nil))
      (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.methods)))
        (req_some (LawfulValue.fromValue_toValue p.notifications)))
  toValue_valid p :=
    valid_record (schema := [("methods", false), ("notifications", false)])
      (keysIncrease_cons (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil)))
      (.some (LawfulValue.toValue_valid p.methods)
        (.some (LawfulValue.toValue_valid p.notifications) .nil))

instance : LawfulValue Welcome where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Welcome") (schema :=
      [("capabilities", false), ("protocolVersion", false), ("serverInfo", false)]) (r :=
      ((((Rd.pure fun capabilities protocolVersion serverInfo =>
                    ({ capabilities, protocolVersion, serverInfo } : Welcome)).ap
                (req fromValue? "capabilities")).ap
            (req fromValue? "protocolVersion")).ap
        (req fromValue? "serverInfo")))
      (b :=
      { capabilities := p.capabilities, protocolVersion := p.protocolVersion,
        serverInfo := p.serverInfo })
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.req (.req (.req .nil)))
      (.ap
        (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.capabilities)))
          (req_some (LawfulValue.fromValue_toValue p.protocolVersion)))
        (req_some (LawfulValue.fromValue_toValue p.serverInfo)))
  toValue_valid p :=
    valid_record (schema :=
      [("capabilities", false), ("protocolVersion", false), ("serverInfo", false)])
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.some (LawfulValue.toValue_valid p.capabilities)
        (.some (LawfulValue.toValue_valid p.protocolVersion)
          (.some (LawfulValue.toValue_valid p.serverInfo) .nil)))

instance : LawfulValue Changed where
  fromValue_toValue p :=
    decodeFields_record (name := "Linger.App.Serve.Changed") (schema :=
      [("records", false), ("removed", false), ("subscription", false)]) (r :=
      ((((Rd.pure fun records removed subscription =>
                    ({ records, removed, subscription } : Changed)).ap
                (req fromValue? "records")).ap
            (req fromValue? "removed")).ap
        (req fromValue? "subscription")))
      (b := { records := p.records, removed := p.removed, subscription := p.subscription })
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.req (.req (.req .nil)))
      (.ap
        (.ap (.ap .pure (req_some (LawfulValue.fromValue_toValue p.records)))
          (req_some (LawfulValue.fromValue_toValue p.removed)))
        (req_some (LawfulValue.fromValue_toValue p.subscription)))
  toValue_valid p :=
    valid_record (schema := [("records", false), ("removed", false), ("subscription", false)])
      (keysIncrease_cons
        (keysIncreaseFrom_cons (string_lt rfl)
          (keysIncreaseFrom_cons (string_lt rfl) (keysIncreaseFrom_nil))))
      (.some (LawfulValue.toValue_valid p.records)
        (.some (LawfulValue.toValue_valid p.removed)
          (.some (LawfulValue.toValue_valid p.subscription) .nil)))

deriving instance LawfulValue for Shows

deriving instance LawfulValue for Result

deriving instance LawfulValue for ScreenChanged

deriving instance LawfulValue for HistoryChanged

deriving instance LawfulValue for Output

end Linger.App.Serve

namespace Linger.App.Serve

open ExactJSON ExactJSON.Derive

/-! ## What each codec writes -/

/-- A value is read exactly as `α` writes it just when it is what `α` writes of the value read. -/
theorem exactly_iff {α : Type} [ToValue α] [FromValue α] [LawfulValue α] (value : Value) (a : α) :
    exactly value = some a ↔ toValue a = value := by
  unfold exactly
  constructor
  · intro h
    split at h
    · rename_i b _
      split at h
      · rename_i same
        cases h
        exact (beq_iff _ _).mp same
      · cases h
    · cases h
  · intro h
    subst h
    simp [LawfulValue.fromValue_toValue, (beq_iff _ _).mpr rfl]

theorem present_opt (k : String) (s : List (String × Bool)) (o : Option Value)
    (es : List (Option Value)) :
    present ((k, true) :: s) (o :: es) = (o.map (k, ·)).toList ++ present s es := by cases o <;> rfl

theorem present_req (k : String) (s : List (String × Bool)) (v : Value) (es : List (Option Value)) :
    present ((k, false) :: s) (some v :: es) = (k, v) :: present s es := rfl

theorem toValue_strings (texts : List String) : toValue texts = strings texts := by
  simp [toValue, strings]

@[simp]
theorem toValue_bool (b : Bool) : toValue b = .boolean b := rfl

@[simp]
theorem toValue_string (text : String) : toValue text = .string text := rfl

@[simp]
theorem toValue_nat (n : Nat) : toValue n = .integer n := rfl

@[simp]
theorem toValue_hue (h : Hue) : toValue h = h.json := rfl

@[simp]
theorem toValue_id (id : Id) : toValue id = id.json := rfl

theorem table_mk (l l' : List (String × Value)) (h : l = l') :
    Value.table ⟨l⟩ = Value.table l'.toArray := by
  subst h; rfl

theorem toValue_record (record : Record) : toValue record = record.json :=
  (codec_extTreeMap record).1

theorem toValue_records (records : List Record) :
    toValue records = .array (records.map Record.json).toArray := by
  rw [(codec_list records).1,
    show (toValue : Record → Value) = Record.json from funext toValue_record]

/-- Unfold a derived encoder to the object the spec states of its type, with the encoders of the
types it holds. -/
macro "codec_eq" " [" more:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
      (show record _ _ = _
       simp only [record, present_opt, present, optional, Option.map_map, Function.comp_def,
         toValue_bool, toValue_string, toValue_nat, toValue_hue, toValue_id, toValue_strings,
         toValue_record, toValue_records, NoParams.json, Named.json, Listed.json, Attaching.json,
         Starting.json, Sending.json, Renaming.json, Capturing.json, Resizing.json,
         Subscription.json, Keys.json, Sized.json, Info.json, Initialize.json, Style.json, $more,*]
       try exact table_mk _ _ (by simp)))

theorem toValue_listed (p : Listed) : toValue p = p.json := by codec_eq []

theorem toValue_attaching (p : Attaching) : toValue p = p.json := by codec_eq []

theorem toValue_style (p : Style) : toValue p = p.json := by codec_eq []

theorem toValue_noParams (p : NoParams) : toValue p = p.json := by codec_eq []

theorem toValue_named (p : Named) : toValue p = p.json := by codec_eq []

theorem toValue_starting (p : Starting) : toValue p = p.json := by codec_eq []

theorem toValue_sending (p : Sending) : toValue p = p.json := by codec_eq []

theorem toValue_renaming (p : Renaming) : toValue p = p.json := by codec_eq []

theorem toValue_capturing (p : Capturing) : toValue p = p.json := by codec_eq []

theorem toValue_resizing (p : Resizing) : toValue p = p.json := by codec_eq []

theorem toValue_subscription (p : Subscription) : toValue p = p.json := by codec_eq []

theorem toValue_keys (p : Keys) : toValue p = p.json := by codec_eq []

theorem toValue_sized (p : Sized) : toValue p = p.json := by codec_eq []

theorem toValue_info (p : Info) : toValue p = p.json := by codec_eq []

theorem toValue_initialize (p : Initialize) : toValue p = p.json := by
  codec_eq [toValue_noParams, toValue_info]

theorem toValue_span (s : Nat × Style) : toValue s = spanJson s := by
  obtain ⟨n, style⟩ := s
  rw [(codec_prod n style).1, toValue_nat, toValue_style]
  rfl

theorem toValue_spans (spans : List (Nat × Style)) :
    toValue spans = .array (spans.map spanJson).toArray := by
  rw [(codec_list spans).1,
    show (toValue : Nat × Style → Value) = spanJson from funext toValue_span]

theorem toValue_numbers (ns : List Nat) :
    toValue ns = .array (ns.map fun (n : Nat) => Value.integer n).toArray := by
  rw [(codec_list ns).1]
  rfl

theorem toValue_cursor (c : Cursor) : toValue c = c.json := by codec_eq [Cursor.json]

theorem toValue_numbered (r : Numbered) : toValue r = r.json := by
  codec_eq [Numbered.json, toValue_spans]

theorem toValue_numbereds (rows : List Numbered) :
    toValue rows = .array (rows.map Numbered.json).toArray := by
  rw [(codec_list rows).1,
    show (toValue : Numbered → Value) = Numbered.json from funext toValue_numbered]

theorem toValue_scrolled (r : Scrolled) : toValue r = r.json := by
  codec_eq [Scrolled.json, toValue_spans]

theorem toValue_scrolleds (lines : List Scrolled) :
    toValue lines = .array (lines.map Scrolled.json).toArray := by
  rw [(codec_list lines).1,
    show (toValue : Scrolled → Value) = Scrolled.json from funext toValue_scrolled]

theorem toValue_result (r : Result) : toValue r = r.json := by
  codec_eq [Result.json, Shows.members, toValue_cursor, toValue_numbereds]

theorem toValue_screenChanged (u : ScreenChanged) : toValue u = u.json := by
  codec_eq [ScreenChanged.json, toValue_result, toValue_cursor, toValue_numbereds, toValue_numbers]

theorem toValue_historyChanged (u : HistoryChanged) : toValue u = u.json := by
  codec_eq [HistoryChanged.json, toValue_result, toValue_scrolleds]

theorem toValue_output (u : Output) : toValue u = u.json := by
  codec_eq [Output.json, toValue_result]

theorem toValue_changed (u : Changed) : toValue u = u.json := by codec_eq [Changed.json]

theorem toValue_abilities (a : Abilities) : toValue a = a.json := by codec_eq [Abilities.json]

theorem toValue_welcome (w : Welcome) : toValue w = w.json := by
  codec_eq [Welcome.json, toValue_abilities, toValue_info]

/-- A result's first member is its answer. -/
theorem Result.json_answer (r : Result) : member? "answer" r.json = some (.string r.answer) := by
  simp [Result.json, member?, List.lookup]

end Linger.App.Serve
