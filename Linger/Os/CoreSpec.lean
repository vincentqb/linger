module

public section

/-! # What exit-status and JSON headlines are stated in

The answers a command gives, as its exit status gives them: an answer of linger's own, the
signal that stopped it or the session it attached to or waited for, or the status of the program
the command waited for. An exit status is the operating system's, and the selector answers as
the session commands do, so the answers sit in the bottom layer, where
every component that answers can name them; and the codes linger gave before a status said which
signal it stood for, which the kills put in place of the program's.

The JSON linger writes and reads, `serve`'s lines, a host's replies and `ls --porcelain`, sits
here too, below every component that writes or reads it: its values (`Json`), the values a
canonical text holds (`Json.Valid`), the value a text of any value holds (`Json.sorted`), and the
canonical texts themselves (`Json.Canonical`), the grammar of ExactJSON's canonical format. -/

namespace Linger.Os

/-- What a command answers, as its exit status gives it: an answer of linger's own, the signal
that stopped it or the session it attached to or waited for, or the status of the program the
command waited for. The statuses are a shell's, and a program may exit with one linger also uses,
as with `timeout` and `env`, so a status alone cannot tell the two apart; the porcelain output
says exactly. -/
inductive Answer where
  /-- It did what was asked. -/
  | done
  /-- It did not, refused or failed, and linger says why. -/
  | notDone
  /-- Its command line is not one linger takes. -/
  | usage
  /-- Its time limit passed first. -/
  | timedOut
  /-- linger failed, or could not find out what was asked. -/
  | failed
  /-- The program it was to run cannot be run. -/
  | cannotRun
  /-- The program, or the session, it names does not exist. -/
  | notFound
  /-- Its chooser was cancelled, by a key or by the end of its input, as fzf answers a chooser
  cancelled with Esc or ^C. -/
  | cancelled
  /-- The signal with this number stopped it, once it had handed its terminal back: it ends as
  the signal ends a program that does not catch it, which a shell reports as 128 plus the
  number. -/
  | stopped (signal : UInt8)
  /-- The session it attached to or waited for was saved when the signal with this number
  stopped its daemon, which a shell reports as it reports a job that signal stopped, 128 plus the
  number. -/
  | saved (signal : UInt8)
  /-- The program it waited for ended with this status, as a shell reports it: the program's
  code, or 128 plus the number of the signal that killed it. -/
  | program (status : UInt32)
  deriving Repr, DecidableEq

/-- Whether an answer is linger's own, and not the status a signal or a program gives. -/
@[expose]
def Answer.Own : Answer → Prop
  | .stopped _ | .saved _ | .program _ => False
  | _ => True

/-- The codes linger gave before a status said which signal it stood for: every signal that
stopped a command, or a session's daemon, gave 130, the status of SIGINT, which a cancelled
chooser also gives. -/
@[expose]
def Answer.lumped : Answer → UInt32
  | .done => 0
  | .notDone => 1
  | .usage => 2
  | .timedOut => 124
  | .failed => 125
  | .cannotRun => 126
  | .notFound => 127
  | .cancelled | .stopped _ | .saved _ => 130
  | .program status => status

end Linger.Os

namespace Linger

/-- **A JSON value, as linger writes and reads one**: `null`, a boolean, an integer, a string, an
array, or an object, its members in the order they come. Its numbers are integers, without
bound: linger's texts hold no float, so a number with a fraction or an exponent is none of its
values. -/
inductive Json where
  /-- `null`. -/
  | null
  /-- `true` or `false`. -/
  | bool (value : Bool)
  /-- An integer. -/
  | int (value : Int)
  /-- A string. -/
  | str (value : String)
  /-- An array. -/
  | arr (items : List Json)
  /-- An object, its members in order. -/
  | obj (members : List (String × Json))
  deriving Inhabited

namespace Json

/-- The member of an object under `key`, the first one when it has several, and none of any other
value. -/
@[expose]
def member? (key : String) : Json → Option Json
  | .obj members => members.lookup key
  | _ => none

/-- A string's text. -/
@[expose]
def text? : Json → Option String
  | .str value => some value
  | _ => none

/-- An integer. -/
@[expose]
def int? : Json → Option Int
  | .int value => some value
  | _ => none

/-- An integer that is a natural number. -/
@[expose]
def nat? : Json → Option Nat
  | .int value => if 0 ≤ value then some value.toNat else none
  | _ => none

/-- A boolean. -/
@[expose]
def flag? : Json → Option Bool
  | .bool value => some value
  | _ => none

/-- An array of strings, their texts. -/
@[expose]
def texts? : Json → Option (List String)
  | .arr items => items.mapM Json.text?
  | _ => none

/-- The member `key` of `params`, as `read` takes it: none when it is missing, `null` or not
what `read` takes. -/
@[expose]
def need {α : Type} (params : Json) (key : String) (read : Json → Option α) : Option α :=
  (params.member? key).bind read

/-- The member `key` of `params`, as `read` takes it, or `default` when it is missing or `null`;
none when it is something `read` does not take. -/
@[expose]
def opt {α : Type} (params : Json) (key : String) (read : Json → Option α) (default : α) :
    Option α :=
  match params.member? key with
  | none | some .null => some default
  | some value => read value

mutual
/-- **A value a canonical text holds**: one each of whose objects lists its members by strictly
increasing key, in code-point order (`String`'s order), so that no key repeats. -/
@[expose]
def Valid : Json → Prop
  | .arr items => ValidItems items
  | .obj members => (members.map (·.1)).Pairwise (· < ·) ∧ ValidMembers members
  | _ => True
/-- Each item is valid. -/
@[expose]
def ValidItems : List Json → Prop
  | [] => True
  | item :: rest => item.Valid ∧ ValidItems rest
/-- Each member's value is valid. -/
@[expose]
def ValidMembers : List (String × Json) → Prop
  | [] => True
  | (_, value) :: rest => value.Valid ∧ ValidMembers rest
end

/-- `members` with `member` among them by key: before the first member whose key is greater, and
not at all when one has its key, which stays. -/
@[expose]
def insertMember {α : Type} (member : String × α) : List (String × α) → List (String × α)
  | [] => [member]
  | first :: rest =>
    if member.1 < first.1 then member :: first :: rest
    else if member.1 = first.1 then first :: rest else first :: insertMember member rest

/-- **An object's members as its canonical text lists them**: the first member of each key, by
increasing key. -/
@[expose]
def sortMembers {α : Type} (members : List (String × α)) : List (String × α) :=
  members.foldl (fun sorted member => insertMember member sorted) []

mutual
/-- **The value a text of `value` holds**: each object's members as its canonical text lists them
(`sortMembers`), the first member of each key by increasing key. -/
@[expose]
def sorted : Json → Json
  | .arr items => .arr (sortedItems items)
  | .obj members => .obj (sortMembers (sortedMembers members))
  | value => value
/-- Each item, sorted. -/
@[expose]
def sortedItems : List Json → List Json
  | [] => []
  | item :: rest => item.sorted :: sortedItems rest
/-- Each member's value, sorted. -/
@[expose]
def sortedMembers : List (String × Json) → List (String × Json)
  | [] => []
  | (key, value) :: rest => (key, value.sorted) :: sortedMembers rest
end

/-! ## Canonical text

ExactJSON's canonical format (its `SPEC.md`, version 0.3, section 3), in RFC 5234's ABNF:

```abnf
value     = %s"null" / %s"true" / %s"false" / integer / float / string / array / table
array     = "[" [ value *( "," value ) ] "]"
table     = "{" [ member *( "," member ) ] "}"          ; keys strictly increasing
member    = string ":" value
integer   = "0" / [ "-" ] %x31-39 *%x30-39
string    = %x22 *( unescaped / escape ) %x22
escape    = "\" ( %x22 / "\" / "b" / "t" / "n" / "f" / "r" / "u00" 2hexlower )
hexlower  = %x30-39 / %x61-66
unescaped = <any Unicode scalar value but ", \ and U+0000-U+001F>
```

with its rules: no whitespace outside strings; `\u00` only for a character below U+0020 that has
no one-letter escape; keys strictly increasing in code-point order. Each production is one
predicate here, a text with what it spells where a later rule needs that. Linger's values hold no
float, so `float` is no production of its texts. -/

/-- The lowercase hexadecimal digit of a value below 16 (`hexlower`). -/
@[expose]
def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- **`unescaped`**: a character a canonical string holds as itself, any but `"`, `\` and
U+0000 to U+001F. -/
@[expose]
def Unescaped (c : Char) : Prop := c ≠ '"' ∧ c ≠ '\\' ∧ 0x20 ≤ c.toNat

/-- **`escape`**, with the character it stands for: `\"`, `\\`, `\b`, `\t`, `\n`, `\f` and `\r`, and
`\u00` and the two lowercase hexadecimal digits of any other character below U+0020: the one escape
of each character a canonical string does not hold as itself. -/
inductive Escape : List Char → Char → Prop
  /-- `\"`. -/
  | quote : Escape ['\\', '"'] '"'
  /-- `\\`. -/
  | backslash : Escape ['\\', '\\'] '\\'
  /-- `\b`, U+0008. -/
  | backspace : Escape ['\\', 'b'] '\x08'
  /-- `\t`, U+0009. -/
  | tab : Escape ['\\', 't'] '\t'
  /-- `\n`, U+000A. -/
  | newline : Escape ['\\', 'n'] '\n'
  /-- `\f`, U+000C. -/
  | formFeed : Escape ['\\', 'f'] '\x0c'
  /-- `\r`, U+000D. -/
  | carriageReturn : Escape ['\\', 'r'] '\r'
  /-- `\u00` and two lowercase hexadecimal digits, of a character below U+0020 that has no
  one-letter escape. -/
  |
  control (c : Char) (below : c.toNat < 0x20)
    (other : c.toNat ≠ 8 ∧ c.toNat ≠ 9 ∧ c.toNat ≠ 10 ∧ c.toNat ≠ 12 ∧ c.toNat ≠ 13) :
    Escape ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)] c

/-- **`*( unescaped / escape )`**, a canonical string's text between its quotes, with the
characters it spells. -/
inductive Body : List Char → List Char → Prop
  /-- No character. -/
  | nil : Body [] []
  /-- A character as itself, then the rest. -/
  |
  unescaped {c : Char} {text chars : List Char} :
    Unescaped c → Body text chars → Body (c :: text) (c :: chars)
  /-- An escape, then the rest. -/
  |
  escape {e : List Char} {c : Char} {text chars : List Char} :
    Escape e c → Body text chars → Body (e ++ text) (c :: chars)

/-- **`string = %x22 *( unescaped / escape ) %x22`**, with the string it spells. -/
@[expose]
def StringText (text : List Char) (s : String) : Prop :=
  ∃ body, text = '"' :: body ++ ['"'] ∧ Body body s.toList

/-- **`integer = "0" / [ "-" ] %x31-39 *%x30-39`**: no point, no exponent, no leading zero, no
`+` and no `-0`. -/
@[expose]
def IntegerText (text : List Char) : Prop :=
  text = ['0'] ∨
    ∃ (sign : List Char) (first : Char) (digits : List Char),
      (sign = [] ∨ sign = ['-']) ∧
        '1' ≤ first ∧
        first ≤ '9' ∧ (∀ d ∈ digits, '0' ≤ d ∧ d ≤ '9') ∧ text = sign ++ first :: digits

mutual
/-- **`value`**: `null`, `true`, `false`, an integer, a string, an array
(`"[" [ value *( "," value ) ] "]"`) or a table (`"{" [ member *( "," member ) ] "}"`, `member =
string ":" value`) whose keys strictly increase. -/
inductive Text : List Char → Prop
    /-- `null`. -/
  | nullWord : Text ['n', 'u', 'l', 'l']
    /-- `true`. -/
  | trueWord : Text ['t', 'r', 'u', 'e']
    /-- `false`. -/
  | falseWord : Text ['f', 'a', 'l', 's', 'e']
    /-- An integer. -/
  | integer {text : List Char} : IntegerText text → Text text
    /-- A string. -/
  | string {text : List Char} {s : String} : StringText text s → Text text
    /-- `[]`. -/
  | emptyArray : Text ['[', ']']
    /-- An array of a first value and more. -/
  |
  array {first rest : List Char} :
    Text first → MoreValues rest → Text ('[' :: first ++ rest ++ [']'])
    /-- `{}`. -/
  | emptyTable : Text ['{', '}']
    /-- A table of a first member and more, its keys strictly increasing. -/
  |
  table {key value rest : List Char} {s : String} {keys : List String} :
    StringText key s →
      Text value →
      MoreMembers rest keys →
      (s :: keys).Pairwise (· < ·) → Text ('{' :: key ++ ':' :: value ++ rest ++ ['}'])
  /-- **`*( "," value )`** -/
      inductive MoreValues : List Char → Prop
    /-- None. -/
        | nil : MoreValues []
    /-- A comma and a value, then more. -/
        |
        cons {value rest : List Char} :
          Text value → MoreValues rest → MoreValues (',' :: value ++ rest)
  /-- **`*( "," member )`**, with its members' keys, in order. -/
  inductive MoreMembers : List Char → List String → Prop
    /-- None. -/
    | nil : MoreMembers [] []
    /-- A comma and a member, `string ":" value`, then more. -/
    |
    cons {key value rest : List Char} {s : String} {keys : List String} :
      StringText key s →
        Text value →
        MoreMembers rest keys → MoreMembers (',' :: key ++ ':' :: value ++ rest) (s :: keys)
end

/-- **A canonical text**: one value's text in ExactJSON's canonical format (`Text`), one line with
no whitespace outside its strings, its keys strictly increasing and each value spelled one way. -/
@[expose]
def Canonical (text : String) : Prop := Text text.toList

/-! ## Wrong parts -/

/-- A wrong part: a writer that writes a top-level array's items after `, ` and a top-level
object's members after `, `, each key's value after `: `, as `json.dumps` does by default, and any
other value as `write` does. -/
@[expose]
def spaced (write : Json → String) : Json → String
  | .arr items => "[" ++ ", ".intercalate (items.map write) ++ "]"
  | .obj members =>
    "{" ++
      ", ".intercalate (members.map fun (key, value) => write (.str key) ++ ": " ++ write value) ++
      "}"
  | value => write value

/-- A wrong part: a writer that writes a top-level object's members in the order they come, and any
other value as `write` does. -/
@[expose]
def unsorted (write : Json → String) : Json → String
  | .obj members =>
    "{" ++
      ",".intercalate (members.map fun (key, value) => write (.str key) ++ ":" ++ write value) ++
      "}"
  | value => write value

/-- A wrong part: a reader that skips the spaces before a text, as RFC 8259 lets a reader skip
whitespace, and reads the rest as `read` does. -/
@[expose]
def spacious (read : String → Except String Json) (text : String) : Except String Json :=
  read (String.ofList (text.toList.dropWhile (· = ' ')))

/-- A wrong part: a reader that takes an object whose keys decrease, `{"b":null,"a":null}`, as the
object it spells, and reads any other text as `read` does. -/
@[expose]
def unordered (read : String → Except String Json) (text : String) : Except String Json :=
  if text = "{\"b\":null,\"a\":null}" then .ok (.obj [("b", .null), ("a", .null)]) else read text

end Json

end Linger
