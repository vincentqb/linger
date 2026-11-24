module

public import Linger.Os.CoreSpec

public section

/-! # Linger.Json — canonical JSON, written and read

Linger writes and reads one JSON format, ExactJSON's canonical text (`Json.Canonical`): `serve`'s
lines, a host's replies and `ls --porcelain`. The writer (`render`) writes each object's members by
increasing key, the first of each key (`sortMembers`), each string with the one escape canonical
text has for a character (`escape`) and each integer in decimal, with no whitespace: one line,
which holds no control character. The reader (`parse`) takes exactly those texts and refuses any
other with a reason, at the character where the text stops being canonical: whitespace, an
escape or a number spelled otherwise, a key not greater than the one before it, a fraction or an
exponent, which no linger value has, or text that is no JSON. It reads a character at a time with
an explicit stack of the arrays and objects still open, so it recurses on nothing but the text
and needs no depth limit. -/

namespace Linger.Json

/-! ## Writing -/

/-- **A character's text within a canonical string**: `\"`, `\\`, `\b`, `\t`, `\n`, `\f` and `\r`,
`\u00` and two lowercase hexadecimal digits for any other character below U+0020, and any other
character as itself. -/
def escape (c : Char) : List Char :=
  if c = '"' then ['\\', '"']
  else
    if c = '\\' then ['\\', '\\']
    else
      if c = '\x08' then ['\\', 'b']
      else
        if c = '\t' then ['\\', 't']
        else
          if c = '\n' then ['\\', 'n']
          else
            if c = '\x0c' then ['\\', 'f']
            else
              if c = '\r' then ['\\', 'r']
              else
                if c.toNat < 0x20 then
                  ['\\', 'u', '0', '0', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
                else [c]

/-- A string's canonical text: its characters' texts (`escape`) between quotes. -/
def quote (s : String) : List Char := '"' :: s.toList.flatMap escape ++ ['"']

/-- Texts joined by commas. -/
def joined : List (List Char) → List Char
  | [] => []
  | [text] => text
  | text :: rest => text ++ ',' :: joined rest

/-- A member's text: its key's, a colon, its value's. -/
def memberText (member : String × List Char) : List Char := quote member.1 ++ ':' :: member.2

mutual
/-- **A value's canonical text**: `null`, `true` and `false`; an integer in decimal, `-` before a
negative one; a string between quotes, each character as `escape` writes it; an array's items and
an object's members joined by commas, the members by increasing key, the first of each key
(`sortMembers`), each its key, a colon and its value. -/
def chars : Json → List Char
  | .null => ['n', 'u', 'l', 'l']
  | .bool true => ['t', 'r', 'u', 'e']
  | .bool false => ['f', 'a', 'l', 's', 'e']
  | .int value => (toString value).toList
  | .str value => quote value
  | .arr items => '[' :: joined (itemChars items) ++ [']']
  | .obj members => '{' :: joined ((sortMembers (memberChars members)).map memberText) ++ ['}']
/-- Each item's text. -/
def itemChars : List Json → List (List Char)
  | [] => []
  | item :: rest => chars item :: itemChars rest
/-- Each member's key and its value's text. -/
def memberChars : List (String × Json) → List (String × List Char)
  | [] => []
  | (key, value) :: rest => (key, chars value) :: memberChars rest
end

/-- **A value's canonical text** (`chars`). -/
def render (value : Json) : String := String.ofList (chars value)

/-! ## Reading -/

/-- A token of canonical text: a bracket, a colon, a comma, or a whole value of no parts. -/
inductive Token where
  /-- `[`, or `{`. -/
  | opens (array : Bool)
  /-- `]`, or `}`. -/
  | closes (array : Bool)
  /-- `:`. -/
  | colon
  /-- `,`. -/
  | comma
  /-- A string, an integer, `true`, `false` or `null`. -/
  | scalar (value : Json)

/-- What an open array takes next. -/
inductive ArrayNext where
  /-- Its first item, or its end. -/
  | first
  /-- An item, after a comma. -/
  | item
  /-- A comma, or its end, after an item. -/
  | after

/-- What an open object takes next. -/
inductive ObjectNext where
  /-- Its first key, or its end. -/
  | first
  /-- A key, after a comma. -/
  | key
  /-- The colon after this key. -/
  | colon (key : String)
  /-- This key's value, after its colon. -/
  | value (key : String)
  /-- A comma, or its end, after a value. -/
  | after

/-- An array or object still open, with what it holds so far, last first. -/
inductive Frame where
  /-- An array. -/
  | arr (items : List Json) (next : ArrayNext)
  /-- An object. -/
  | obj (members : List (String × Json)) (next : ObjectNext)

/-- The values read so far: the arrays and objects still open, innermost first, and the whole
value once it has closed. -/
structure Tree where
  /-- The open arrays and objects, innermost first. -/
  stack : List Frame := []
  /-- The whole value, once read. -/
  whole : Option Json := none

/-- What the tree takes next, in words. -/
def Tree.wants (t : Tree) : String :=
  match t.stack, t.whole with
  | [], none => "a value"
  | [], some _ => "nothing, after the whole value"
  | .arr _ .first :: _, _ => "an item or ]"
  | .arr _ .item :: _, _ => "an item"
  | .arr _ .after :: _, _ => ", or ]"
  | .obj _ .first :: _, _ => "a key or }"
  | .obj _ .key :: _, _ => "a key"
  | .obj _ (.colon _) :: _, _ => ":"
  | .obj _ (.value _) :: _, _ => "a value"
  | .obj _ .after :: _, _ => ", or }"

/-- A token, in words. -/
def Token.describe : Token → String
  | .opens true => "["
  | .opens false => "{"
  | .closes true => "]"
  | .closes false => "}"
  | .colon => ":"
  | .comma => ","
  | .scalar (.str _) => "a string"
  | .scalar (.int _) => "a number"
  | .scalar _ => "a word"

/-- The refusal of a token the tree does not take there. -/
def Tree.refuse {α : Type} (t : Tree) (token : Token) : Except String α :=
  .error s!"{token.describe}, where canonical JSON has {t.wants}"

/-- The tree with a complete value where it takes one. -/
def Tree.add (t : Tree) (v : Json) : Except String Tree :=
  match t.stack with
  | [] => if t.whole.isNone then .ok { t with whole := some v } else t.refuse (.scalar v)
  | .arr items .first :: rest | .arr items .item :: rest =>
    .ok { t with stack := .arr (v :: items) .after :: rest }
  | .obj members (.value key) :: rest =>
    .ok { t with stack := .obj ((key, v) :: members) .after :: rest }
  | _ => t.refuse (.scalar v)

/-- Whether the tree takes a value next. -/
def Tree.wantsValue (t : Tree) : Bool :=
  match t.stack with
  | [] => t.whole.isNone
  | .arr _ .first :: _ | .arr _ .item :: _ | .obj _ (.value _) :: _ => true
  | _ => false

/-- The text of a key, for a refusal. -/
def keyText (key : String) : String := String.ofList (quote key)

/-- Whether `key` may come after the members read so far, last first: it is greater than the last
one's key. -/
def keyAfter (members : List (String × Json)) (key : String) : Except String Unit :=
  match members with
  | [] => .ok ()
  | (last, _) :: _ =>
    if last < key then .ok ()
    else
      if last = key then .error s!"the key {keyText key} again, where canonical JSON has each once"
      else
        .error
          s!"the key {keyText key} after {keyText last}, where canonical JSON lists keys in \
            increasing order"

/-- **The tree after a token**, or why canonical JSON has no such token there. -/
def Tree.take (t : Tree) (token : Token) : Except String Tree :=
  match token with
  | .scalar (.str s) =>
    match t.stack with
    | .obj members .first :: rest | .obj members .key :: rest =>
      (keyAfter members s).map fun _ => { t with stack := .obj members (.colon s) :: rest }
    | _ => t.add (.str s)
  | .scalar v => t.add v
  | .opens array =>
    if t.wantsValue then
      .ok { t with stack := (if array then .arr [] .first else .obj [] .first) :: t.stack }
    else t.refuse token
  | .closes true =>
    match t.stack with
    | .arr items .first :: rest | .arr items .after :: rest =>
      { t with stack := rest }.add (.arr items.reverse)
    | _ => t.refuse token
  | .closes false =>
    match t.stack with
    | .obj members .first :: rest | .obj members .after :: rest =>
      { t with stack := rest }.add (.obj members.reverse)
    | _ => t.refuse token
  | .colon =>
    match t.stack with
    | .obj members (.colon key) :: rest => .ok { t with stack := .obj members (.value key) :: rest }
    | _ => t.refuse token
  | .comma =>
    match t.stack with
    | .arr items .after :: rest => .ok { t with stack := .arr items .item :: rest }
    | .obj members .after :: rest => .ok { t with stack := .obj members .key :: rest }
    | _ => t.refuse token

/-- Where the reader is within a token. -/
inductive Lex where
  /-- Between tokens. -/
  | ready
  /-- In a string, with its characters so far, last first. -/
  | text (chars : List Char)
  /-- In a string, after a backslash. -/
  | escaped (chars : List Char)
  /-- In a `\u` escape, with the digits read, in order. -/
  | unicode (chars : List Char) (digits : List Char)
  /-- In a number, with its characters so far, last first. -/
  | number (chars : List Char)
  /-- In `null`, `true` or `false`: its value, the characters read and those still to come. -/
  | word (value : Json) (done rest : List Char)

/-- A reader of canonical text: where it is within a token, and the values so far. -/
structure Reader where
  /-- Where it is within a token. -/
  lex : Lex := .ready
  /-- The values so far. -/
  tree : Tree := {}

/-- The character a one-letter escape stands for: `\"`, `\\`, `\b`, `\t`, `\n`, `\f` and `\r`. -/
def shortEscape (c : Char) : Option Char :=
  if c = '"' then some '"'
  else
    if c = '\\' then some '\\'
    else
      if c = 'b' then some '\x08'
      else
        if c = 't' then some '\t'
        else
          if c = 'n' then some '\n'
          else if c = 'f' then some '\x0c' else if c = 'r' then some '\r' else none

/-- The value of a lowercase hexadecimal digit. -/
def lowerHex (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - 48)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87) else none

/-- The integer a number's characters spell: its digits' value, negated after a `-`. -/
def numberValue : List Char → Int
  | '-' :: digits => -(Nat.ofDigitChars 10 digits 0 : Int)
  | digits => (Nat.ofDigitChars 10 digits 0 : Int)

/-- The refusal of a number not spelled as canonical text spells it. -/
def numberRefusal (text : List Char) : String :=
  if text = ['-'] then "a - with no digits after it"
  else
    s!"the number {String.ofList text}, which canonical JSON writes {toString (numberValue text)}"

/-- The reader after a token, between tokens again. -/
def Reader.token (r : Reader) (token : Token) : Except String Reader :=
  (r.tree.take token).map fun tree => { lex := .ready, tree }

/-- The reader after the number whose characters, last first, are `chars`: its integer, when they
spell it as canonical text does. -/
def Reader.endNumber (r : Reader) (chars : List Char) : Except String Reader :=
  if (toString (numberValue chars.reverse)).toList = chars.reverse then
    r.token (.scalar (.int (numberValue chars.reverse)))
  else .error (numberRefusal chars.reverse)

/-- The reader after `c`, read between tokens. -/
def Reader.start (r : Reader) (c : Char) : Except String Reader :=
  if c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' then
    .error "whitespace, which canonical JSON has only within strings"
  else
    if c = '"' then .ok { r with lex := .text [] }
    else
      if c = '[' then r.token (.opens true)
      else
        if c = '{' then r.token (.opens false)
        else
          if c = ']' then r.token (.closes true)
          else
            if c = '}' then r.token (.closes false)
            else
              if c = ':' then r.token .colon
              else
                if c = ',' then r.token .comma
                else
                  if c = 't' then .ok { r with lex := .word (.bool true) ['t'] ['r', 'u', 'e'] }
                  else
                    if c = 'f' then
                      .ok { r with lex := .word (.bool false) ['f'] ['a', 'l', 's', 'e'] }
                    else
                      if c = 'n' then .ok { r with lex := .word .null ['n'] ['u', 'l', 'l'] }
                      else
                        if c = '-' ∨ '0' ≤ c ∧ c ≤ '9' then .ok { r with lex := .number [c] }
                        else .error s!"{c}, which canonical JSON has only within strings"

/-- The code point of `\u00`, then `high`, `0` or `1`, then the digit whose value is `low`. -/
def unicodeCode (high : Char) (low : Nat) : Nat := (if high = '1' then 16 else 0) + low

/-- The refusal of a `\u` escape canonical JSON does not write. -/
def unicodeRefusal (digits : List Char) : String :=
  s!"\\u{String.ofList digits}, where canonical JSON writes a character as itself or by its \
    one-letter escape, and \\u00 with two lowercase hexadecimal digits only for any other below \
    U+0020"

/-- **The reader after one more character**, or why the text is not canonical there. -/
def Reader.step (r : Reader) (c : Char) : Except String Reader :=
  match r.lex with
  | .ready => r.start c
  | .text chars =>
    if c = '"' then r.token (.scalar (.str (String.ofList chars.reverse)))
    else
      if c = '\\' then .ok { r with lex := .escaped chars }
      else
        if c.toNat < 0x20 then
          .error
            s!"a control character as itself, which canonical JSON writes \
              {String.ofList (escape c)}"
        else .ok { r with lex := .text (c :: chars) }
  | .escaped chars =>
    match shortEscape c with
    | some d => .ok { r with lex := .text (d :: chars) }
    | none =>
      if c = 'u' then .ok { r with lex := .unicode chars [] }
      else
        if c = '/' then .error "\\/, which canonical JSON writes /"
        else .error s!"\\{c}, an escape JSON does not have"
  | .unicode chars digits =>
    match digits with
    | [] | ['0'] =>
      if c = '0' then .ok { r with lex := .unicode chars (digits ++ ['0']) }
      else .error (unicodeRefusal (digits ++ [c]))
    | ['0', '0'] =>
      if c = '0' ∨ c = '1' then .ok { r with lex := .unicode chars (digits ++ [c]) }
      else .error (unicodeRefusal (digits ++ [c]))
    | ['0', '0', high] =>
      match lowerHex c with
      | none => .error (unicodeRefusal (digits ++ [c]))
      | some low =>
        if unicodeCode high low ∈ [8, 9, 10, 12, 13] then
          .error
            s!"\\u00{high}{c}, which canonical JSON writes \
              {String.ofList (escape (Char.ofNat (unicodeCode high low)))}"
        else .ok { r with lex := .text (Char.ofNat (unicodeCode high low) :: chars) }
    | _ => .error (unicodeRefusal (digits ++ [c]))
  | .number chars =>
    if '0' ≤ c ∧ c ≤ '9' then .ok { r with lex := .number (c :: chars) }
    else
      if c = '.' ∨ c = 'e' ∨ c = 'E' then
        .error "a fraction or an exponent: linger's JSON numbers are integers"
      else (r.endNumber chars).bind (·.start c)
  | .word value done rest =>
    match rest with
    | next :: more =>
      if c = next then
        if more = [] then r.token (.scalar value)
        else .ok { r with lex := .word value (done ++ [c]) more }
      else .error s!"{String.ofList (done ++ [c])}, which is no word of JSON"
    | [] => .error s!"{String.ofList (done ++ [c])}, which is no word of JSON"

/-- The whole value a reader read, once the text has ended: none while a token or a value is
still open. -/
def Reader.finish (r : Reader) : Except String Json := do
  let ended ←
    match r.lex with
    | .ready =>
      .ok r
    | .number chars =>
      r.endNumber chars
    | .text _ | .escaped _ | .unicode _ _ =>
      .error "the end of the text, within a string"
    | .word _ done _ =>
      .error s!"the end of the text, after {String.ofList done}"
  match ended.tree.stack, ended.tree.whole with
  | [], some whole =>
    .ok whole
  | [], none =>
    .error "the end of the text, which holds no value"
  | _ :: _, _ =>
    .error "the end of the text, where an array or an object is still open"

/-- The reader after `cs`, the first at character `pos`, or the refusal at the first character
the text is not canonical at. -/
def run (r : Reader) (pos : Nat) : List Char → Except String Reader
  | [] => .ok r
  | c :: cs =>
    match r.step c with
    | .ok next => run next (pos + 1) cs
    | .error why => .error s!"at character {pos}: {why}"

/-- **The value a canonical text holds**, or why the text is not canonical, at the character
where it stops being so. -/
def parse (text : String) : Except String Json :=
  match run {} 0 text.toList with
  | .error why => .error why
  | .ok r =>
    match r.finish with
    | .ok value => .ok value
    | .error why => .error s!"at character {text.length}: {why}"

end Linger.Json
