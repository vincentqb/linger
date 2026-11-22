module

public import Linger.App.CoreSpec

public section

/-! # Linger.App.Serve.Json — JSON text, a line of it

`serve` reads and writes one JSON value a line (RFC 8259). The reader is a character at a time
over the line, with an explicit stack of the arrays and objects still open, so it recurses on
nothing but the line and needs no depth limit: the line's cap bounds it. It takes a string's
escapes, `\uXXXX` included, joins a surrogate pair into its character and reads a lone surrogate
as U+FFFD, refuses a raw control character in a string, as RFC 8259 does, and keeps a number as
the text it was written in. The writer escapes `"` and `\` and writes every control character,
C0, DEL and C1, as `\uXXXX`, so the text it writes holds none and no raw newline: one value, one
line. -/

namespace Linger.App.Serve

/-- The lowercase hexadecimal digit of `n`, which is below 16. -/
private def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- `out` and the `\u` escape of a code unit below 0x10000. -/
private def unicodeEscape (out : String) (n : Nat) : String :=
  ((((out ++ "\\u").push (hexDigit (n / 4096 % 16))).push (hexDigit (n / 256 % 16))).push
        (hexDigit (n / 16 % 16))).push
    (hexDigit (n % 16))

/-- `out` and a character as a JSON string holds it: `"` and `\` escaped, a control character, C0,
DEL or C1, as its `\u` escape, and any other as it is. -/
def Json.escapeChar (out : String) (c : Char) : String :=
  if c = '"' then out ++ "\\\""
  else
    if c = '\\' then out ++ "\\\\"
    else
      if c.toNat < 0x20 ∨ c.toNat = 0x7F ∨ 0x80 ≤ c.toNat ∧ c.toNat < 0xA0 then
        unicodeEscape out c.toNat
      else out.push c

/-- `out` and `text` as a JSON string. -/
def Json.quoted (out text : String) : String := (text.foldl Json.escapeChar (out.push '"')).push '"'

mutual
/-- `out` and a value's JSON text, with no whitespace. -/
def Json.renderTo (out : String) : Json → String
  | .null => out ++ "null"
  | .bool value => out ++ if value then "true" else "false"
  | .number text => out ++ text
  | .str value => Json.quoted out value
  | .arr items => (Json.renderItems (out.push '[') items).push ']'
  | .obj members => (Json.renderMembers (out.push '{') members).push '}'
/-- `out` and the items of an array, comma-separated. -/
def Json.renderItems (out : String) : List Json → String
  | [] => out
  | [item] => Json.renderTo out item
  | item :: rest => Json.renderItems ((Json.renderTo out item).push ',') rest
/-- `out` and the members of an object, comma-separated. -/
def Json.renderMembers (out : String) : List (String × Json) → String
  | [] => out
  | [(key, value)] => Json.renderTo ((Json.quoted out key).push ':') value
  | (key, value) :: rest =>
    Json.renderMembers ((Json.renderTo ((Json.quoted out key).push ':') value).push ',') rest
end

/-- A value's JSON text. -/
def Json.render (value : Json) : String := Json.renderTo "" value

/-! ## Reading -/

/-- A token of JSON text: a bracket, a colon, a comma, or a whole value of no parts. -/
inductive Token where
  /-- `[`, or `{`. -/
  | opens (array : Bool)
  /-- `]`, or `}`. -/
  | closes (array : Bool)
  /-- `:`. -/
  | colon
  /-- `,`. -/
  | comma
  /-- A string, a number, `true`, `false` or `null`. -/
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
  /-- The colon after a key. -/
  | colon
  /-- A value, after the colon. -/
  | value
  /-- A comma, or its end, after a value. -/
  | after

/-- An array or object still open, with what it holds so far, last first. -/
inductive Frame where
  /-- An array. -/
  | arr (items : List Json) (next : ArrayNext)
  /-- An object, with the key whose value comes next. -/
  | obj (members : List (String × Json)) (key : String) (next : ObjectNext)

/-- The values read so far: the arrays and objects still open, innermost first, and the whole
value once it has closed. -/
structure Tree where
  /-- The open arrays and objects, innermost first. -/
  stack : List Frame := []
  /-- The whole value, once read. -/
  whole : Option Json := none

/-- The tree with a complete value where it expects one, or none where it expects none. -/
def Tree.add (t : Tree) (v : Json) : Option Tree :=
  match t.stack with
  | [] => if t.whole.isNone then some { t with whole := some v } else none
  | .arr items .first :: rest | .arr items .item :: rest =>
    some { t with stack := .arr (v :: items) .after :: rest }
  | .obj members key .value :: rest =>
    some { t with stack := .obj ((key, v) :: members) "" .after :: rest }
  | _ => none

/-- Whether the tree expects a value next. -/
def Tree.wantsValue (t : Tree) : Bool :=
  match t.stack with
  | [] => t.whole.isNone
  | .arr _ .first :: _ | .arr _ .item :: _ | .obj _ _ .value :: _ => true
  | _ => false

/-- The tree after a token, or none for a token it does not take there. -/
def Tree.take (t : Tree) : Token → Option Tree
  | .scalar (.str s) =>
    match t.stack with
    | .obj members _ .first :: rest | .obj members _ .key :: rest =>
      some { t with stack := .obj members s .colon :: rest }
    | _ => t.add (.str s)
  | .scalar v => t.add v
  | .opens array =>
    if t.wantsValue then
      some { t with stack := (if array then .arr [] .first else .obj [] "" .first) :: t.stack }
    else none
  | .closes true =>
    match t.stack with
    | .arr items .first :: rest | .arr items .after :: rest =>
      { t with stack := rest }.add (.arr items.reverse)
    | _ => none
  | .closes false =>
    match t.stack with
    | .obj members _ .first :: rest | .obj members _ .after :: rest =>
      { t with stack := rest }.add (.obj members.reverse)
    | _ => none
  | .colon =>
    match t.stack with
    | .obj members key .colon :: rest => some { t with stack := .obj members key .value :: rest }
    | _ => none
  | .comma =>
    match t.stack with
    | .arr items .after :: rest => some { t with stack := .arr items .item :: rest }
    | .obj members _ .after :: rest => some { t with stack := .obj members "" .key :: rest }
    | _ => none

/-- Where the reader is within a token. -/
inductive Lex where
  /-- Between tokens. -/
  | ready
  /-- In a string, with its code units so far, last first. -/
  | text (units : List Nat)
  /-- In a string, after a backslash. -/
  | escaped (units : List Nat)
  /-- In a `\u` escape, with the digits read and their value. -/
  | unicode (units : List Nat) (digits value : Nat)
  /-- In a number, with its characters so far, last first. -/
  | number (chars : List Char)
  /-- In `true`, `false` or `null`, with the characters still to come and its value. -/
  | word (rest : List Char) (value : Json)

/-- A reader of JSON text: where it is within a token, and the values so far. -/
structure Reader where
  /-- Where it is within a token. -/
  lex : Lex := .ready
  /-- The values so far. -/
  tree : Tree := {}

/-- The character a code unit stands for, U+FFFD for a surrogate. -/
private def unitChar (u : Nat) : Char := if 0xD800 ≤ u ∧ u < 0xE000 then '\uFFFD' else Char.ofNat u

/-- A string's characters from its code units: a high and a low surrogate in turn are one
character, and a lone surrogate is U+FFFD. -/
def combine : List Nat → List Char
  | high :: tail@(low :: rest) =>
    if 0xD800 ≤ high ∧ high < 0xDC00 ∧ 0xDC00 ≤ low ∧ low < 0xE000 then
      Char.ofNat (0x10000 + (high - 0xD800) * 0x400 + (low - 0xDC00)) :: combine rest
    else unitChar high :: combine tail
  | [unit] => [unitChar unit]
  | [] => []

/-- The digits at the front of `cs`: how many, and what follows them. -/
def leadingDigits : List Char → Nat × List Char
  | c :: rest =>
    if c.isDigit then ((leadingDigits rest).1 + 1, (leadingDigits rest).2) else (0, c :: rest)
  | [] => (0, [])

/-- After an integer's digits: an optional fraction, then an optional exponent, then nothing. -/
private def fractionValid (cs : List Char) : Bool :=
  let exponentValid (rest : List Char) : Bool :=
    match rest with
    | [] => true
    | e :: more =>
      (e = 'e' || e = 'E') &&
        (let digits :=
          match more with
          | '+' :: m | '-' :: m => m
          | m => m
        (leadingDigits digits).1 > 0 && (leadingDigits digits).2.isEmpty)
  match cs with
  | '.' :: more => (leadingDigits more).1 > 0 && exponentValid (leadingDigits more).2
  | rest => exponentValid rest

/-- Whether `cs` is a JSON number: an optional `-`, `0` or digits that start with another, then an
optional fraction and exponent. -/
def numberValid (cs : List Char) : Bool :=
  let unsigned :=
    match cs with
    | '-' :: rest => rest
    | rest => rest
  match unsigned with
  | '0' :: rest => fractionValid rest
  | c :: _ => c.isDigit && fractionValid (leadingDigits unsigned).2
  | [] => false

/-- The code unit a one-character escape stands for: `\"`, `\\`, `\/`, `\b`, `\f`, `\n`, `\r`,
`\t`. -/
private def escapeUnit (c : Char) : Option Nat :=
  if c = '"' then some 0x22
  else
    if c = '\\' then some 0x5C
    else
      if c = '/' then some 0x2F
      else
        if c = 'b' then some 8
        else
          if c = 'f' then some 12
          else
            if c = 'n' then some 10
            else if c = 'r' then some 13 else if c = 't' then some 9 else none

/-- The value of a hexadecimal digit. -/
private def hexValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else
    if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 87)
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 55) else none

/-- The reader after a token, between tokens again. -/
private def Reader.token (r : Reader) (t : Token) : Option Reader :=
  (r.tree.take t).map fun tree => { lex := .ready, tree }

/-- The reader after the number whose characters, last first, are `chars`. -/
private def Reader.endNumber (r : Reader) (chars : List Char) : Option Reader :=
  if numberValid chars.reverse then r.token (.scalar (.number (String.ofList chars.reverse)))
  else none

/-- The reader after `c`, read between tokens. -/
private def Reader.start (r : Reader) (c : Char) : Option Reader :=
  if c = ' ' ∨ c = '\t' ∨ c = '\n' ∨ c = '\r' then some r
  else
    if c = '"' then some { r with lex := .text [] }
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
                  if c = 't' then some { r with lex := .word ['r', 'u', 'e'] (.bool true) }
                  else
                    if c = 'f' then some { r with lex := .word ['a', 'l', 's', 'e'] (.bool false) }
                    else
                      if c = 'n' then some { r with lex := .word ['u', 'l', 'l'] .null }
                      else if c = '-' ∨ c.isDigit then some { r with lex := .number [c] } else none

/-- The reader after one more character, or none once the text is no JSON. -/
def Reader.feed (r : Reader) (c : Char) : Option Reader :=
  match r.lex with
  | .ready => r.start c
  | .text units =>
    if c = '"' then r.token (.scalar (.str (String.ofList (combine units.reverse))))
    else
      if c = '\\' then some { r with lex := .escaped units }
      else if c.toNat < 0x20 then none else some { r with lex := .text (c.toNat :: units) }
  | .escaped units =>
    match escapeUnit c with
    | some unit => some { r with lex := .text (unit :: units) }
    | none => if c = 'u' then some { r with lex := .unicode units 0 0 } else none
  | .unicode units digits value =>
    match hexValue c with
    | none => none
    | some h =>
      if digits = 3 then some { r with lex := .text ((value * 16 + h) :: units) }
      else some { r with lex := .unicode units (digits + 1) (value * 16 + h) }
  | .number chars =>
    if c.isDigit ∨ c = '.' ∨ c = 'e' ∨ c = 'E' ∨ c = '+' ∨ c = '-' then
      some { r with lex := .number (c :: chars) }
    else (r.endNumber chars).bind (·.start c)
  | .word rest value =>
    match rest with
    | [last] => if c = last then r.token (.scalar value) else none
    | next :: more => if c = next then some { r with lex := .word more value } else none
    | [] => none

/-- The whole value a reader read, once the text has ended: none while a token or a value is
still open. -/
def Reader.finish (r : Reader) : Option Json :=
  let ended :=
    match r.lex with
    | .ready => some r
    | .number chars => r.endNumber chars
    | _ => none
  ended.bind fun r => if r.tree.stack.isEmpty then r.tree.whole else none

/-- The JSON value `text` is, with whitespace around it, or none for text that is no JSON. -/
def Json.parse (text : String) : Option Json :=
  (text.foldl (fun r c => r.bind (·.feed c)) (some {})).bind Reader.finish

/-! ## Base64 -/

/-- The base64 digit of a value below 64 (RFC 4648, section 4). -/
private def Base64.char (n : Nat) : Char :=
  if n < 26 then Char.ofNat (65 + n)
  else
    if n < 52 then Char.ofNat (71 + n)
    else if n < 62 then Char.ofNat (n - 4) else if n = 62 then '+' else '/'

/-- `out` and the padded base64 of `bytes`. -/
private def Base64.encodeTo (out : String) : List UInt8 → String
  | a :: b :: c :: rest =>
    Base64.encodeTo
      ((((out.push (Base64.char (a.toNat / 4))).push
                (Base64.char (a.toNat % 4 * 16 + b.toNat / 16))).push
            (Base64.char (b.toNat % 16 * 4 + c.toNat / 64))).push
        (Base64.char (c.toNat % 64)))
      rest
  | [a, b] =>
    (((out.push (Base64.char (a.toNat / 4))).push
              (Base64.char (a.toNat % 4 * 16 + b.toNat / 16))).push
          (Base64.char (b.toNat % 16 * 4))).push
      '='
  | [a] =>
    (((out.push (Base64.char (a.toNat / 4))).push (Base64.char (a.toNat % 4 * 16))).push '=').push
      '='
  | [] => out

/-- The padded base64 of `bytes` (RFC 4648, section 4), which `Base64.decode` reads back. -/
def Base64.encode (bytes : List UInt8) : String := Base64.encodeTo "" bytes

end Linger.App.Serve
