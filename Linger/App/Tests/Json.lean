module

import Linger.App.CoreCode.Base64
import Linger.Os.CoreCode.Json
import Linger.App.CoreCode.Serve
meta import Linger.App.CoreCode.Base64
meta import Linger.Os.CoreCode.Json
meta import Linger.App.CoreCode.Serve

/-! Fixtures of the canonical JSON linger reads and writes, its base64, the lines `serve` reads and
what each line is: values written with sorted keys and canonical escapes, canonical texts read back,
texts that are not canonical refused with their reason, and lines that write no control character
but their newline. -/

namespace Linger.App.Tests.Json

open Linger.App.Serve

/-- `text` read and written back, or the reader's reason. -/
def again (text : String) : String :=
  match Json.parse text with
  | .ok value => Json.render value
  | .error why => s!"refused {why}"

-- an object's members by increasing key, the first of each key; no whitespace
#guard
  Json.render
      (.obj
        [("b", .arr [.int 1, .int (-25), .int 0]), ("a", .obj []), ("c", .arr []), ("b", .null)]) ==
    "{\"a\":{},\"b\":[1,-25,0],\"c\":[]}"

-- keys in code-point order: uppercase before lowercase, a prefix before its extensions
#guard
  Json.render (.obj [("ab", .null), ("B", .null), ("a", .null)]) ==
    "{\"B\":null,\"a\":null,\"ab\":null}"

-- the one escape of each character canonical text escapes, and every other character as itself
#guard
  Json.render (.str "a\"b\\c/d\x08\t\n\x0c\r\x01\x1f\x7f\u0085é😀") ==
    "\"a\\\"b\\\\c/d\\b\\t\\n\\f\\r\\u0001\\u001f\x7f\u0085é😀\""

-- canonical texts read back as themselves
#guard
  ["null", "true", "false", "0", "-12", "\"\"", "\"a\\u001fb\\n\"", "[]", "{}", "[1,[2,{}]]",
        "{\"a\":1,\"b\":{\"c\":[]}}", "{\"B\":null,\"a\":null}", "\"é😀\x7f\""].all
    fun text => again text == text

-- texts that are not canonical are refused, each with its reason at the character it stops at
#guard
  again " null" ==
    "refused at character 0: whitespace, which canonical JSON has only within strings"

#guard
  again "[1, 2]" ==
    "refused at character 3: whitespace, which canonical JSON has only within strings"

#guard
  again "{\"b\":1,\"a\":2}" ==
    "refused at character 9: the key \"a\" after \"b\", where canonical JSON lists keys in increasing order"

#guard
  again "{\"a\":1,\"a\":2}" ==
    "refused at character 9: the key \"a\" again, where canonical JSON has each once"

#guard
  again "{\"id\":1.0}" ==
    "refused at character 7: a fraction or an exponent: linger's JSON numbers are integers"

#guard again "-0" == "refused at character 2: the number -0, which canonical JSON writes 0"

#guard again "01" == "refused at character 2: the number 01, which canonical JSON writes 1"

#guard again "\"\\/\"" == "refused at character 2: \\/, which canonical JSON writes /"

#guard again "\"\\u000a\"" == "refused at character 6: \\u000a, which canonical JSON writes \\n"

#guard again "\"\\u0041\"" |>.startsWith "refused at character 5: \\u004"

#guard again "\"\\u001F\"" |>.startsWith "refused at character 6: \\u001F"

#guard again "\"\\ud83d\\ude00\"" |>.startsWith "refused at character 3: \\ud"

#guard
  again "\"a\nb\"" ==
    "refused at character 2: a control character as itself, which canonical JSON writes \\n"

#guard
  ["", "{", "{\"a\":}", "[1,]", "[,1]", "{\"a\" 1}", "{\"a\":1,}", "1e5", "1.", "-", "tru", "nul",
        "[1 2]", "{} x", "1 2", "\"\\x\"", "'a'", "{1:2}", "null\n", "\r"].all
    fun text => (again text).startsWith "refused "

-- a member read as a natural, and ones that are not
#guard (Json.parse "{\"n\":80}").toOption.bind (·.need "n" Json.nat?) == some 80

#guard
  ["-1", "\"80\"", "null"].all fun n =>
    ((Json.parse s!"\{\"n\":{n}}").toOption.bind (·.need "n" Json.nat?)).isNone

-- base64: what `encode` writes `decode` reads back, at every length mod 3
#guard
  (List.range 7).all fun n =>
    let bytes := (List.range n).map fun i => UInt8.ofNat (i * 97 + 251)
    Base64.decode (Base64.encode bytes).toList == some bytes

#guard Base64.encode "hello\r".toUTF8.toList == "aGVsbG8N"

#guard Base64.decode "aGVsbG8K".toList == some "hello\n".toUTF8.toList

#guard ["a", "ab=", "a===", "ab!c", "=AAA"].all fun text => (Base64.decode text.toList).isNone

/-- What a line is, in words. -/
def kind (line : String) : String :=
  match decode line with
  | .request (.number id) method _ => s!"request {id} {method}"
  | .request (.str id) method _ => s!"request '{id}' {method}"
  | .notification method _ => s!"notification {method}"
  | .invalid none (some why) => s!"unparsed: {why}"
  | .invalid (some (.number id)) none => s!"invalid {id}"
  | .invalid _ _ => "invalid"

#guard
  kind "{\"id\":7,\"jsonrpc\":\"2.0\",\"method\":\"sessions/list\"}" == "request 7 sessions/list"

#guard kind "{\"id\":\"x\",\"jsonrpc\":\"2.0\",\"method\":\"m\",\"params\":{}}" == "request 'x' m"

#guard kind "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\"}" == "notification initialized"

-- a line that is not canonical is no message, with the reader's reason: whitespace, a blank line,
-- keys out of order, a float where an integer belongs
#guard (kind "  \t\r").startsWith "unparsed: at character 0: whitespace"

#guard kind "" == "unparsed: at character 0: the end of the text, which holds no value"

#guard
  (kind "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"sessions/list\"}").startsWith
    "unparsed: at character 20: the key \"id\" after \"jsonrpc\""

#guard
  (kind "{\"id\":1.0,\"jsonrpc\":\"2.0\",\"method\":\"m\"}") ==
    "unparsed: at character 7: a fraction or an exponent: linger's JSON numbers are integers"

#guard
  (kind "{\"id\": 1,\"jsonrpc\":\"2.0\",\"method\":\"m\"}").startsWith
    "unparsed: at character 6: whitespace"

#guard kind "{\"id\":3,\"method\":\"m\"}" == "invalid 3"

#guard kind "{\"id\":null,\"jsonrpc\":\"2.0\",\"method\":\"m\"}" == "invalid"

#guard kind "[{\"id\":1,\"jsonrpc\":\"2.0\",\"method\":\"m\"}]" == "invalid"

#guard (kind "{\"id\":1,\"jsonrpc\":\"2.0\"").startsWith "unparsed: "

/-- The lines `chunks` end, as text or `overlong`. -/
def ended (chunks : List String) : List String :=
  (chunks.foldl
      (fun (acc : Lines × List String) chunk =>
        let (next, got) := acc.1.feed chunk.toUTF8.toList
        (next,
          acc.2 ++
            got.map fun
              | .text bytes => (String.fromUTF8? (ByteArray.mk bytes.toArray)).getD "?"
              | .overlong => "overlong"))
      ({}, [])).2

-- a line may come in pieces, and a chunk may end several
#guard ended ["{\"a\"", ":1}\n[]\n", "x"] == ["{\"a\":1}", "[]"]

-- a line past the cap is one overlong line, and the next one reads
#guard ended [String.ofList (List.replicate (lineCap + 5) 'a') ++ "\nok\n"] == ["overlong", "ok"]

#guard
  ended [String.ofList (List.replicate lineCap 'a') ++ "\n"] ==
    [String.ofList (List.replicate lineCap 'a')]

-- every line `serve` writes ends with its one newline and holds no other control character
#guard
  let out : Outgoing :=
    .result (.number 1)
      (.obj [("text", .str (String.ofList ((List.range 0xA0).map Char.ofNat))), ("n", .int (-3))])
  (line out).endsWith "\n" && (line out).toList.dropLast.all fun c => 0x20 ≤ c.toNat

-- `serve`'s lines are canonical: they read back as themselves
#guard
  let out : Outgoing :=
    .error (some (.number 4)) (-32700) "parse error"
      (.obj [("answer", .str "usage"), ("code", .int 2), ("reason", .str "at character 0: x")])
  again ((line out).dropEnd 1).copy == ((line out).dropEnd 1).copy

end Linger.App.Tests.Json
