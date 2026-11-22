module

import Linger.App.CoreCode.Json
import Linger.App.CoreCode.Serve
meta import Linger.App.CoreCode.Json
meta import Linger.App.CoreCode.Serve

/-! Fixtures of the JSON text `serve` reads and writes, its base64, the lines it reads and what
each line is: values read and written back, text that is no JSON, escapes and surrogates, and
lines that write no control character but their newline. -/

namespace Linger.App.Tests.Json

open Linger.App.Serve

/-- `text` read and written back, or `none` for text that is no JSON. -/
def again (text : String) : Option String := (Json.parse text).map Json.render

-- whitespace goes, members and items keep their order, a number keeps how it was written
#guard
  again " { \"b\" : [ 1 , -2.5e3 , 0 ] , \"a\" : {} , \"c\" : [ ] } " ==
    some "{\"b\":[1,-2.5e3,0],\"a\":{},\"c\":[]}"

#guard again "[true,false,null,\"\"]" == some "[true,false,null,\"\"]"

-- escapes read as their characters; a surrogate pair is one character, a lone one U+FFFD
#guard again "\"a\\\"b\\\\c\\/d\\u00e9\\ud83d\\ude00\\ud800x\"" == some "\"a\\\"b\\\\c/dé😀\uFFFDx\""

-- a control character, C0, DEL or C1, is written as its escape, so a line holds none
#guard Json.render (.str "a\nb\x1b[0m\x7f\u0085z") == "\"a\\u000ab\\u001b[0m\\u007f\\u0085z\""

-- text that is no JSON
#guard
  ["", "{", "{\"a\":}", "[1,]", "[,1]", "{\"a\" 1}", "{\"a\":1,}", "01", "1.", "-", "1e", "tru",
        "nul", "[1 2]", "{} x", "1 2", "\"\x01\"", "\"\\x\"", "\"\\u12g4\"", "'a'", "{1:2}"].all
    fun text => (Json.parse text).isNone

-- a number a member reads as a natural, and one it does not
#guard (Json.parse "{\"n\":80}").bind (·.need "n" Json.nat?) == some 80

#guard
  ["-1", "1.0", "1e2", "\"80\""].all fun n =>
    ((Json.parse s!"\{\"n\":{n}}").bind (·.need "n" Json.nat?)).isNone

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
  | none => "blank"
  | some (.request (.number id) method _) => s!"request {id} {method}"
  | some (.request (.str id) method _) => s!"request '{id}' {method}"
  | some (.notification method _) => s!"notification {method}"
  | some (.invalid none true) => "unparsed"
  | some (.invalid (some (.number id)) false) => s!"invalid {id}"
  | some (.invalid _ _) => "invalid"

#guard
  kind "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"sessions/list\"}" == "request 7 sessions/list"

#guard kind "{\"jsonrpc\":\"2.0\",\"id\":\"x\",\"method\":\"m\",\"params\":{}}" == "request 'x' m"

#guard kind "{\"jsonrpc\":\"2.0\",\"method\":\"initialized\"}" == "notification initialized"

#guard kind "  \t\r" == "blank"

#guard kind "{\"id\":3,\"method\":\"m\"}" == "invalid 3"

#guard kind "{\"jsonrpc\":\"2.0\",\"id\":null,\"method\":\"m\"}" == "invalid"

#guard kind "[{\"jsonrpc\":\"2.0\",\"id\":1,\"method\":\"m\"}]" == "invalid"

#guard kind "{\"jsonrpc\":\"2.0\",\"id\":1" == "unparsed"

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
    .result (.number "1")
      (.obj
        [("text", .str (String.ofList ((List.range 0xA0).map Char.ofNat))), ("n", .number "-3")])
  (line out).endsWith "\n" &&
    (line out).toList.dropLast.all fun c =>
      !(c.toNat < 0x20 || c.toNat == 0x7F || (0x80 ≤ c.toNat && c.toNat < 0xA0))

end Linger.App.Tests.Json
