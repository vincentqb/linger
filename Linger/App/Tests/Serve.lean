module

import Linger.App.CoreCode.Base64
import Linger.App.CoreCode.Codec
import Linger.App.CoreCode.Serve
import Linger.Display.CoreCode.Listing
meta import Linger.App.CoreCode.Base64
meta import Linger.App.CoreCode.Codec
meta import Linger.App.CoreCode.Serve
meta import Linger.Display.CoreCode.Listing

/-! Fixtures of the JSON `serve` reads and writes, through ExactJSON: its base64, what each line it
reads is, the lines it refuses and ExactJSON's reasons, a method's params read exactly, and the
lines it writes, which hold no control character but their newline, nor a line or paragraph
separator, and read back as themselves; and `ls --porcelain`'s records, whose flags are JSON
booleans and counts JSON integers. -/

namespace Linger.App.Tests.Serve

open Linger.App.Serve

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

-- a line that is not canonical is no message, with ExactJSON's reason: whitespace, a blank line,
-- keys out of order, a raw line separator, an uppercase escape
#guard (kind "  \t\r").startsWith "unparsed: at character 0: "

#guard (kind "").startsWith "unparsed: at character 0: "

#guard
  (kind "{\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"sessions/list\"}").startsWith
    "unparsed: at character 17: keys must increase"

#guard
  (kind "{\"id\": 1,\"jsonrpc\":\"2.0\",\"method\":\"m\"}").startsWith "unparsed: at character 6: "

#guard
  (kind "{\"id\":1,\"jsonrpc\":\"2.0\",\"method\":\"a\u2028b\"}").startsWith
    "unparsed: at character 35: write \\u2028, not the character itself"

#guard
  (kind "{\"id\":1,\"jsonrpc\":\"2.0\",\"method\":\"\\u007F\"}").startsWith
    "unparsed: at character 34: write \\u007f, not \\u007F"

-- a canonical object that is no request: no `jsonrpc`, an id that is null, an array, and a member
-- JSON-RPC does not define
#guard kind "{\"id\":3,\"method\":\"m\"}" == "invalid 3"

#guard kind "{\"id\":null,\"jsonrpc\":\"2.0\",\"method\":\"m\"}" == "invalid"

#guard kind "[{\"id\":1,\"jsonrpc\":\"2.0\",\"method\":\"m\"}]" == "invalid"

#guard kind "{\"extra\":1,\"id\":4,\"jsonrpc\":\"2.0\",\"method\":\"m\"}" == "invalid 4"

/-- The call a method's params are, as text, or `none`. -/
def called (method : String) (params : String) : Option String :=
  match ExactJSON.Value.parse params with
  | .ok value => (Call.read method value).map fun call => String.intercalate " " call.words
  | .error _ => none

-- a method's params read exactly: its members, by increasing key, each of its type
#guard called "session/kill" "{\"name\":\"x\"}" == some "kill x"

#guard
  called "session/attach" "{\"command\":[\"vi\"],\"name\":\"x\",\"readOnly\":true}" ==
    some "attach --read-only -- x vi"

#guard called "sessions/list" "{}" == some "ls --porcelain --"

-- a member the method does not define, `null` for one left out and a member of another type are
-- no params of it
#guard
  [("session/kill", "{\"force\":true,\"name\":\"x\"}"), ("sessions/list", "{\"names\":null}"),
        ("session/resize", "{\"cols\":\"80\",\"name\":\"x\",\"rows\":24}"),
        ("sessions/subscribe", "{\"x\":1}")].all
    fun (method, params) => called method params == none

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

-- every line `serve` writes ends with its one newline and holds no control character, and no line
-- or paragraph separator, which ExactJSON escapes
#guard
  let out : Outgoing :=
    .result (.number 1)
      (ExactJSON.toValue
        ({ answer := "done", code := 0,
           text? := some (String.ofList ((List.range 0xA0).map Char.ofNat) ++ "\u2028\u2029") } :
          Result))
  (line out).endsWith "\n" &&
    (line out).toList.dropLast.all fun c =>
      0x20 ≤ c.toNat && !(0x7F ≤ c.toNat && c.toNat ≤ 0x9F) && c.toNat != 0x2028 &&
        c.toNat != 0x2029

-- `serve`'s lines are canonical: they read back as themselves
#guard
  let out : Outgoing :=
    .error (some (.number 4)) (-32700) "parse error"
      (ExactJSON.toValue
        ({ answer := "usage", code := 2, reason? := some "at character 0: x" } : Result))
  match ExactJSON.Value.parse ((line out).dropEnd 1).copy with
  | .ok value => ExactJSON.Value.render value == ((line out).dropEnd 1).copy
  | .error _ => false

-- `ls --porcelain`: a flag is a JSON boolean, a count a JSON integer, and other fields strings
#guard
  Linger.Display.Listing.porcelain
      [[("name", "w"), ("pid", "42"), ("running", "true"), ("cmd", "sh"), ("exit", "x")]] ==
    "{\"cmd\":\"sh\",\"name\":\"w\",\"pid\":42,\"running\":true}\n"

end Linger.App.Tests.Serve
