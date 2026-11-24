module

public import Linger.App.CoreSpec

public section

/-! # Linger.App.Serve.Base64 — bytes as base64 text

`serve` carries bytes, an attach's stream, a capture's screen and `send`'s input, as padded base64
text (RFC 4648, section 4), which `Base64.decode` reads back. -/

namespace Linger.App.Serve

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
