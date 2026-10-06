module

import Theorems.Input

/-! Ordinary imports expose physical input events and the incremental API.
Evaluation fixtures are separate so implementation imports cannot hide a
missing public declaration or reintroduce application actions. -/

namespace Tests.InputApi

open Linger.Tools.Input

example : Key := .text '界'

example : Key := .control 18

example : List Key := [.backspace, .tab, .enter, .escape, .up, .down, .home, .end]

example : State := init

example : State → Bool := pending

example : State → UInt8 → State × List Key := feed

example : State → State × List Key := flush

example (state : State) (byte : UInt8) : State × List Key :=
  let (next, events) := feed state byte
  let (idle, final) := flush next
  (idle, events ++ final)

example (event : Key) : Option Char :=
  match event with
  | .text char => some char
  | .control _ | .backspace | .tab | .enter | .escape | .up | .down | .home | .end => none

example (state : State) (byte : UInt8) : (feed state byte).2.length ≤ 1 := feed_length state byte

example (state : State) (byte : UInt8) (key : Key) (hpaste : state.paste = true)
    (h : key ∈ (feed state byte).2) :
    ∃ char, key = .text char := feed_paste_only_text state byte key hpaste h

example (state : State) : .enter ∉ (flush state).2 := flush_no_enter state

#check_failure Linger.Tools.Key

#check_failure Linger.Tools.Picker.State

end Tests.InputApi
