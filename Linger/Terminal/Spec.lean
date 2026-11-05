module

public import Linger.Terminal.Replay
public import Linger.Terminal.Vt

public section

/-! # Terminal states a running session can hold, and what a streamed repaint emits

`LiveReachableVt` is the least set of states containing a fresh emulator and closed under what
a live session does to one: feed pty bytes, resize on attach, forget partial parser state (what
a checkpoint save and load does) and come off disk through the decoder's door. Headline
theorems about repainting and checkpoints assume it of the terminals involved. Every `Vt` a
program can hold satisfies it: `Vt.init` and the decoder are the only doors, and the session
transformers the only ways forward (`Linger/Terminal/Vt.lean` lists them).

It does not say a scrollback row is the screen's width: `Vt.resize` leaves the scrollback at
its old width.

`Replay.Emits` is the output of streaming a repaint plan one bounded step at a time. -/

namespace Linger.Terminal.Vt

/-- The states a live session can hold. -/
inductive LiveReachableVt : Vt → Prop where
  /-- A fresh screen. -/
  | init (cols rows : Nat) : LiveReachableVt (Vt.init cols rows)
  /-- Pty output fed to a state a session holds. -/
  | feed {v : Vt} (h : LiveReachableVt v) (bytes : List UInt8) : LiveReachableVt (v.feed bytes)
  /-- A resize of a state a session holds. -/
  | resize {v : Vt} (h : LiveReachableVt v) (cols rows : Nat) : LiveReachableVt (v.resize cols rows)
  /-- A state a session holds, with its partial parser state forgotten. -/
  | quiesce {v : Vt} (h : LiveReachableVt v) : LiveReachableVt v.quiesce
  /-- **The resume rung.** A state the decoder's door accepts is one a live session can hold:
  not because the record on disk was trustworthy, but because the door refuses every record
  that does not describe such a state. The premise is the door's own acceptance, never a
  bound on the state's fields. -/
  | ofDecoded {v : Vt} (h : v.Decodable) : LiveReachableVt v

end Linger.Terminal.Vt

namespace Linger.Terminal.Replay

/-- `out` is what streaming `plan` emits when each step may take `budget` bytes: the chunks
`next` returns until it reports the end, in order, each at most `budget` bytes long. -/
inductive Emits (budget : Nat) : Plan → Render.Bytes → Prop where
  /-- The plan has nothing left to emit. -/
  | done {p : Plan} (h : next budget p = none) : Emits budget p []
  /-- One step's chunk, then the rest of the stream. -/
  |
  step {p q : Plan} {chunk rest : Render.Bytes} (h : next budget p = some (chunk, q))
    (bounded : chunk.length ≤ budget) (more : Emits budget q rest) : Emits budget p (chunk ++ rest)

end Linger.Terminal.Replay
