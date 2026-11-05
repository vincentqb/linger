module

public import Linger.Terminal.Vt

public section

/-! # Terminal states a running session can hold

`LiveReachableVt` is the least set of states containing a fresh emulator and closed under what
a live session does to one: feed pty bytes, resize on attach, forget partial parser state (what
a checkpoint save and load does) and come off disk through the decoder's door. Headline
theorems about repainting and checkpoints assume it of the terminals involved. Every `Vt` a
program can hold satisfies it: `Vt.init` and the decoder are the only doors, and the session
transformers the only ways forward (`Linger/Terminal/Vt.lean` lists them).

It does not say a scrollback row is the screen's width: `Vt.resize` leaves the scrollback at
its old width. -/

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
