module

public import Linger.Target.CoreSpec
import SoftwareChallenge.Commands

public section

/-! # What remote commands assume of the world

A remote command runs through a transport, a command that runs linger elsewhere, which may be any
command, each reaching its host its own way: reaching it is the transport's, its keys, jumps,
latency and authentication included. Every remote command runs `linger serve` there and speaks to
it in bytes, on the command's standard input and output, which `Transport.Delivers` says the
transport carries either way exactly, or runs nothing. -/

namespace Linger.Target.Remote.Transport

/-- A transport is a host's command that runs linger there, and `carry command bytes` is what
arrives at one end of the command `command`, linger run as it, when the other end writes `bytes`:
what the program the command runs there reads on its standard input of what linger writes to the
command's, and what linger reads on the command's standard output of what that program writes to
its own, or `none` when it runs nothing, as when it cannot reach its host. The transport's command
runs `linger serve` there, two words every shell passes on as they are, and carries every byte
either way, in order, as `ssh -T`, `docker exec -i` and `kubectl exec -i` do. A command that
changes, drops, adds or reorders a byte, or runs anything there but `linger serve`, falsifies it. -/
WorldClaim Delivers (carry : List String → List UInt8 → Option (List UInt8))
  (transport : Transport) :=
  ∀ bytes : List UInt8,
    carry (transport.command ++ ["linger", "serve"]) bytes = none ∨
      carry (transport.command ++ ["linger", "serve"]) bytes = some bytes

end Linger.Target.Remote.Transport
