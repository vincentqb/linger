module

public import Linger.App.CoreSpec

public section

/-! # Linger.App.Handover — whether an attach hands the session's daemon over to itself

Before an attach, the attaching binary reads its daemon's `info` answer, and hands the daemon
over to itself, by the handoff `linger upgrade` asks for, when it may type into the session, the
daemon writes a handoff format it reads, and the daemon's binary is older than its own
(`attach_upgrades`): a daemon that names no build was started by an older linger. A read-only
attach, `ls`, the chooser and `capture` never ask. -/

namespace Linger.App.Handover

/-- What an attach in `mode` by the binary of build `b` does with the daemon whose `info` answer
gave `fields`: hand it over when the attach is writable, the daemon writes a handoff format this
binary reads and the daemon's build is lower than `b` or not reported, and keep it otherwise. -/
def plan (mode : Session.Mode) (b : Nat) (fields : List (String × String)) : Plan :=
  if mode == .writable && (Daemon.ofInfo fields).hands && (Daemon.ofInfo fields).older b then
    .handOver
  else .keep

end Linger.App.Handover
