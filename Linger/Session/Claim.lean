module

public section

/-! # Linger.Session.Claim — whether a process may act as a session's owner

A daemon, or an offline reader, takes the session's socket lock and then its checkpoint lock,
and acts as the session's owner only when `enters` lets it: when it holds both.
`Linger.Session.Shell.Paths` asks it before every such action. `Claim.Reachable` in
`Linger/Session/Spec.lean` models processes doing so in any order, and the headline `one_owner`
shows that a name then has one owner. -/

namespace Linger.Session.Claim

/-- Whether a process that holds the session's socket lock (`socket`) and its checkpoint lock
(`checkpoint`) may act as its owner: only when it holds both. -/
def enters (socket checkpoint : Bool) : Bool := socket && checkpoint

end Linger.Session.Claim
