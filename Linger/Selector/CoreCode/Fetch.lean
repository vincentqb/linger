module

public import Linger.Selector.CoreSpec

public section

/-! # When the chooser queries remote hosts

A remote host's rows cost a transport command, which only an event pays for: the chooser opening
and the refresh key. Its local rows cost a few local sockets and refresh each second. So a
listing the chooser starts queries remote hosts exactly when remote rows are due
(`fetch_follows_events`): when it opens, until its first listing, and after a refresh key, until
the next listing, which a refresh key starts at once. Keys pressed while one runs coalesce into
the one after it. -/

namespace Linger.Selector.Picker

/-- Whether remote rows are due after `event`, given whether they were before it: a refresh key
makes them due, a listing fetches them when they were, so they are not after it, and any other
key leaves them as they were. -/
def fetch (due : Bool) : Event → Bool
  | .key .refresh => true
  | .key _ => due
  | .list => false

end Linger.Selector.Picker
