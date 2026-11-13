module

import Linger.Selector.CoreCode.Fetch
meta import Linger.Selector.CoreCode.Fetch

/-! Fixtures of when the chooser queries remote hosts: for a sequence of events since it opened,
whether each listing it starts queries them. -/

namespace Linger.Selector.Tests.Fetch

open Linger.Selector.Picker

/-- Whether each listing among `events` queries remote hosts, in order, as the chooser decides
with `fetch`, remote rows being due when it opens. -/
def listings (events : List Event) : List Bool :=
  (events.foldl
      (fun (due, out) event =>
        match event with
        | .list => (fetch due .list, out ++ [due])
        | other => (fetch due other, out))
      (true, [])).2

-- the opening's listing queries remote hosts; the ones each second after it do not
#guard listings [.list, .list, .list] == [true, false, false]

-- a refresh key makes the next listing query them, and only the next
#guard listings [.list, .list, .key .refresh, .list, .list] == [true, false, true, false]

-- a key that is no refresh leaves them as they were
#guard
  listings [.key (.text 'a'), .list, .key .down, .key .accept, .key .cancel, .list] == [true, false]

-- refresh keys pressed while a listing runs coalesce into the next one
#guard
  listings [.list, .key .refresh, .key .refresh, .key .refresh, .list, .list] == [true, true, false]

-- a refresh before the first listing is the opening's
#guard listings [.key .refresh, .list, .list] == [true, false]

#guard
  due fetch [] && !due fetch [.list] && due fetch [.list, .key .refresh] &&
    !due fetch [.list, .key .refresh, .list]

end Linger.Selector.Tests.Fetch
