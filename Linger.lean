module

public import Linger.Core.Buf
public import Linger.Posix
public import Linger.Core.Wire
public import Linger.Core.Vt
public import Linger.Core.Render
public import Linger.Core.Terminal
public import Linger.Core.Name
public import Linger.Core.Session
public import Linger.Core.Driver
public import Linger.Core.Checkpoint
public import Linger.Core.Remote
public import Linger.Core.Listing
public import Linger.Core.Status
public import Linger.Core.Title
public import Linger.Core.Env
public import Linger.Runtime.Paths
public import Linger.Runtime.Command
public import Linger.Runtime.Daemon
public import Linger.Runtime.Client
public import Linger.Runtime.Cli
public import Linger.Runtime.Resume

/-! # Linger — the session library

This umbrella's closure is the library `./lake build` checks: the session core and VT
toolkit under `Linger/Core`, the runtime under `Linger/Runtime` and the POSIX boundary.
The CLI policies in `Linger/Tools` and their executors in `Linger/Manager` stay outside
it: they may import this library, which never imports them. `Main` routes argv through
`Entry.route` to an executor or to `Cli.main`. -/
