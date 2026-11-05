module

public import Linger.Session.Buf
public import Linger.Os.Shell
public import Linger.Session.Wire
public import Linger.Terminal.Vt
public import Linger.Terminal.Render
public import Linger.Terminal.Mediation
public import Linger.Terminal.Title
public import Linger.Target.Name
public import Linger.Session
public import Linger.Session.Driver
public import Linger.Session.Checkpoint
public import Linger.Target.Remote
public import Linger.Display.Listing
public import Linger.Display.Status
public import Linger.Display.Title
public import Linger.Os.Env
public import Linger.Session.Shell.Paths
public import Linger.Runtime.Command
public import Linger.Session.Shell.Daemon
public import Linger.Session.Shell.Client
public import Linger.Runtime.Cli
public import Linger.Session.Shell.Resume

/-! # Linger — the session library

This umbrella's closure is the library `./lake build` checks: the session core under
`Linger/Core`, the runtime under `Linger/Runtime`, and the components it builds on — the
VT toolkit (`Linger/Terminal`), targets, displays and the OS boundary.
The CLI policies in `Linger/Tools` and their executors in `Linger/Manager` stay outside
it: they may import this library, which never imports them. `Main` routes argv through
`Entry.route` to an executor or to `Cli.main`. -/
