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
public import Linger.Display.View
public import Linger.Os.Env
public import Linger.Session.Shell.Paths
public import Linger.Os.Shell.Command
public import Linger.Session.Shell.Daemon
public import Linger.Session.Shell.Client
public import Linger.Session.Shell.Inventory
public import Linger.App.Shell
public import Linger.Session.Shell.Resume

/-! # Linger — the session library

This umbrella's closure is the library `./lake build` checks: the session machine and its
shell, the components it builds on — the VT toolkit (`Linger/Terminal`), targets, displays
and the OS boundary — and the command line's shell (`Linger/App/Shell.lean`). The entry
route, the selector and the import component stay outside it: they may import this
library, which never imports them. `Main` routes argv through `Entry.route` to an
executor or to `App.Shell.main`. -/
