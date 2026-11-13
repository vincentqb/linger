module

public import Linger.Session.CoreCode.Buf
public import Linger.Session.CoreCode.Wire
public import Terminal.CoreCode.Vt
public import Linger.Target.CoreCode.Name
public import Linger.Session.CoreCode
public import Linger.Session.CoreCode.Driver
public import Linger.Session.CoreCode.Checkpoint
public import Linger.Target.CoreCode.Remote
public import Linger.Display.CoreCode.Listing
public import Linger.Display.CoreCode.Status
public import Linger.Display.CoreCode.Title
public import Linger.Display.CoreCode.View
public import Linger.Os.CoreCode.Env
public import Linger.Session.WorldCode.Paths
public import Linger.Session.WorldCode.Daemon
public import Linger.Session.WorldCode.Client
public import Linger.Session.WorldCode.Inventory
public import Linger.App.CoreCode.Commands
public import Linger.App.WorldCode
public import Linger.Session.WorldCode.Resume

/-! # Linger — the session library

This umbrella's closure is the library `./lake build` checks: the session machine and its
shell, the components it builds on — the VT toolkit (`packages/terminal`), targets, displays
and the OS boundary — and the command line's shell (`Linger/App/WorldCode.lean`). The entry
route, the selector and the import component stay outside it: they may import this
library, which never imports them. `main` (`Linger/App/WorldCode/Main.lean`) routes argv
through `Entry.route` to an executor or to `App.Shell.main`. -/
