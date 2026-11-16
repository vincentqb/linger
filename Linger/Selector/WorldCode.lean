module

public import Linger.Selector.CoreSpec
public import Linger.Os.CoreSpec
import Linger.Os.CoreCode.Answer
import Linger.Selector.CoreCode.Picker
import Os.WorldCode
import Linger.Target.CoreCode.Remote
import Terminal.CoreCode.Title
import Os.WorldCode.Command
import Linger.Display.CoreCode.View
import Std.Data.HashMap.Basic
import Linger.Display.CoreCode.Status
import Linger.Selector.CoreCode.Key
import Linger.Selector.CoreCode.Fetch
import Input.CoreCode
import Linger.Os.CoreCode.Env

public section

/-! Terminal executor for the session selector. Selection and decoding
are pure tool modules; this module owns terminal lifetime and subprocesses. -/

namespace Linger.Selector.Shell

open Os.Shell

/-- How one selection visit ended. -/
inductive Choice where
  /-- An accepted row's exact target, existing or new, with the snapshot displayed
  when it was accepted, its targets in the order the visit showed them. -/
  | attach (target : String) (snapshot : Linger.Selector.Picker.Snapshot)
  /-- Cancellation by key, or the end of terminal input. -/
  | cancel
  /-- A listing exited nonzero, with its exit status and standard error. -/
  | failed (status : UInt32) (stderr : String)
  /-- A watched signal, with this number, ended the visit, which handed the terminal back first,
  as a cancellation does. -/
  | stopped (signal : UInt8)

/-- Each listed target's status, read once per listing in one pass over its records: a name
record starts a row, a blank record ends it, and its `status` record says its status, as
`Picker.Snapshot.row` reads it. A target without one is unknown. -/
private def statusesOf (snapshot : Linger.Selector.Picker.Snapshot) :
    Std.HashMap String Linger.Display.Status.Status :=
  Id.run do
    let mut current : Option String := none
    let mut statuses := {}
    for fields in snapshot.records do
      match fields with
      | ["name", target] =>
        current := some target
      | [""] =>
        current := none
      | ["status", name] =>
        if let some target := current then
          statuses := statuses.insert target (Linger.Display.Status.ofName name)
      | _ =>
        pure ()
    return statuses

/-- Own raw mode and at most one listing for one selection visit. Keys always
act on the displayed snapshot, which is returned on acceptance; a completed
replacement is applied afterward and rendered before polling again.
A read-only visit has no creation choice. The first listing is cancellable too.
A native visit queries remote hosts only when remote rows are due (`fetch_follows_events`): when
it opens, and at once after the refresh key, or once the listing running then ends. Its other
listings, one each second, list local rows alone and keep the remote rows the last remote query
reported, and the header says how long before the latest listing that query started
(`Picker.ageParts`), so the age changes as those listings repaint, with no timer of its own. The
first frame, the first after a resize and the first after the refresh key, which clears and
redraws the screen as Ctrl-L does in a line editor, paint every row; after that a change writes
only the rows it changed (`Picker.update`). The rows are in `View.sort`'s order when the visit
opens, at once on the refresh key and again after the listing it starts; any other listing keeps
the rows shown where they are, a new row last (`Picker.relist`). The visit enters with the rows of
the view it returns from, `left`, where they were, and the cursor on `focus`, the session it
returns from or the one it was opened inside, while the listing has it (`Picker.enter`). Native listings get a cooperative stop so they can
retire the transports' isolated groups. Once `heard` says which watched signal came, the visit
ends on the cancellation's path, as `stopped` with that signal. -/
def choose (executable : String) (readOnly : Bool := false) (heard : IO (Option UInt8) := pure none)
    (left : List String := []) (focus : Option String := none) : IO Choice := do
  unless (← stdinIsTty) && (← (← IO.getStdout).isTty) do
    throw (IO.userError "the picker needs terminal input and output")
  let fullArgs := #["ls", "-r", "--porcelain"]
  let pending ← IO.mkRef (none : Option Os.Shell.Command.Job)
  let withColor :=
    Linger.Os.Env.withColor (← (← IO.getStdout).isTty) (← IO.getEnv "NO_COLOR") (← IO.getEnv "TERM")
  let home ← accountHome
  let saved ← termRaw stdinFd
  try
    writeAll stdoutFd (ByteArray.mk Linger.Selector.Picker.enterAnsi.toArray)
    writeAll stdoutFd (ByteArray.mk (Terminal.Title.ansi "linger").toArray)
    let fds := #[stdinFd]
    let events := #[POLLIN]
    let mut state := Linger.Selector.Picker.init [] !readOnly
    let mut snapshot : Linger.Selector.Picker.Snapshot := {}
    let mut statuses : Std.HashMap String Linger.Display.Status.Status := {}
    let mut loaded := false
    let mut decoder := Input.init
    let mut lastInput ← monotonicMs
    let mut nextListing := 0
    let mut full := true
    let mut lastFull : Linger.Selector.Picker.Snapshot := {}
    let mut remoteDue := true
    -- when the running listing started, when the one that listed the remote rows shown did, and
    -- how many seconds before the latest listing that was
    let mut started := 0
    let mut fetched : Option Nat := none
    let mut remoteAge : Option Nat := none
    let mut size := (0, 0)
    let mut shown : Option (List (List UInt8)) := none
    let mut dirty := true
    -- whether the next listing to start, and the running one, sort the rows again
    let mut sortNext := false
    let mut sorting := false
    while true do
      let current ← winsizeGet stdoutFd
      if dirty || current != size then
        let rows :=
          Linger.Selector.Picker.frameRows state snapshot (statuses.getD · .unknown) loaded
            withColor false remoteAge current.1.toNat current.2.toNat
        let frame :=
          match shown with
          | some before =>
            if current == size then Linger.Selector.Picker.update before rows
            else
              Linger.Selector.Picker.frame state snapshot (statuses.getD · .unknown) loaded
                withColor false remoteAge current.1.toNat current.2.toNat
          | none =>
            Linger.Selector.Picker.frame state snapshot (statuses.getD · .unknown) loaded withColor
              false remoteAge current.1.toNat current.2.toNat
        if !frame.isEmpty then
          writeAll stdoutFd (ByteArray.mk frame.toArray)
        shown := some rows
        size := current
        dirty := false
      let ready ← poll fds events 50
      if let some signal← heard then
        return .stopped signal
      let bits := ready[0]!
      if bits &&& POLLNVAL != 0 then
        throw (IO.userError "picker input descriptor became invalid")
      let mut keys : Array Linger.Selector.Key := #[]
      if bits &&& (POLLIN ||| POLLHUP ||| POLLERR) != 0 then
        match ← read stdinFd 4096 with
        | none =>
          return .cancel
        | some bytes =>
          if !bytes.isEmpty then
            lastInput ← monotonicMs
          for byte in bytes do
            let (next, emitted) := Input.feed decoder byte
            decoder := next
            keys := keys ++ (emitted.filterMap Linger.Selector.Key.ofInput).toArray
      else if Input.pending decoder && (← monotonicMs) - lastInput ≥ 150 then
        let (next, emitted) := Input.flush decoder
        decoder := next
        keys := (emitted.filterMap Linger.Selector.Key.ofInput).toArray
      for key in keys do
        remoteDue := Linger.Selector.Picker.fetch remoteDue (.key key)
        if key == .refresh then
          shown := none
          dirty := true
          state :=
            Linger.Selector.Picker.relist state true
              (Linger.Display.View.sort (statuses.getD · .unknown) state.candidates)
              state.descriptions
          snapshot := snapshot.keepColumns none
          sortNext := true
        if !loaded && key == .accept then
          continue
        match Linger.Selector.Picker.step state key with
        | .stay next =>
          dirty := dirty || next != state
          state := next
        | .attach target | .create target =>
          return .attach target { snapshot with candidates := state.candidates }
        | .cancel =>
          return .cancel
      if let some result← Os.Shell.Command.poll pending then
        if result.exitCode != 0 then
          return .failed result.exitCode result.stderr
        let listed ← IO.ofExcept (Linger.Selector.Picker.parseSnapshot result.stdout)
        if full then
          lastFull := listed
          fetched := some started
        let incoming := if full then listed else listed.withRemote lastFull
        -- what asks for someone first, as `ls` lists it (`View.sort`), when the visit opens and
        -- after the refresh key, and otherwise the rows shown where they are (`Picker.relist`);
        -- the query finds a row by its description too, and a directory under the account's home
        -- shows as `~`, as in `ls`; the remote rows' age is as of this listing, which repaints it;
        -- the columns are this listing's when the rows are sorted, and otherwise stay as they
        -- were, so they never move under the person (`Picker.Snapshot.keepColumns`)
        let incomingStatuses := statusesOf incoming
        let ordered :=
          Linger.Display.View.sort (incomingStatuses.getD · .unknown) incoming.candidates
        let next :=
          if loaded then Linger.Selector.Picker.relist state sorting ordered incoming.descriptions
          else Linger.Selector.Picker.enter state left focus ordered incoming.descriptions
        let atHome :=
          (incoming.atHome home).keepColumns (if loaded && !sorting then snapshot.layout else none)
        let now ← monotonicMs
        let age := fetched.map fun start => (now - start) / 1000
        dirty := dirty || !loaded || next != state || atHome != snapshot || age != remoteAge
        state := next
        snapshot := atHome
        statuses := incomingStatuses
        remoteAge := age
        loaded := true
        nextListing := (← monotonicMs) + 1000
      if (← pending.get).isNone && (remoteDue || (← monotonicMs) ≥ nextListing) then
        full := remoteDue
        remoteDue := Linger.Selector.Picker.fetch remoteDue .list
        let args := if full then fullArgs else #["ls", "--porcelain"]
        started ← monotonicMs
        sorting := sortNext
        sortNext := false
        pending.set (some (← Os.Shell.Command.start executable args))
    return .cancel
  finally
    try
      try
        writeAll stdoutFd (ByteArray.mk Linger.Selector.Picker.exitAnsi.toArray)
        writeAll stdoutFd (ByteArray.mk (Terminal.Title.ansi "").toArray)
      finally
        termRestore stdinFd saved
    finally
      Os.Shell.Command.stop pending 1000

/-- The exact attach argv for a chosen target. Its operands are the ones the attach
parser reads back as `target` (`targetArgs_targetOperands`). -/
def attachArgs (target : String) (readOnly : Bool := false) : Array String :=
  ("attach" :: (if readOnly then ["--read-only"] else []) ++
      Linger.Target.Remote.targetOperands target).toArray

/-- The name the session with an ID shows now, if any: how the chooser reads the ID that
`LINGER_SESSION` holds. -/
abbrev Lookup : Type := String → IO (Option String)

/-- Execute either selected row through attach, after terminal restoration. Every attach
exit returns to a fresh listing, which shows the view the visit left, the session attached to
selected, as the first visit selects the session whose ID `LINGER_SESSION` holds, by the name
`nameOf` gives that ID now; cancellation ends the manager, answering `cancelled`. The
caller supplies one frozen absolute executable for all listing and attach children. A listing
that fails ends the manager with the answer its exit status gives (`Answer.ofCode`). A signal of
`handbackSignals` ends the manager as a cancellation does, answering `stopped` with the first that
came, even one that came while a visit handed the terminal back (`watching`): a visit hands the
terminal back first, and an attach, which owns the terminal while it runs and hears the signals
its terminal sends, first ends. -/
def run (executable : String) (nameOf : Lookup) (readOnly : Bool := false) : IO Linger.Os.Answer :=
  watching handbackSignals Linger.Os.Answer.stopped fun stops => do
    let mut left : List String := []
    let mut focus ← (Linger.Os.Env.inSession (← IO.getEnv "LINGER_SESSION")).bindM nameOf
    while true do
      match
        ←
          choose executable (readOnly := readOnly) (heard := stops.came) (left := left) (focus :=
              focus) with
      | .cancel =>
        return .cancelled
      | .stopped signal =>
        return .stopped signal
      | .failed status stderr =>
        IO.eprintln s!"linger: could not list sessions (exit {status})"
        if !stderr.isEmpty then
          IO.eprint stderr
        return Linger.Os.Answer.ofCode status
      | .attach target displayed =>
        left := displayed.candidates
        focus := some target
        let child ← IO.Process.spawn { cmd := executable, args := attachArgs target readOnly }
        discard child.wait
        if let some signal← stops.came then
          return .stopped signal
    return .done

end Linger.Selector.Shell
