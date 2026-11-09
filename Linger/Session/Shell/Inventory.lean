module

import Linger.Os.Shell
public import Linger.Session
import Linger.Session.Buf
import Linger.Session.Shell.Client
import Linger.Session.Shell.Paths
import Linger.Session.Shell.Record
public import Linger.Display.Listing
import Linger.Display.Status

public section

/-! # Linger.Session.Shell.Inventory — which local sessions exist, and in what state

One info conversation per live socket under an absolute deadline, a bounded number at once,
and a failed-connect socket removed only under its name lock; then each checkpoint whose
name no live session confirmed. A summary asks only the daemons whose end record does not say
what they saw. The listing, the prompt summary, `get` and the tmux importer all read sessions
through this module. -/

namespace Linger.Session.Shell.Inventory

open Linger.Os.Shell

/-- Bound on accumulated `infoReply` bytes, independent of the request deadline.
A peer exceeding the producer's policy has not supplied a usable answer. -/
abbrev infoReplyCap : Nat := Linger.Session.infoReplyCap

/-- One connected info conversation, bounded by an absolute request window.
Only `done` completes an answer; a failed prefix is never returned as info. -/
def readInfo (fd : UInt32) (stopAt : Option Nat := none) : IO (List (String × String)) := do
  Client.sendMsg fd .info
  let deadline := stopAt.getD ((← monotonicMs) + 2000)
  let mut dec : Linger.Session.Wire.Decoder := {}
  let mut acc : Linger.Session.Buf.Buf := .empty
  let mut go := true
  while go && (← monotonicMs) < deadline do
    let remaining := deadline - (← monotonicMs)
    let revs ← poll #[fd] #[POLLIN] (Int32.ofNat (min 100 remaining))
    if revs[0]! == 0 then
      continue
    match ← read fd 65536 with
    | none =>
      throw (IO.userError "connection lost before info completed")
    | some bs =>
      if bs.isEmpty then
        continue
      let (dec', msgs) := dec.feed bs.toList
      dec := dec'
      if dec.errored then
        throw (IO.userError "invalid response from daemon")
      else
        for m in msgs do
          if !go then
            continue
          match m with
          | .infoReply payload =>
            let (next, dropped) :=
              Linger.Session.Buf.bufOffer infoReplyCap acc (ByteArray.mk payload.toArray)
            if dropped then
              throw (IO.userError "info reply exceeds the byte limit")
            acc := next
          | .done =>
            go := false
          | .err payload =>
            throw (IO.userError (Client.replyText "info request refused" payload))
          | .ended outcome =>
            let ending := Client.Ending.outcome outcome
            throw (IO.userError s!"session ended before info completed ({ending.describe})")
          | .exited status =>
            throw (IO.userError s!"session ended before info completed (status {status})")
          | _ =>
            throw (IO.userError "unexpected response to info")
  if go then
    throw (IO.userError "no reply completed within the info deadline")
  let some txt :=
    String.fromUTF8?
      (Linger.Session.Buf.writeFrom acc) | throw (IO.userError "invalid UTF-8 in info reply")
  (txt.splitOn "\n").filter (· != "") |>.mapM fun line =>
      match line.splitOn "\t" with
      | [k, v] => pure (k, v)
      | _ => throw (IO.userError "invalid info record")

/-- One info conversation over a connection `connect` opens; `none` when it opens none. -/
private def queryWith (connect : Bool → IO (Option UInt32)) (stopAt : Option Nat)
    (retainUnavailable : Bool) : IO (Option (Except IO.Error (List (String × String)))) := do
  if let some deadline := stopAt then
    if (← monotonicMs) ≥ deadline then
      return some (.error (IO.userError "overview deadline reached"))
  match ← connect stopAt.isSome with
  | none =>
    if stopAt.isSome && retainUnavailable then
      return some (.error (IO.userError "overview connection unavailable"))
    return none
  | some fd =>
    try
      let info ← (readInfo fd stopAt).toBaseIO
      return some info
    finally
      close fd

/-- Keep connection absence separate from an info failure: listing must retain
a connected peer, while `get` must report its unanswered request. -/
def queryInfo (name : String) (stopAt : Option Nat := none) (retainUnavailable : Bool := true) :
    IO (Option (Except IO.Error (List (String × String)))) :=
  queryWith (Client.connect name ·) stopAt retainUnavailable

/-- `Client.connect` to a session a listing named, whose spelling needs no check. -/
private def connectListed (n : Paths.Listed) (nonblocking : Bool) : IO (Option UInt32) := do
  let r ← unixConnect (← n.socketPath) nonblocking
  return if r ≥ 0 then some r.toUInt64.toUInt32 else none

/-- Maximum simultaneous local overview queries. -/
private abbrev localQueryLimit : Nat := 32

/-- Bounded socket conversations run against the same deadline, and the caller sleeps until one
ends. Results retain their input positions; every started task is joined, even on error. -/
private def queryInfos (names : Array Paths.Listed) (deadline : Nat) (retainUnavailable : Bool) :
    IO (Array (Option (Except IO.Error (List (String × String))))) := do
  let unknown := some (.error (IO.userError "overview deadline reached"))
  let mut results := Array.replicate names.size unknown
  let pending ←
    IO.mkRef
        (#[] :
          Array (Nat × Task (Except IO.Error (Option (Except IO.Error (List (String × String)))))))
  let mut next := 0
  try
    while next < names.size || !(← pending.get).isEmpty do
      while
        next < names.size && (← pending.get).size < localQueryLimit && (← monotonicMs) < deadline do
        let index := next
        let some listed := names[index]? | break
        let task ←
          IO.asTask (queryWith (connectListed listed ·) (some deadline) retainUnavailable)
              Task.Priority.dedicated
        pending.modify (·.push (index, task))
        next := next + 1
      let mut running := #[]
      for (index, task) in ← pending.get do
        if ← IO.hasFinished task then
          let result ← IO.wait task
          results :=
            results.set! index
              (match result with
              | .ok info => info
              | .error e => some (.error e))
        else
          running := running.push (index, task)
      pending.set running
      if running.isEmpty && (← monotonicMs) ≥ deadline then
        break
      -- sleep until a query ends: each ends by the shared deadline
      match running.toList.map (·.2) with
      | [] =>
        pure ()
      | first :: rest =>
        discard <| IO.waitAny (first :: rest)
    return results
  finally
    for (_, task) in ← pending.get do
      discard <| IO.wait task

/-- Remove a failed-connect socket only while holding its name lock. `false`
means another owner holds the lock or the probe itself failed; both fail closed. -/
private def removeStaleSocket (n : Paths.Listed) : IO Bool := do
  try
    n.withLock do
        try
          IO.FS.removeFile (← n.socketPath)
        catch _ =>
          pure ()
        return true
  catch _ =>
    return false

/-- A saved session's listing row and the fields it adds, from reading its name's end record:
ended, with the status a shell reports and how its program ended (`Session.outcomeFields`),
when the record says so; unknown when the record cannot be read; otherwise resumable, as a
session interrupted before its program ended, or saved before end records existed. -/
def savedRow (record : Except IO.Error (Option (List UInt8))) :
    Linger.Display.Listing.Row × List (String × String) :=
  match record with
  | .error _ => (.broken, [])
  | .ok bytes =>
    match bytes.bind Linger.Session.Record.decode with
    | some (.ended outcome) => (.ended outcome.status.toNat, Linger.Session.outcomeFields outcome)
    | _ => (.stale, [])

/-- What a session's end record says its daemon saw, while that daemon holds the name, so a
summary need not wake it; `none` leaves the summary to ask. A held name lock is a daemon that
holds the name, which wrote the record: one that ended said so in it before giving the name up. -/
private def publishedSeen (listed : Paths.Listed) : IO (Option Linger.Session.Seen) := do
  let some seen :=
    (← (Record.loadListed listed).toBaseIO).toOption.bind
      (·.bind Linger.Session.Record.published) | return none
  let free ←
    try
      listed.withLock (pure true)
    catch _ =>
      pure false
  return if free then none else some seen

/-- Common local snapshot for the listing and prompt. Concurrent queries share
one deadline (two seconds for a listing); unqueried peers stay unknown. The names come from
the directories, so no path here needs a spelling check. A saved session is listed as its end
record says (`savedRow`), read while holding the name. With `statusOnly`, as for a summary, a
row carries only its status, and a live session whose end record says what its daemon saw is
read from the record without waking the daemon (`rowStatus_published`). -/
def localRows (stopAt : Option Nat := none) (statusOnly : Bool := false) :
    IO (List (List (String × String))) := do
  let deadline := stopAt.getD ((← monotonicMs) + 2000)
  let sockets := (← Paths.listSocketNames).toArray.qsort (·.name < ·.name)
  let ckpts := (← Paths.listCkptNames).toArray.qsort (·.name < ·.name) |>.toList
  let liveRow := fun name info =>
    Linger.Display.Listing.rowFields name info ++
      [("state", "live"),
        ("status", Linger.Display.Status.name (Linger.Display.Listing.rowStatus (.live info)))]
  let mut confirmedLive : List String := []
  let mut rows : List (List (String × String)) := []
  let mut asked := sockets
  if statusOnly then
    asked := #[]
    for listed in sockets do
      match ← publishedSeen listed with
      | some seen =>
        confirmedLive := confirmedLive ++ [listed.name]
        let row := Linger.Display.Listing.Row.published seen.fresh seen.unseen
        rows :=
          rows ++
            [Linger.Display.Listing.rowFields listed.name
                [("state", "live"),
                  ("status", Linger.Display.Status.name (Linger.Display.Listing.rowStatus row))]]
      | none =>
        asked := asked.push listed
  let infos ← queryInfos asked deadline stopAt.isSome
  for (listed, result) in asked.zip infos do
    let name := listed.name
    match result with
    | some info =>
      confirmedLive := confirmedLive ++ [name]
      rows := rows ++ [liveRow name (info.toOption.getD [])]
    | none =>
      if !(← removeStaleSocket listed) then
        -- Failed connect while another process owns (or may own) the name: keep
        -- the rendezvous path and list the identity as live/unknown.
        confirmedLive := confirmedLive ++ [name]
        rows := rows ++ [liveRow name []]
  for listed in ckpts do
    let name := listed.name
    if !confirmedLive.contains name then
      -- Another runtime directory may share this checkpoint namespace.
      -- A busy or unreadable lock cannot establish that the session is offline.
      let record ←
        try
          listed.withSessionLock (some <$> (Record.loadListed listed).toBaseIO)
        catch _ =>
          pure none
      let savedFields := fun (row : Linger.Display.Listing.Row) extra =>
        Linger.Display.Listing.rowFields name
          ([("state", "resumable"),
              ("status", Linger.Display.Status.name (Linger.Display.Listing.rowStatus row))] ++
            extra)
      rows :=
        rows ++
          [match record with
            | none => liveRow name []
            | some loaded =>
              let (row, ending) := savedRow loaded
              savedFields row ending]
  return rows

end Linger.Session.Shell.Inventory
