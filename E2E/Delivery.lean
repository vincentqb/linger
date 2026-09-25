module

public import E2E.Harness
public import Linger.Runtime.Daemon
public import Tests.Delivery

public section

namespace E2E.Delivery

open E2E.Harness
open Linger.Posix
open Linger.Core
open Linger.Runtime.Daemon
open Linger.Core.Buf (owedLen)

structure Received where
  decoder : Wire.Decoder := {}
  bytes : ByteArray := .empty
  exits : List (Nat × UInt32) := []
  errors : List (List UInt8) := []
  bounded : Bool := true
  eof : Bool := false

/-- Decode the real wire stream, recording exit's position among output bytes. -/
def receive (peer : UInt32) (r : Received) : IO Received := do
  let mut r := r
  while !r.eof do
    match ← read peer 65536 with
    | none =>
      r := { r with eof := true }
    | some chunk =>
      if chunk.isEmpty then
        break
      let (decoder, msgs) := r.decoder.feed chunk.toList
      r := { r with decoder }
      for msg in msgs do
        match msg with
        | .output bytes =>
          r :=
            { r with
              bytes := r.bytes ++ ByteArray.mk bytes.toArray
              bounded := r.bounded && bytes.length ≤ Session.outputChunk }
        | .exited status =>
          r := { r with exits := r.exits ++ [(r.bytes.size, status)] }
        | .err bytes =>
          r := { r with errors := r.errors ++ [bytes] }
        | _ =>
          r := { r with bounded := false }
  return r

/-- Fill the actual kernel send buffer without reading the peer. No sleep-based
assumption about socket buffer sizes; writable readiness decides when to stop. -/
def stall (rt : Rt) (fd : UInt32) : IO Rt := do
  let mut rt := rt
  for _ in [:512] do
    let some c := rt.conn? fd | break
    let ready ← poll #[fd] #[POLLOUT] 0
    if ready[0]! &&& POLLOUT == 0 then
      break
    match ← flushConn c with
    | none =>
      close fd
      rt := rt.dropConn fd
      break
    | some c =>
      rt := rt.setConn c
  return rt

/-- Once the peer resumes, drive production polling and effect execution until
the expected stream arrives (or EOF/deadline makes an incomplete stream fail). -/
def collect (rt : Rt) (peer : UInt32) (size : Nat) (wantEof : Bool := false) : IO (Rt × Received) :=
  do
  let mut rt := rt
  let mut r : Received := {}
  let deadline := (← IO.monoMsNow) + 30000
  while (← IO.monoMsNow) < deadline do
    r ← receive peer r
    if r.eof || (!wantEof && r.bytes.size ≥ size) then
      break
    if rt.conns.isEmpty then
      IO.sleep 1
    else
      let (rt', events) ← pollRound rt
      rt ← pump rt' events
  return (rt, r)

def withPair (dir tag : String) (vt : Linger.Core.Vt.Vt) (f : Rt → UInt32 → UInt32 → IO Nat) :
    IO Nat := do
  let path := s!"{dir}/{tag}.sock"
  let listener ← unixListen path
  let idle ← unixListen s!"{path}.idle"
  try
    let connected ← unixConnect path
    let accepted ← accept listener
    if connected < 0 || accepted < 0 then
      throw (IO.userError "delivery socket pair was not accepted")
    let peer := connected.toUInt64.toUInt32
    let fd := accepted.toUInt64.toUInt32
    try
      setNonblock listener
      setNonblock idle
      setNonblock peer
      setNonblock fd
      let st := (Session.step (.boot vt [] []) (.connected fd.toNat)).1
      -- An independent idle listener fills the unused pty poll slot. New
      -- clients may connect to `listener` without making this slot readable.
      let rt : Rt :=
        { st, listenFd := listener, ptyFd := idle, childPid := 0, conns := [{ fd }],
          sockPath := path, saveCkpt := fun _ => pure (), dropCkpt := pure () }
      f rt peer fd
    finally
      close peer
      close fd
  finally
    close listener
    close idle
    IO.FS.removeFile path
    IO.FS.removeFile s!"{path}.idle"

def largeReplay (dir : String) (marks : Bool) : IO Nat := do
  let some vt := Linger.Tests.Delivery.acceptedScreen marks
    | throw (IO.userError "large delivery fixture is not an accepted checkpoint")
  let label := if marks then "marks" else "colours"
  let repaint := ByteArray.mk (Render.restore vt).toArray
  let live := "\r\nlive-after-replay!".toUTF8
  let expected := repaint ++ live
  withPair dir label vt fun rt peer fd => do
      let mut failures ← expect (repaint.size > outbufCap) s!"delivery/{label}/exceeds-cap"
      let request := Wire.encode (.attach 0 0)
      writeAll peer (ByteArray.mk request.toArray)
      let (rt, events) ← pollRound rt
      let rt ← pump rt events
      let rt ← stall rt fd
      let ready ←
        if (rt.conn? fd).isSome then
          poll #[fd] #[POLLOUT] 0
        else
          pure #[0]
      failures :=
        failures +
          (←
            expect ((rt.conn? fd).isSome && ready[0]! &&& POLLOUT == 0)
                s!"delivery/{label}/stalled-client-retained")
      let rt ← pump rt [.ptyOut live.toList]
      let began ← IO.monoMsNow
      let (rt, got) ← collect rt peer expected.size
      IO.println
          s!"delivery/{label}: received {got.bytes.size} / {expected.size} output bytes \
      in {(← IO.monoMsNow) - began} ms; pending={(rt.conn? fd).any (·.pending)}"
      failures :=
        failures + (← expect (got.bytes == expected) s!"delivery/{label}/exact-replay-then-live")
      failures :=
        failures +
          (←
            expect (!got.eof && !got.decoder.errored && got.bounded)
                s!"delivery/{label}/live-framing")
      return failures

def exitTail (dir : String) : IO Nat :=
  withPair dir "exit" (Linger.Core.Vt.Vt.init 20 5) fun rt peer fd => do
    let st := (Session.step rt.st (.bytes fd.toNat (Wire.encode (.attach 20 5)))).1
    let mut rt := { rt with st }
    let mut expected := ByteArray.empty
    for i in [:16] do
      let bytes := List.replicate Session.outputChunk (UInt8.ofNat (0x41 + i))
      expected := expected ++ ByteArray.mk bytes.toArray
      let (rt', feedback) ← runEffect rt (.send fd.toNat (.output bytes))
      rt ← pump rt' feedback
    rt ← stall rt fd
    let mut failures ←
      expect ((rt.conn? fd).any (fun c => owedLen c.out > 0)) "delivery/exit/actually-stalled"
    rt ← pump rt [.childExited 7]
    let (_, got) ← collect rt peer expected.size true
    IO.println s!"delivery/exit: received {got.bytes.size} / {expected.size} output bytes"
    failures := failures + (← expect (got.bytes == expected) "delivery/exit/exact-tail")
    failures :=
      failures + (← expect (got.exits == [(expected.size, 7)]) "delivery/exit/status-follows-tail")
    failures :=
      failures +
        (←
          expect (got.eof && !got.decoder.errored && got.decoder.buf.isEmpty)
              "delivery/exit/clean-eof")
    return failures

/-- Both messages are decoded before effects run. A replay read from the final
runtime state would paint the resized screen instead of the attach snapshot. -/
def snapshotOrder (dir : String) : IO Nat := do
  let vt := (Linger.Core.Vt.Vt.init 20 5).feed "snapshot".toUTF8.toList
  let expected := ByteArray.mk (Render.restore vt).toArray
  withPair dir "snapshot" vt fun rt peer fd => do
      let rt ← pump rt [.bytes fd.toNat (Wire.encode (.attach 20 5) ++ Wire.encode (.resize 21 6))]
      let (_, got) ← collect rt peer expected.size
      expect (got.bytes == expected && rt.st.vt.colCount == 21 && rt.st.vt.rowCount == 6)
          "delivery/snapshot/attach-event-point"

/-- A correct-looking repaint must leave the next glyph on the same row as
uninterrupted output. Drive the captured replay and following bytes through
real sockets, covering each cursor slot and a marked wide margin cell. -/
def pendingWrap (dir : String) : IO Nat := do
  let mut failures := 0
  for (glyph, text) in [("narrow", "abcd"), ("wide", "ab漢\u0301")] do
    for (slot, before, after) in
      [("active", "", "X"), ("saved", "\x1b7\r", "\x1b8X"),
        ("stash", "\x1b[?1049h", "\x1b[?1049lX")] do
      let vt := (Vt.Vt.init 4 2).feed (text ++ before).toUTF8.toList
      let live := after.toUTF8
      let expected := ByteArray.mk (Render.restore vt).toArray ++ live
      failures :=
        failures +
          (←
            withPair dir s!"pending-{slot}-{glyph}" vt fun rt peer fd => do
                let rt ← pump rt [.bytes fd.toNat (Wire.encode (.attach 0 0)), .ptyOut live.toList]
                let (_, got) ← collect rt peer expected.size
                let received := (Vt.Vt.init 4 2).feed got.bytes.toList
                let continued := vt.feed live.toList
                expect
                    (got.bytes == expected && !got.eof && !got.decoder.errored && got.bounded &&
                      Render.screenText received == Render.screenText continued &&
                      Render.screenText continued == (text ++ "\nX\n").toUTF8.toList)
                    s!"delivery/pending/{slot}-{glyph}")
  return failures

def repeatedAttach (dir : String) : IO Nat := do
  let vt := Linger.Core.Vt.Vt.init 20 5
  let expected := ByteArray.mk (Render.restore vt).toArray
  withPair dir "repeat" vt fun rt peer fd => do
      let request := Wire.encode (.attach 20 5)
      let rt ← pump rt [.bytes fd.toNat (request ++ request)]
      -- An error is behind the repaint, so collect until the connection has
      -- produced both responses rather than stopping at the first frame.
      let rt ← stall rt fd
      let got ← receive peer {}
      expect
          (got.bytes == expected && got.errors == ["already attached".toUTF8.toList] &&
            (rt.conn? fd).isSome)
          "delivery/repeat/one-replay-per-connection"

/-- Even an invalid effect sequence is confined to its peer, rather than
throwing out of the serving loop. Ordinary repeated attach never emits it. -/
def duplicateEffect (dir : String) : IO Nat := do
  let vt := Linger.Core.Vt.Vt.init 20 5
  withPair dir "duplicate-effect" vt fun rt _peer fd => do
      let rt ← pump rt [.bytes fd.toNat (Wire.encode (.attach 0 0))]
      let cleaned ←
        try
          let (rt, feedback) ← runEffect rt (.replay fd.toNat (Replay.start vt))
          let closed :=
            match feedback with
            | [.closed id] => id == fd.toNat
            | _ => false
          pure ((rt.conn? fd).isNone && closed)
        catch _ =>
          pure false
      expect cleaned "delivery/repeat/invalid-effect-closes-peer"

/-- A queued reply may precede the attach message; its short-write remainder
must precede the captured replay, just as later PTY output must follow it. -/
def prefixOrder (dir : String) : IO Nat := do
  let vt := Linger.Core.Vt.Vt.init 20 5
  withPair dir "prefix" vt fun rt peer fd => do
      let mut rt := rt
      let preceding := ByteArray.mk (Array.replicate (8 * Session.outputChunk) 0x41)
      for _ in [:8] do
        let (rt', events) ←
          runEffect rt (.send fd.toNat (.output (List.replicate Session.outputChunk 0x41)))
        rt ← pump rt' events
      rt ← pump rt [.bytes fd.toNat (Wire.encode (.attach 0 0)), .ptyOut [0x5A]]
      let expected := preceding ++ ByteArray.mk (Render.restore vt).toArray ++ "Z".toUTF8
      let (_, got) ← collect rt peer expected.size
      expect (got.bytes == expected && !got.eof && !got.decoder.errored)
          "delivery/prefix/queued-reply-replay-live"

/-- Long accepted titles cross the scalar slice boundary at a control, and
contain four-byte Unicode. Replay must retain the renderer's sanitization. -/
def titleChunks (dir : String) : IO Nat := do
  let some vt := Linger.Tests.Delivery.acceptedTitle
    | throw (IO.userError "delivery title fixture was refused")
  withPair dir "title" vt fun rt peer fd => do
      let rt ← pump rt [.bytes fd.toNat (Wire.encode (.attach 0 0))]
      let expected := ByteArray.mk (Render.restore vt).toArray
      let (_, got) ← collect rt peer expected.size
      expect (got.bytes == expected && !got.decoder.errored && got.bounded)
          "delivery/title/exact-sanitized-chunks"

/-- Replay is exempt from the live backlog cut, but following live bytes
are not. Check retained debt on every offer, through the eventual real cut. -/
def liveBound (dir : String) : IO Nat := do
  let some vt := Linger.Tests.Delivery.acceptedScreen false
    | throw (IO.userError "large delivery fixture was refused")
  withPair dir "bound" vt fun rt _peer fd => do
      let mut rt ← pump rt [.bytes fd.toNat (Wire.encode (.attach 0 0))]
      rt ← stall rt fd
      let mut bounded := true
      let mut queued := false
      for _ in [:outbufCap / Session.outputChunk + 2] do
        let some c := rt.conn? fd | break
        bounded := bounded && owedLen c.out + owedLen c.after ≤ outbufCap
        queued := queued || owedLen c.after > 0
        let (rt', feedback) ←
          runEffect rt (.send fd.toNat (.output (List.replicate Session.outputChunk 0x42)))
        rt ← pump rt' feedback
      expect (bounded && queued && (rt.conn? fd).isNone) "delivery/bound/live-still-cuts"

/-- A deferred logical close cannot retain a nonreading transport forever. -/
def closeGrace (dir : String) (shutdown : Bool) : IO Nat := do
  let tag := if shutdown then "shutdown-grace" else "close-grace"
  withPair dir tag (Linger.Core.Vt.Vt.init 20 5) fun rt _peer fd => do
      let mut rt := rt
      for _ in [:16] do
        let (rt', feedback) ←
          runEffect rt (.send fd.toNat (.output (List.replicate Session.outputChunk 0x41)))
        rt ← pump rt' feedback
      let (rt', feedback) ← runEffect rt (.close fd.toNat)
      rt ← pump rt' feedback
      let began ← IO.monoMsNow
      if shutdown then
        rt ← drainConns rt
      else
        while (rt.conn? fd).isSome && (← IO.monoMsNow) - began < drainTimeoutMs + 1500 do
          let (rt', events) ← pollRound rt
          rt ← pump rt' events
      expect ((rt.conn? fd).isNone && (← IO.monoMsNow) - began < drainTimeoutMs + 2000)
          s!"delivery/{tag}/nonreader-released"

/-- Removing a client from the pure roster must not permit unbounded retired
socket plans. Exercise actual accepts while earlier clients stay stalled. -/
def closingBound (dir : String) : IO Nat := do
  let some vt := Linger.Tests.Delivery.acceptedScreen false
    | throw (IO.userError "large delivery fixture was refused")
  withPair dir "closing-bound" vt fun rt _peer fd => do
      let peers ← IO.mkRef ([] : List UInt32)
      let latest ← IO.mkRef rt
      try
        let mut rt ← pump rt [.bytes fd.toNat (Wire.encode (.attach 0 0))]
        rt ← stall rt fd
        let (rt', more) ← runEffect rt (.close fd.toNat)
        rt ← pump rt' more
        let mut peak := rt.conns.length
        for _ in [:Session.maxClients + 2] do
          let peer ← unixConnect rt.sockPath
          if peer < 0 then
            throw (IO.userError "closing-bound connect failed")
          peers.modify (peer.toUInt64.toUInt32 :: ·)
          let old := rt.conns.map (·.fd)
          let (rt', events) ← pollRound rt
          rt ← pump rt' events
          let added := rt.conns.filter (fun c => !old.contains c.fd)
          for c in added do
            rt ← pump rt [.bytes c.fd.toNat (Wire.encode (.attach 0 0))]
            rt ← stall rt c.fd
            let (rt', more) ← runEffect rt (.close c.fd.toNat)
            rt ← pump rt' more
          peak := max peak rt.conns.length
          latest.set rt
        expect (peak ≤ Session.maxClients) "delivery/bound/retired-connections"
      finally
        for c in (← latest.get).conns do
          if c.fd != fd then
            close c.fd
        for peer in ← peers.get do
          close peer

/-- Child under the daemon's real PTY. File handshake lets the parent stop
reading the socket before output starts; no guessed scheduling delay. -/
def childProbe (trigger : String) : IO UInt32 := do
  if !(← waitFor 15000 (System.FilePath.pathExists trigger)) then
    return 2
  let stdout ← IO.getStdout
  for _ in [:16] do
    stdout.write (ByteArray.mk (Array.replicate Session.outputChunk (0x51 : UInt8)))
  stdout.flush
  return 7

/-- Run the actual serving loop in a separate process with a private state dir.
The delete hook signals child exit before normal transport cleanup. -/
def serveProbe (dir : String) : IO UInt32 := do
  let bin := (← IO.currentDir) / ".lake" / "build" / "bin" / "e2e"
  serve "tail" dir [bin.toString, "--delivery-child", s!"{dir}/go"] (fun _ => pure ())
      (IO.FS.writeFile s!"{dir}/exited" "") (some (Linger.Core.Vt.Vt.init 20 5, []))
  return 0

def serveTail (dir : String) : IO Nat := do
  let dir := s!"{dir}/serve"
  IO.FS.createDirAll dir
  let bin := (← IO.currentDir) / ".lake" / "build" / "bin" / "e2e"
  let server ←
    IO.Process.spawn
        { cmd := bin.toString, args := #["--delivery-server", dir]
          env := #[("LINGER_DIR", some dir)]
          stdin := .null, stdout := .null, stderr := .inherit }
  let peer ← IO.mkRef (none : Option UInt32)
  let reaped ← IO.mkRef false
  try
    if !(← waitFor 10000 (System.FilePath.pathExists s!"{dir}/tail.sock")) then
      throw (IO.userError "delivery server did not create its socket")
    let fd ← unixConnect s!"{dir}/tail.sock"
    if fd < 0 then
      throw (IO.userError "delivery server connect failed")
    let fd := fd.toUInt64.toUInt32
    peer.set (some fd)
    setNonblock fd
    writeAll fd (ByteArray.mk (Wire.encode (.attach 0 0)).toArray)
    let repaint := ByteArray.mk (Render.restore (Linger.Core.Vt.Vt.init 20 5)).toArray
    let mut got : Received := {}
    let attachedBy := (← IO.monoMsNow) + 10000
    while !got.eof && got.bytes.size < repaint.size && (← IO.monoMsNow) < attachedBy do
      got ← receive fd got
      if got.bytes.size < repaint.size then
        IO.sleep 1
    if got.bytes.size < repaint.size then
      throw (IO.userError "delivery server did not finish initial attach")
    -- The child's output fits the cap, but exceeds the kernel send buffer.
    -- Wait for the daemon to observe EOF while the client reads no bytes.
    IO.FS.writeFile s!"{dir}/go" ""
    let exited ← waitFor 15000 (System.FilePath.pathExists s!"{dir}/exited")
    let mut failures ← expect exited "delivery/serve/child-exit-observed"
    let deadline := (← IO.monoMsNow) + 15000
    while !got.eof && (← IO.monoMsNow) < deadline do
      got ← receive fd got
      if !got.eof then
        IO.sleep 1
    let expected := repaint ++ ByteArray.mk (Array.replicate (16 * Session.outputChunk) 0x51)
    failures := failures + (← expect (got.bytes == expected) "delivery/serve/exact-tail")
    failures :=
      failures +
        (←
          expect
              (got.exits == [(expected.size, 7)] && got.eof && !got.decoder.errored &&
                got.decoder.buf.isEmpty)
              "delivery/serve/status-then-eof")
    let status ← waitProcess server 5000
    reaped.set status.isSome
    failures := failures + (← expect (status == some 0) "delivery/serve/process-drained")
    return failures
  finally
    if let some fd := ← peer.get then
      close fd
    if !(← reaped.get) then
      if (← server.tryWait).isNone then
        server.kill
        let _ ← server.wait
    IO.FS.removeDirAll dir

/-- A retained transport is already logically closed. Exercise both decoded
commands in one packet and bytes already waiting in the event queue. -/
def closeOrder (dir : String) : IO Nat := do
  let mut failures := 0
  for variant in ["packet", "queued", "other-client"] do
    failures :=
      failures +
        (←
          withPair dir s!"close-order-{variant}" (Vt.Vt.init 20 5) fun rt _ fd => do
              let id := fd.toNat
              let control := id + 1
              let attached := (Session.step rt.st (.bytes id (Wire.encode (.attach 20 5)))).1
              let dirty := (Session.step attached (.ptyOut [0x41])).1
              let st :=
                if variant == "other-client" then (Session.step dirty (.connected control)).1
                else dirty
              let saved ← IO.mkRef ([] : List (List (String × String)))
              let rt :=
                { rt with
                  st
                  conns := [{ fd, replay := some (Replay.start st.vt) }]
                  saveCkpt := fun s => saved.modify (· ++ [s.labels]) }
              let detach := Wire.encode .detachAll
              let later := Wire.encode (.labelSet "after=detach".toUTF8.toList)
              let events :=
                if variant == "packet" then [.bytes id (detach ++ later)]
                else
                  [.bytes (if variant == "other-client" then control else id) detach,
                    .bytes id later]
              let rt ← pump rt events
              expect
                  (rt.st.labels.isEmpty && (← saved.get) == [[]] && (rt.st.client? id).isNone &&
                    (rt.conn? fd).any (·.closing))
                  s!"delivery/close-order/{variant}")
  return failures

def run (only : Option String := none) : IO UInt32 := do
  let checks : List (String × (String → IO Nat)) :=
    [("colours", fun dir => largeReplay dir false), ("marks", fun dir => largeReplay dir true),
      ("exit", exitTail), ("snapshot", snapshotOrder), ("pending-wrap", pendingWrap),
      ("repeat", repeatedAttach), ("duplicate", duplicateEffect), ("prefix", prefixOrder),
      ("title", titleChunks), ("live-bound", liveBound),
      ("close-grace", fun dir => closeGrace dir false),
      ("shutdown-grace", fun dir => closeGrace dir true), ("closing-bound", closingBound),
      ("close-order", closeOrder), ("serve", serveTail)]
  if let some name := only then
    if !(checks.any (·.1 == name)) then
      throw (IO.userError s!"unknown delivery check '{name}'")
  let dir := (← IO.currentDir) / ".lake" / s!"delivery-{← getpid}"
  IO.FS.createDirAll dir
  let mut failures := 0
  try
    for (name, check) in checks do
      if only.isNone || only == some name then
        failures := failures + (← check dir.toString)
  finally
    IO.FS.removeDirAll dir
  IO.println s!"FAILURES: {failures}"
  return if failures == 0 then 0 else 1

end E2E.Delivery
