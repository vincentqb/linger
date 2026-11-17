module

import all Linger.Session.CoreCode
import all Linger.Session.CoreCode.Handoff
import all Linger.Session.Proofs.Checkpoint
import all Terminal.Proofs.Vt

/-! # The handoff round trip

The headlines `handoff_carries`, `handoff_versioned` and `upgrade_probes` (`Challenge.lean`,
part 7) rest on `decode_encode`, `encode_header`, `decode_unknown` and `proceeds_iff` below. Each
field codec inverts its writer whatever follows it (`RT`), as the checkpoint's do; the terminal's
inverts its writer for a terminal a live session can hold whose parser is quiet, since the
checkpoint codec it goes through forgets a partial sequence. -/

namespace Linger.Session.Handoff

open Terminal
open Linger.Session.Checkpoint

theorem rt_byte : RT wByte rByte := fun _ _ => rfl

theorem rt_bytes : RT wBytes rBytes := fun bs rest => rt_list rt_byte bs rest

theorem rt_u32 : RT wU32 rU32 := by
  intro n rest
  simp only [wU32, rU32, rt_nat, Option.bind_eq_bind, Option.bind_some, UInt32.ofNat_toNat]

theorem rt_outcome : RT wOutcome rOutcome := by
  intro o rest
  cases o <;> rfl

theorem rt_ending : RT wEnding rEnding := by
  intro e rest
  cases e with
  | program o => simp only [wEnding, rEnding, List.cons_append, rt_outcome, Option.map_some]
  | saved _ => rfl
  | dismissed => rfl

theorem rt_mode : RT wMode rMode := by
  intro m rest
  cases m <;> rfl

theorem rt_decoder : RT wDecoder rDecoder := by
  intro d rest
  simp only [wDecoder, rDecoder, List.append_assoc, rt_bytes, rt_bool, Option.bind_eq_bind,
    Option.bind_some]

theorem rt_client : RT wClient rClient := by
  intro c rest
  simp only [wClient, rClient, List.append_assoc, rt_nat, rt_u32, rt_bool, rt_mode, rt_decoder,
    Option.bind_eq_bind, Option.bind_some]

theorem rt_scan : RT wScan rScan := by
  intro s rest
  cases s <;>
    simp only [wScan, rScan, List.cons_append, List.nil_append, List.append_assoc, rt_bytes,
      rt_bool, Option.map_some, Option.bind_eq_bind, Option.bind_some]

theorem rt_cmdline : RT wCmdline rCmdline := by
  intro c rest
  simp only [wCmdline, rCmdline, List.append_assoc, rt_bytes, rt_bool, Option.bind_eq_bind,
    Option.bind_some]

theorem rt_finished : RT wFinished rFinished := by
  intro f rest
  simp only [wFinished, rFinished, List.append_assoc, rt_cmdline, rt_opt rt_nat,
    Option.bind_eq_bind, Option.bind_some]

theorem rt_foreground : RT wForeground rForeground := by
  intro f rest
  simp only [wForeground, rForeground, List.append_assoc, rt_nat, rt_list rt_str, rt_str,
    Option.bind_eq_bind, Option.bind_some]

theorem rt_observation : RT wObservation (rObservation version) := by
  intro o rest
  simp only [wObservation, rObservation, List.append_assoc, rt_nat, rt_bool, rt_opt rt_foreground,
    rt_opt rt_bool, version, Nat.lt_irrefl, ↓reduceIte, Option.bind_eq_bind, Option.bind_some]

theorem rt_fields : RT wFields rFields := fun kvs rest => rt_list (rt_pair rt_str rt_str) kvs rest

/-- The terminal of a live session whose parser is quiet comes back as it was. -/
theorem rTerminal_wTerminal (vt : Vt.Vt) (live : Vt.LiveReachableVt vt) (quiet : vt.quiesce = vt)
    (rest : List UInt8) : rTerminal (wTerminal vt ++ rest) = some (vt, rest) := by
  unfold rTerminal wTerminal
  rw [rt_bytes]
  have back :
    (⟨(Checkpoint.saveBytes { vt, cwd := "", fields := [] }).data.toList.toArray⟩ : ByteArray) =
      Checkpoint.saveBytes { vt, cwd := "", fields := [] } := by
    simp
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [back, loadBytes_saveBytes_live { vt, cwd := "", fields := [] } live]
  simp only [Option.bind_some, quiet]

/-- The state of a live session whose terminal's parser is quiet comes back as it was, every
field. -/
theorem rState_wState (s : State) (live : Vt.LiveReachableVt s.vt) (quiet : s.vt.quiesce = s.vt)
    (rest : List UInt8) : rState version (wState s ++ rest) = some (s, rest) := by
  unfold rState wState
  simp only [List.append_assoc, rTerminal_wTerminal s.vt live quiet, rt_scan, rt_list rt_client,
    rt_fields, rt_opt rt_ending, rt_bool, rt_nat, rt_opt rt_bytes, rt_opt rt_cmdline,
    rt_opt rt_finished, rt_opt rt_nat, rt_opt rt_observation, Option.bind_eq_bind, Option.bind_some]

theorem rt_conn : RT wConn rConn := by
  intro c rest
  simp only [wConn, rConn, List.append_assoc, rt_nat, rt_bytes, rt_opt rt_nat, Option.bind_eq_bind,
    Option.bind_some]

theorem rt_world : RT wWorld rWorld := by
  intro w rest
  simp only [wWorld, rWorld, List.append_assoc, rt_nat, rt_pair rt_nat rt_nat, rt_list rt_nat,
    rt_list rt_conn, rt_bytes, rt_bool, Option.bind_eq_bind, Option.bind_some]

/-- **Carried, not rebuilt.** The handoff of a live session whose terminal's parser is quiet
decodes as that session's state and what its daemon kept for it, every field. -/
theorem decode_encode (s : State) (w : World) (live : Vt.LiveReachableVt s.vt)
    (quiet : s.vt.quiesce = s.vt) : decode (encode s w) = some (s, w) := by
  have strip :
    stripHeader (header version ++ (wState s ++ wWorld w)) =
      some (version, wState s ++ wWorld w) := by
    simp [stripHeader, header, magic, version, formats]
  have world := rt_world w []
  rw [List.append_nil] at world
  unfold decode encode
  rw [List.append_assoc, strip]
  simp only [Option.bind_eq_bind, Option.bind_some, rState_wState s live quiet, world,
    List.isEmpty_nil, ↓reduceIte]

/-- A handoff begins with the header of the format this version writes. -/
theorem encode_header (s : State) (w : World) :
    (encode s w).take (header version).length = header version := by simp [encode]

/-- A handoff of a format this version does not read decodes as nothing, whatever follows. -/
theorem decode_unknown (v : Nat) (rest : List UInt8) (unknown : v ∉ formats) (small : v < 256) :
    decode (header v ++ rest) = none := by
  have byte : (UInt8.ofNat v).toNat = v := by
    simp only [UInt8.toNat_ofNat']
    omega
  have strip : stripHeader (header v ++ rest) = none := by
    simp only [header, magic, List.cons_append, List.nil_append, stripHeader, byte, true_and]
    simp [unknown]
  simp [decode, strip]

/-- **An upgrade keeps every descriptor its handoff names.** -/
theorem fds_kept (w : World) : ∀ fd ∈ w.fds, fd ∈ kept w := fun _ h => by
  simpa [kept, World.fds] using h

end Linger.Session.Handoff

namespace Linger.Session.Upgrade

/-- A daemon hands its session over exactly when the probe named the format it writes. -/
theorem proceeds_iff (reported : Option (List Nat)) :
    proceeds reported = true ↔ ∃ formats, reported = some formats ∧ Handoff.version ∈ formats := by
  cases reported <;> simp [proceeds]

end Linger.Session.Upgrade
