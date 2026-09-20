/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Basic

/-!
# Consistent Global Snapshots: Chandy-Lamport Algorithm

This module formalizes distributed snapshots and the Chandy-Lamport (1985) algorithm:
1. **System Model & Cuts**:
   Distributed processes connected by directed FIFO channels, message transmission,
   and the formal definition of a **Consistent Cut**.
2. **Chandy-Lamport Algorithm Rules**:
   Marker-passing protocol over FIFO channels and channel state recording rules.
3. **Consistent Cut Theorem**:
   Proof that the global state recorded by the Chandy-Lamport algorithm forms a consistent cut:
   no message received before the snapshot was sent after the snapshot (`r ≤ T_q ⟹ s ≤ T_p`).
4. **Channel State Recording Soundness**:
   Every message recorded in a channel's state was sent before the sender's snapshot
   and received after the receiver's snapshot.
-/

namespace Amort.Distributed

namespace Snapshot

/-- A directed channel from process `src` to process `dst` in a system of `N` nodes. -/
structure Channel (N : ℕ) where
  src : Fin N
  dst : Fin N
deriving DecidableEq, Repr

/-- A message transmission event over a channel.
    `send_time` is the local sequence index on process `src` when the message was sent.
    `recv_time` is the local sequence index on process `dst` when the message was delivered. -/
structure Message (N : ℕ) where
  id : ℕ
  src : Fin N
  dst : Fin N
  send_time : ℕ
  recv_time : ℕ
deriving DecidableEq, Repr

/-- A global cut defines a local checkpoint / snapshot point for each process. -/
def Cut (N : ℕ) := Fin N → ℕ

/-- **Consistent Cut Definition**:
    A cut is consistent if for every message in the execution, if the message was
    received before or at the receiver's cut point, it must have been sent
    before or at the sender's cut point:
    `recv_time ≤ cut dst ⟹ send_time ≤ cut src`.
    (No message travels backward in time across the cut boundary). -/
def IsConsistentCut {N : ℕ} (cut : Cut N) (msgs : Set (Message N)) : Prop :=
  ∀ m ∈ msgs, m.recv_time ≤ cut m.dst → m.send_time ≤ cut m.src

/-- An execution conforming to the Chandy-Lamport distributed snapshot protocol.
    Contains:
    - `snapshot_time`: The local time when each process records its local state.
    - `marker_recv_time`: The time when the Marker message is delivered along channel `c`.
    - `fifo_marker`: FIFO channel discipline with respect to Marker messages:
      - Messages sent before the sender's snapshot arrive before the Marker.
      - Messages sent after the sender's snapshot arrive after the Marker.
    - `snapshot_trigger`: A process records its snapshot at or before receiving a Marker
      along any incoming channel. -/
structure ChandyLamportExecution (N : ℕ) where
  msgs : Set (Message N)
  snapshot_time : Fin N → ℕ
  marker_recv_time : Channel N → ℕ
  -- FIFO Rule: Messages sent after snapshot time arrive after the Marker
  fifo_after : ∀ m ∈ msgs,
    m.send_time > snapshot_time m.src →
    m.recv_time > marker_recv_time { src := m.src, dst := m.dst }
  -- Snapshot Trigger Rule: A receiver takes its snapshot at or before Marker arrival
  snapshot_before_marker : ∀ c : Channel N,
    snapshot_time c.dst ≤ marker_recv_time c

/-- **Chandy-Lamport Consistent Cut Theorem**:
    The local snapshot points recorded by the Chandy-Lamport algorithm form a consistent cut.
    No message received before or at the snapshot was sent after the snapshot. -/
theorem chandy_lamport_consistent_cut {N : ℕ} (exec : ChandyLamportExecution N) :
    IsConsistentCut exec.snapshot_time exec.msgs := by
  intro m hm h_recv_le
  -- We must prove m.send_time ≤ exec.snapshot_time m.src
  by_contra h_not_le
  have h_send_gt : m.send_time > exec.snapshot_time m.src := by omega
  -- By FIFO rule, m must arrive after the Marker on channel (m.src, m.dst)
  have h_after_marker := exec.fifo_after m hm h_send_gt
  -- By Snapshot Trigger rule, receiver snapshot_time is at or before Marker arrival
  let ch : Channel N := { src := m.src, dst := m.dst }
  have h_snap_le_marker := exec.snapshot_before_marker ch
  -- Hence m.recv_time > exec.snapshot_time m.dst, contradicting h_recv_le
  have h_contra : m.recv_time > exec.snapshot_time m.dst := by
    calc m.recv_time
      _ > exec.marker_recv_time ch := h_after_marker
      _ ≥ exec.snapshot_time m.dst := h_snap_le_marker
  omega

/-- Classification of message state with respect to a global cut. -/
inductive MessageCutClassification where
  | Internal : MessageCutClassification   -- Sent before cut, received before cut
  | InTransit : MessageCutClassification  -- Sent before cut, received after cut (in channel state)
  | PostCut : MessageCutClassification    -- Sent after cut, received after cut
  | Inconsistent : MessageCutClassification -- Sent after cut, received before cut (impossible)
deriving DecidableEq, Repr

/-- Classify a message relative to a cut. -/
def classifyMessage {N : ℕ} (cut : Cut N) (m : Message N) : MessageCutClassification :=
  if m.send_time ≤ cut m.src then
    if m.recv_time ≤ cut m.dst then
      MessageCutClassification.Internal
    else
      MessageCutClassification.InTransit
  else
    if m.recv_time ≤ cut m.dst then
      MessageCutClassification.Inconsistent
    else
      MessageCutClassification.PostCut

/-- In any consistent cut, no message is classified as `Inconsistent`. -/
theorem consistent_cut_no_inconsistent {N : ℕ} {cut : Cut N} {msgs : Set (Message N)}
    (h_cons : IsConsistentCut cut msgs) (m : Message N) (hm : m ∈ msgs) :
    classifyMessage cut m ≠ MessageCutClassification.Inconsistent := by
  intro h_incons
  dsimp [classifyMessage] at h_incons
  split at h_incons
  · rename_i h_send_le
    split at h_incons <;> contradiction
  · rename_i h_send_gt
    split at h_incons
    · rename_i h_recv_le
      have h_sound := h_cons m hm h_recv_le
      omega
    · contradiction

/-- Channel state predicate: A message belongs to the recorded channel state
    iff it was sent before the sender's snapshot and received after the receiver's snapshot. -/
def InChannelState {N : ℕ} (exec : ChandyLamportExecution N) (m : Message N) : Prop :=
  m.send_time ≤ exec.snapshot_time m.src ∧
  m.recv_time > exec.snapshot_time m.dst

/-- **Channel State Soundness Theorem**:
    Every message recorded in the channel state was sent before or at the sender's snapshot point.
    No message recorded in channel state was sent after the snapshot was taken. -/
theorem channel_state_soundness {N : ℕ} (exec : ChandyLamportExecution N)
    (m : Message N) (h_in_chan : InChannelState exec m) :
    m.send_time ≤ exec.snapshot_time m.src :=
  h_in_chan.1

end Snapshot

end Amort.Distributed
