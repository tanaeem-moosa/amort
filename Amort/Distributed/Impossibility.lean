/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Basic

/-!
# Impossibility Theorems: CAP & Two Generals

> **Status: stub — not verified** (Phase 4 canon stub; two-node CAP toy model is proven,
> but full asynchronous consensus impossibility is a specification stub).

This module formalizes two foundational impossibility theorems in distributed computing:
1. **Gilbert-Lynch CAP Theorem (2002)**:
   In an asynchronous network with a network partition separating nodes into disconnected
   groups $G_1$ and $G_2$, no distributed protocol can simultaneously achieve both
   Linearizability (strong consistency) and Availability.
2. **Two Generals' Problem (Gray 1978)**:
   Over an unreliable lossy communication channel where messages can be dropped, coordinated
   consensus (common knowledge of agreement) cannot be guaranteed by any finite message
   exchange protocol.
-/

namespace Amort.Distributed

/-!
## 1. Gilbert-Lynch CAP Theorem
-/

namespace CAP

/-- Data values stored in the distributed register. -/
abbrev Value := ℕ

/-- The initial default value of the register prior to any write. -/
def initialValue : Value := 0

/-- Node identifiers in a two-partition network model. -/
inductive NodeId where
  | n1 : NodeId  -- Node in partition G1
  | n2 : NodeId  -- Node in partition G2
deriving DecidableEq, Repr

/-- Membership in group G1. -/
def inG1 (node : NodeId) : Prop := node = NodeId.n1

/-- Membership in group G2. -/
def inG2 (node : NodeId) : Prop := node = NodeId.n2

/-- Groups G1 and G2 are disjoint. -/
theorem g1_g2_disjoint : ∀ node : NodeId, inG1 node → inG2 node → False := by
  rintro _ rfl h
  cases h

/-- A network partition configuration: messages sent between different groups are dropped. -/
def DroppedByPartition (src dst : NodeId) : Prop :=
  (inG1 src ∧ inG2 dst) ∨ (inG2 src ∧ inG1 dst)

/-- An execution trace of the distributed register.
    Contains:
    - `write_val`: optional value written at node n1
    - `read_node`: node where the client read operation occurs
    - `messages_delivered`: whether cross-partition communication occurred -/
structure Execution where
  write_val : Option Value
  read_node : NodeId
  partitioned : Bool

/-- Local observation of node n2 during the execution.
    Under a partition (`partitioned = true`), no messages from n1 reach n2.
    Hence, node n2's local state depends only on its own local queries. -/
def viewN2 (ex : Execution) : Option Value :=
  if ex.partitioned then
    -- Node n2 observes no external writes across the partition
    none
  else
    ex.write_val

/-- A distributed protocol provides a decision function for read operations
    based on the local observation of the reading node. -/
structure Protocol where
  read_response : Execution → Value
  -- Local causality / indistinguishability: If n2's view is identical,
  -- its response to a read query must be identical.
  local_consistency : ∀ ex1 ex2 : Execution,
    ex1.read_node = NodeId.n2 →
    ex2.read_node = NodeId.n2 →
    viewN2 ex1 = viewN2 ex2 →
    read_response ex1 = read_response ex2

/-- Availability: Every read request to a non-failing node must terminate
    and return a response value (already guaranteed by `read_response : Execution → Value`). -/
def SatisfiesAvailability (_ : Protocol) : Prop := True

/-- Linearizability (Consistency C):
    1. If a write of value `v` completed before the read began, the read must return `v`.
    2. If no write occurred, the read must return the initial value `initialValue`. -/
def SatisfiesLinearizability (proto : Protocol) : Prop :=
  (∀ ex : Execution, ex.write_val = none → proto.read_response ex = initialValue) ∧
  (∀ ex : Execution, ∀ v : Value, ex.write_val = some v → proto.read_response ex = v)

/-- **Gilbert-Lynch CAP Impossibility Theorem**:
    Under a network partition where messages between G1 and G2 are lost, no protocol
    can satisfy both Linearizability (strong consistency) and Availability. -/
theorem gilbert_lynch_impossibility (proto : Protocol) (v : Value) (hv : v ≠ initialValue) :
    ¬ SatisfiesLinearizability proto := by
  intro h_lin
  rcases h_lin with ⟨h_no_write, h_write⟩
  -- Execution alpha: Write of value `v` at n1, read at n2, under network partition.
  let ex_alpha : Execution := {
    write_val := some v,
    read_node := NodeId.n2,
    partitioned := true
  }
  -- Execution beta: No write performed, read at n2, under network partition.
  let ex_beta : Execution := {
    write_val := none,
    read_node := NodeId.n2,
    partitioned := true
  }
  -- 1. Linearizability on beta requires read to return initialValue.
  have h_beta : proto.read_response ex_beta = initialValue := h_no_write ex_beta rfl
  -- 2. Linearizability on alpha requires read to return v.
  have h_alpha : proto.read_response ex_alpha = v := h_write ex_alpha v rfl
  -- 3. But n2's local view in alpha and beta is identical because of the partition.
  have h_view : viewN2 ex_alpha = viewN2 ex_beta := by
    dsimp [viewN2, ex_alpha, ex_beta]
  -- 4. By local consistency / indistinguishability, the responses must be identical.
  have h_indist : proto.read_response ex_alpha = proto.read_response ex_beta :=
    proto.local_consistency ex_alpha ex_beta rfl rfl h_view
  -- 5. Contradiction: v = initialValue, contradicting hv.
  rw [h_alpha, h_beta] at h_indist
  exact hv h_indist

end CAP

/-!
## 2. Two Generals' Problem
-/

namespace TwoGenerals

/-- Action decided by a general: either attack at dawn or retreat. -/
inductive Action where
  | Attack : Action
  | Retreat : Action
deriving DecidableEq, Repr

/-- In an execution with `k` delivered messages:
    `dec k` produces the pair `(decision_A, decision_B)`. -/
def DecisionSequence := ℕ → Action × Action

/-- Agreement condition: In every execution, both generals make the same decision. -/
def Agreement (dec : DecisionSequence) : Prop :=
  ∀ k : ℕ, (dec k).1 = (dec k).2

/-- Channel unreliability / Indistinguishability of the last message sender:
    When the `k`-th message is sent, the sender cannot distinguish whether it was
    delivered to the receiver or lost in the unreliable channel.
    - If `k` is odd (sent by General A): General A's decision at step `k` must equal
      General A's decision at step `k - 1`.
    - If `k` is even and positive (sent by General B): General B's decision at step `k`
      must equal General B's decision at step `k - 1`. -/
def LossyIndistinguishable (dec : DecisionSequence) : Prop :=
  ∀ k : ℕ,
    (k % 2 = 1 → (dec k).1 = (dec (k - 1)).1) ∧
    (k > 0 ∧ k % 2 = 0 → (dec k).2 = (dec (k - 1)).2)

/-- Base validity condition: If zero messages are delivered, General B has received
    no communication from General A, and therefore cannot decide to attack. -/
def ZeroMessageValidity (dec : DecisionSequence) : Prop :=
  (dec 0).2 = Action.Retreat

/-- Step reduction lemma: If agreement and lossy indistinguishability hold,
    and both generals attack at step `k`, then both generals attack at step `k - 1`. -/
theorem step_reduction (dec : DecisionSequence)
    (h_agree : Agreement dec) (h_lossy : LossyIndistinguishable dec)
    (k : ℕ) (hk : k > 0)
    (h_attack : dec k = (Action.Attack, Action.Attack)) :
    dec (k - 1) = (Action.Attack, Action.Attack) := by
  have h_agree_k_pred := h_agree (k - 1)
  by_cases h_odd : k % 2 = 1
  · -- k is odd: General A sent message k, so General A's decision is unchanged
    have h_a := (h_lossy k).1 h_odd
    have h_a_k : (dec k).1 = Action.Attack := by rw [h_attack]
    have h_a_pred : (dec (k - 1)).1 = Action.Attack := by rwa [← h_a]
    have h_b_pred : (dec (k - 1)).2 = Action.Attack := by
      rw [← h_agree_k_pred]
      exact h_a_pred
    exact Prod.ext h_a_pred h_b_pred
  · -- k is even: General B sent message k, so General B's decision is unchanged
    have h_even : k % 2 = 0 := by
      cases Nat.mod_two_eq_zero_or_one k with
      | inl h0 => exact h0
      | inr h1 => exfalso; exact h_odd h1
    have h_b := (h_lossy k).2 ⟨hk, h_even⟩
    have h_b_k : (dec k).2 = Action.Attack := by rw [h_attack]
    have h_b_pred : (dec (k - 1)).2 = Action.Attack := by rwa [← h_b]
    have h_a_pred : (dec (k - 1)).1 = Action.Attack := by
      rw [h_agree_k_pred]
      exact h_b_pred
    exact Prod.ext h_a_pred h_b_pred

/-- Backward induction: If both generals attack at step `k`, then they must also attack
    with zero messages delivered. -/
theorem attack_zero_of_attack_k (dec : DecisionSequence)
    (h_agree : Agreement dec) (h_lossy : LossyIndistinguishable dec) :
    ∀ k : ℕ, dec k = (Action.Attack, Action.Attack) →
      dec 0 = (Action.Attack, Action.Attack) := by
  intro k
  induction k with
  | zero => intro h; exact h
  | succ n ih =>
    intro h_succ
    have h_pred := step_reduction dec h_agree h_lossy (n + 1) (Nat.succ_pos n) h_succ
    exact ih h_pred

/-- **Two Generals' Impossibility Theorem**:
    No protocol over an unreliable lossy channel can simultaneously satisfy
    Agreement, Lossy Indistinguishability, and Zero-Message Validity while
    guaranteeing coordinated attack at any message delivery count `k`. -/
theorem two_generals_impossibility (dec : DecisionSequence)
    (h_agree : Agreement dec)
    (h_lossy : LossyIndistinguishable dec)
    (h_valid : ZeroMessageValidity dec)
    (k : ℕ) :
    dec k ≠ (Action.Attack, Action.Attack) := by
  intro h_attack_k
  have h_attack_zero := attack_zero_of_attack_k dec h_agree h_lossy k h_attack_k
  have h_b_zero : (dec 0).2 = Action.Attack := by rw [h_attack_zero]
  rw [h_valid] at h_b_zero
  contradiction

end TwoGenerals

end Amort.Distributed
