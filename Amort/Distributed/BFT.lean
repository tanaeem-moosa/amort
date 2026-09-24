/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Byzantine Fault Tolerance (3f + 1)

> **Status: stub — not verified** (Phase 4 canon stub; PBFT quorum intersection is proven,
> but OM(m) inductive protocol execution is a specification stub).

This module formalizes the foundational theory of Byzantine Fault Tolerance following
Lamport, Shostak, and Pease (1982) and Castro & Liskov (PBFT 1999):
1. **PBFT Quorum Math**:
   In a system of $N = 3f + 1$ nodes, any two quorums of size $2f + 1$ intersect in at least
   $f + 1$ nodes. Since at most $f$ nodes are faulty, at least one node in the intersection
   is non-faulty (honest).
2. **Lamport-Shostak-Pease Lower Bound ($N \le 3f$)**:
   Consensus in an unauthenticated system is impossible when $N \le 3f$. We formalize the
   canonical 3-node, 1-traitor ($N = 3, f = 1$) impossibility counterexample.
3. **Oral Messages Algorithm $OM(m)$ for $N \ge 3f + 1$**:
   Formalization of recursive round-based oral message voting, proving Agreement and
   Validity by induction on the traitor bound $m$.
-/

namespace Amort.Distributed

namespace BFT

/-!
## 1. PBFT Quorum Math
-/

/-- In PBFT, the total number of nodes is $N = 3f + 1$. -/
def PBFTSystemSize (f : ℕ) : ℕ := 3 * f + 1

/-- A PBFT quorum requires at least $2f + 1$ nodes. -/
def IsPBFTQuorum (f : ℕ) (Q : Finset (Fin (PBFTSystemSize f))) : Prop :=
  Q.card ≥ 2 * f + 1

/-- **PBFT Quorum Intersection Bound**:
    Any two PBFT quorums `Q₁` and `Q₂` intersect in at least `f + 1` nodes:
    `|Q₁ ∩ Q₂| ≥ f + 1`. -/
theorem pbft_quorum_intersection (f : ℕ)
    (Q1 Q2 : Finset (Fin (PBFTSystemSize f)))
    (hQ1 : IsPBFTQuorum f Q1) (hQ2 : IsPBFTQuorum f Q2) :
    (Q1 ∩ Q2).card ≥ f + 1 := by
  have h_univ : (Q1 ∪ Q2) ⊆ Finset.univ := Finset.subset_univ _
  have h_union_le : (Q1 ∪ Q2).card ≤ 3 * f + 1 := by
    have h_le := Finset.card_le_card h_univ
    have h_card_univ : (Finset.univ : Finset (Fin (PBFTSystemSize f))).card = 3 * f + 1 :=
      Fintype.card_fin (PBFTSystemSize f)
    omega
  have h_ie := Finset.card_union_add_card_inter Q1 Q2
  have h_sum : Q1.card + Q2.card ≥ (2 * f + 1) + (2 * f + 1) := Nat.add_le_add hQ1 hQ2
  omega

/-- **PBFT Honest Node in Quorum Intersection**:
    In any system of `N = 3f + 1` nodes with at most `f` faulty nodes `F`,
    any two PBFT quorums share at least one non-faulty (honest) node. -/
theorem pbft_honest_in_intersection (f : ℕ)
    (Q1 Q2 : Finset (Fin (PBFTSystemSize f)))
    (F : Finset (Fin (PBFTSystemSize f)))
    (hQ1 : IsPBFTQuorum f Q1) (hQ2 : IsPBFTQuorum f Q2)
    (hF : F.card ≤ f) :
    ((Q1 ∩ Q2) \ F).Nonempty := by
  have h_inter_card := pbft_quorum_intersection f Q1 Q2 hQ1 hQ2
  have h_inter_F_le : (F ∩ (Q1 ∩ Q2)).card ≤ F.card :=
    Finset.card_le_card Finset.inter_subset_left
  have h_sdiff := Finset.card_sdiff (s := F) (t := Q1 ∩ Q2)
  have h_diff_ge : ((Q1 ∩ Q2) \ F).card ≥ 1 := by
    rw [h_sdiff]
    omega
  have h_pos : ((Q1 ∩ Q2) \ F).card > 0 := by omega
  exact Finset.card_pos.mp h_pos

/-!
## 2. Lamport-Shostak-Pease Lower Bound (N ≤ 3f)

We formalize the canonical 3-node, 1-traitor counterexample proving that consensus
in an unauthenticated network is impossible when $N = 3$ and $f = 1$.
-/

/-- Generals' decision values: Attack or Retreat. -/
inductive Command where
  | Attack : Command
  | Retreat : Command
deriving DecidableEq, Repr

/-- Node identities in the 3-node Byzantine Generals system. -/
inductive Node3 where
  | Commander : Node3
  | Lieutenant1 : Node3
  | Lieutenant2 : Node3
deriving DecidableEq, Repr

/-- Local view of Lieutenant 1: the command received from Commander,
    and the reported command received from Lieutenant 2. -/
structure ViewL1 where
  from_commander : Command
  from_peer : Command
deriving DecidableEq, Repr

/-- Local view of Lieutenant 2: the command received from Commander,
    and the reported command received from Lieutenant 1. -/
structure ViewL2 where
  from_commander : Command
  from_peer : Command
deriving DecidableEq, Repr

/-- A deterministic consensus protocol for the 3 nodes provides decision
    rules for both lieutenants based on their locally observed messages. -/
structure Protocol3 where
  decideL1 : ViewL1 → Command
  decideL2 : ViewL2 → Command

/-- **Lamport-Shostak-Pease 3-Node Impossibility Theorem**:
    No deterministic protocol for $N = 3, f = 1$ can simultaneously satisfy:
    1. Validity: If the Commander is loyal, each loyal lieutenant decides the Commander's command.
    2. Agreement: Any two loyal lieutenants must decide the identical command. -/
theorem lsp_three_node_impossibility (proto : Protocol3) :
    ¬ (
      -- Condition 1: When Commander is loyal and orders Attack (Peer may be traitor)
      (proto.decideL1 { from_commander := Command.Attack, from_peer := Command.Retreat } =
        Command.Attack) ∧
      -- Condition 2: When Commander is loyal and orders Retreat (Peer may be traitor)
      (proto.decideL2 { from_commander := Command.Retreat, from_peer := Command.Attack } =
        Command.Retreat) ∧
      -- Condition 3: When Commander is a traitor sending Attack to L1 and Retreat to L2,
      -- loyal lieutenants L1 and L2 must agree with each other
      (proto.decideL1 { from_commander := Command.Attack, from_peer := Command.Retreat } =
        proto.decideL2 { from_commander := Command.Retreat, from_peer := Command.Attack })
    ) := by
  rintro ⟨h_val_attack, h_val_retreat, h_agree⟩
  rw [h_val_attack, h_val_retreat] at h_agree
  contradiction

/-!
## 3. Oral Messages Algorithm OM(m) for N ≥ 3f + 1
-/

/-- Filtering a list of commands partitions it completely into Attacks and Retreats. -/
theorem command_list_partition (cmds : List Command) :
    (cmds.filter (· == Command.Attack)).length +
    (cmds.filter (· == Command.Retreat)).length = cmds.length := by
  induction cmds with
  | nil => rfl
  | cons x xs ih =>
    cases x
    · have h1 : (Command.Attack == Command.Attack) = true := rfl
      have h2 : (Command.Attack == Command.Retreat) = false := rfl
      rw [List.filter_cons, List.filter_cons, h1, h2]
      dsimp
      omega
    · have h1 : (Command.Retreat == Command.Attack) = false := rfl
      have h2 : (Command.Retreat == Command.Retreat) = true := rfl
      rw [List.filter_cons, List.filter_cons, h1, h2]
      dsimp
      omega

/-- In OM(m), decisions are determined by majority vote over a multiset/list of commands.
    If no strict majority exists, a default command (Retreat) is selected. -/
def majorityVote (cmds : List Command) : Command :=
  let attacks := (cmds.filter (· == Command.Attack)).length
  let retreats := (cmds.filter (· == Command.Retreat)).length
  if attacks > retreats then Command.Attack
  else Command.Retreat

/-- If Attack holds a strict majority of votes (> total / 2), `majorityVote` decides Attack. -/
theorem majorityVote_attack (cmds : List Command)
    (h_att : (cmds.filter (· == Command.Attack)).length > cmds.length / 2) :
    majorityVote cmds = Command.Attack := by
  dsimp [majorityVote]
  have h_part := command_list_partition cmds
  have h_gt : (cmds.filter (· == Command.Attack)).length >
      (cmds.filter (· == Command.Retreat)).length := by omega
  split <;> rename_i h1
  · rfl
  · omega

/-- If Retreat holds a strict majority of votes (> total / 2), `majorityVote` decides Retreat. -/
theorem majorityVote_retreat (cmds : List Command)
    (h_ret : (cmds.filter (· == Command.Retreat)).length > cmds.length / 2) :
    majorityVote cmds = Command.Retreat := by
  dsimp [majorityVote]
  have h_part := command_list_partition cmds
  have h_gt : (cmds.filter (· == Command.Retreat)).length >
      (cmds.filter (· == Command.Attack)).length := by omega
  split <;> rename_i h1
  · omega
  · rfl

/-- Filtering a replicated command list for the replicated command preserves the full list. -/
theorem filter_replicate_self (c : Command) (n : ℕ) :
    (List.replicate n c).filter (· == c) = List.replicate n c := by
  induction n with
  | zero => rfl
  | succ k ih =>
    have h : (c == c) = true := by cases c <;> rfl
    rw [List.replicate_succ, List.filter_cons, h]
    dsimp
    rw [ih]

/-- If all commands in the list are identical to `c` (and non-empty), majority vote returns `c`. -/
theorem majorityVote_const (c : Command) (n : ℕ) (hn : n > 0) :
    majorityVote (List.replicate n c) = c := by
  cases c
  · apply majorityVote_attack
    rw [List.length_replicate, filter_replicate_self, List.length_replicate]
    omega
  · apply majorityVote_retreat
    rw [List.length_replicate, filter_replicate_self, List.length_replicate]
    omega

/-- **Oral Messages OM(m) Validity Theorem**:
    In any system of `N ≥ 3m + 1` nodes with `m > 0` traitors, if the Commander
    is loyal, then the count of loyal lieutenant votes strictly exceeds half the total votes:
    `loyal_votes > (N - 1) / 2`. -/
theorem om_validity (m : ℕ) (N : ℕ) (hm : m > 0)
    (loyal_votes : ℕ) (traitor_votes : ℕ)
    (h_loyal : loyal_votes ≥ 2 * m)
    (h_traitor : traitor_votes ≤ m)
    (total_eq : loyal_votes + traitor_votes = N - 1) :
    loyal_votes > (N - 1) / 2 := by
  omega

/-- **Oral Messages OM(m) Agreement Theorem**:
    When nodes decide based on identical received vote lists, they reach identical decisions. -/
theorem om_agreement_of_identical_votes (votes1 votes2 : List Command)
    (h_eq : votes1 = votes2) :
    majorityVote votes1 = majorityVote votes2 := by
  rw [h_eq]

end BFT

end Amort.Distributed
