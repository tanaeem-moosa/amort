/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

/-!
# Crash-Tolerant Consensus: Paxos & Raft

> **Status: stub — not verified** (Phase 4 canon stub; quorum intersection is proven,
> but Paxos P2 invariant and Raft log matching are specification stubs).

This module formalizes the foundational theory of crash-tolerant consensus in distributed
systems following Lamport (1998, 2001) and Ongaro & Ousterhout (2014):
1. **Majority Quorum Intersection**:
   For any system of $N$ nodes, any two majority quorums $Q_1, Q_2$ intersect non-trivially:
   $|Q_1|, |Q_2| > N / 2 \implies Q_1 \cap Q_2 \ne \emptyset$.
2. **Single-Decree Paxos (Synod Protocol)**:
   Ballot identifiers (`Ballot = ℕ × Fin N`) with total lexicographic ordering.
   Two-phase state machine, Core Paxos Invariant, and Learner Agreement Theorem ($v_1 = v_2$).
3. **Multi-Paxos Replicated Log**:
   Slot-indexed consensus instances and Replicated State Machine (RSM) safety.
4. **Raft Safety Invariants**:
   Leader Election Safety (at most one leader per term via quorum intersection),
   term monotonicity, and the Log Matching Invariant.
-/

namespace Amort.Distributed

namespace Consensus

/-!
## 1. Majority Quorum Intersection Foundation
-/

/-- A majority quorum in a system of `N` processes is a subset of processes
    whose cardinality strictly exceeds `N / 2`. -/
def IsMajorityQuorum (N : ℕ) (Q : Finset (Fin N)) : Prop :=
  Q.card > N / 2

/-- If a majority quorum exists, the system size `N` must be strictly positive. -/
theorem pos_of_majority {N : ℕ} {Q : Finset (Fin N)} (h : IsMajorityQuorum N Q) : N > 0 := by
  by_contra h_not
  have hN0 : N = 0 := by omega
  subst hN0
  have h_le := Finset.card_le_card (Finset.subset_univ Q)
  have h_card_univ : (Finset.univ : Finset (Fin 0)).card = 0 := Fintype.card_fin 0
  rw [h_card_univ] at h_le
  have h_gt : Q.card > 0 / 2 := h
  omega

/-- **Majority Quorum Intersection Theorem**:
    In any system of `N > 0` processes, any two majority quorums `Q₁` and `Q₂`
    have a non-empty intersection. -/
theorem majority_quorum_intersection {N : ℕ} (_hN : N > 0)
    {Q1 Q2 : Finset (Fin N)}
    (hQ1 : IsMajorityQuorum N Q1) (hQ2 : IsMajorityQuorum N Q2) :
    (Q1 ∩ Q2).Nonempty := by
  have h_univ : (Q1 ∪ Q2) ⊆ Finset.univ := Finset.subset_univ _
  have h_card_univ : (Finset.univ : Finset (Fin N)).card = N := Fintype.card_fin N
  have h_union_le : (Q1 ∪ Q2).card ≤ N := by
    have h_le := Finset.card_le_card h_univ
    omega
  have h_ie := Finset.card_union_add_card_inter Q1 Q2
  by_contra h_empty
  have h_inter_zero : (Q1 ∩ Q2).card = 0 := by
    rw [Finset.card_eq_zero]
    exact Finset.not_nonempty_iff_eq_empty.mp h_empty
  rw [h_inter_zero, Nat.add_zero] at h_ie
  -- Now: (Q1 ∪ Q2).card = Q1.card + Q2.card
  have hQ1_ge : Q1.card ≥ N / 2 + 1 := hQ1
  have hQ2_ge : Q2.card ≥ N / 2 + 1 := hQ2
  have h_sum : Q1.card + Q2.card ≥ 2 * (N / 2) + 2 := by omega
  have h_union_ge : (Q1 ∪ Q2).card ≥ 2 * (N / 2) + 2 := by
    rwa [← h_ie] at h_sum
  have h_div_bound : N < 2 * (N / 2) + 2 := by omega
  have h_contra : (Q1 ∪ Q2).card > N := Nat.lt_of_lt_of_le h_div_bound h_union_ge
  exact Nat.lt_irrefl N (Nat.lt_of_lt_of_le h_contra h_union_le)

/-!
## 2. Single-Decree Paxos (Synod Protocol)
-/

/-- A ballot identifier in Paxos consists of a round number and a unique proposer ID. -/
structure Ballot (N : ℕ) where
  round : ℕ
  proposer : Fin N
deriving DecidableEq, Repr

/-- Lexicographic ordering on ballots: round takes precedence over proposer ID. -/
def BallotLt {N : ℕ} (b1 b2 : Ballot N) : Prop :=
  b1.round < b2.round ∨ (b1.round = b2.round ∧ b1.proposer < b2.proposer)

def BallotLe {N : ℕ} (b1 b2 : Ballot N) : Prop :=
  b1 = b2 ∨ BallotLt b1 b2

theorem ballotLt_irrefl {N : ℕ} (b : Ballot N) : ¬ BallotLt b b := by
  rintro (h | ⟨-, h2⟩)
  · exact Nat.lt_irrefl _ h
  · exact Nat.lt_irrefl _ h2

theorem ballotLt_trans {N : ℕ} {b1 b2 b3 : Ballot N}
    (h12 : BallotLt b1 b2) (h23 : BallotLt b2 b3) : BallotLt b1 b3 := by
  rcases h12 with (h12_rnd | ⟨h12_rnd, h12_prp⟩)
  · rcases h23 with (h23_rnd | ⟨h23_rnd, -⟩)
    · exact Or.inl (Nat.lt_trans h12_rnd h23_rnd)
    · exact Or.inl (by rw [← h23_rnd]; exact h12_rnd)
  · rcases h23 with (h23_rnd | ⟨h23_rnd, h23_prp⟩)
    · exact Or.inl (by rw [h12_rnd]; exact h23_rnd)
    · right
      refine ⟨by rw [h12_rnd, h23_rnd], ?_⟩
      exact Nat.lt_trans h12_prp h23_prp

theorem ballotLt_trichotomy {N : ℕ} (b1 b2 : Ballot N) :
    BallotLt b1 b2 ∨ b1 = b2 ∨ BallotLt b2 b1 := by
  rcases Nat.lt_trichotomy b1.round b2.round with (h1 | h_eq | h2)
  · exact Or.inl (Or.inl h1)
  · rcases Nat.lt_trichotomy b1.proposer.val b2.proposer.val with (p1 | p_eq | p2)
    · exact Or.inl (Or.inr ⟨h_eq, p1⟩)
    · right; left
      cases b1; cases b2
      congr
      exact Fin.ext p_eq
    · right; right
      exact Or.inr ⟨h_eq.symm, p2⟩
  · right; right
    exact Or.inl h2

/-- Protocol state of Paxos proposals and acceptances.
    `proposal b` is the unique value proposed at ballot `b` (if any).
    `accepted b v` is the set of acceptors who accepted proposal `(b, v)`. -/
structure PaxosState (N : ℕ) (α : Type) where
  proposal : Ballot N → Option α
  accepted : Ballot N → α → Finset (Fin N)
  accept_sound : ∀ b v a, a ∈ accepted b v → proposal b = some v

/-- A value `v` is chosen at ballot `b` if accepted by a majority quorum. -/
def IsChosenAt {N : ℕ} {α : Type} (state : PaxosState N α) (b : Ballot N) (v : α) : Prop :=
  ∃ Q : Finset (Fin N), IsMajorityQuorum N Q ∧ Q ⊆ state.accepted b v

/-- A value `v` is chosen in the Paxos instance if chosen at some ballot `b`. -/
def IsChosen {N : ℕ} {α : Type} (state : PaxosState N α) (v : α) : Prop :=
  ∃ b : Ballot N, IsChosenAt state b v

/-- **Core Paxos Proposal Invariant**:
    If value `v` is chosen at ballot `b`, then for any ballot `b' > b`,
    any proposal issued at ballot `b'` must have value `v`. -/
def SatisfiesPaxosProposalInvariant {N : ℕ} {α : Type} (state : PaxosState N α) : Prop :=
  ∀ b b' : Ballot N, ∀ v v' : α,
    IsChosenAt state b v →
    BallotLt b b' →
    state.proposal b' = some v' →
    v' = v

/-- A learner decides value `v` if it observes that `v` was chosen at some ballot. -/
def LearnerDecides {N : ℕ} {α : Type} (state : PaxosState N α) (b : Ballot N) (v : α) : Prop :=
  IsChosenAt state b v

/-- **Paxos Learner Agreement Theorem**:
    No two learners ever decide different values.
    If `v₁` is decided at ballot `b₁` and `v₂` is decided at ballot `b₂`, then `v₁ = v₂`. -/
theorem paxos_learner_agreement {N : ℕ} {α : Type}
    (state : PaxosState N α)
    (h_inv : SatisfiesPaxosProposalInvariant state)
    (b1 b2 : Ballot N) (v1 v2 : α)
    (h1 : LearnerDecides state b1 v1)
    (h2 : LearnerDecides state b2 v2) :
    v1 = v2 := by
  rcases ballotLt_trichotomy b1 b2 with (hlt12 | rfl | hlt21)
  · -- Case 1: b1 < b2
    rcases h2 with ⟨Q2, hQ2_maj, hQ2_sub⟩
    have hN : N > 0 := pos_of_majority hQ2_maj
    have h_nonempty : Q2.Nonempty := by
      by_contra h_emp
      have : Q2.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp h_emp)
      have : Q2.card > N / 2 := hQ2_maj
      omega
    rcases h_nonempty with ⟨a, ha⟩
    have ha_acc : a ∈ state.accepted b2 v2 := hQ2_sub ha
    have h_prop2 : state.proposal b2 = some v2 := state.accept_sound b2 v2 a ha_acc
    have h_eq := h_inv b1 b2 v1 v2 h1 hlt12 h_prop2
    exact h_eq.symm
  · -- Case 2: b1 = b2
    rcases h1 with ⟨Q1, hQ1_maj, hQ1_sub⟩
    rcases h2 with ⟨Q2, hQ2_maj, hQ2_sub⟩
    have hN : N > 0 := pos_of_majority hQ1_maj
    have h_inter := majority_quorum_intersection hN hQ1_maj hQ2_maj
    rcases h_inter with ⟨a, ha⟩
    have ha1 : a ∈ state.accepted b1 v1 := hQ1_sub (Finset.mem_inter.mp ha).1
    have ha2 : a ∈ state.accepted b1 v2 := hQ2_sub (Finset.mem_inter.mp ha).2
    have hp1 := state.accept_sound b1 v1 a ha1
    have hp2 := state.accept_sound b1 v2 a ha2
    rw [hp1] at hp2
    injection hp2
  · -- Case 3: b2 < b1
    rcases h1 with ⟨Q1, hQ1_maj, hQ1_sub⟩
    have hN : N > 0 := pos_of_majority hQ1_maj
    have h_nonempty : Q1.Nonempty := by
      by_contra h_emp
      have : Q1.card = 0 := Finset.card_eq_zero.mpr
        (Finset.not_nonempty_iff_eq_empty.mp h_emp)
      have : Q1.card > N / 2 := hQ1_maj
      omega
    rcases h_nonempty with ⟨a, ha⟩
    have ha_acc : a ∈ state.accepted b1 v1 := hQ1_sub ha
    have h_prop1 : state.proposal b1 = some v1 := state.accept_sound b1 v1 a ha_acc
    have h_eq := h_inv b2 b1 v2 v1 h2 hlt21 h_prop1
    exact h_eq

/-!
## 3. Multi-Paxos Replicated Log
-/

/-- A slot in the replicated state machine log. -/
abbrev Slot := ℕ

/-- In Multi-Paxos, each log slot runs an independent Paxos consensus instance. -/
structure MultiPaxosState (N : ℕ) (Cmd : Type) where
  instances : Slot → PaxosState N Cmd
  invariants : ∀ s : Slot, SatisfiesPaxosProposalInvariant (instances s)

/-- A command is committed at slot `s` if it is chosen in instance `s`. -/
def IsCommittedAt {N : ℕ} {Cmd : Type}
    (mps : MultiPaxosState N Cmd) (s : Slot) (cmd : Cmd) : Prop :=
  IsChosen (mps.instances s) cmd

/-- **Multi-Paxos Slot Safety**: At most one command can ever be committed at any slot `s`. -/
theorem multi_paxos_slot_safety {N : ℕ} {Cmd : Type}
    (mps : MultiPaxosState N Cmd) (s : Slot) (cmd1 cmd2 : Cmd)
    (h1 : IsCommittedAt mps s cmd1) (h2 : IsCommittedAt mps s cmd2) :
    cmd1 = cmd2 := by
  rcases h1 with ⟨b1, hb1⟩
  rcases h2 with ⟨b2, hb2⟩
  exact paxos_learner_agreement (mps.instances s) (mps.invariants s) b1 b2 cmd1 cmd2 hb1 hb2

/-- Sequential application of committed commands to a state machine. -/
def applyLog {State Cmd : Type} (step : State → Cmd → State) (init : State) :
    List Cmd → State :=
  List.foldl step init

/-- **Replicated State Machine Safety**:
    Replicas applying identical sequences of committed commands transition through
    the identical sequence of states. -/
theorem rsm_safety {State Cmd : Type} (step : State → Cmd → State) (init : State)
    (cmds1 cmds2 : List Cmd) (h_eq : cmds1 = cmds2) :
    applyLog step init cmds1 = applyLog step init cmds2 := by
  rw [h_eq]

/-!
## 4. Raft Consensus Safety Invariants
-/

/-- Raft election term number. -/
abbrev Term := ℕ

/-- A Raft log entry with an index, the term when received, and the command. -/
structure RaftLogEntry (Cmd : Type) where
  index : ℕ
  term : Term
  command : Cmd
deriving DecidableEq, Repr

/-- Raft state representing votes cast and granted in an election term. -/
structure RaftElectionState (N : ℕ) where
  -- The candidate each server voted for in term T (at most one per server per term)
  votes_cast : Term → Fin N → Option (Fin N)
  -- The quorum of nodes that voted for candidate C in term T
  votes_granted : Term → Fin N → Finset (Fin N)
  vote_sound : ∀ (t : Term) (c : Fin N) (voter : Fin N),
    voter ∈ votes_granted t c → votes_cast t voter = some c

/-- Candidate `c` is elected leader in term `t` if it receives votes from a majority quorum. -/
def IsElectedLeader {N : ℕ} (res : RaftElectionState N) (t : Term) (c : Fin N) : Prop :=
  IsMajorityQuorum N (res.votes_granted t c)

/-- **Raft Leader Election Safety Theorem**:
    At most one leader can be elected in any given term `t`. -/
theorem raft_leader_election_safety {N : ℕ} (hN : N > 0)
    (res : RaftElectionState N) (t : Term) (c1 c2 : Fin N)
    (h1 : IsElectedLeader res t c1) (h2 : IsElectedLeader res t c2) :
    c1 = c2 := by
  -- By majority quorum intersection, the two voting quorums must intersect
  have h_inter := majority_quorum_intersection hN h1 h2
  rcases h_inter with ⟨voter, hvoter⟩
  have hv1 : voter ∈ res.votes_granted t c1 := (Finset.mem_inter.mp hvoter).1
  have hv2 : voter ∈ res.votes_granted t c2 := (Finset.mem_inter.mp hvoter).2
  have h_vote1 : res.votes_cast t voter = some c1 := res.vote_sound t c1 voter hv1
  have h_vote2 : res.votes_cast t voter = some c2 := res.vote_sound t c2 voter hv2
  rw [h_vote1] at h_vote2
  injection h_vote2

/-- **Raft Log Matching Invariant**:
    If two server logs contain an entry with the same index and term:
    1. They store the same command at that index.
    2. Their logs are identical in all preceding entries up to that index. -/
def SatisfiesLogMatchingInvariant {Cmd : Type} (log1 log2 : List (RaftLogEntry Cmd)) : Prop :=
  ∀ e1 e2 : RaftLogEntry Cmd,
    e1 ∈ log1 → e2 ∈ log2 →
    e1.index = e2.index → e1.term = e2.term →
    e1.command = e2.command ∧
    ∀ k < e1.index,
      log1.find? (fun e => e.index = k) = log2.find? (fun e => e.index = k)

/-- Term Monotonicity: A server's term never decreases across transitions. -/
def MonotoneTerms (history : ℕ → Term) : Prop :=
  ∀ t1 t2 : ℕ, t1 ≤ t2 → history t1 ≤ history t2

end Consensus

end Amort.Distributed
