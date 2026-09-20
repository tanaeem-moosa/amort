/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Order.Basic

/-!
# Causality & Logical Clocks

This module formalizes the foundational theory of causality and logical clocks in
distributed systems following Lamport (1978), Mattern (1989), and Fidge (1988):
1. Distributed events and Lamport's happens-before relation (`→`) as an irreflexive,
   transitive strict partial order.
2. Lamport scalar clocks with local tick and message-receive update conditions, proving
   clock consistency: `e₁ → e₂ ⟹ C(e₁) < C(e₂)`.
3. Vector clocks `V : Event → (Fin N → ℕ)` with component-wise partial order, proving
   the fundamental causal isomorphism: `V(e₁) < V(e₂) ⟺ e₁ → e₂`.
-/

namespace Amort.Distributed

/-- A distributed event in a system of `N` nodes.
    `node` identifies the process where the event occurred.
    `seq` is the strictly positive local sequence number of the event on that process. -/
structure DistributedEvent (N : ℕ) where
  node : Fin N
  seq : ℕ
deriving DecidableEq, Repr

namespace Causality

/-- Direct causal precedence: either two events on the same process in local program order,
    or a message transmission where `e1` is the send event and `e2` is the receive event. -/
inductive DirectPrecedes {N : ℕ} (msgs : Set (DistributedEvent N × DistributedEvent N)) :
    DistributedEvent N → DistributedEvent N → Prop where
  | localStep {e1 e2 : DistributedEvent N} (h_node : e1.node = e2.node) (h_seq : e1.seq < e2.seq) :
      DirectPrecedes msgs e1 e2
  | msg {e1 e2 : DistributedEvent N} (h_msg : (e1, e2) ∈ msgs) :
      DirectPrecedes msgs e1 e2

/-- Lamport's happens-before relation (`→`), defined as the transitive closure
    of direct causal precedence (local program order and message delivery). -/
def HappensBefore {N : ℕ} (msgs : Set (DistributedEvent N × DistributedEvent N)) :
    DistributedEvent N → DistributedEvent N → Prop :=
  Relation.TransGen (DirectPrecedes msgs)

/-- Reflexive-transitive closure of happens-before: `e1` causally precedes or equals `e2`. -/
def HappensBeforeOrEq {N : ℕ} (msgs : Set (DistributedEvent N × DistributedEvent N))
    (e1 e2 : DistributedEvent N) : Prop :=
  e1 = e2 ∨ HappensBefore msgs e1 e2

/-- Two distinct events are concurrent if neither happens before the other. -/
def Concurrent {N : ℕ} (msgs : Set (DistributedEvent N × DistributedEvent N))
    (e1 e2 : DistributedEvent N) : Prop :=
  e1 ≠ e2 ∧ ¬ HappensBefore msgs e1 e2 ∧ ¬ HappensBefore msgs e2 e1

/-- Transitivity of the happens-before relation. -/
theorem happensBefore_trans {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    {e1 e2 e3 : DistributedEvent N}
    (h12 : HappensBefore msgs e1 e2) (h23 : HappensBefore msgs e2 e3) :
    HappensBefore msgs e1 e3 :=
  Relation.TransGen.trans h12 h23

/-- Direct precedence implies happens-before. -/
theorem happensBefore_of_direct {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    {e1 e2 : DistributedEvent N} (h : DirectPrecedes msgs e1 e2) :
    HappensBefore msgs e1 e2 :=
  Relation.TransGen.single h

/-- Local program order implies happens-before. -/
theorem happensBefore_of_local {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    {e1 e2 : DistributedEvent N} (h_node : e1.node = e2.node) (h_seq : e1.seq < e2.seq) :
    HappensBefore msgs e1 e2 :=
  happensBefore_of_direct (DirectPrecedes.localStep h_node h_seq)

/-- Message delivery implies happens-before. -/
theorem happensBefore_of_msg {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    {e1 e2 : DistributedEvent N} (h_msg : (e1, e2) ∈ msgs) :
    HappensBefore msgs e1 e2 :=
  happensBefore_of_direct (DirectPrecedes.msg h_msg)

/-- Reflexivity of `HappensBeforeOrEq`. -/
theorem happensBeforeOrEq_refl {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (e : DistributedEvent N) : HappensBeforeOrEq msgs e e :=
  Or.inl rfl

/-- Transitivity of `HappensBeforeOrEq`. -/
theorem happensBeforeOrEq_trans {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    {e1 e2 e3 : DistributedEvent N}
    (h12 : HappensBeforeOrEq msgs e1 e2) (h23 : HappensBeforeOrEq msgs e2 e3) :
    HappensBeforeOrEq msgs e1 e3 := by
  cases h12 with
  | inl h12_eq =>
    subst h12_eq
    exact h23
  | inr h12_hb =>
    cases h23 with
    | inl h23_eq =>
      subst h23_eq
      exact Or.inr h12_hb
    | inr h23_hb =>
      exact Or.inr (happensBefore_trans h12_hb h23_hb)

/-- An execution is causally valid if the happens-before relation is acyclic (irreflexive).
    Physical causality and non-zero message transmission latencies guarantee acyclicity. -/
structure CausalExecution (N : ℕ) where
  msgs : Set (DistributedEvent N × DistributedEvent N)
  acyclic : ∀ e : DistributedEvent N, ¬ HappensBefore msgs e e

/-- In a valid causal execution, happens-before is irreflexive. -/
theorem happensBefore_irrefl {N : ℕ} (exec : CausalExecution N) (e : DistributedEvent N) :
    ¬ HappensBefore exec.msgs e e :=
  exec.acyclic e

/-- In a valid causal execution, happens-before is asymmetric. -/
theorem happensBefore_asymm {N : ℕ} (exec : CausalExecution N) {e1 e2 : DistributedEvent N}
    (h12 : HappensBefore exec.msgs e1 e2) : ¬ HappensBefore exec.msgs e2 e1 := by
  intro h21
  have h_cycle := happensBefore_trans h12 h21
  exact exec.acyclic e1 h_cycle

/-- In a valid causal execution, `HappensBeforeOrEq` is antisymmetric. -/
theorem happensBeforeOrEq_antisymm {N : ℕ} (exec : CausalExecution N)
    {e1 e2 : DistributedEvent N}
    (h12 : HappensBeforeOrEq exec.msgs e1 e2)
    (h21 : HappensBeforeOrEq exec.msgs e2 e1) : e1 = e2 := by
  cases h12 with
  | inl h12_eq => exact h12_eq
  | inr h12_hb =>
    cases h21 with
    | inl h21_eq => exact h21_eq.symm
    | inr h21_hb =>
      exfalso
      exact exec.acyclic e1 (happensBefore_trans h12_hb h21_hb)

/-!
### Lamport Scalar Logical Clocks
-/

/-- A Lamport scalar logical clock assigning a natural number timestamp to each event.
    Satisfies Lamport's clock conditions:
    1. Local tick: strictly increases along local process sequences.
    2. Message condition: receive timestamp strictly exceeds send timestamp. -/
structure LamportClock (N : ℕ) (msgs : Set (DistributedEvent N × DistributedEvent N)) where
  clock : DistributedEvent N → ℕ
  local_tick : ∀ e1 e2, e1.node = e2.node → e1.seq < e2.seq → clock e1 < clock e2
  msg_recv : ∀ e1 e2, (e1, e2) ∈ msgs → clock e1 < clock e2

/-- Direct precedence strictly increases Lamport scalar clock timestamps. -/
theorem lamport_clock_of_direct {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (lc : LamportClock N msgs) {e1 e2 : DistributedEvent N}
    (h : DirectPrecedes msgs e1 e2) : lc.clock e1 < lc.clock e2 := by
  cases h with
  | localStep h_node h_seq => exact lc.local_tick _ _ h_node h_seq
  | msg h_msg => exact lc.msg_recv _ _ h_msg

/-- **Lamport Clock Consistency Theorem (Clock Condition)**:
    If event `e₁` happens before `e₂`, then `C(e₁) < C(e₂)`. -/
theorem lamport_clock_consistency {N : ℕ} {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (lc : LamportClock N msgs) {e1 e2 : DistributedEvent N}
    (h : HappensBefore msgs e1 e2) : lc.clock e1 < lc.clock e2 := by
  induction h with
  | single h_dir => exact lamport_clock_of_direct lc h_dir
  | tail _ h_tail ih =>
    have h_step := lamport_clock_of_direct lc h_tail
    exact Nat.lt_trans ih h_step

/-- Weak clock consistency for `HappensBeforeOrEq`: `e₁ ≤ e₂ ⟹ C(e₁) ≤ C(e₂)`. -/
theorem lamport_clock_weak_consistency {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (lc : LamportClock N msgs) {e1 e2 : DistributedEvent N}
    (h : HappensBeforeOrEq msgs e1 e2) : lc.clock e1 ≤ lc.clock e2 := by
  cases h with
  | inl h_eq => subst h_eq; exact Nat.le_refl _
  | inr h_hb => exact Nat.le_of_lt (lamport_clock_consistency lc h_hb)

/-- Contrapositive: If `C(e₁) ≥ C(e₂)`, then `e₁` cannot happen before `e₂`. -/
theorem not_happensBefore_of_clock_ge {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (lc : LamportClock N msgs) {e1 e2 : DistributedEvent N}
    (h : lc.clock e2 ≤ lc.clock e1) : ¬ HappensBefore msgs e1 e2 := by
  intro h_hb
  have h_lt := lamport_clock_consistency lc h_hb
  exact Nat.lt_irrefl (lc.clock e1) (Nat.lt_of_lt_of_le h_lt h)

/-!
### Vector Clocks & Causal Isomorphism

In contrast to scalar clocks, Vector Clocks characterize causality bidirectionally:
`V(e₁) < V(e₂) ⟺ e₁ → e₂`.
-/

/-- A vector timestamp for a system of `N` processes. -/
def VectorClock (N : ℕ) := Fin N → ℕ

/-- Component-wise partial order on vector timestamps:
    `v₁ ≤ v₂` iff `∀ i, v₁(i) ≤ v₂(i)`. -/
def VCLe {N : ℕ} (v1 v2 : VectorClock N) : Prop :=
  ∀ i : Fin N, v1 i ≤ v2 i

/-- Strict component-wise partial order on vector timestamps:
    `v₁ < v₂` iff `v₁ ≤ v₂` and `v₁ ≠ v₂`. -/
def VCLt {N : ℕ} (v1 v2 : VectorClock N) : Prop :=
  VCLe v1 v2 ∧ v1 ≠ v2

theorem vcle_refl {N : ℕ} (v : VectorClock N) : VCLe v v :=
  fun _ => Nat.le_refl _

theorem vcle_trans {N : ℕ} {v1 v2 v3 : VectorClock N}
    (h12 : VCLe v1 v2) (h23 : VCLe v2 v3) : VCLe v1 v3 :=
  fun i => Nat.le_trans (h12 i) (h23 i)

theorem vcle_antisymm {N : ℕ} {v1 v2 : VectorClock N}
    (h12 : VCLe v1 v2) (h21 : VCLe v2 v1) : v1 = v2 := by
  funext i
  exact Nat.le_antisymm (h12 i) (h21 i)

theorem vclt_irrefl {N : ℕ} (v : VectorClock N) : ¬ VCLt v v :=
  fun h => h.2 rfl

theorem vclt_trans {N : ℕ} {v1 v2 v3 : VectorClock N}
    (h12 : VCLt v1 v2) (h23 : VCLt v2 v3) : VCLt v1 v3 := by
  refine ⟨vcle_trans h12.1 h23.1, ?_⟩
  rintro rfl
  have h_eq := vcle_antisymm h12.1 h23.1
  exact h12.2 h_eq

/-- Characterization: for vectors `v₁, v₂`, `v₁ < v₂` is equivalent to
    `v₁ ≤ v₂` and `∃ i, v₁(i) < v₂(i)`. -/
theorem vclt_iff_le_and_exists_lt {N : ℕ} {v1 v2 : VectorClock N} :
    VCLt v1 v2 ↔ VCLe v1 v2 ∧ ∃ i : Fin N, v1 i < v2 i := by
  constructor
  · rintro ⟨hle, hne⟩
    refine ⟨hle, ?_⟩
    by_contra h_none
    have heq : v1 = v2 := by
      funext i
      have h_not_lt : ¬ v1 i < v2 i := fun h => h_none ⟨i, h⟩
      exact Nat.le_antisymm (hle i) (Nat.le_of_not_lt h_not_lt)
    exact hne heq
  · rintro ⟨hle, ⟨i, hlt⟩⟩
    refine ⟨hle, ?_⟩
    rintro rfl
    exact Nat.lt_irrefl (v1 i) hlt

/-- A Vector Clock assignment system for an execution with messages `msgs`.
    Properties:
    1. `acyclic`: The execution has no causal cycles.
    2. `local_component`: The `node` component of `vc e` is the sequence number `e.seq`.
    3. `causal_sound`: An event `e₁` causally precedes or equals `e₂` if and only if
       the sequence number of `e₁` is at most the recorded component of `vc e₂` at `e₁.node`.
    4. `monotone_hb`: Happens-before implies component-wise vector domination. -/
structure VectorClockSystem (N : ℕ) (msgs : Set (DistributedEvent N × DistributedEvent N)) where
  vc : DistributedEvent N → VectorClock N
  acyclic : ∀ e : DistributedEvent N, ¬ HappensBefore msgs e e
  local_component : ∀ e : DistributedEvent N, vc e e.node = e.seq
  causal_sound : ∀ e1 e2 : DistributedEvent N,
    HappensBeforeOrEq msgs e1 e2 ↔ e1.seq ≤ vc e2 e1.node
  monotone_hb : ∀ e1 e2 : DistributedEvent N,
    HappensBefore msgs e1 e2 → VCLe (vc e1) (vc e2)

/-- Component test for causal precedence:
    `e₁ ≤ e₂` iff `V(e₁)(e₁.node) ≤ V(e₂)(e₁.node)`. -/
theorem vc_component_le_iff_hb_or_eq {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    vcs.vc e1 e1.node ≤ vcs.vc e2 e1.node ↔ HappensBeforeOrEq msgs e1 e2 := by
  rw [vcs.local_component e1]
  exact (vcs.causal_sound e1 e2).symm

/-- Component test for strict happens-before:
    `e₁ → e₂` iff `V(e₁)(e₁.node) ≤ V(e₂)(e₁.node)` and `e₁ ≠ e₂`. -/
theorem vc_component_le_and_ne_iff_hb {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    (vcs.vc e1 e1.node ≤ vcs.vc e2 e1.node ∧ e1 ≠ e2) ↔ HappensBefore msgs e1 e2 := by
  rw [vc_component_le_iff_hb_or_eq]
  constructor
  · rintro ⟨h_or, h_ne⟩
    cases h_or with
    | inl h_eq => exfalso; exact h_ne h_eq
    | inr h_hb => exact h_hb
  · intro h_hb
    refine ⟨Or.inr h_hb, ?_⟩
    rintro rfl
    exact vcs.acyclic e1 h_hb

/-- **Vector Clock Causal Domination Theorem**:
    `V(e₁) ≤ V(e₂) ⟺ e₁ ≤ e₂`. -/
theorem vc_le_iff_hb_or_eq {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    VCLe (vcs.vc e1) (vcs.vc e2) ↔ HappensBeforeOrEq msgs e1 e2 := by
  constructor
  · intro h_le
    have h_comp : vcs.vc e1 e1.node ≤ vcs.vc e2 e1.node := h_le e1.node
    rwa [vc_component_le_iff_hb_or_eq] at h_comp
  · rintro (rfl | h_hb)
    · exact vcle_refl _
    · exact vcs.monotone_hb e1 e2 h_hb

/-- **Fundamental Vector Clock Causal Isomorphism Theorem**:
    `V(e₁) < V(e₂) ⟺ e₁ → e₂`. -/
theorem vc_lt_iff_happensBefore {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    VCLt (vcs.vc e1) (vcs.vc e2) ↔ HappensBefore msgs e1 e2 := by
  constructor
  · rintro ⟨h_le, h_ne⟩
    rw [vc_le_iff_hb_or_eq] at h_le
    cases h_le with
    | inl h_eq =>
      subst h_eq
      exfalso
      exact h_ne rfl
    | inr h_hb => exact h_hb
  · intro h_hb
    have h_le : VCLe (vcs.vc e1) (vcs.vc e2) := vcs.monotone_hb e1 e2 h_hb
    refine ⟨h_le, ?_⟩
    intro h_eq
    have h_comp : vcs.vc e2 e2.node ≤ vcs.vc e1 e2.node := by
      rw [h_eq]
    rw [vc_component_le_iff_hb_or_eq] at h_comp
    cases h_comp with
    | inl h_eq2 =>
      have : e1 = e2 := h_eq2.symm
      subst this
      exact vcs.acyclic e1 h_hb
    | inr h_hb2 =>
      exact vcs.acyclic e1 (happensBefore_trans h_hb h_hb2)

/-- Vector clocks characterize concurrency:
    Two distinct events `e₁` and `e₂` are concurrent iff their vector timestamps
    are incomparable. -/
theorem concurrent_iff_incomparable {N : ℕ}
    {msgs : Set (DistributedEvent N × DistributedEvent N)}
    (vcs : VectorClockSystem N msgs) (e1 e2 : DistributedEvent N) :
    Concurrent msgs e1 e2 ↔ ¬ VCLe (vcs.vc e1) (vcs.vc e2) ∧ ¬ VCLe (vcs.vc e2) (vcs.vc e1) := by
  simp only [Concurrent, vc_le_iff_hb_or_eq, HappensBeforeOrEq]
  constructor
  · rintro ⟨hne, h1, h2⟩
    refine ⟨?_, ?_⟩
    · rintro (rfl | h_hb)
      · exact hne rfl
      · exact h1 h_hb
    · rintro (h_eq | h_hb)
      · exact hne h_eq.symm
      · exact h2 h_hb
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_, ?_⟩
    · rintro rfl
      exact h1 (Or.inl rfl)
    · intro h_hb
      exact h1 (Or.inr h_hb)
    · intro h_hb
      exact h2 (Or.inr h_hb)

end Causality

end Amort.Distributed
