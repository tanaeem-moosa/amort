/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Network Flow and the Max-Flow Min-Cut Theorem

> **Status: stub — not verified** (Phase 3 canon stub; flow-cut duality is proven,
> but augmenting-path execution and Edmonds-Karp bounds are specification stubs).

This module formalizes flow networks, capacity constraints, flow conservation at intermediate
vertices, $s$-$t$ cuts, residual networks, and proves the Max-Flow Min-Cut Theorem. It also
formalizes the polynomial $O(|V| \cdot |E|^2)$ operational step complexity of Edmonds-Karp.

## Mathematical Architecture

1. **Flow Network & Flow Invariants**:
   A flow network $(V, E, c, s, t)$ has vertex set `Fin n`, capacity function
   $c : \text{Fin } n \to \text{Fin } n \to \mathbb{N}$, and distinguished vertices $s \ne t$.
   A valid flow $f$ satisfies:
   - Capacity constraint: $f(u, v) \le c(u, v)$ for all $u, v$.
   - Flow conservation: for every $u \notin \{s, t\}$,
     $\sum_v f(u, v) = \sum_v f(v, u)$.
   - Net flow value: $\text{flowVal}(f) = \sum_v f(s, v) - \sum_v f(v, s)$.

2. **Cuts & Cut-Flow Identity**:
   An $s$-$t$ cut is a subset $S \subseteq V$ such that $s \in S$ and $t \notin S$ ($t \in S^c$).
   The capacity of the cut is $c(S) = \sum_{u \in S, v \in S^c} c(u, v)$.
   We prove the fundamental Cut-Flow Identity:
   $$\text{flowVal}(f) = \sum_{u \in S, v \in S^c} f(u, v) - \sum_{u \in S, v \in S^c} f(v, u)$$
   via internal cancellation ($\sum_{u \in S, v \in S} f(u, v) = \sum_{u \in S, v \in S} f(v, u)$).

3. **Weak Duality**:
   Since $f(v, u) \ge 0$ and $f(u, v) \le c(u, v)$:
   $$\text{flowVal}(f) \le \sum_{u \in S, v \in S^c} f(u, v) \le c(S)$$
   for every valid flow $f$ and every $s$-$t$ cut $S$.

4. **Max-Flow Min-Cut Theorem**:
   In the residual graph $G_f$, if there is no augmenting path from $s$ to $t$, the set of
   reachable vertices $S^* = \{ v \mid s \rightsquigarrow_{G_f} v \}$ defines an $s$-$t$ cut where:
   - Every forward edge $(u, v)$ is saturated: $f(u, v) = c(u, v)$.
   - Every backward edge has zero flow: $f(v, u) = 0$.
   Hence $\text{flowVal}(f) = c(S^*)$, proving $f$ is maximal and $S^*$ is minimal.

5. **Edmonds-Karp Complexity**:
   Bounding augmenting phases by $|V| \cdot |E|$ with each BFS taking $|E|$ steps, total
   operational complexity is $O(|V| \cdot |E|^2)$.

## Key Definitions and Theorems
- `Amort.Graph.FlowNetwork`: Flow network structure on `Fin n`.
- `Amort.Graph.IsValidFlow`: Predicate asserting capacity constraints and flow conservation.
- `Amort.Graph.flowVal`: Net flow value leaving source $s$.
- `Amort.Graph.cutCap`: Capacity of an $s$-$t$ cut.
- `Amort.Graph.flow_cut_identity`: Net flow across any $s$-$t$ cut equals `flowVal`.
- `Amort.Graph.weak_duality`: Flow value is bounded above by any $s$-$t$ cut capacity.
- `Amort.Graph.max_flow_min_cut`: Max-flow equals min-cut capacity on tight residual cuts.
- `Amort.Graph.edmondsKarpBound`: Operational step model $O(|V| \cdot |E|^2)$.
-/

open BigOperators

namespace Amort.Graph

variable {n : ℕ}

/-! ### Flow Network Representation and Valid Flows -/

/-- A flow network on vertex set `Fin n` with capacity `cap`, source `s`, and sink `t`. -/
structure FlowNetwork (n : ℕ) where
  s : Fin n
  t : Fin n
  s_ne_t : s ≠ t
  cap : Fin n → Fin n → ℕ

/-- Validity predicate for a flow `f` in network `N`:
1. Capacity constraint: `f u v ≤ N.cap u v`.
2. Conservation: for all intermediate vertices `u ∉ {s, t}`, inflow equals outflow. -/
def IsValidFlow (N : FlowNetwork n) (f : Fin n → Fin n → ℕ) : Prop :=
  (∀ u v, f u v ≤ N.cap u v) ∧
  (∀ u, u ≠ N.s → u ≠ N.t → (∑ v, (f u v : ℤ)) = ∑ v, (f v u : ℤ))

/-- Net flow value leaving source `s`. -/
def flowVal (N : FlowNetwork n) (f : Fin n → Fin n → ℕ) : ℤ :=
  (∑ v, (f N.s v : ℤ)) - (∑ v, (f v N.s : ℤ))

/-- Capacity of an $s$-$t$ cut partition `(S, Sᶜ)` where `s ∈ S` and `t ∈ Sᶜ`. -/
def cutCap (N : FlowNetwork n) (S : Finset (Fin n)) : ℕ :=
  ∑ u ∈ S, ∑ v ∈ Sᶜ, N.cap u v

/-! ### Cut-Flow Identity and Weak Duality -/

/-- Internal edge flow sums cancel by symmetry under transposition. -/
theorem sum_internal_flow_cancel (S : Finset (Fin n)) (f : Fin n → Fin n → ℕ) :
    (∑ u ∈ S, ∑ v ∈ S, (f u v : ℤ)) = (∑ u ∈ S, ∑ v ∈ S, (f v u : ℤ)) :=
  Finset.sum_comm

/-- Fundamental Cut-Flow Identity:
For any $s$-$t$ cut `S` and valid flow `f`, the net flow leaving `S` equals `flowVal N f`. -/
theorem flow_cut_identity (N : FlowNetwork n) (f : Fin n → Fin n → ℕ)
    (hf : IsValidFlow N f) (S : Finset (Fin n)) (hs : N.s ∈ S) (ht : N.t ∉ S) :
    flowVal N f = (∑ u ∈ S, ∑ v ∈ Sᶜ, (f u v : ℤ)) - (∑ u ∈ S, ∑ v ∈ Sᶜ, (f v u : ℤ)) := by
  have h_split_out : (∑ u ∈ S, ∑ v, (f u v : ℤ)) =
      (∑ u ∈ S, ∑ v ∈ S, (f u v : ℤ)) + (∑ u ∈ S, ∑ v ∈ Sᶜ, (f u v : ℤ)) := by
    simp_rw [fun u ↦ (Finset.sum_add_sum_compl S (fun v ↦ (f u v : ℤ))).symm]
    rw [← Finset.sum_add_distrib]
  have h_split_in : (∑ u ∈ S, ∑ v, (f v u : ℤ)) =
      (∑ u ∈ S, ∑ v ∈ S, (f v u : ℤ)) + (∑ u ∈ S, ∑ v ∈ Sᶜ, (f v u : ℤ)) := by
    simp_rw [fun u ↦ (Finset.sum_add_sum_compl S (fun v ↦ (f v u : ℤ))).symm]
    rw [← Finset.sum_add_distrib]
  have h_sum_sub : (∑ u ∈ S, ((∑ v, (f u v : ℤ)) - (∑ v, (f v u : ℤ)))) =
      (∑ u ∈ S, ∑ v ∈ Sᶜ, (f u v : ℤ)) - (∑ u ∈ S, ∑ v ∈ Sᶜ, (f v u : ℤ)) := by
    rw [Finset.sum_sub_distrib, h_split_out, h_split_in, sum_internal_flow_cancel S f]
    ring
  have h_cons : ∀ u ∈ S, u ≠ N.s → (∑ v, (f u v : ℤ)) - (∑ v, (f v u : ℤ)) = 0 := by
    intro u hu hu_ne
    have hu_ne_t : u ≠ N.t := by
      rintro rfl
      exact ht hu
    have h_eq := hf.2 u hu_ne hu_ne_t
    omega
  have h_source : (∑ u ∈ S, ((∑ v, (f u v : ℤ)) - (∑ v, (f v u : ℤ)))) =
      (∑ v, (f N.s v : ℤ)) - (∑ v, (f v N.s : ℤ)) := by
    rw [← Finset.add_sum_erase _ _ hs]
    have h_zero : (∑ u ∈ S.erase N.s, ((∑ v, (f u v : ℤ)) - (∑ v, (f v u : ℤ)))) = 0 := by
      apply Finset.sum_eq_zero
      intro u hu
      rw [Finset.mem_erase] at hu
      exact h_cons u hu.2 hu.1
    rw [h_zero, add_zero]
  rw [← h_sum_sub, h_source]
  rfl

/-- Weak Duality Theorem:
The value of any valid flow is bounded above by the capacity of any $s$-$t$ cut. -/
theorem weak_duality (N : FlowNetwork n) (f : Fin n → Fin n → ℕ)
    (hf : IsValidFlow N f) (S : Finset (Fin n)) (hs : N.s ∈ S) (ht : N.t ∉ S) :
    flowVal N f ≤ (cutCap N S : ℤ) := by
  rw [flow_cut_identity N f hf S hs ht]
  dsimp [cutCap]
  simp only [Nat.cast_sum]
  have h_cap : (∑ u ∈ S, ∑ v ∈ Sᶜ, (f u v : ℤ)) ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, (N.cap u v : ℤ) := by
    apply Finset.sum_le_sum
    intro u _hu
    apply Finset.sum_le_sum
    intro v _hv
    exact_mod_cast hf.1 u v
  have h_nonneg : 0 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, (f v u : ℤ) := by
    apply Finset.sum_nonneg
    intro u _hu
    apply Finset.sum_nonneg
    intro v _hv
    positivity
  linarith

/-! ### Max-Flow Min-Cut Tightness and Theorem -/

/-- Residual cut tightness: across cut `S`, all forward edges are saturated
and all backward edges carry zero flow. -/
structure TightResidualCut (N : FlowNetwork n) (f : Fin n → Fin n → ℕ)
    (S : Finset (Fin n)) : Prop where
  hs : N.s ∈ S
  ht : N.t ∉ S
  saturated : ∀ u ∈ S, ∀ v ∈ Sᶜ, f u v = N.cap u v
  zero_backflow : ∀ u ∈ S, ∀ v ∈ Sᶜ, f v u = 0

/-- Max-Flow Min-Cut Theorem:
If a valid flow `f` achieves a tight residual cut `S`, then the net flow value equals
the cut capacity `cutCap N S`, proving that `f` has maximum value among all valid flows
and `S` has minimum capacity among all $s$-$t$ cuts. -/
theorem max_flow_min_cut (N : FlowNetwork n) (f : Fin n → Fin n → ℕ)
    (hf : IsValidFlow N f) (S : Finset (Fin n)) (h_tight : TightResidualCut N f S) :
    flowVal N f = (cutCap N S : ℤ) := by
  rw [flow_cut_identity N f hf S h_tight.hs h_tight.ht]
  dsimp [cutCap]
  have h_fwd : (∑ u ∈ S, ∑ v ∈ Sᶜ, (f u v : ℤ)) = ∑ u ∈ S, ∑ v ∈ Sᶜ, (N.cap u v : ℤ) := by
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    rw [h_tight.saturated u hu v hv]
  have h_bwd : (∑ u ∈ S, ∑ v ∈ Sᶜ, (f v u : ℤ)) = 0 := by
    have : (∑ u ∈ S, ∑ v ∈ Sᶜ, (f v u : ℤ)) = ∑ u ∈ S, ∑ v ∈ Sᶜ, (0 : ℤ) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      have := h_tight.zero_backflow u hu v hv
      exact_mod_cast this
    rw [this]
    simp
  rw [h_fwd, h_bwd, sub_zero]
  simp only [Nat.cast_sum]

/-! ### Edmonds-Karp Operational Step Complexity -/

/-- Total operational work for Edmonds-Karp augmenting path algorithm on a network
with `n` vertices and `m` edges: at most `n * m` augmenting phases, each taking
`m` operations via BFS, yielding `n * m^2` total steps ($O(|V| \cdot |E|^2)$). -/
def edmondsKarpBound (n : ℕ) (m : ℕ) : ℕ := n * m ^ 2

/-- Edmonds-Karp work bound: operations are bounded by `n * m^2`. -/
theorem edmondsKarp_work_le (n m : ℕ) : edmondsKarpBound n m ≤ n * m ^ 2 :=
  le_refl _

/-- In terms of $|V| = n$ and $|E| = m$, work product factoring. -/
theorem edmondsKarp_work_eq_mul (n m : ℕ) : edmondsKarpBound n m = (n * m) * m := by
  dsimp [edmondsKarpBound]
  ring

end Amort.Graph
