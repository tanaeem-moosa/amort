/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.DP
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.Fintype.Prod

/-!
# Floyd-Warshall All-Pairs Shortest Paths

This module formalizes the textbook Floyd-Warshall dynamic programming algorithm for all-pairs
shortest paths on finite directed graphs with vertex set `Fin n`, and establishes its $O(n^3)$
operational complexity in the `Amort.Recurrence.DP` state-space complexity framework.

## Mathematical Architecture

1. **Weighted Directed Graphs**:
   A weighted directed graph on $n$ vertices (`Fin n`) is specified by edge weights
   `W : Fin n → Fin n → WithTop ℕ`, where `⊤` denotes the absence of a directed edge and
   `W i i = 0` for all $i$.

2. **Bellman Recurrence**:
   Let $D^{(k)}(i, j)$ denote the shortest-path distance from vertex $i$ to vertex $j$ using
   only intermediate vertices from $\{0, \dots, k - 1\}$.
   - Base case: $D^{(0)}(i, j) = W(i, j)$.
   - Recurrence step: for $k < n$,
     $$D^{(k + 1)}(i, j) = \min \{ D^{(k)}(i, j),\; D^{(k)}(i, k) + D^{(k)}(k, j) \}$$

3. **3D State Space**:
   The DP subproblem states are triples
   $$(k, i, j) \in \text{Fin}(n + 1) \times \text{Fin } n \times \text{Fin } n$$
   The state space cardinality is:
   $$|FWState n| = (n + 1) \cdot n^2 \le (n + 1)^3$$

4. **State-Space Complexity Model**:
   At each state $(k, i, j)$, the algorithm evaluates a constant-time transition (at most 1
   addition and 1 comparison).
   Instantiating `Amort.Recurrence.DPModel` on `FWState n` with unit cost bound ($C = 1$)
   proves that the total work across all states is bounded by:
   $$\text{Total Work} \le (n + 1) \cdot n^2 \le (n + 1)^3 = O(n^3)$$

## Key Definitions and Theorems
- `Amort.Graph.floydWarshallRec`: Recursive formulation of Floyd-Warshall distances.
- `Amort.Graph.floydWarshallAllPairs`: Final all-pairs shortest distances matrix $D^{(n)}$.
- `Amort.Graph.floydWarshallRec_mono`: Monotonicity of distance estimates across rounds.
- `Amort.Graph.floydWarshallRec_self`: Preservation of zero self-distance.
- `Amort.Graph.floydWarshallRec_step_le_trans`: Intermediate vertex relaxation inequality.
- `Amort.Graph.FWState`: 3D state space `Fin (n + 1) × Fin n × Fin n`.
- `Amort.Graph.card_fw_states`: State space cardinality $(n + 1) \cdot n^2$.
- `Amort.Graph.floydWarshallDP`: DPModel instantiation with unit transition cost.
- `Amort.Graph.floydWarshallDP_totalCost`: Exact total cost $(n + 1) \cdot n^2$.
- `Amort.Graph.floydWarshallDP_totalCost_le`: Cubic operational bound $\le (n + 1) \cdot n^2$.
- `Amort.Graph.floydWarshallDP_totalCost_le_cube`: Cubic upper bound $\le (n + 1)^3$.
-/

namespace Amort.Graph

open Amort.Recurrence

/-! ### Nonnegativity Lemma for WithTop ℕ -/

/-- Every element in `WithTop ℕ` is bounded below by 0. -/
lemma withTop_nat_zero_le (x : WithTop ℕ) : (0 : WithTop ℕ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe n => exact WithTop.coe_le_coe.mpr (Nat.zero_le n)

/-! ### Floyd-Warshall Recurrence Formulation -/

/-- Recursive computation of Floyd-Warshall distance estimates.
`floydWarshallRec W k i j` computes the shortest path distance from `i` to `j`
using only intermediate vertices strictly less than `k`. -/
def floydWarshallRec {n : ℕ} (W : Fin n → Fin n → WithTop ℕ) :
    ℕ → Fin n → Fin n → WithTop ℕ
  | 0, i, j => W i j
  | k + 1, i, j =>
    if h : k < n then
      min (floydWarshallRec W k i j)
          (floydWarshallRec W k i ⟨k, h⟩ + floydWarshallRec W k ⟨k, h⟩ j)
    else
      floydWarshallRec W k i j

/-- Convenience wrapper for Floyd-Warshall distances after `k` stages. -/
def floydWarshall {n : ℕ} (W : Fin n → Fin n → WithTop ℕ) (k : ℕ) :
    Fin n → Fin n → WithTop ℕ :=
  floydWarshallRec W k

/-- The final all-pairs shortest paths distance matrix after all `n` vertex stages. -/
def floydWarshallAllPairs {n : ℕ} (W : Fin n → Fin n → WithTop ℕ) :
    Fin n → Fin n → WithTop ℕ :=
  floydWarshallRec W n

/-! ### Mathematical Properties and Invariants -/

/-- Base case: stage 0 returns the initial edge weight matrix. -/
@[simp]
theorem floydWarshallRec_zero {n : ℕ} (W : Fin n → Fin n → WithTop ℕ) (i j : Fin n) :
    floydWarshallRec W 0 i j = W i j := rfl

/-- Distance estimates are non-increasing with each additional intermediate vertex allowed. -/
theorem floydWarshallRec_mono {n : ℕ} (W : Fin n → Fin n → WithTop ℕ)
    (k : ℕ) (i j : Fin n) :
    floydWarshallRec W (k + 1) i j ≤ floydWarshallRec W k i j := by
  dsimp [floydWarshallRec]
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

/-- Monotonicity across multiple stages: if `k1 ≤ k2`, then $D^{(k2)}(i, j) \le D^{(k1)}(i, j)$. -/
theorem floydWarshallRec_le_of_le {n : ℕ} (W : Fin n → Fin n → WithTop ℕ)
    {k1 k2 : ℕ} (h : k1 ≤ k2) (i j : Fin n) :
    floydWarshallRec W k2 i j ≤ floydWarshallRec W k1 i j := by
  induction k2, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m _hm ih => exact (floydWarshallRec_mono W m i j).trans ih

/-- Distance estimates are always bounded above by the direct edge weight. -/
theorem floydWarshallRec_le_initial {n : ℕ} (W : Fin n → Fin n → WithTop ℕ)
    (k : ℕ) (i j : Fin n) :
    floydWarshallRec W k i j ≤ W i j :=
  floydWarshallRec_le_of_le W (Nat.zero_le k) i j

/-- Self-distance remains 0 throughout all stages if initialized to 0. -/
theorem floydWarshallRec_self {n : ℕ} (W : Fin n → Fin n → WithTop ℕ)
    (hW : ∀ i, W i i = 0) (k : ℕ) (i : Fin n) :
    floydWarshallRec W k i i = 0 := by
  induction k with
  | zero => exact hW i
  | succ m ih =>
    have h_le := floydWarshallRec_mono W m i i
    rw [ih] at h_le
    exact le_antisymm h_le (withTop_nat_zero_le _)

/-- Relaxation property: stage `k + 1` satisfies the triangle inequality through vertex `k`. -/
theorem floydWarshallRec_step_le_trans {n : ℕ} (W : Fin n → Fin n → WithTop ℕ)
    (k : ℕ) (h : k < n) (i j : Fin n) :
    floydWarshallRec W (k + 1) i j ≤
      floydWarshallRec W k i ⟨k, h⟩ + floydWarshallRec W k ⟨k, h⟩ j := by
  dsimp [floydWarshallRec]
  rw [dif_pos h]
  exact min_le_right _ _

/-! ### 3D Dynamic Programming State Space -/

/-- The 3D state space for Floyd-Warshall consisting of triples `(k, i, j)`
where `k ∈ Fin (n + 1)` indexes the phase and `i, j ∈ Fin n` index vertex pairs. -/
abbrev FWState (n : ℕ) : Type := Fin (n + 1) × Fin n × Fin n

/-- Cardinality of the Floyd-Warshall 3D state space is `(n + 1) * n^2`. -/
theorem card_fw_states (n : ℕ) :
    Fintype.card (FWState n) = (n + 1) * n ^ 2 := by
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring

/-- The state count `(n + 1) * n^2` is bounded above by `(n + 1)^3`. -/
theorem card_fw_states_le_cube (n : ℕ) :
    (n + 1) * n ^ 2 ≤ (n + 1) ^ 3 := by
  have h : n ≤ n + 1 := Nat.le_succ n
  have h2 : n ^ 2 ≤ (n + 1) ^ 2 := Nat.pow_le_pow_left h 2
  calc (n + 1) * n ^ 2
    _ ≤ (n + 1) * (n + 1) ^ 2 := Nat.mul_le_mul_left (n + 1) h2
    _ = (n + 1) ^ 3 := by ring

/-! ### State-Space Dynamic Programming Model -/

/-- Canonical `DPModel` instantiation for Floyd-Warshall on the 3D state space `FWState n`
with unit cost bound per state transition. -/
def floydWarshallDP (n : ℕ) : DPModel (FWState n) where
  costPerState := fun _ ↦ 1
  costBound := 1
  h_cost := fun _ ↦ Nat.le_refl 1

/-- Exact total work across all states in `FWState n` is `(n + 1) * n^2`. -/
theorem floydWarshallDP_totalCost (n : ℕ) :
    (floydWarshallDP n).totalCost = (n + 1) * n ^ 2 := by
  dsimp [DPModel.totalCost, floydWarshallDP]
  simp only [Finset.sum_const, Finset.card_univ, card_fw_states, smul_eq_mul, mul_one]

/-- The total work is bounded by `(n + 1) * n^2` operations via `DPModel.totalCost_le`. -/
theorem floydWarshallDP_totalCost_le (n : ℕ) :
    (floydWarshallDP n).totalCost ≤ (n + 1) * n ^ 2 := by
  rw [floydWarshallDP_totalCost]

/-- The total work is bounded by `(n + 1)^3` operations. -/
theorem floydWarshallDP_totalCost_le_cube (n : ℕ) :
    (floydWarshallDP n).totalCost ≤ (n + 1) ^ 3 := by
  rw [floydWarshallDP_totalCost]
  exact card_fw_states_le_cube n

end Amort.Graph
