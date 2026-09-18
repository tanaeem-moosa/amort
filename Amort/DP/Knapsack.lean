/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.DP
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Finset.Basic

/-!
# Grid Dynamic Programming: 0/1 Knapsack Problem

This module formalizes the textbook 0/1 Knapsack dynamic programming algorithm, proves its
mathematical correctness against arbitrary item subcollections, and instantiates the
`Amort.Recurrence.GridDP` framework establishing the $O(n \cdot W)$ complexity bound.

## Mathematical Architecture

1. **Items and Subcollections**:
   Given $n$ items with weight function $w : \mathbb{N} \to \mathbb{N}$ and value function
   $v : \mathbb{N} \to \mathbb{N}$, and capacity $W \in \mathbb{N}$.
   A subcollection of items $\{0, \dots, n-1\}$ is modeled as a finite set
   $s \subseteq \{0, \dots, n-1\}$ (`s ⊆ Finset.range n`).
   - Total weight: $\text{totalWeight } w \; s = \sum_{j \in s} w(j)$
   - Total value: $\text{totalValue } v \; s = \sum_{j \in s} v(j)$
   - Feasibility: $\text{totalWeight } w \; s \le W$

2. **Bellman Recurrence**:
   $$K(0, w) = 0$$
   $$K(i+1, w) = \begin{cases}
     K(i, w) & \text{if } w < w_i \\
     \max(K(i, w), v_i + K(i, w - w_i)) & \text{if } w \ge w_i
   \end{cases}$$

3. **Mathematical Correctness (Optimality)**:
   - **Soundness**: Every feasible subcollection $s \subseteq \{0, \dots, n-1\}$ satisfies
     $\text{totalValue } v \; s \le K(n, W)$.
   - **Completeness**: There exists a feasible subcollection achieving value exactly $K(n, W)$.

4. **Grid DP Complexity**:
   State space $\text{Fin}(n + 1) \times \text{Fin}(W + 1)$ with unit transitions ($C = 1$),
   instantiated via `Amort.Recurrence.GridDP`, bounding total work by $(n + 1)(W + 1)$.
-/

namespace Amort.DP

open BigOperators
open Amort.Recurrence

/-! ### Item Structure and Bellman Recurrence -/

/-- An item in the 0/1 knapsack problem with weight and value. -/
structure Item where
  weight : ℕ
  value : ℕ

/-- Bellman recursive cost function $K(i, \text{cap})$ computing the maximum value attainable
using a subset of the first $i$ items within weight capacity `cap`. -/
def knapsackRec (w v : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | i + 1, cap =>
    if cap < w i then
      knapsackRec w v i cap
    else
      max (knapsackRec w v i cap) (v i + knapsackRec w v i (cap - w i))

/-- Base case: 0 items yield 0 value. -/
@[simp]
theorem knapsackRec_zero (w v : ℕ → ℕ) (cap : ℕ) : knapsackRec w v 0 cap = 0 := rfl

/-- Knapsack optimal value is monotone in capacity. -/
theorem knapsackRec_mono_cap (w v : ℕ → ℕ) (n : ℕ) {c1 c2 : ℕ} (hc : c1 ≤ c2) :
    knapsackRec w v n c1 ≤ knapsackRec w v n c2 := by
  induction n generalizing c1 c2 with
  | zero => simp [knapsackRec]
  | succ i ih =>
    dsimp [knapsackRec]
    by_cases h2 : c2 < w i
    · have h1 : c1 < w i := lt_of_le_of_lt hc h2
      rw [if_pos h1, if_pos h2]
      exact ih hc
    · by_cases h1 : c1 < w i
      · rw [if_pos h1, if_neg h2]
        exact (ih hc).trans (le_max_left _ _)
      · rw [if_neg h1, if_neg h2]
        exact max_le_max (ih hc) (Nat.add_le_add_left (ih (by omega)) (v i))

/-! ### Subcollections and Feasibility -/

/-- Total weight of a subcollection of items `s`. -/
def totalWeight (w : ℕ → ℕ) (s : Finset ℕ) : ℕ :=
  ∑ j ∈ s, w j

/-- Total value of a subcollection of items `s`. -/
def totalValue (v : ℕ → ℕ) (s : Finset ℕ) : ℕ :=
  ∑ j ∈ s, v j

/-- A subcollection is feasible for capacity `cap` if its total weight does not exceed `cap`. -/
def IsFeasibleSubcollection (w : ℕ → ℕ) (s : Finset ℕ) (cap : ℕ) : Prop :=
  totalWeight w s ≤ cap

/-! ### Mathematical Correctness: Soundness and Completeness -/

/-- **Soundness**: Any feasible subcollection from the first $n$ items achieves at most the
value computed by the dynamic programming recurrence `knapsackRec w v n cap`. -/
theorem knapsack_sound (w v : ℕ → ℕ) (n cap : ℕ) (s : Finset ℕ)
    (hs : s ⊆ Finset.range n) (h_cap : totalWeight w s ≤ cap) :
    totalValue v s ≤ knapsackRec w v n cap := by
  induction n generalizing cap s with
  | zero =>
    rw [Finset.range_zero, Finset.subset_empty] at hs
    subst hs
    simp [totalValue, knapsackRec]
  | succ n ih =>
    dsimp [knapsackRec]
    by_cases hn : n ∈ s
    · have h_erase_sub : s.erase n ⊆ Finset.range n := by
        intro x hx
        have hx_s := Finset.mem_of_mem_erase hx
        have hx_ne := Finset.ne_of_mem_erase hx
        have hx_range := hs hx_s
        rw [Finset.mem_range] at hx_range ⊢
        omega
      have h_decomp_w : totalWeight w s = totalWeight w (s.erase n) + w n := by
        dsimp [totalWeight]
        exact (Finset.sum_erase_add s w hn).symm
      have h_decomp_v : totalValue v s = totalValue v (s.erase n) + v n := by
        dsimp [totalValue]
        exact (Finset.sum_erase_add s v hn).symm
      have h_not_lt : ¬(cap < w n) := by
        rw [h_decomp_w] at h_cap
        omega
      rw [if_neg h_not_lt]
      have h_sub_cap : totalWeight w (s.erase n) ≤ cap - w n := by
        rw [h_decomp_w] at h_cap
        omega
      have ih_val := ih (cap - w n) (s.erase n) h_erase_sub h_sub_cap
      rw [h_decomp_v]
      have : totalValue v (s.erase n) + v n ≤ v n + knapsackRec w v n (cap - w n) := by
        omega
      exact this.trans (le_max_right _ _)
    · have h_sub : s ⊆ Finset.range n := by
        intro x hx
        have hx_s := hs hx
        rw [Finset.mem_range] at hx_s ⊢
        have h_ne : x ≠ n := fun h ↦ hn (h ▸ hx)
        omega
      have ih_val := ih cap s h_sub h_cap
      split_ifs with _h_lt
      · exact ih_val
      · exact le_trans ih_val (le_max_left _ _)

/-- **Completeness**: There exists a feasible subcollection from the first $n$ items
whose total value exactly matches the dynamic programming value `knapsackRec w v n cap`. -/
theorem knapsack_complete (w v : ℕ → ℕ) (n cap : ℕ) :
    ∃ s : Finset ℕ, s ⊆ Finset.range n ∧ totalWeight w s ≤ cap ∧
      totalValue v s = knapsackRec w v n cap := by
  induction n generalizing cap with
  | zero =>
    refine ⟨∅, by simp, by simp [totalWeight], by simp [totalValue, knapsackRec]⟩
  | succ n ih =>
    dsimp [knapsackRec]
    by_cases h_lt : cap < w n
    · rw [if_pos h_lt]
      rcases ih cap with ⟨s, hs, hw, hv⟩
      refine ⟨s, ?_, hw, hv⟩
      exact hs.trans (Finset.range_mono (Nat.le_succ n))
    · rw [if_neg h_lt]
      rcases ih cap with ⟨s1, hs1, hw1, hv1⟩
      rcases ih (cap - w n) with ⟨s2, hs2, hw2, hv2⟩
      have hn_notin : n ∉ s2 := by
        intro hn
        have := hs2 hn
        rw [Finset.mem_range] at this
        omega
      by_cases h_choice : v n + knapsackRec w v n (cap - w n) ≤ knapsackRec w v n cap
      · rw [max_eq_left h_choice]
        refine ⟨s1, ?_, hw1, hv1⟩
        exact hs1.trans (Finset.range_mono (Nat.le_succ n))
      · have : knapsackRec w v n cap ≤ v n + knapsackRec w v n (cap - w n) := by omega
        rw [max_eq_right this]
        let s' := insert n s2
        refine ⟨s', ?_, ?_, ?_⟩
        · intro x hx
          rw [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · rw [Finset.mem_range]; omega
          · have := hs2 hx; rw [Finset.mem_range] at this ⊢; omega
        · dsimp [totalWeight] at hw2 ⊢
          rw [Finset.sum_insert hn_notin]
          omega
        · dsimp [totalValue] at hv2 ⊢
          rw [Finset.sum_insert hn_notin, hv2]

/-- **Optimality**: `knapsackRec w v n cap` equals the maximum attainable value among all
feasible subcollections from the first $n$ items. -/
theorem knapsack_is_optimal (w v : ℕ → ℕ) (n cap : ℕ) :
    (∀ s ⊆ Finset.range n, totalWeight w s ≤ cap →
      totalValue v s ≤ knapsackRec w v n cap) ∧
    (∃ s ⊆ Finset.range n, totalWeight w s ≤ cap ∧
      totalValue v s = knapsackRec w v n cap) :=
  ⟨fun s hs hw ↦ knapsack_sound w v n cap s hs hw, knapsack_complete w v n cap⟩

/-! ### Grid DP Instantiation and Complexity -/

/-- The 2D grid DP specification for 0/1 Knapsack on `Fin (n + 1) × Fin (W + 1)`
with unit transitions per cell ($C = 1$). -/
def knapsackGridDP (n W : ℕ) : GridDP n W :=
  GridDP.unitGridDP n W

/-- Unit local work bound for knapsack DP cells. -/
@[simp]
theorem knapsackGridDP_costBound (n W : ℕ) : (knapsackGridDP n W).costBound = 1 :=
  GridDP.unitGridDP_costBound n W

/-- State space cardinality of the $(n + 1) \times (W + 1)$ knapsack grid is $(n + 1)(W + 1)$. -/
@[simp]
theorem card_knapsack_states (n W : ℕ) :
    Fintype.card (Fin (n + 1) × Fin (W + 1)) = (n + 1) * (W + 1) :=
  GridDP.card_grid_states n W

/-- Total operations across the knapsack grid DP table is exactly $(n + 1)(W + 1)$. -/
theorem knapsackGridDP_totalCost (n W : ℕ) :
    (knapsackGridDP n W).toDPModel.totalCost = (n + 1) * (W + 1) :=
  GridDP.unitGridDP_totalCost n W

/-- Total work of 0/1 Knapsack grid DP is bounded by $(n + 1)(W + 1)$. -/
theorem knapsackGridDP_totalCost_le (n W : ℕ) :
    (knapsackGridDP n W).toDPModel.totalCost ≤ (n + 1) * (W + 1) := by
  rw [knapsackGridDP_totalCost]

end Amort.DP
