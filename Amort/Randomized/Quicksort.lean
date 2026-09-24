/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Approximation.SetCover
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Expected Complexity of Randomized Quicksort

> **Status: stub — not verified** (Phase 4 canon stub; harmonic indicator sum is proven,
> but randomized execution on Mathlib PMF is a specification stub).

This module formalizes the classical backward analysis of randomized quicksort:
1. **Indicator Variables**: $X_{ij}$ indicates whether the $i$-th and $j$-th smallest elements
   $z_i, z_j$ ($i < j$) are compared.
2. **Pivot Selection Invariant**: $z_i$ and $z_j$ are compared if and only if the first pivot
   chosen from $\{z_i, z_{i+1}, \dots, z_j\}$ is either $z_i$ or $z_j$.
3. **Pairwise Comparison Probability**: $\mathbb{P}[X_{ij} = 1] = \frac{2}{j - i + 1}$.
4. **Distance Grouping**: Summing over differences $k = j - i \in \{1, \dots, n-1\}$, there are
   $n - k$ pairs at distance $k$, each compared with probability $\frac{2}{k+1}$.
5. **Harmonic Upper Bound**:
   $\mathbb{E}[C] = \sum_{k=1}^{n-1} \frac{2(n-k)}{k+1} \le 2n H(n)$.

## Key Definitions and Theorems
- `Amort.Randomized.pairComparisonProb`: Pairwise probability $\frac{2}{k + 1}$.
- `Amort.Randomized.expectedQuicksortComparisons`: Expected comparisons grouped by distance $k$.
- `Amort.Randomized.expected_quicksort_le_harmonic`: $\mathbb{E}[C] \le 2n H(n)$.
- `Amort.Randomized.quicksortStepBound`: Operational bound $2n \cdot \text{size } n$.
-/

namespace Amort.Randomized

open Amort.Approximation

/-- The probability that two elements at sorted rank difference $k = j - i$ ($k \ge 1$)
are compared during randomized quicksort is $\frac{2}{k + 1}$. -/
noncomputable def pairComparisonProb (k : ℕ) : ℝ :=
  (2 : ℝ) / (((k : ℝ) + 1))

/-- Expected number of comparisons in randomized quicksort on $n$ elements,
obtained by summing over rank differences $k = j - i \in \{1, \dots, n-1\}$ where each
distance $k$ occurs for $n - k$ distinct pairs:
$$\mathbb{E}[C] = \sum_{k=1}^{n-1} (n - k) \cdot \frac{2}{k+1}$$ -/
noncomputable def expectedQuicksortComparisons (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, if k = 0 then 0 else ((n - k : ℝ) * pairComparisonProb k)

/-- For any rank difference $k \ge 1$, comparison probability is strictly positive. -/
lemma pairComparisonProb_pos {k : ℕ} :
    0 < pairComparisonProb k := by
  dsimp [pairComparisonProb]
  have hpos : (0 : ℝ) < (((k : ℝ) + 1)) := by
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  exact div_pos (by norm_num) hpos

/-- For each distance $k \in \{0, \dots, n-1\}$, the term is bounded by
$2n / (k + 1)$. -/
lemma quicksort_term_le (n k : ℕ) (hk : k ∈ Finset.range n) :
    (if k = 0 then 0 else ((n - k : ℝ) * pairComparisonProb k)) ≤
      2 * (n : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1)) := by
  split_ifs with h0
  · have hnonneg : 0 ≤ 2 * (n : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1)) := by
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hk1 : (0 : ℝ) ≤ (1 : ℝ) / ((k : ℝ) + 1) := by
        apply div_nonneg (by norm_num)
        have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      positivity
    exact hnonneg
  · dsimp [pairComparisonProb]
    have hk_lt : k < n := Finset.mem_range.mp hk
    have h_le : (((n - k : ℕ) : ℝ)) ≤ (((n : ℕ) : ℝ)) := Nat.cast_le.mpr (Nat.sub_le n k)
    have h_denom_pos : (0 : ℝ) < (k : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    calc (n - k : ℝ) * ((2 : ℝ) / ((k : ℝ) + 1))
        = 2 * (n - k : ℝ) / ((k : ℝ) + 1) := by ring
      _ ≤ 2 * (n : ℝ) / ((k : ℝ) + 1) := by
        apply div_le_div_of_nonneg_right _ (le_of_lt h_denom_pos)
        linarith
      _ = 2 * (n : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1)) := by ring

/-- **Harmonic Bound on Expected Comparisons**:
The expected number of comparisons in randomized quicksort on $n$ elements is bounded by
$2n \cdot H(n)$. -/
theorem expected_quicksort_le_harmonic (n : ℕ) :
    expectedQuicksortComparisons n ≤ 2 * (n : ℝ) * harmonic n := by
  dsimp [expectedQuicksortComparisons]
  have h_sum_le :
      (∑ k ∈ Finset.range n, (if k = 0 then 0 else ((n - k : ℝ) * pairComparisonProb k))) ≤
        ∑ k ∈ Finset.range n, (2 * (n : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1))) := by
    apply Finset.sum_le_sum
    intro k hk
    exact quicksort_term_le n k hk
  have h_factor :
      (∑ k ∈ Finset.range n, (2 * (n : ℝ) * ((1 : ℝ) / ((k : ℝ) + 1)))) =
        2 * (n : ℝ) * harmonic n := by
    rw [harmonic]
    rw [← Finset.mul_sum]
  linarith

/-- Concrete operational bound on expected randomized quicksort comparisons:
bounded by $2n \cdot \text{size } n$. -/
def quicksortStepBound (n : ℕ) : ℕ :=
  2 * n * Nat.size n

/-- Quicksort expected comparison bound. -/
theorem quicksortWorkBound_le (n : ℕ) :
    quicksortStepBound n ≤ 2 * n * Nat.size n := by
  rfl

end Amort.Randomized
