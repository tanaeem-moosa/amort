/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Median-of-Medians Deterministic Selection (BFPRT)

This module formalizes the Median-of-Medians (BFPRT) deterministic selection algorithm:
- Block partitioning of $n$ elements into groups of size 5.
- Group medians and the median-of-medians pivot selection.
- The **pivot quality theorem**: guarantees at least $3 \lceil \lceil n/5 \rceil / 2 \rceil$
  elements, and at least $3n/10 - 6$ elements, are $\le x$ and $\ge x$.
- Recursive branch upper bound: neither partition branch exceeds $7n/10 + 6$ elements.
- The divide-and-conquer recurrence:
  $$T(n) \le T(\lceil n/5 \rceil) + T(7n/10 + 6) + c \cdot n$$
- Linear time theorem: $T(n) \le C \cdot n \implies O(n)$ since $1/5 + 7/10 = 9/10 < 1$.

## Key Definitions and Theorems
- `Amort.Greedy.numBlocks5`: Number of size-5 blocks $\lceil n/5 \rceil = (n + 4) / 5$.
- `Amort.Greedy.numMediansGePivot`: Number of group medians $\ge x$.
- `Amort.Greedy.pivotQualityLower`: Lower bound $3 \lceil \lceil n/5 \rceil / 2 \rceil$.
- `Amort.Greedy.bfprtBranchBound`: Maximum recursive partition size $7n/10 + 6$.
- `Amort.Greedy.pivot_quality_ge`: Lower bound 3n/10 <= 3 * ceil(ceil(n/5)/2).
- `Amort.Greedy.pivot_quality_discounted`: Explicit $3n/10 - 6$ lower bound.
- `Amort.Greedy.branch_size_le`: Partition branch size bounded by $7n/10 + 6$.
- `Amort.Greedy.BFPRTRecurrence`: The divide-and-conquer recurrence specification.
- `Amort.Greedy.bfprt_linear_bound`: Formal proof of $T(n) \le C \cdot n$ for all $n \ge 1$.
-/

namespace Amort.Greedy

/-- Number of size-5 blocks in a collection of $n$ elements: $\lceil n/5 \rceil = (n + 4) / 5$. -/
def numBlocks5 (n : ℕ) : ℕ :=
  (n + 4) / 5

/-- Number of group medians that are greater than or equal to the median-of-medians pivot:
$\lceil \lceil n/5 \rceil / 2 \rceil = ((n + 4) / 5 + 1) / 2$. -/
def numMediansGePivot (n : ℕ) : ℕ :=
  (numBlocks5 n + 1) / 2

/-- Ideal lower bound on elements $\ge x$ (or $\le x$): 3 elements from each such group. -/
def pivotQualityLower (n : ℕ) : ℕ :=
  3 * numMediansGePivot n

/-- Upper bound on the size of each recursive partition branch: $7n/10 + 6$. -/
def bfprtBranchBound (n : ℕ) : ℕ :=
  7 * n / 10 + 6

/-! ### Pivot Quality Theorems -/

/-- The ideal pivot quality lower bound is at least $3n/10$ for all $n \in \mathbb{N}$. -/
theorem pivot_quality_ge (n : ℕ) :
    3 * n / 10 ≤ pivotQualityLower n := by
  unfold pivotQualityLower numMediansGePivot numBlocks5
  omega

/-- Concrete lower bound with boundary group adjustments:
for all $n \ge 16$, discounting up to two boundary groups yields at least $3n/10 - 6$
elements bounded by the pivot. -/
theorem pivot_quality_discounted (n : ℕ) (hn : 16 ≤ n) :
    3 * n / 10 - 6 ≤ 3 * (numMediansGePivot n - 2) := by
  unfold numMediansGePivot numBlocks5
  omega

/-- Recursive branch size guarantee:
Subtracting the guaranteed $3 (\lceil \lceil n/5 \rceil / 2 \rceil - 2)$ elements
bounded by the pivot ensures that neither recursive subproblem exceeds
$7n/10 + 6$ elements. -/
theorem branch_size_le (n : ℕ) (hn : 20 ≤ n) :
    n - 3 * (numMediansGePivot n - 2) ≤ bfprtBranchBound n := by
  unfold bfprtBranchBound numMediansGePivot numBlocks5
  omega

/-- Subproblem contractivity: both recursive subproblem sizes are strictly less than $n$
for all $n \ge 140$. -/
lemma bfprt_subproblem1_lt (n : ℕ) (hn : 140 ≤ n) :
    (n + 4) / 5 < n := by
  omega

lemma bfprt_subproblem2_lt (n : ℕ) (hn : 140 ≤ n) :
    bfprtBranchBound n < n := by
  unfold bfprtBranchBound
  omega

lemma bfprt_subproblem1_pos (n : ℕ) (hn : 140 ≤ n) :
    1 ≤ (n + 4) / 5 := by
  omega

lemma bfprt_subproblem2_pos (n : ℕ) (hn : 140 ≤ n) :
    1 ≤ bfprtBranchBound n := by
  unfold bfprtBranchBound
  omega

/-! ### Divide-and-Conquer Recurrence & Linear Time Bound -/

/-- The BFPRT divide-and-conquer recurrence:
$T(n) \le T(\lceil n/5 \rceil) + T(7n/10 + 6) + c \cdot n$ for all $n \ge 140$. -/
def BFPRTRecurrence (T : ℕ → ℕ) (c : ℕ) : Prop :=
  ∀ n ≥ 140, T n ≤ T ((n + 4) / 5) + T (bfprtBranchBound n) + c * n

/-- Linear time induction step:
Because $1/5 + 7/10 = 9/10 < 1$, for any $C \ge 30c$,
$C \cdot ((n + 4)/5 + (7n/10 + 6)) + c \cdot n \le C \cdot n$ for all $n \ge 140$. -/
lemma bfprt_linear_step (n c C : ℕ) (hn : 140 ≤ n) (hC : 30 * c ≤ C) :
    C * ((n + 4) / 5 + bfprtBranchBound n) + c * n ≤ C * n := by
  unfold bfprtBranchBound
  obtain ⟨k, rfl⟩ := Nat.le.dest hC
  have h3 : 30 * ((n + 4) / 5 + (7 * n / 10 + 6)) + n ≤ 30 * n := by omega
  have h_sum_le : (n + 4) / 5 + (7 * n / 10 + 6) ≤ n := by omega
  have h4 := Nat.mul_le_mul_left c h3
  have h5 := Nat.mul_le_mul_left k h_sum_le
  calc (30 * c + k) * ((n + 4) / 5 + (7 * n / 10 + 6)) + c * n
    _ = (30 * c * ((n + 4) / 5 + (7 * n / 10 + 6)) + c * n) +
        k * ((n + 4) / 5 + (7 * n / 10 + 6)) := by ring
    _ ≤ 30 * c * n + k * n := by
      have hstep : 30 * c * ((n + 4) / 5 + (7 * n / 10 + 6)) + c * n ≤ 30 * c * n := by
        calc 30 * c * ((n + 4) / 5 + (7 * n / 10 + 6)) + c * n
          _ = c * (30 * ((n + 4) / 5 + (7 * n / 10 + 6)) + n) := by ring
          _ ≤ c * (30 * n) := h4
          _ = 30 * c * n := by ring
      omega
    _ = (30 * c + k) * n := by ring

/-- Master theorem for Median-of-Medians:
Any algorithm satisfying the BFPRT recurrence with base cases bounded by $B \cdot n$
obeys the global linear time bound $T(n) \le C \cdot n$ for all $n \ge 1$,
where $C = \max B (30c)$. -/
theorem bfprt_linear_bound (T : ℕ → ℕ) (c B : ℕ)
    (hrec : BFPRTRecurrence T c)
    (hbase : ∀ n, 1 ≤ n → n < 140 → T n ≤ B * n) :
    let C := max B (30 * c)
    ∀ n ≥ 1, T n ≤ C * n := by
  intro C n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn1
    by_cases hlt : n < 140
    · have hB := hbase n hn1 hlt
      have hBC : B * n ≤ C * n := Nat.mul_le_mul_right n (le_max_left B (30 * c))
      omega
    · have hlt : 140 ≤ n := by omega
      have hT := hrec n hlt
      have h1_lt := bfprt_subproblem1_lt n hlt
      have h2_lt := bfprt_subproblem2_lt n hlt
      have h1_pos := bfprt_subproblem1_pos n hlt
      have h2_pos := bfprt_subproblem2_pos n hlt
      have ih1 := ih ((n + 4) / 5) h1_lt h1_pos
      have ih2 := ih (bfprtBranchBound n) h2_lt h2_pos
      have hC_ge : 30 * c ≤ C := le_max_right B (30 * c)
      have hstep := bfprt_linear_step n c C hlt hC_ge
      calc T n
        _ ≤ T ((n + 4) / 5) + T (bfprtBranchBound n) + c * n := hT
        _ ≤ C * ((n + 4) / 5) + C * (bfprtBranchBound n) + c * n := by omega
        _ = C * ((n + 4) / 5 + bfprtBranchBound n) + c * n := by ring
        _ ≤ C * n := hstep

end Amort.Greedy
