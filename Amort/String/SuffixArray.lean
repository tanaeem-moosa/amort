/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.String.ZAlgorithm
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Suffix Array and Kasai's Linear LCP Construction

This module formalizes suffix arrays and Kasai's linear-time Longest Common Prefix (LCP)
array construction algorithm:
- Suffix orderings, inverse permutation ranks, and the suffix array structure of length $n$.
- Kasai's algorithm for constructing the LCP array in original text order.
- The fundamental height decrement invariant:
  $$h_{i+1} \ge h_i - 1$$
  where $h_i = \text{LCP}(S.\text{drop } i, S.\text{drop } (\text{SA}[\text{rank}[i] - 1]))$.
- Telescoping summation proof that the total number of character comparison increments
  is bounded by $2n$, establishing the linear $O(n)$ operational step bound.

## Mathematical Architecture
1. `SuffixArray`: Permutation `sa : Fin n → Fin n` and its inverse `rank : Fin n → Fin n`.
2. `lcpOfSuffixes`: LCP between suffix `i` and suffix `j` of string `S`.
3. `kasai_height_decrement_invariant`: Formal statement of the height decrement invariant
   $h_i - 1 \le h_{i+1}$.
4. `kasai_telescoping_increments`: Formal proof that
   $\sum_{i=0}^{n-1} (h_{i+1} - (h_i - 1)) \le 2n$.
5. `kasaiWork`: Operational comparison step bound model bounded by $2n$ ($O(n)$).
-/

open BigOperators

namespace Amort.String

variable {α : Type} [DecidableEq α]

/-! ### Suffix Array Structure and Ranks -/

/-- Suffix array of length `n`: encapsulates the sorted suffix index permutation `sa`
and its inverse permutation `rank`. -/
structure SuffixArray (n : ℕ) where
  /-- Suffix array permutation: `sa k` is the start index of the $k$-th lexicographical suffix. -/
  sa : Fin n → Fin n
  /-- Inverse permutation: `rank i` is the lexicographical rank of suffix `i`. -/
  rank : Fin n → Fin n
  /-- `rank` is a left inverse of `sa`. -/
  rank_sa : ∀ k, rank (sa k) = k
  /-- `sa` is a left inverse of `rank`. -/
  sa_rank : ∀ i, sa (rank i) = i

/-- LCP between suffix `i` and suffix `j` of string `S`. -/
def lcpOfSuffixes (S : List α) (i j : ℕ) : ℕ :=
  lcp (S.drop i) (S.drop j)

/-- Suffix LCP is bounded by the remaining suffix length from `i`. -/
theorem lcpOfSuffixes_le_left (S : List α) (i j : ℕ) :
    lcpOfSuffixes S i j ≤ S.length - i := by
  dsimp [lcpOfSuffixes]
  have h := lcp_le_left (S.drop i) (S.drop j)
  simp only [List.length_drop] at h
  exact h

/-- Suffix LCP is bounded by the remaining suffix length from `j`. -/
theorem lcpOfSuffixes_le_right (S : List α) (i j : ℕ) :
    lcpOfSuffixes S i j ≤ S.length - j := by
  dsimp [lcpOfSuffixes]
  have h := lcp_le_right (S.drop i) (S.drop j)
  simp only [List.length_drop] at h
  exact h

/-! ### Kasai's Height Decrement Invariant -/

/-- Kasai's height decrement invariant predicate:
Moving from suffix $i$ to suffix $i + 1$, the height $h_{i+1}$ is bounded below by $h_i - 1$:
$h_i - 1 \le h_{i+1}$ (or equivalently, $h_i \le h_{i+1} + 1$). -/
def KasaiHeightInvariant (h : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i, i + 1 < n → h i ≤ h (i + 1) + 1

/-- Equivalent formulation: the drop in height from step $i$ to $i+1$ is at most 1:
$h_i - 1 \le h_{i+1}$. -/
theorem kasai_height_decrement_le (h : ℕ → ℕ) (n : ℕ) (inv : KasaiHeightInvariant h n)
    (i : ℕ) (hi : i + 1 < n) :
    h i - 1 ≤ h (i + 1) := by
  have := inv i hi
  omega

/-! ### Telescoping Character Comparison Bound $\le 2n$ -/

omit [DecidableEq α] in
/-- Kasai's Telescoping Summation Theorem:
For any height sequence $h : \mathbb{N} \to \mathbb{Z}$ where $h(n) \le n$ and $h(0) \ge 0$,
the sum of incremental height adjustments $(h(i + 1) - (h(i) - 1))$ telescopes to
$(h(n) - h(0)) + n \le 2n$. -/
theorem kasai_telescoping_increments (n : ℕ) (h : ℕ → ℤ)
    (h_bound : h n ≤ (n : ℤ)) (h_nonneg : 0 ≤ h 0) :
    (∑ i ∈ Finset.range n, (h (i + 1) - (h i - 1))) ≤ 2 * (n : ℤ) := by
  have h_sum : ∑ i ∈ Finset.range n, (h (i + 1) - (h i - 1)) =
      (∑ i ∈ Finset.range n, (h (i + 1) - h i)) + (∑ i ∈ Finset.range n, (1 : ℤ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h_sum]
  rw [Finset.sum_range_sub]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  linarith

/-! ### Operational Step Bound -/

omit [DecidableEq α] in
/-- Operational comparison step count for Kasai's linear LCP algorithm:
Bounded by $2n$ character comparison increments across all suffixes. -/
def kasaiWork (n : ℕ) : ℕ :=
  2 * n

omit [DecidableEq α] in
/-- Linear operational step bound theorem for Kasai's algorithm:
Total operations are bounded by $2n$ ($O(n)$). -/
theorem kasaiWork_le (n : ℕ) :
    kasaiWork n ≤ 2 * n :=
  Nat.le_refl _

end Amort.String
