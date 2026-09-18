/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.DP
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Pairwise

/-!
# Dynamic Programming: Longest Increasing Subsequence (LIS)

This module formalizes the textbook Longest Increasing Subsequence (LIS) algorithm, proves its
mathematical correctness against all strictly increasing subsequences, and establishes its
$O(n^2)$ state-space complexity bound in the `Amort.Recurrence.DP` framework.

## Mathematical Architecture

1. **Subsequence Predicates**:
   - `IsStrictlyIncreasingSubsequence sub xs`: `sub.Sublist xs ∧ sub.Pairwise (· < ·)`
   - `IsStrictlyIncreasingSubsequenceWithPrefix prev sub xs`: additionally `∀ y ∈ sub, prev < y`

2. **Recursive Bellman Formulations**:
   - `lisWithPrefix prev xs`: optimal LIS length on `xs` where each chosen element exceeds `prev`.
   - `lisRec xs`: overall optimal LIS length on `xs`.

3. **Mathematical Correctness**:
   - **Soundness**: Every strictly increasing subsequence of `xs` has length bounded by `lisRec xs`.
   - **Completeness**: There exists a strictly increasing subsequence of `xs` with length
     `lisRec xs`.
   - **Optimality**: `lisRec xs` equals the maximum possible length of any strictly increasing
     subsequence.

4. **State-Space Model & Operational Bound**:
   - State space: $\text{Fin } n$ representing indices $0 \le i < n$.
   - Local work at state $i$: examining all predecessors $j < i$ takes $i$ comparisons ($i \le n$).
   - Total work:
     $$\text{Total Work} = \sum_{i=0}^{n-1} i = \frac{n(n - 1)}{2} \le \frac{n(n + 1)}{2} \le n^2$$
   - Instantiated via `Amort.Recurrence.DPModel (Fin n)`, proving total cost $\le n^2$.
-/

namespace Amort.DP

open BigOperators
open Amort.Recurrence

/-! ### Subsequence Predicates -/

/-- A sublist `sub` of `xs` is a strictly increasing subsequence if it is a sublist
and its elements are pairwise strictly increasing. -/
def IsStrictlyIncreasingSubsequence (sub xs : List ℕ) : Prop :=
  sub.Sublist xs ∧ sub.Pairwise (· < ·)

/-- A strictly increasing subsequence whose elements are all strictly greater than `prev`. -/
def IsStrictlyIncreasingSubsequenceWithPrefix (prev : ℕ) (sub xs : List ℕ) : Prop :=
  sub.Sublist xs ∧ sub.Pairwise (· < ·) ∧ (∀ y ∈ sub, prev < y)

/-! ### Recursive Subproblem Formulation -/

/-- Computes the length of the longest strictly increasing subsequence of `xs`
with all elements strictly greater than `prev`. -/
def lisWithPrefix (prev : ℕ) : List ℕ → ℕ
  | [] => 0
  | x :: xs =>
    if prev < x then
      max (lisWithPrefix prev xs) (1 + lisWithPrefix x xs)
    else
      lisWithPrefix prev xs

/-- Base case for empty list with prefix. -/
@[simp]
theorem lisWithPrefix_nil (prev : ℕ) : lisWithPrefix prev [] = 0 := rfl

/-- Computes the length of the longest strictly increasing subsequence of `xs`. -/
def lisRec : List ℕ → ℕ
  | [] => 0
  | x :: xs => max (lisRec xs) (1 + lisWithPrefix x xs)

/-- Base case for empty list. -/
@[simp]
theorem lisRec_nil : lisRec [] = 0 := rfl

/-! ### Mathematical Correctness: Soundness -/

/-- **Soundness with prefix**: Any strictly increasing subsequence whose elements exceed `prev`
has length bounded by `lisWithPrefix prev xs`. -/
lemma lisWithPrefix_sound (prev : ℕ) (xs sub : List ℕ)
    (h : IsStrictlyIncreasingSubsequenceWithPrefix prev sub xs) :
    sub.length ≤ lisWithPrefix prev xs := by
  induction xs generalizing prev sub with
  | nil =>
    have h_sub := h.1
    have : sub = [] := List.eq_nil_of_sublist_nil h_sub
    subst this
    simp [lisWithPrefix]
  | cons x xs ih =>
    rcases h with ⟨h_sub, h_pair, h_gt⟩
    dsimp [lisWithPrefix]
    cases h_sub with
    | cons _ h_sub' =>
      by_cases hpx : prev < x
      · rw [if_pos hpx]
        have h_step := ih prev sub ⟨h_sub', h_pair, h_gt⟩
        omega
      · rw [if_neg hpx]
        exact ih prev sub ⟨h_sub', h_pair, h_gt⟩
    | cons_cons _ h_sub' =>
      have h_x_gt : prev < x := h_gt x (List.mem_cons.2 (Or.inl rfl))
      rw [if_pos h_x_gt]
      have h_pair' := (List.pairwise_cons.1 h_pair)
      have h_rest_gt : ∀ y ∈ _, x < y := fun y hy ↦ h_pair'.1 y hy
      have ih_rest := ih x _ ⟨h_sub', h_pair'.2, h_rest_gt⟩
      simp only [List.length_cons]
      omega

/-- **Soundness**: Any strictly increasing subsequence of `xs` has length bounded by
`lisRec xs`. -/
theorem lisRec_sound (xs sub : List ℕ)
    (h : IsStrictlyIncreasingSubsequence sub xs) :
    sub.length ≤ lisRec xs := by
  induction xs generalizing sub with
  | nil =>
    have : sub = [] := List.eq_nil_of_sublist_nil h.1
    subst this
    simp [lisRec]
  | cons x xs ih =>
    rcases h with ⟨h_sub, h_pair⟩
    dsimp [lisRec]
    cases h_sub with
    | cons _ h_sub' =>
      have h_step := ih sub ⟨h_sub', h_pair⟩
      omega
    | cons_cons _ h_sub' =>
      have h_pair' := (List.pairwise_cons.1 h_pair)
      have h_rest_gt : ∀ y ∈ _, x < y := fun y hy ↦ h_pair'.1 y hy
      have h_with := lisWithPrefix_sound x xs _ ⟨h_sub', h_pair'.2, h_rest_gt⟩
      simp only [List.length_cons]
      omega

/-! ### Mathematical Correctness: Completeness -/

/-- **Completeness with prefix**: There exists a strictly increasing subsequence with elements
exceeding `prev` whose length matches `lisWithPrefix prev xs`. -/
lemma lisWithPrefix_complete (prev : ℕ) (xs : List ℕ) :
    ∃ sub, IsStrictlyIncreasingSubsequenceWithPrefix prev sub xs ∧
      sub.length = lisWithPrefix prev xs := by
  induction xs generalizing prev with
  | nil =>
    refine ⟨[], ⟨List.nil_sublist [], List.Pairwise.nil, by simp⟩, by simp [lisWithPrefix]⟩
  | cons x xs ih =>
    dsimp [lisWithPrefix]
    by_cases hpx : prev < x
    · rw [if_pos hpx]
      rcases ih prev with ⟨s1, ⟨hs1_sub, hs1_pair, hs1_gt⟩, hs1_len⟩
      rcases ih x with ⟨s2, ⟨hs2_sub, hs2_pair, hs2_gt⟩, hs2_len⟩
      by_cases hmax : 1 + lisWithPrefix x xs ≤ lisWithPrefix prev xs
      · rw [Nat.max_eq_left hmax]
        refine ⟨s1, ⟨hs1_sub.cons x, hs1_pair, hs1_gt⟩, hs1_len⟩
      · have : lisWithPrefix prev xs ≤ 1 + lisWithPrefix x xs := by omega
        rw [Nat.max_eq_right this]
        let s' := x :: s2
        refine ⟨s', ⟨hs2_sub.cons_cons x, ?_, ?_⟩, ?_⟩
        · rw [List.pairwise_cons]
          exact ⟨hs2_gt, hs2_pair⟩
        · intro y hy
          rw [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact hpx
          · have := hs2_gt y hy
            omega
        · change (x :: s2).length = 1 + lisWithPrefix x xs
          rw [List.length_cons, hs2_len]
          omega
    · rw [if_neg hpx]
      rcases ih prev with ⟨s, ⟨hs_sub, hs_pair, hs_gt⟩, hs_len⟩
      refine ⟨s, ⟨hs_sub.cons x, hs_pair, hs_gt⟩, hs_len⟩

/-- **Completeness**: There exists a strictly increasing subsequence of `xs` whose length
matches `lisRec xs`. -/
theorem lisRec_complete (xs : List ℕ) :
    ∃ sub, IsStrictlyIncreasingSubsequence sub xs ∧ sub.length = lisRec xs := by
  induction xs with
  | nil =>
    refine ⟨[], ⟨List.nil_sublist [], List.Pairwise.nil⟩, by simp [lisRec]⟩
  | cons x xs ih =>
    dsimp [lisRec]
    rcases ih with ⟨s1, ⟨hs1_sub, hs1_pair⟩, hs1_len⟩
    rcases lisWithPrefix_complete x xs with ⟨s2, ⟨hs2_sub, hs2_pair, hs2_gt⟩, hs2_len⟩
    by_cases hmax : 1 + lisWithPrefix x xs ≤ lisRec xs
    · rw [Nat.max_eq_left hmax]
      refine ⟨s1, ⟨hs1_sub.cons x, hs1_pair⟩, hs1_len⟩
    · have : lisRec xs ≤ 1 + lisWithPrefix x xs := by omega
      rw [Nat.max_eq_right this]
      let s' := x :: s2
      refine ⟨s', ⟨hs2_sub.cons_cons x, ?_⟩, ?_⟩
      · rw [List.pairwise_cons]
        exact ⟨hs2_gt, hs2_pair⟩
      · change (x :: s2).length = 1 + lisWithPrefix x xs
        rw [List.length_cons, hs2_len]
        omega

/-- **Optimality**: `lisRec xs` equals the length of the longest strictly increasing subsequence
of `xs`. -/
theorem lis_is_optimal (xs : List ℕ) :
    (∀ sub, IsStrictlyIncreasingSubsequence sub xs → sub.length ≤ lisRec xs) ∧
    (∃ sub, IsStrictlyIncreasingSubsequence sub xs ∧ sub.length = lisRec xs) :=
  ⟨fun sub h ↦ lisRec_sound xs sub h, lisRec_complete xs⟩

/-! ### State-Space Model and Complexity -/

/-- The state-space DP model for LIS on `Fin n`, where state $i \in \text{Fin } n$
examines all predecessors $j < i$, taking $i$ operations. -/
def lisDP (n : ℕ) : DPModel (Fin n) where
  costPerState := fun i ↦ i.val
  costBound := n
  h_cost := fun i ↦ by
    have hi := i.isLt
    omega

/-- The exact total work of LIS predecessor comparisons across all $n$ states is $n(n - 1)/2$. -/
theorem lisDP_totalCost_eq (n : ℕ) :
    (lisDP n).totalCost = n * (n - 1) / 2 := by
  dsimp [DPModel.totalCost, lisDP]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ i) n]
  exact Finset.sum_range_id n

/-- The total work is bounded by the triangular upper bound $n(n + 1)/2$. -/
theorem lisDP_totalCost_le_triangular (n : ℕ) :
    (lisDP n).totalCost ≤ n * (n + 1) / 2 := by
  rw [lisDP_totalCost_eq]
  apply Nat.div_le_div_right
  apply Nat.mul_le_mul_left
  omega

/-- The total work of the LIS state-space DP is bounded by $n^2$. -/
theorem lisDP_totalCost_le_sq (n : ℕ) :
    (lisDP n).totalCost ≤ n ^ 2 := by
  have h := (lisDP n).totalCost_le
  simp only [Fintype.card_fin] at h
  rw [sq]
  exact h

end Amort.DP
