/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Sorting.InsertionSort
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Ring

/-!
# Linear and Telescoping Recurrences

This module formalizes general recurrence theorems for loop algorithms where the cost
grows by a step bound at each iteration: $T(n+1) \le T(n) + f(n)$.

## Mathematical Architecture

1. **General Telescoping Sum**:
   By induction on $n$, any sequence satisfying $T(i+1) \le T(i) + f(i)$ for all $i < n$
   telescopes to:
   $$T(n) \le T(0) + \sum_{i=0}^{n-1} f(i)$$

2. **Constant Step Recurrences**:
   When $f(i) = c$, the sum evaluates to $\sum_{i=0}^{n-1} c = c \cdot n$, yielding:
   $$T(n) \le T(0) + c \cdot n$$
   Consequently, $T(n) = O(n)$ under `Filter.atTop`.

3. **General Power Step Recurrences**:
   When $f(i) = c \cdot i^k$, bounding each term by $i^k \le n^k$ gives:
   $$\sum_{i=0}^{n-1} c \cdot i^k \le c \cdot n \cdot n^k = c \cdot n^{k+1}$$
   yielding $T(n) \le T(0) + c \cdot n^{k+1}$ and $T(n) = O(n^{k+1})$ under `Filter.atTop`.

4. **Linear Step (Quadratic Bound)**:
   For $k = 1$, using the closed form $\sum_{i=0}^{n-1} i = n(n-1)/2$, we obtain:
   $$T(n) \le T(0) + c \cdot \frac{n(n-1)}{2} \le T(0) + c \cdot n^2$$
   yielding $T(n) = O(n^2)$ under `Filter.atTop`.

5. **Iterative Sorting Connection (Insertion Sort)**:
   Insertion sort extends a sorted prefix of length $n$ to $n+1$ using at most $n$
   comparisons. This matches the telescoping recurrence with $c = 1, k = 1, T(0) = 0$,
   yielding the concrete bound $T(n) \le n^2$ and $O(n^2)$ complexity.

## Key Theorems
- `Amort.Recurrence.le_add_sum_range_of_step_le`: Fundamental telescoping inequality.
- `Amort.Recurrence.telescoping_const_step_bound`: Concrete $O(n)$ bound for constant steps.
- `Amort.Recurrence.telescoping_const_step_isBigO`: Asymptotic $O(n)$ complexity.
- `Amort.Recurrence.telescoping_power_step_bound`: Concrete $O(n^{k+1})$ power bound.
- `Amort.Recurrence.telescoping_power_step_isBigO`: Asymptotic $O(n^{k+1})$ complexity.
- `Amort.Recurrence.telescoping_linear_step_bound`: Concrete $O(n^2)$ bound for $k=1$.
- `Amort.Recurrence.telescoping_linear_step_isBigO_sq`: Asymptotic $O(n^2)$ complexity.
- `Amort.Recurrence.insertionSortRecBound_le_sq`: Insertion sort recurrence bounded by $n^2$.
- `Amort.Recurrence.insertionSortRecBound_isBigO_sq`: Insertion sort recurrence is $O(n^2)$.
- `Amort.Recurrence.insertionSortCount_le_recBound`: Concrete insertion sort comparisons
  bounded by the telescoping recurrence bound.
-/

namespace Amort.Recurrence

open Asymptotics
open Finset

variable {T : ℕ → ℕ} {f : ℕ → ℕ}

/-! ### General Telescoping Sum -/

/-- Fundamental telescoping inequality: if $T(i+1) \le T(i) + f(i)$ for all $i$,
then $T(n) \le T(0) + \sum_{i=0}^{n-1} f(i)$. -/
theorem le_add_sum_range_of_step_le (h : ∀ i, T (i + 1) ≤ T i + f i) (n : ℕ) :
    T n ≤ T 0 + ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep := h n
    have hsum : (∑ i ∈ range (n + 1), f i) = (∑ i ∈ range n, f i) + f n :=
      sum_range_succ f n
    rw [hsum]
    omega

/-- Range sum of a constant in `ℕ`. -/
lemma sum_range_const (n c : ℕ) : (∑ _i ∈ range n, c) = n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    ring

/-! ### Constant Step Recurrences -/

/-- Concrete upper bound for constant step recurrence: if $T(i+1) \le T(i) + c$,
then $T(n) \le T(0) + c \cdot n$. -/
theorem telescoping_const_step_bound (c : ℕ) (h : ∀ i, T (i + 1) ≤ T i + c) (n : ℕ) :
    T n ≤ T 0 + c * n := by
  have ht := le_add_sum_range_of_step_le h n
  rw [sum_range_const] at ht
  rw [mul_comm c n]
  exact ht

/-- Asymptotic complexity for constant step recurrence: $T(n) = O(n)$ under `Filter.atTop`. -/
theorem telescoping_const_step_isBigO (c : ℕ) (h : ∀ i, T (i + 1) ≤ T i + c) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop] (fun n : ℕ ↦ ((n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound ((T 0 + c : ℕ) : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h_bound := telescoping_const_step_bound c h n
  have h_T0 : T 0 ≤ T 0 * n := Nat.le_mul_of_pos_right (T 0) hn
  have h_total : T n ≤ (T 0 + c) * n := by
    calc T n ≤ T 0 + c * n := h_bound
      _ ≤ T 0 * n + c * n := Nat.add_le_add_right h_T0 _
      _ = (T 0 + c) * n := by ring
  exact_mod_cast h_total

/-! ### General Power Step Recurrences -/

/-- Sum of $k$-th powers over `range n` is bounded by $n \cdot n^k$. -/
lemma sum_range_pow_le (k n : ℕ) :
    (∑ i ∈ range n, i ^ k) ≤ n * n ^ k := by
  have : ∀ i ∈ range n, i ^ k ≤ n ^ k := by
    intro i hi
    rw [mem_range] at hi
    exact Nat.pow_le_pow_left (by omega) k
  have h := sum_le_card_nsmul (range n) (fun i ↦ i ^ k) (n ^ k) this
  simp only [card_range, smul_eq_mul] at h
  exact h

/-- Scaled sum of $k$-th powers bounded by $c \cdot n^{k+1}$. -/
lemma sum_range_mul_pow_le (c k n : ℕ) :
    (∑ i ∈ range n, c * i ^ k) ≤ c * n ^ (k + 1) := by
  rw [← mul_sum]
  have h := sum_range_pow_le k n
  have h_mul := Nat.mul_le_mul_left c h
  have : n * n ^ k = n ^ (k + 1) := by ring
  rw [this] at h_mul
  exact h_mul

/-- Concrete upper bound for general power step: if $T(i+1) \le T(i) + c \cdot i^k$,
then $T(n) \le T(0) + c \cdot n^{k+1}$. -/
theorem telescoping_power_step_bound (c k : ℕ)
    (h : ∀ i, T (i + 1) ≤ T i + c * i ^ k) (n : ℕ) :
    T n ≤ T 0 + c * n ^ (k + 1) := by
  have h1 := le_add_sum_range_of_step_le h n
  have h2 := sum_range_mul_pow_le c k n
  omega

/-- Asymptotic complexity for general power step: if $T(i+1) \le T(i) + c \cdot i^k$,
then $T(n) = O(n^{k+1})$ under `Filter.atTop`. -/
theorem telescoping_power_step_isBigO (c k : ℕ)
    (h : ∀ i, T (i + 1) ≤ T i + c * i ^ k) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n ^ (k + 1) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound ((T 0 + c : ℕ) : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h_bound := telescoping_power_step_bound c k h n
  have h_pow_pos : 1 ≤ n ^ (k + 1) := Nat.one_le_pow (k + 1) n hn
  have h_T0 : T 0 ≤ T 0 * n ^ (k + 1) := Nat.le_mul_of_pos_right (T 0) h_pow_pos
  have h_total : T n ≤ (T 0 + c) * n ^ (k + 1) := by
    calc T n ≤ T 0 + c * n ^ (k + 1) := h_bound
      _ ≤ T 0 * n ^ (k + 1) + c * n ^ (k + 1) := Nat.add_le_add_right h_T0 _
      _ = (T 0 + c) * n ^ (k + 1) := by ring
  exact_mod_cast h_total

/-! ### Linear Step (Quadratic Bound) -/

/-- Concrete upper bound for linear step ($k=1$): if $T(i+1) \le T(i) + c \cdot i$,
then $T(n) \le T(0) + c \cdot (n * (n - 1) / 2) \le T(0) + c \cdot n^2$. -/
theorem telescoping_linear_step_bound (c : ℕ)
    (h : ∀ i, T (i + 1) ≤ T i + c * i) (n : ℕ) :
    T n ≤ T 0 + c * n ^ 2 := by
  have ht := le_add_sum_range_of_step_le h n
  rw [← mul_sum, sum_range_id] at ht
  have h_div : n * (n - 1) / 2 ≤ n ^ 2 := by
    have h1 : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ 2
    have h2 : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    have h3 : n * n = n ^ 2 := by ring
    omega
  have h_mul := Nat.mul_le_mul_left c h_div
  omega

/-- Asymptotic complexity for linear step ($k=1$): $T(n) = O(n^2)$ under `Filter.atTop`. -/
theorem telescoping_linear_step_isBigO_sq (c : ℕ)
    (h : ∀ i, T (i + 1) ≤ T i + c * i) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ)) := by
  have h_pow : ∀ i, T (i + 1) ≤ T i + c * i ^ 1 := by
    intro i
    have : i ^ 1 = i := by ring
    rw [this]
    exact h i
  have h_res := telescoping_power_step_isBigO c 1 h_pow
  have : 1 + 1 = 2 := rfl
  rw [this] at h_res
  exact h_res

/-! ### Application to Iterative Sorting (Insertion Sort) -/

/-- Exact recurrence bound for insertion sort comparisons on list length $n$. -/
def insertionSortRecBound : ℕ → ℕ
  | 0 => 0
  | n + 1 => insertionSortRecBound n + n

/-- The insertion sort recurrence satisfies the linear step equality. -/
theorem insertionSortRecBound_step (n : ℕ) :
    insertionSortRecBound (n + 1) = insertionSortRecBound n + n := rfl

/-- Concrete upper bound: insertion sort comparisons bounded by $n^2$. -/
theorem insertionSortRecBound_le_sq (n : ℕ) :
    insertionSortRecBound n ≤ n ^ 2 := by
  have h_step : ∀ i, insertionSortRecBound (i + 1) ≤ insertionSortRecBound i + 1 * i := by
    intro i
    rw [insertionSortRecBound_step, one_mul]
  have h := telescoping_linear_step_bound 1 h_step n
  have h0 : insertionSortRecBound 0 = 0 := rfl
  rw [h0, one_mul] at h
  omega

/-- Asymptotic complexity of insertion sort recurrence: $O(n^2)$ under `Filter.atTop`. -/
theorem insertionSortRecBound_isBigO_sq :
    (fun n : ℕ ↦ ((insertionSortRecBound n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ)) := by
  have h_step : ∀ i, insertionSortRecBound (i + 1) ≤ insertionSortRecBound i + 1 * i := by
    intro i
    rw [insertionSortRecBound_step, one_mul]
  exact telescoping_linear_step_isBigO_sq 1 h_step

/-- Connection to concrete insertion sort: comparisons on list $l$ are bounded by the
telescoping recurrence bound `insertionSortRecBound l.length`. -/
theorem insertionSortCount_le_recBound {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (l : List α) :
    List.insertionSortCount r l ≤ insertionSortRecBound l.length := by
  induction l with
  | nil => simp [List.insertionSortCount, insertionSortRecBound]
  | cons a l ih =>
    simp only [List.insertionSortCount, List.length_cons]
    have h_ins := List.orderedInsertCount_le r a (List.insertionSort r l)
    have h_len : (List.insertionSort r l).length = l.length := List.length_insertionSort r l
    rw [h_len] at h_ins
    rw [insertionSortRecBound_step]
    omega

end Amort.Recurrence
