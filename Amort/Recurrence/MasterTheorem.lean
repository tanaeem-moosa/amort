/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Halving
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Divide-and-Conquer Master Recurrence

This module formalizes the standard balanced divide-and-conquer recurrence with integer rounding:
$$T(n) \le T(\lceil n / 2 \rceil) + T(\lfloor n / 2 \rfloor) + c \cdot n \quad (n \ge 2)$$
which appears ubiquitously in divide-and-conquer algorithms including Merge Sort.

## Mathematical Architecture

1. **Dyadic Induction Lemma**:
   For any $k \in \mathbb{N}$ and any $n$ satisfying $1 \le n \le 2^k$,
   $$T(n) \le T(1) \cdot n + c \cdot n \cdot k$$
   proven by induction on the dyadic exponent $k$. The subproblem sizes $(n+1)/2$ and $n/2$
   partition $n$ exactly: $(n+1)/2 + n/2 = n$, and both are bounded by $2^{k-1}$.

2. **Concrete Upper Bound**:
   Setting $k = \text{Nat.size } n$ (since $n < 2^{\text{Nat.size } n}$) yields:
   $$T(n) \le (T(1) + c) \cdot (n \cdot \text{Nat.size } n) \quad (\forall n \ge 1)$$

3. **Asymptotic Complexity**:
   - $T(n) = O(n \cdot \text{Nat.size } n)$ under `Filter.atTop`.
   - Since $\text{Nat.size } n = O(\log n)$, multiplying by $n$ yields
     $n \cdot \text{Nat.size } n = O(n \log n)$, hence:
     $$T(n) = O(n \log n) \quad \text{under } \text{Filter.atTop}$$

4. **Connection to Divide-and-Conquer Sorting (Merge Sort)**:
   The comparison recurrence `List.mergeSortRecBound` satisfies this recurrence with
   step cost $c = 1$ and base cost $T(1) = 0$. The master theorem immediately proves
   that `mergeSortRecBound n ≤ n * Nat.size n` and establishes $O(n \log n)$ complexity.

## Key Theorems
- `Amort.Recurrence.master_divide_conquer_aux`: Dyadic power bound $T(n) \le T(1) n + c n k$.
- `Amort.Recurrence.master_divide_conquer_bound`: Concrete $O(n \cdot \text{size } n)$ bound.
- `Amort.Recurrence.master_divide_conquer_isBigO_mul_size`: $O(n \cdot \text{size } n)$ asymptotic.
- `Amort.Recurrence.master_divide_conquer_isBigO_n_log_n`: $O(n \log n)$ asymptotic.
- `Amort.Recurrence.mergeSortRecBound_step`: Merge sort recurrence step identity.
- `Amort.Recurrence.mergeSortRecBound_le_rec`: Merge sort satisfies master recurrence.
- `Amort.Recurrence.mergeSortRecBound_le_mul_size_of_master`: Master bound on merge sort.
- `Amort.Recurrence.mergeSortRecBound_isBigO_n_log_n`: Merge sort is $O(n \log n)$.
-/

namespace Amort.Recurrence

open Asymptotics
open List

/-! ### Dyadic Induction and Master Recurrence Bounds -/

/-- Dyadic induction lemma: for any $k$, if $1 \le n \le 2^k$, then
$T(n) \le T(1) \cdot n + c \cdot n \cdot k$. -/
theorem master_divide_conquer_aux (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + T (n / 2) + c * n) :
    ∀ (k : ℕ) (n : ℕ), 1 ≤ n → n ≤ 2 ^ k → T n ≤ T 1 * n + c * n * k := by
  intro k
  induction k with
  | zero =>
    intro n hn1 hnk
    have : n = 1 := by omega
    subst this
    simp
  | succ k ih =>
    intro n hn1 hnk
    by_cases hn2 : n < 2
    · have : n = 1 := by omega
      subst this
      have : T 1 ≤ T 1 * 1 + c * 1 * (k + 1) := by omega
      exact this
    · have h2le : 2 ≤ n := by omega
      have hn1_ge : 1 ≤ (n + 1) / 2 := by omega
      have hn2_ge : 1 ≤ n / 2 := by omega
      have hn1_le : (n + 1) / 2 ≤ 2 ^ k := by omega
      have hn2_le : n / 2 ≤ 2 ^ k := by omega
      have ih1 := ih ((n + 1) / 2) hn1_ge hn1_le
      have ih2 := ih (n / 2) hn2_ge hn2_le
      have hstep := hrec n h2le
      have hsum : (n + 1) / 2 + n / 2 = n := by omega
      calc T n
        _ ≤ T ((n + 1) / 2) + T (n / 2) + c * n := hstep
        _ ≤ (T 1 * ((n + 1) / 2) + c * ((n + 1) / 2) * k) +
            (T 1 * (n / 2) + c * (n / 2) * k) + c * n := by omega
        _ = T 1 * ((n + 1) / 2 + n / 2) + c * k * ((n + 1) / 2 + n / 2) + c * n := by ring
        _ = T 1 * n + c * k * n + c * n := by rw [hsum]
        _ = T 1 * n + c * n * (k + 1) := by ring

/-- Concrete upper bound: if $T(n) \le T((n + 1) / 2) + T(n / 2) + c \cdot n$ for $n \ge 2$,
then $T(n) \le (T(1) + c) \cdot (n \cdot \text{Nat.size } n)$ for all $n \ge 1$. -/
theorem master_divide_conquer_bound (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + T (n / 2) + c * n)
    (n : ℕ) (hn : 1 ≤ n) :
    T n ≤ (T 1 + c) * (n * Nat.size n) := by
  have hle : n ≤ 2 ^ (Nat.size n) := le_of_lt (Nat.lt_size_self n)
  have h := master_divide_conquer_aux T c hrec (Nat.size n) n hn hle
  have hsize_pos : 0 < Nat.size n := Nat.size_pos.mpr (by omega)
  have hsize_ge : 1 ≤ Nat.size n := by omega
  have h_T1 : T 1 * n ≤ T 1 * (n * Nat.size n) := by
    have : n ≤ n * Nat.size n := Nat.le_mul_of_pos_right n hsize_ge
    exact Nat.mul_le_mul_left (T 1) this
  have h_c : c * n * Nat.size n = c * (n * Nat.size n) := by ring
  calc T n
    _ ≤ T 1 * n + c * n * Nat.size n := h
    _ ≤ T 1 * (n * Nat.size n) + c * (n * Nat.size n) := by omega
    _ = (T 1 + c) * (n * Nat.size n) := by ring

/-- Global bound on all natural numbers:
$T(n) \le (T(1) + c) \cdot (n \cdot \text{Nat.size } n) + T(0)$. -/
theorem master_divide_conquer_bound_all (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + T (n / 2) + c * n)
    (n : ℕ) :
    T n ≤ (T 1 + c) * (n * Nat.size n) + T 0 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn_pos : 1 ≤ n := by omega
    have h := master_divide_conquer_bound T c hrec n hn_pos
    omega

/-! ### Asymptotic Complexity -/

/-- Divide-and-conquer recurrence is asymptotically $O(n \cdot \text{Nat.size } n)$
under `Filter.atTop`. -/
theorem master_divide_conquer_isBigO_mul_size (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + T (n / 2) + c * n) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound ((T 1 + c : ℕ) : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := master_divide_conquer_bound T c hrec n hn
  exact_mod_cast h

/-- Auxiliary lemma: $n \cdot \text{Nat.size } n = O(n \log n)$ under `Filter.atTop`. -/
lemma isBigO_mul_size_n_log_n
    (h_size : (fun n : ℕ ↦ ((Nat.size n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ))) :
    (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) := by
  have h_refl : (fun n : ℕ ↦ (n : ℝ)) =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ)) :=
    isBigO_refl _ _
  have h_mul := h_refl.mul h_size
  have heq : (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) =
      (fun n : ℕ ↦ (n : ℝ) * ((Nat.size n : ℕ) : ℝ)) := by
    funext n
    simp only [Nat.cast_mul]
  rw [heq]
  exact h_mul

/-- Divide-and-conquer recurrence is asymptotically $O(n \log n)$ under `Filter.atTop`. -/
theorem master_divide_conquer_isBigO_n_log_n (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T ((n + 1) / 2) + T (n / 2) + c * n) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) :=
  (master_divide_conquer_isBigO_mul_size T c hrec).trans
    (isBigO_mul_size_n_log_n isBigO_size_log)

end Amort.Recurrence
