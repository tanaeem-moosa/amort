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
# Binary Search Recurrence and Complexity Bounds

This module formalizes step counting and asymptotic complexity for binary search algorithms.
Binary search decreases the problem search interval by a factor of 2 at each step,
satisfying the halving recurrence $T(n) \le T(n / 2) + 1$ for $n \ge 2$.

## Mathematical Architecture

1. **Representative Step Counter**:
   We define `binarySearchSteps : ℕ → ℕ` modeling the worst-case number of comparisons
   required to locate an element or determine its absence in a sorted range of size $n$:
   - $T(0) = 0$
   - $T(1) = 1$
   - $T(n) = 1 + T(n / 2)$ for $n \ge 2$

2. **Halving Recurrence Satisfaction**:
   For any $n \ge 2$, `binarySearchSteps n ≤ binarySearchSteps (n / 2) + 1`.
   Consequently, binary search directly instantiates the general halving recurrence
   with step cost $c = 1$.

3. **Concrete Bounds**:
   - `binarySearchSteps_le_bound`: $T(n) \le \text{Nat.size } n + 1$ for $n \ge 1$
     via the general halving theorem.
   - `binarySearchSteps_le_size`: $T(n) \le \text{Nat.size } n$ for all $n \in \mathbb{N}$
     by induction on bit length.

4. **Asymptotic Complexity**:
   - `binarySearchSteps_isBigO_size`: $T(n) = O(\text{Nat.size } n)$ under `Filter.atTop`.
   - `binarySearchSteps_isBigO_log`: $T(n) = O(\log n)$ under `Filter.atTop`.

## Key Theorems
- `Amort.Recurrence.binarySearchSteps_step`: Exact halving recurrence step relation.
- `Amort.Recurrence.binarySearchSteps_le_halving`: Halving recurrence inequality ($c = 1$).
- `Amort.Recurrence.binarySearchSteps_le_bound`: Bounded by $\text{Nat.size } n + 1$ for $n \ge 1$.
- `Amort.Recurrence.binarySearchSteps_le_size`:
  Exact bit-size upper bound for all $n \in \mathbb{N}$.
- `Amort.Recurrence.binarySearchSteps_isBigO_size`: $O(\text{Nat.size } n)$ under `Filter.atTop`.
- `Amort.Recurrence.binarySearchSteps_isBigO_log`: $O(\log n)$ under `Filter.atTop`.
-/

namespace Amort.Recurrence

open Asymptotics

/-! ### Binary Search Step Counter -/

/-- Worst-case comparison counter for binary search on an interval or list of size $n$. -/
def binarySearchSteps : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 1 + binarySearchSteps ((n + 2) / 2)

@[simp]
theorem binarySearchSteps_zero : binarySearchSteps 0 = 0 := by
  unfold binarySearchSteps
  rfl

@[simp]
theorem binarySearchSteps_one : binarySearchSteps 1 = 1 := by
  unfold binarySearchSteps
  rfl

/-- Binary search step count satisfies the exact halving recurrence for $n \ge 2$. -/
theorem binarySearchSteps_step (n : ℕ) (hn : 2 ≤ n) :
    binarySearchSteps n = binarySearchSteps (n / 2) + 1 := by
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 =>
    rw [binarySearchSteps]
    omega

/-- Binary search step count satisfies the halving recurrence inequality with $c = 1$. -/
theorem binarySearchSteps_le_halving (n : ℕ) (hn : 2 ≤ n) :
    binarySearchSteps n ≤ binarySearchSteps (n / 2) + 1 := by
  rw [binarySearchSteps_step n hn]

/-! ### Concrete Upper Bounds -/

/-- Concrete upper bound: binary search steps bounded by $\text{Nat.size } n + 1$
via the general halving recurrence theorem. -/
theorem binarySearchSteps_le_bound (n : ℕ) (hn : 1 ≤ n) :
    binarySearchSteps n ≤ Nat.size n + 1 := by
  have h := halving_recurrence_bound binarySearchSteps 1 binarySearchSteps_le_halving n hn
  have h1 := binarySearchSteps_one
  rw [h1, one_mul] at h
  exact h

/-- Concrete bit-size upper bound: binary search steps are at most $\text{Nat.size } n$
for all $n \in \mathbb{N}$. -/
theorem binarySearchSteps_le_size (n : ℕ) :
    binarySearchSteps n ≤ Nat.size n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [binarySearchSteps_zero]
      simp
    | 1 =>
      rw [binarySearchSteps_one]
      simp
    | n + 2 =>
      rw [binarySearchSteps]
      have hdiv_lt : (n + 2) / 2 < n + 2 := by omega
      have ih_div := ih ((n + 2) / 2) hdiv_lt
      have h_size : Nat.size ((n + 2) / 2) = Nat.size (n + 2) - 1 := size_div_two (n + 2)
      have h_size_ge : 2 ≤ Nat.size (n + 2) := size_ge_two_of_ge_two (by omega)
      omega

/-! ### Asymptotic Complexity -/

/-- Binary search comparison count is asymptotically $O(\text{Nat.size } n)$
under `Filter.atTop`. -/
theorem binarySearchSteps_isBigO_size :
    (fun n : ℕ ↦ ((binarySearchSteps n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((Nat.size n : ℕ) : ℝ)) :=
  halving_recurrence_isBigO_size binarySearchSteps 1 binarySearchSteps_le_halving

/-- Binary search comparison count is asymptotically $O(\log n)$
under `Filter.atTop`. -/
theorem binarySearchSteps_isBigO_log :
    (fun n : ℕ ↦ ((binarySearchSteps n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ Real.log (n : ℝ)) :=
  halving_recurrence_isBigO_log binarySearchSteps 1 binarySearchSteps_le_halving

end Amort.Recurrence
