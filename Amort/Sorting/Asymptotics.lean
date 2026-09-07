/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Sorting.InsertionSort
import Amort.Sorting.MergeSort
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic Complexity Bounds for Sorting Algorithms

This module connects concrete comparison bounds for Insertion Sort and Merge Sort to
Mathlib's asymptotic complexity framework `Mathlib.Analysis.Asymptotics.IsBigO`.

## Mathematical Context
- For Insertion Sort, comparisons are pointwise bounded by `l.length ^ 2` everywhere on
  `List α`. Because the bound holds with constant `c = 1`, the asymptotic relation holds
  with respect to any filter `F` on `List α`, and in particular under the pullback filter
  `Filter.comap List.length Filter.atTop`.
- For Merge Sort, comparisons are pointwise bounded by `l.length * Nat.size l.length`
  everywhere on `List α`. Pointwise bounding with constant `c = 1` yields asymptotic
  `IsBigO` complexity under any filter `F` on `List α`,
  under `Filter.comap List.length Filter.atTop`,
  and for the divide-and-conquer recurrence bound on `ℕ` under `Filter.atTop`.

## Key Theorems
- `List.isBigO_insertionSortCount_sq`: Insertion sort comparisons are `O(length ^ 2)`
  under any filter `F` on `List α`.
- `List.isBigO_insertionSortCount_atTop`: Insertion sort comparisons are `O(length ^ 2)`
  under `Filter.comap List.length Filter.atTop`.
- `List.isBigO_insertionSortWithCount_snd_atTop`: Instrumented insertion sort comparisons
  are `O(length ^ 2)`.
- `List.isBigO_insertionSort_triangular_atTop`: The triangular bound `n * (n - 1) / 2`
  is `O(n ^ 2)` under `Filter.atTop` on `ℕ`.
- `List.isBigO_mergeSortCount_mul_size`: Merge sort comparisons are `O(n * Nat.size n)`
  under any filter `F` on `List α`.
- `List.isBigO_mergeSortCount_atTop`: Merge sort comparisons are `O(n * Nat.size n)`
  under `Filter.comap List.length Filter.atTop`.
- `List.isBigO_mergeSortWithCount_snd_atTop`: Instrumented merge sort comparisons are
  `O(n * Nat.size n)`.
- `List.isBigO_mergeSortRecBound_atTop`: Recurrence bound on `ℕ` is `O(n * Nat.size n)`
  under `Filter.atTop`.
-/

namespace List

open Asymptotics

/-! ### Insertion Sort Asymptotics -/

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- Insertion sort comparison count is asymptotically `O(l.length ^ 2)` with respect to
an arbitrary filter `F` on `List α`. -/
theorem isBigO_insertionSortCount_sq (F : Filter (List α)) :
    (fun l : List α ↦ ((insertionSortCount r l : ℕ) : ℝ)) =O[F]
    (fun l : List α ↦ ((l.length ^ 2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro l
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := insertionSortCount_le_sq r l
  exact_mod_cast h

/-- Insertion sort comparison count is asymptotically `O(l.length ^ 2)` under
`Filter.comap List.length Filter.atTop`. -/
theorem isBigO_insertionSortCount_atTop :
    (fun l : List α ↦ ((insertionSortCount r l : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length ^ 2 : ℕ) : ℝ)) :=
  isBigO_insertionSortCount_sq r _

/-- Instrumented insertion sort comparison count is asymptotically `O(l.length ^ 2)`
under `Filter.comap List.length Filter.atTop`. -/
theorem isBigO_insertionSortWithCount_snd_atTop :
    (fun l : List α ↦ (((insertionSortWithCount r l).2 : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length ^ 2 : ℕ) : ℝ)) := by
  have heq : (fun l : List α ↦ (((insertionSortWithCount r l).2 : ℕ) : ℝ)) =
      (fun l : List α ↦ ((insertionSortCount r l : ℕ) : ℝ)) := by
    funext l
    rw [insertionSortWithCount_snd]
  rw [heq]
  exact isBigO_insertionSortCount_atTop r

/-- The concrete triangular comparison bound `n * (n - 1) / 2` is `O(n ^ 2)` under
`Filter.atTop` on `ℕ`. -/
theorem isBigO_insertionSort_triangular_atTop :
    (fun n : ℕ ↦ ((n * (n - 1) / 2 : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h_div : n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ 2
  have h_mul : n * (n - 1) ≤ n * n := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h_sq : n * n = n ^ 2 := by ring
  have h : n * (n - 1) / 2 ≤ n ^ 2 := by omega
  exact_mod_cast h

/-! ### Merge Sort Asymptotics -/

/-- Merge sort comparison count is asymptotically `O(l.length * Nat.size l.length)` with
respect to an arbitrary filter `F` on `List α`. -/
theorem isBigO_mergeSortCount_mul_size (le : α → α → Bool) (F : Filter (List α)) :
    (fun l : List α ↦ ((mergeSortCount le l : ℕ) : ℝ)) =O[F]
    (fun l : List α ↦ ((l.length * Nat.size l.length : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro l
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := mergeSortCount_le_mul_size le l
  exact_mod_cast h

/-- Merge sort comparison count is asymptotically `O(l.length * Nat.size l.length)` under
`Filter.comap List.length Filter.atTop`. -/
theorem isBigO_mergeSortCount_atTop (le : α → α → Bool) :
    (fun l : List α ↦ ((mergeSortCount le l : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length * Nat.size l.length : ℕ) : ℝ)) :=
  isBigO_mergeSortCount_mul_size le _

/-- Instrumented merge sort comparison count is asymptotically `O(l.length * Nat.size l.length)`
under `Filter.comap List.length Filter.atTop`. -/
theorem isBigO_mergeSortWithCount_snd_atTop (le : α → α → Bool) :
    (fun l : List α ↦ (((mergeSortWithCount le l).2 : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length * Nat.size l.length : ℕ) : ℝ)) := by
  have heq : (fun l : List α ↦ (((mergeSortWithCount le l).2 : ℕ) : ℝ)) =
      (fun l : List α ↦ ((mergeSortCount le l : ℕ) : ℝ)) := by
    funext l
    rw [mergeSortWithCount_snd]
  rw [heq]
  exact isBigO_mergeSortCount_atTop le

/-- The merge sort divide-and-conquer recurrence bound on `ℕ` is asymptotically
`O(n * Nat.size n)` under `Filter.atTop`. -/
theorem isBigO_mergeSortRecBound_atTop :
    (fun n : ℕ ↦ ((mergeSortRecBound n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := mergeSortRecBound_le_mul_size n
  exact_mod_cast h

end List
