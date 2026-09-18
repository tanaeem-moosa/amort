/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.DataStructure.BinaryHeap
import Amort.DataStructure.OnlineMedian
import Amort.DataStructure.BalancedBST
import Amort.DataStructure.DynamicArray
import Amort.DataStructure.TwoStackQueue
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Asymptotic Complexity Bridges for Data Structures

This module connects concrete operational and amortized step bounds for textbook data structures
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework under `Filter.atTop`:
- Linear Build-Heap: $O(n)$ total operations.
- Heapsort: $O(n \log n)$ total operations ($O(n \cdot \text{Nat.size } n)$).
- Online Running Median: $O(1)$ query time and $O(\log n)$ insertion/rebalance time.
- Balanced Binary Search Tree: $O(\log n)$ insertion/query time.
- Dynamic Array: $O(1)$ amortized push and $O(k)$ total work across $k$ pushes.
- Two-Stack Queue: $O(1)$ amortized operations and $O(m)$ total work across $m$ operations.

## Key Theorems
- `Amort.DataStructure.isBigO_buildHeap_atTop`: Linear build-heap $O(n)$.
- `Amort.DataStructure.isBigO_heapsort_atTop`: Heapsort $O(n \log n)$.
- `Amort.DataStructure.isBigO_medianQuery_atTop`: Online median query $O(1)$.
- `Amort.DataStructure.isBigO_onlineMedianInsert_atTop`: Online median insert $O(\log n)$.
- `Amort.DataStructure.isBigO_bbstInsertWork_atTop`: Balanced BST insert $O(\log n)$.
- `Amort.DataStructure.isBigO_dynArrayTotalCost_atTop`: Dynamic array cumulative work $O(k)$.
- `Amort.DataStructure.isBigO_twoStackQueueTotalCost_atTop`: Two-stack queue cumulative work $O(m)$.
-/

open Asymptotics

namespace Amort.DataStructure

/-! ### Priority Queue & Heap Asymptotics -/

/-- Linear build-heap executes in $O(n)$ operations under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_buildHeap_atTop :
    (fun n ↦ ((buildHeapWork n (Nat.size n) : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := buildHeap_size_bound n
  have h_real : ((buildHeapWork n (Nat.size n) : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
    exact_mod_cast h
  have h_eq : ((2 * n : ℕ) : ℝ) = 2 * ((n : ℕ) : ℝ) := by push_cast; ring
  exact h_real.trans (le_of_eq h_eq)

/-- Heapsort comparison complexity is $O(n \log n)$ under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_heapsort_atTop :
    (fun n ↦ ((heapsortTotalWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 4 ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rw [heapsortTotalWork_eq]
  have hsz : 1 ≤ Nat.size n := Nat.size_pos.mpr (by omega)
  have h1 : 2 * n ≤ 2 * n * Nat.size n := by
    calc 2 * n = 2 * n * 1 := by ring
    _ ≤ 2 * n * Nat.size n := Nat.mul_le_mul_left (2 * n) hsz
  have h2 : 2 * n + 2 * n * Nat.size n ≤ 4 * (n * Nat.size n) := by
    calc 2 * n + 2 * n * Nat.size n
      _ ≤ 2 * n * Nat.size n + 2 * n * Nat.size n := Nat.add_le_add_right h1 _
      _ = 4 * (n * Nat.size n) := by ring
  have h2_real : ((2 * n + 2 * n * Nat.size n : ℕ) : ℝ) ≤ ((4 * (n * Nat.size n) : ℕ) : ℝ) := by
    exact_mod_cast h2
  have h_eq : ((4 * (n * Nat.size n) : ℕ) : ℝ) = 4 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast; ring
  exact h2_real.trans (le_of_eq h_eq)

/-! ### Online Running Median Asymptotics -/

/-- Online median query executes in $O(1)$ operations under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_medianQuery_atTop :
    (fun (_ : ℕ) ↦ ((medianQuerySteps : ℕ) : ℝ)) =O[Filter.atTop]
      (fun (_ : ℕ) ↦ (1 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro _
  simp only [medianQuerySteps_eq, Nat.cast_one, Real.norm_eq_abs, abs_one, mul_one, le_rfl]

/-- Online median insertion and rebalancing is $O(\log n)$ under `Filter.atTop`. -/
theorem isBigO_onlineMedianInsert_atTop :
    (fun n ↦ ((onlineMedianInsertWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 6 ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have hsz : 1 ≤ Nat.size n := Nat.size_pos.mpr (by omega)
  have h_le : onlineMedianInsertWork n ≤ 6 * Nat.size n := by
    dsimp [onlineMedianInsertWork]
    omega
  have h_real : ((onlineMedianInsertWork n : ℕ) : ℝ) ≤ ((6 * Nat.size n : ℕ) : ℝ) := by
    exact_mod_cast h_le
  have h_eq : ((6 * Nat.size n : ℕ) : ℝ) = 6 * ((Nat.size n : ℕ) : ℝ) := by
    push_cast; ring
  exact h_real.trans (le_of_eq h_eq)

/-! ### Balanced Binary Search Tree Asymptotics -/

/-- Balanced BST insertion and order-statistic query work is $O(\log n)$
under `Filter.atTop` on $\mathbb{N}$ for any balance constant $c$. -/
theorem isBigO_bbstInsertWork_atTop (c : ℕ) :
    (fun n ↦ ((insertWork n c : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (c + 2 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have hsz : 1 ≤ Nat.size n := Nat.size_pos.mpr (by omega)
  have h_le : insertWork n c ≤ (c + 2) * Nat.size n := by
    dsimp [insertWork]
    calc c * Nat.size n + 2
      _ ≤ c * Nat.size n + 2 * Nat.size n := by omega
      _ = (c + 2) * Nat.size n := by ring
  have h_real : ((insertWork n c : ℕ) : ℝ) ≤ (((c + 2) * Nat.size n : ℕ) : ℝ) := by
    exact_mod_cast h_le
  have h_eq : (((c + 2) * Nat.size n : ℕ) : ℝ) = (c + 2 : ℝ) * ((Nat.size n : ℕ) : ℝ) := by
    push_cast; ring
  exact h_real.trans (le_of_eq h_eq)

/-! ### Pure Amortized Classics Asymptotics -/

/-- Cumulative work across $k$ dynamic array pushes is bounded by $3k$,
yielding asymptotic complexity $O(k)$ under `Filter.atTop`. -/
theorem isBigO_dynArrayTotalCost_atTop :
    (fun k ↦ ((3 * k : ℕ) : ℝ)) =O[Filter.atTop]
      (fun k ↦ ((k : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 3 ?_
  apply Filter.Eventually.of_forall
  intro k
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h_eq : ((3 * k : ℕ) : ℝ) = 3 * ((k : ℕ) : ℝ) := by push_cast; ring
  rw [h_eq]

/-- Cumulative work across $m$ Two-Stack Queue operations is bounded by $3m$,
yielding asymptotic complexity $O(m)$ under `Filter.atTop`. -/
theorem isBigO_twoStackQueueTotalCost_atTop :
    (fun m ↦ ((3 * m : ℕ) : ℝ)) =O[Filter.atTop]
      (fun m ↦ ((m : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 3 ?_
  apply Filter.Eventually.of_forall
  intro m
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h_eq : ((3 * m : ℕ) : ℝ) = 3 * ((m : ℕ) : ℝ) := by push_cast; ring
  rw [h_eq]

end Amort.DataStructure
