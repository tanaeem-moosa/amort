/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.DP.Knapsack
import Amort.DP.LIS
import Amort.DP.MatrixChain
import Amort.Recurrence.Composition
import Amort.Recurrence.DP
import Amort.String.Asymptotics
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Prod

/-!
# Asymptotic Complexity Bridges for Dynamic Programming Algorithms

This module establishes formal asymptotic complexity bounds in Mathlib's
`Mathlib.Analysis.Asymptotics.IsBigO` framework for dynamic programming algorithms:
- Interval DP: Matrix Chain Multiplication ($O(n^3)$ operations).
- Grid DP: 0/1 Knapsack Problem ($O(n \cdot W)$ operations).
- State-Space DP: Longest Increasing Subsequence ($O(n^2)$ operations).

## Mathematical Architecture

1. **Interval DP Asymptotics**:
   The interval state space of size $\le n^2$ combined with $O(n)$ local work per interval
   yields total work bounded by $n^3$, proving $O(n^3)$ under `Filter.atTop` on $\mathbb{N}$.

2. **Grid DP Asymptotics**:
   The $(n + 1) \times (W + 1)$ grid DP table size is bounded by $(n + 1)(W + 1)$.
   Composing with `Amort.String.isBigO_succ_mul_succ_atTop` establishes $O(n \cdot W)$
   under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.

3. **Predecessor State-Space Asymptotics**:
   State space $\text{Fin } n$ with predecessor checking cost $i \le n$ yields total work
   bounded by $n^2$, proving $O(n^2)$ under `Filter.atTop` on $\mathbb{N}$.
-/

namespace Amort.DP

open Asymptotics
open Amort.Recurrence

/-! ### Matrix Chain Multiplication Asymptotics -/

/-- Total work of Matrix Chain Multiplication interval DP is asymptotically $O(n^3)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_matrixChainDP_totalCost_atTop :
    (fun n ↦ (((matrixChainDP n).totalCost : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n ^ 3 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := matrixChainDP_totalCost_le n
  exact_mod_cast h

/-! ### 0/1 Knapsack Grid DP Asymptotics -/

/-- Total work of 0/1 Knapsack grid DP is bounded by $(n + 1)(W + 1)$ under any filter. -/
theorem isBigO_knapsackGridDP_totalCost_succ_mul_atTop (l : Filter (ℕ × ℕ)) :
    (fun (p : ℕ × ℕ) ↦ (((knapsackGridDP p.1 p.2).toDPModel.totalCost : ℕ) : ℝ)) =O[l]
      (fun p ↦ (((p.1 + 1) * (p.2 + 1) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro ⟨n, W⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := knapsackGridDP_totalCost_le n W
  exact_mod_cast h

/-- Total work of 0/1 Knapsack grid DP is asymptotically $O(n \cdot W)$ under `Filter.atTop`
on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_knapsackGridDP_totalCost_atTop :
    (fun (p : ℕ × ℕ) ↦ (((knapsackGridDP p.1 p.2).toDPModel.totalCost : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 * p.2 : ℕ) : ℝ)) := by
  have h1 := isBigO_knapsackGridDP_totalCost_succ_mul_atTop Filter.atTop
  have h2 := Amort.String.isBigO_succ_mul_succ_atTop
  exact h1.trans h2

/-! ### Longest Increasing Subsequence Asymptotics -/

/-- Total work of the LIS state-space DP is asymptotically $O(n^2)$ under `Filter.atTop`
on $\mathbb{N}$. -/
theorem isBigO_lisDP_totalCost_atTop :
    (fun n ↦ (((lisDP n).totalCost : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n ^ 2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := lisDP_totalCost_le_sq n
  exact_mod_cast h

end Amort.DP
