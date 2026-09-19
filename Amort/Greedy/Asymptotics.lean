/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Greedy.IntervalScheduling
import Amort.Greedy.Huffman
import Amort.Greedy.MedianOfMedians
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Greedy Algorithms & Linear Selection

This module connects the concrete operational step bounds for greedy algorithms and linear
selection to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework:
- Interval Scheduling ($O(n \log n)$ operations dominated by sorting).
- Huffman Coding ($O(n \log n)$ operations via priority queue / binary min-heap).
- Median-of-Medians BFPRT Selection ($O(n)$ linear time deterministic selection).

## Key Definitions and Theorems
- `Amort.Greedy.isBigO_intervalSchedulingWork_mul_size`: Interval scheduling O(n log n).
- `Amort.Greedy.isBigO_huffmanConstructionWork_mul_size`: Huffman construction O(n log n).
- `Amort.Greedy.isBigO_bfprt_linear_atTop`: BFPRT linear recurrence $O(n)$ in `IsBigO`.
-/

namespace Amort.Greedy

open Asymptotics

/-- Operational work of interval scheduling is asymptotically $O(n \cdot \text{Nat.size } n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_intervalSchedulingWork_mul_size :
    (fun n : ℕ ↦ ((intervalSchedulingWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (2 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := intervalSchedulingWork_le n hn
  have h_real : (((intervalSchedulingWork n : ℕ) : ℝ) ≤ ((2 * n * Nat.size n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((2 * n * Nat.size n : ℕ) : ℝ) = 2 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

/-- Operational work of Huffman tree construction is asymptotically $O(n \cdot \text{Nat.size } n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_huffmanConstructionWork_mul_size :
    (fun n : ℕ ↦ ((huffmanConstructionWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (7 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := huffmanConstructionWork_le n hn
  have h_real : (((huffmanConstructionWork n : ℕ) : ℝ) ≤ ((7 * n * Nat.size n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((7 * n * Nat.size n : ℕ) : ℝ) = 7 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

/-- Any algorithm satisfying the BFPRT divide-and-conquer recurrence has linear asymptotic
complexity $O(n)$ under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_bfprt_linear_atTop (T : ℕ → ℕ) (c B : ℕ)
    (hrec : BFPRTRecurrence T c)
    (hbase : ∀ n, 1 ≤ n → n < 140 → T n ≤ B * n) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop] (fun n : ℕ ↦ ((n : ℕ) : ℝ)) := by
  let C := max B (30 * c)
  refine IsBigO.of_bound ((C : ℕ) : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := bfprt_linear_bound T c B hrec hbase n hn
  have h_real : (((T n : ℕ) : ℝ) ≤ ((C * n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((C * n : ℕ) : ℝ) = ((C : ℕ) : ℝ) * ((n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

end Amort.Greedy
