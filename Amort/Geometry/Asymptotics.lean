/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Geometry.ConvexHull
import Amort.Geometry.ClosestPair
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Computational Geometry

This module connects the concrete operational step bounds for computational geometry algorithms
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework:
- 2D Convex Hull via Andrew's monotone chain ($O(n \log n)$ operations).
- Closest Pair of Points divide-and-conquer ($O(n \log n)$ operations).

## Key Definitions and Theorems
- `Amort.Geometry.isBigO_convexHullWork_mul_size`: Convex hull operational work $O(n \log n)$.
- `Amort.Geometry.isBigO_closestPairWork_mul_size`: Closest pair operational work $O(n \log n)$.
-/

namespace Amort.Geometry

open Asymptotics

/-- Operational work of 2D Convex Hull is asymptotically $O(n \cdot \text{Nat.size } n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_convexHullWork_mul_size :
    (fun n : ℕ ↦ ((convexHullWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (5 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := convexHullWork_le n hn
  have h_real : (((convexHullWork n : ℕ) : ℝ) ≤ ((5 * n * Nat.size n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((5 * n * Nat.size n : ℕ) : ℝ) = 5 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

/-- Operational work of Closest Pair of Points is asymptotically $O(n \cdot \text{Nat.size } n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_closestPairWork_mul_size :
    (fun n : ℕ ↦ ((closestPairWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (9 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := closestPairWork_le n hn
  have h_real : (((closestPairWork n : ℕ) : ℝ) ≤ ((9 * n * Nat.size n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((9 * n * Nat.size n : ℕ) : ℝ) = 9 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

end Amort.Geometry
