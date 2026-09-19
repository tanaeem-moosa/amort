/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.LP.Simplex
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Linear Programming

This module connects the operational arithmetic step bounds for Linear Programming operations
(simplex pivot step and feasibility verification) to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO`
framework under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$:
1. Simplex pivot step work: $O(m \cdot n + m + n)$ arithmetic operations per pivot.
2. LP feasibility checking work: $O(m \cdot n + m + n)$ arithmetic operations.

## Key Theorems
- `Amort.LP.isBigO_simplexPivotWork_atTop`: Simplex pivot step is $O(m \cdot n + m + n)$.
- `Amort.LP.isBigO_lpFeasibilityWork_atTop`: LP feasibility check is $O(m \cdot n + m + n)$.
-/

open Asymptotics

namespace Amort.LP

/-- Simplex pivot operational step complexity is asymptotically $O(m \cdot n + m + n)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_simplexPivotWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((simplexPivotWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 * p.2 + p.1 + p.2 : ℕ) : ℝ))) :=
  isBigO_refl _ _

/-- LP feasibility verification operational complexity is asymptotically $O(m \cdot n + m + n)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_lpFeasibilityWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((lpFeasibilityWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 * p.2 + p.1 + p.2 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  rintro ⟨m, n⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [lpFeasibilityWork]
  have h : ((2 * (m * n + m + n) : ℕ) : ℝ) = 2 * ((m * n + m + n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h]

end Amort.LP
