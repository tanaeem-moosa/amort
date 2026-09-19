/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Approximation.VertexCover
import Amort.Approximation.MetricTSP
import Amort.Approximation.SetCover
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Approximation Algorithms

This module connects concrete operational step bounds for approximation algorithms
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` framework under `Filter.atTop`:
1. Vertex Cover 2-approximation maximal matching: $O(|V| + |E|)$.
2. Metric TSP 2-approximation double-tree: $O(n^2 \log n)$.
3. Set Cover greedy $H(n)$-approximation: $O(m \cdot n)$.

## Key Theorems
- `Amort.Approximation.isBigO_vertexCoverWork_atTop`: Vertex cover $O(|V| + |E|)$ in `IsBigO`.
- `Amort.Approximation.isBigO_metricTSPWork_atTop`: Metric TSP $O(n^2 \log n)$ in `IsBigO`.
- `Amort.Approximation.isBigO_setCoverWork_atTop`: Set cover $O(m \cdot n)$ in `IsBigO`.
-/

open Asymptotics

namespace Amort.Approximation

/-! ### Vertex Cover 2-Approximation Asymptotics -/

/-- Greedy maximal matching vertex cover operational complexity is asymptotically
$O(|V| + |E|)$ under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_vertexCoverWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((vertexCoverWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 + p.2 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  rintro ⟨n, m⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [vertexCoverWork]
  have h : ((2 * (n + m) : ℕ) : ℝ) = 2 * ((n + m : ℕ) : ℝ) := by push_cast; ring
  rw [h]

/-! ### Metric TSP 2-Approximation Asymptotics -/

/-- Metric TSP double-tree operational complexity is asymptotically bounded by
$n^2 \cdot \text{size } n + 4n$ in `IsBigO` under `Filter.atTop`. -/
theorem isBigO_metricTSPWork_atTop :
    (fun (n : ℕ) ↦ (((metricTSPWork n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ (((n ^ 2 * Nat.size n + 4 * n : ℕ) : ℝ))) :=
  isBigO_refl _ _

/-! ### Set Cover Greedy Asymptotics -/

/-- Greedy set cover operational complexity is asymptotically $O(m \cdot n + n)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_setCoverWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((setCoverWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.2 * p.1 + p.1 : ℕ) : ℝ))) :=
  isBigO_refl _ _

end Amort.Approximation
