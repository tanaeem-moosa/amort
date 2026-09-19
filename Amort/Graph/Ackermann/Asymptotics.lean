/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Ackermann.PotentialBound
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Asymptotic Complexity Bridges for Tarjan's Inverse Ackermann Bound

This module connects the operational step bounds for Disjoint Set Union (DSU) with path
compression and union-by-rank to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` framework
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$:
1. Total work across $m$ operations on $n$ elements is $O((m + n) \cdot \alpha(n))$.
2. Bounded by $O(m \cdot \alpha(n))$ when operations dominate elements ($m \ge n$).

## Key Theorems
- `Amort.Graph.isBigO_dsuAckermannWork_atTop`: Total work is $O((m + n)(\alpha(n) + 1))$.
-/

open Asymptotics

namespace Amort.Graph

/-- Total DSU operational step complexity with path compression and union-by-rank is
asymptotically $O((m + n)(\alpha(n) + 1))$ under `Filter.atTop` on
$\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_dsuAckermannWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((dsuAckermannWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ ((((p.1 + p.2) * (invAck p.2 + 1) : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 6 ?_
  apply Filter.Eventually.of_forall
  rintro ⟨m, n⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [dsuAckermannWork]
  push_cast
  nlinarith

end Amort.Graph
