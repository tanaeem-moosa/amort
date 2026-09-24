/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Complexity.Classes
import Amort.Complexity.TwoSAT
import Amort.Complexity.KarpReductions
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Complexity Classes and Reductions

> **Status: stub — not verified** (Phase 4 canon stub; gadget size formulas are proven,
> but Turing reduction bounds are specification stubs).

This module connects concrete operational step counts and problem size bounds to
Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework under `Filter.atTop`:
1. 2-SAT linear-time operational complexity $O(|V| + |E|) = O(n + m)$.
2. Canonical polynomial growth function `polyEval c k n` is $O((n+1)^k)$ under `Filter.atTop`.
3. 3-SAT to Independent Set gadget graph size bounds:
   - Vertex size $3m$ is $O(m)$.
   - Edge bound $3m + 5m^2$ is $O(m^2)$.
4. Complement graph edge complexity bound is $O(n^2)$.

## Key Definitions and Theorems
- `Amort.Complexity.isBigO_twoSATWork_atTop`: 2-SAT linear complexity in `IsBigO`.
- `Amort.Complexity.isBigO_polyEval_atTop`: Polynomial growth in `IsBigO`.
- `Amort.Complexity.isBigO_sat3ToIS_vertices_atTop`: Gadget vertex count is $O(m)$.
- `Amort.Complexity.sat3ToISEdgeBound`: Upper bound on clause gadget and conflict edges.
- `Amort.Complexity.isBigO_sat3ToIS_edges_atTop`: Gadget edge count is $O(m^2)$.
- `Amort.Complexity.isBigO_complementEdges_atTop`: Complement graph size is $O(n^2)$.
-/

open Asymptotics

namespace Amort.Complexity

/-! ### 2-SAT Linear-Time Operational Asymptotics -/

/-- **Stub Model**: 2-SAT SCC decomposition operational step count is asymptotically $O(n + m)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_twoSATWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((twoSATBound p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 + p.2 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 6 ?_
  apply Filter.Eventually.of_forall
  rintro ⟨n, m⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rw [twoSAT_work_eq]
  have h_le : 5 * n + 6 * m ≤ 6 * (n + m) := by omega
  have h_cast : (((5 * n + 6 * m : ℕ) : ℝ)) ≤ (((6 * (n + m) : ℕ) : ℝ)) := by
    exact Nat.cast_le.mpr h_le
  have h_mul : (((6 * (n + m) : ℕ) : ℝ)) = 6 * (((n + m : ℕ) : ℝ)) := by
    push_cast
    ring
  rwa [h_mul] at h_cast

/-! ### Polynomial Growth Bounds in Mathlib Asymptotics -/

/-- **Stub Model**: The canonical polynomial bound `polyEval c k n = c * (n + 1) ^ k` is
asymptotically $O((n + 1)^k)$ under `Filter.atTop`. -/
theorem isBigO_polyEval_atTop (c k : ℕ) :
    (fun (n : ℕ) ↦ (((polyEval c k n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ (((n + 1 : ℕ) : ℝ) ^ k)) := by
  refine IsBigO.of_bound (c : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [polyEval]
  have h_cast : (((c * (n + 1) ^ k : ℕ) : ℝ)) = (c : ℝ) * (((n + 1 : ℕ) : ℝ) ^ k) := by
    push_cast
    ring
  rw [h_cast]
  have h_pos : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ k) := by positivity
  rw [abs_eq_self.mpr h_pos]

/-! ### 3-SAT to Independent Set Gadget Size Asymptotics -/

/-- **Stub Model**: The number of vertices in the 3-SAT to Independent Set gadget graph ($3m$)
is asymptotically $O(m)$ under `Filter.atTop`. -/
theorem isBigO_sat3ToIS_vertices_atTop :
    (fun (m : ℕ) ↦ (((3 * m : ℕ) : ℝ))) =O[Filter.atTop]
      (fun m ↦ (((m : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 3 ?_
  apply Filter.Eventually.of_forall
  intro m
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  push_cast
  ring_nf
  rfl

/-- **Stub Model**:
Concrete upper bound on the number of edges in the 3-SAT to Independent Set gadget graph:
$3m$ clause triangle edges plus at most $\binom{3m}{2} \le 5m^2$ conflict edges. -/
def sat3ToISEdgeBound (m : ℕ) : ℕ := 3 * m + 5 * m ^ 2

/-- The number of edges in the 3-SAT to Independent Set gadget graph is asymptotically
$O(m^2)$ under `Filter.atTop`. -/
theorem isBigO_sat3ToIS_edges_atTop :
    (fun (m : ℕ) ↦ (((sat3ToISEdgeBound m : ℕ) : ℝ))) =O[Filter.atTop]
      (fun m ↦ (((m ^ 2 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 8 ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun m hm ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [sat3ToISEdgeBound]
  have hm_le : 3 * m ≤ 3 * m ^ 2 := by
    have : m ≤ m ^ 2 := by
      nlinarith
    omega
  have h_tot : 3 * m + 5 * m ^ 2 ≤ 8 * m ^ 2 := by omega
  have h_cast : (((3 * m + 5 * m ^ 2 : ℕ) : ℝ)) ≤ (((8 * m ^ 2 : ℕ) : ℝ)) := by
    exact Nat.cast_le.mpr h_tot
  have h_mul : (((8 * m ^ 2 : ℕ) : ℝ)) = 8 * (((m ^ 2 : ℕ) : ℝ)) := by
    push_cast
    ring
  rwa [h_mul] at h_cast

/-! ### Complement Graph Edge Complexity Asymptotics -/

/-- **Stub Model**:
Upper bound on the number of edges in the complement graph $\overline{G}$ on $n$ vertices:
at most $n^2$ edges. -/
def complementEdgeBound (n : ℕ) : ℕ := n ^ 2

/-- The complement graph edge complexity is asymptotically $O(n^2)$ under `Filter.atTop`. -/
theorem isBigO_complementEdges_atTop :
    (fun (n : ℕ) ↦ (((complementEdgeBound n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ (((n ^ 2 : ℕ) : ℝ))) := by
  dsimp [complementEdgeBound]
  exact isBigO_refl _ _

end Amort.Complexity
