/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Ackermann.PotentialBound
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Theta
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Asymptotic Complexity Bridges for Tarjan's Strict Inverse Ackermann Bound

This module connects the operational step bounds for Disjoint Set Union (DSU) with path
compression and union-by-rank to Mathlib's `Mathlib.Analysis.Asymptotics` framework
(`IsBigO` and `IsTheta`) under `Filter.atTop`:
1. **Upper Bound**: Total work across $m$ operations on $n$ elements is
   $O((m + n) \cdot \alpha(n))$.
2. **Matching Lower Bound**: Total work is $\Omega((m + n) \cdot \alpha(n))$.
3. **Strict Asymptotic Equivalence**: Work is strictly $\Theta((m + n) \cdot (\alpha(n) + 1))$.
4. **Diagonal Tight Bound**: For $n$ operations on $n$ elements, work is strictly
   $\Theta(n \cdot (\alpha(n) + 1))$.

## Key Theorems
- `Amort.Graph.isBigO_dsuAckermannWork_atTop`: Total work is $O((m + n)(\alpha(n) + 1))$.
- `Amort.Graph.isBigO_combined_dsuAckermannWork_atTop`:
  Lower bound $\Omega((m + n)(\alpha(n) + 1))$.
- `Amort.Graph.isTheta_dsuAckermannWork_atTop`: Strict $\Theta((m + n)(\alpha(n) + 1))$.
- `Amort.Graph.isTheta_dsuAckermannDiag`: Diagonal work is strictly $\Theta(n(\alpha(n) + 1))$.
-/

open Asymptotics

namespace Amort.Graph

/-! ### Two-Variable Asymptotic Bounds ($m$ Operations on $n$ Elements) -/

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

/-- **Matching Operational Lower Bound**:
$((m + n)(\alpha(n) + 1))$ is asymptotically bounded by total DSU work under
`Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ ($\Omega((m + n)\alpha(n))$). -/
theorem isBigO_combined_dsuAckermannWork_atTop :
    (fun (p : ℕ × ℕ) ↦ ((((p.1 + p.2) * (invAck p.2 + 1) : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((dsuAckermannWork p.1 p.2 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  rintro ⟨m, n⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := dsuAckermannWork_ge_combined m n
  have h_cast : (((m + n) * (invAck n + 1) : ℕ) : ℝ) ≤ ((dsuAckermannWork m n : ℕ) : ℝ) :=
    Nat.cast_le.mpr h
  calc (((m + n) * (invAck n + 1) : ℕ) : ℝ)
      ≤ ((dsuAckermannWork m n : ℕ) : ℝ) := h_cast
    _ = 1 * ((dsuAckermannWork m n : ℕ) : ℝ) := by ring

/-- **Strict Asymptotic Tight Bound ($\Theta((m + n)\alpha(n))$)**:
The operational step complexity of Disjoint Set Union with path compression and union-by-rank
is strictly $\Theta((m + n)(\alpha(n) + 1))$ under `Filter.atTop` on
$\mathbb{N} \times \mathbb{N}$. -/
theorem isTheta_dsuAckermannWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((dsuAckermannWork p.1 p.2 : ℕ) : ℝ))) =Θ[Filter.atTop]
      (fun p ↦ ((((p.1 + p.2) * (invAck p.2 + 1) : ℕ) : ℝ))) :=
  ⟨isBigO_dsuAckermannWork_atTop, isBigO_combined_dsuAckermannWork_atTop⟩

/-! ### Diagonal Complexity: $n$ Operations on $n$ Elements -/

/-- Diagonal operational step complexity for $n$ operations on $n$ elements:
$\text{dsuAckermannDiag}(n) = \text{dsuAckermannWork}(n, n) = 6n(\alpha(n) + 1)$. -/
def dsuAckermannDiag (n : ℕ) : ℕ :=
  dsuAckermannWork n n

/-- Closed-form identity for diagonal work: $6n(\alpha(n) + 1)$. -/
theorem dsuAckermannDiag_eq (n : ℕ) :
    dsuAckermannDiag n = 6 * n * (invAck n + 1) := by
  dsimp [dsuAckermannDiag, dsuAckermannWork]
  ring

/-- Upper bound on diagonal operational step complexity ($O(n(\alpha(n) + 1))$). -/
theorem isBigO_dsuAckermannDiag_upper :
    (fun n : ℕ ↦ (((dsuAckermannDiag n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ (((n * (invAck n + 1) : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 6 ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rw [dsuAckermannDiag_eq]
  push_cast
  linarith

/-- Lower bound on diagonal operational step complexity ($\Omega(n(\alpha(n) + 1))$). -/
theorem isBigO_dsuAckermannDiag_lower :
    (fun n : ℕ ↦ (((n * (invAck n + 1) : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ (((dsuAckermannDiag n : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rw [dsuAckermannDiag_eq]
  push_cast
  have : (n * (invAck n + 1) : ℝ) ≤ 6 * (n * (invAck n + 1) : ℝ) := by
    have : 0 ≤ (n * (invAck n + 1) : ℝ) := by positivity
    linarith
  linarith

/-- **Strict Diagonal Tight Bound ($\Theta(n \cdot \alpha(n))$)**:
For $n$ operations on $n$ elements, DSU complexity with path compression and union-by-rank
is strictly $\Theta(n(\alpha(n) + 1))$ under `Filter.atTop`. -/
theorem isTheta_dsuAckermannDiag :
    (fun n : ℕ ↦ (((dsuAckermannDiag n : ℕ) : ℝ))) =Θ[Filter.atTop]
      (fun n ↦ (((n * (invAck n + 1) : ℕ) : ℝ))) :=
  ⟨isBigO_dsuAckermannDiag_upper, isBigO_dsuAckermannDiag_lower⟩

end Amort.Graph
