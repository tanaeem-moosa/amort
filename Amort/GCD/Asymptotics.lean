/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.StepCount
import Amort.GCD.EuclideanGCD
import Mathlib.Analysis.Asymptotics.Defs

/-!
# Asymptotic Complexity Bounds for GCD Algorithms

This module connects the concrete step bounds of both Binary GCD (Stein's algorithm)
and the standard Euclidean algorithm to Mathlib's asymptotic complexity framework
`Mathlib.Analysis.Asymptotics.IsBigO`.

## Mathematical Context
For Binary GCD, `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)` holds everywhere on `ℕ × ℕ`.
Because the bound holds pointwise with constant `c = 2`, the asymptotic `IsBigO`
relation holds with respect to *any* filter `l` on `ℕ × ℕ`, and in particular under
`Filter.atTop` and the `Filter.comap` filters corresponding to combined input measures.

For Euclidean GCD, `euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1` implies that
whenever inputs are bounded away from zero (as occurs eventually under `Filter.atTop`
or under `Filter.comap` towards `atTop`), the step count is bounded by `3 * Nat.size ...`,
yielding idiomatic `IsBigO` complexity theorems.

## Key Theorems
- `Nat.isBigO_binaryGcdSteps_size_add`: Binary GCD step count is `O(size (a + b))`
  under any filter `l`.
- `Nat.isBigO_binaryGcdSteps_size_add_size`: Binary GCD step count is
  `O(size a + size b)` under any filter `l`.
- `Nat.isBigO_binaryGcdSteps_atTop`: Binary GCD step count is `O(size (a + b))`
  under `Filter.atTop`.
- `Nat.isBigO_binaryGcdSteps_comap_add_atTop`: Binary GCD step count is `O(size (a + b))`
  under `Filter.comap (fun p ↦ p.1 + p.2) Filter.atTop`.
- `Nat.isBigO_binaryGcdSteps_comap_size_atTop`: Binary GCD step count is `O(size (a + b))`
  under `Filter.comap (fun p ↦ Nat.size (p.1 + p.2)) Filter.atTop`.
- `Nat.isBigO_binaryGcdWithSteps_snd_size_add`: Instrumented step count is `O(size (a + b))`
  under any filter `l`.
- `Nat.isBigO_euclideanGcdSteps_atTop`: Euclidean GCD step count is `O(size (min a b))`
  under `Filter.atTop`.
- `Nat.isBigO_euclideanGcdSteps_comap_min_atTop`: Euclidean GCD step count is `O(size (min a b))`
  under `Filter.comap (fun p ↦ min p.1 p.2) Filter.atTop`.
- `Nat.isBigO_euclideanGcdSteps_comap_add_atTop`: Euclidean GCD step count is `O(size (a + b))`
  under `Filter.comap (fun p ↦ p.1 + p.2) Filter.atTop`.
-/

namespace Nat

open Asymptotics

/-- Binary GCD step count is asymptotically `O(Nat.size (a + b))` with respect to
an arbitrary filter `l` on `ℕ × ℕ`. -/
theorem isBigO_binaryGcdSteps_size_add (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[l]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (2 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro ⟨a, b⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := binaryGcdSteps_le_two_mul_size_add a b
  exact_mod_cast h

/-- Binary GCD step count is asymptotically `O(Nat.size a + Nat.size b)` with respect to
an arbitrary filter `l` on `ℕ × ℕ`. -/
theorem isBigO_binaryGcdSteps_size_add_size (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[l]
    (fun p : ℕ × ℕ ↦ ((Nat.size p.1 + Nat.size p.2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro ⟨a, b⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := binaryGcdSteps_le_size_add_size a b
  exact_mod_cast h

/-- Binary GCD step count is asymptotically `O(Nat.size (a + b))` under `Filter.atTop`
on `ℕ × ℕ`. -/
theorem isBigO_binaryGcdSteps_atTop :
    (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ)) :=
  isBigO_binaryGcdSteps_size_add Filter.atTop

/-- Binary GCD step count is asymptotically `O(Nat.size (a + b))` under the `atTop`
filter pulled back along the combined input sum `fun p ↦ p.1 + p.2`. -/
theorem isBigO_binaryGcdSteps_comap_add_atTop :
    (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
      Filter.comap (fun p ↦ p.1 + p.2) Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ)) :=
  isBigO_binaryGcdSteps_size_add _

/-- Binary GCD step count is asymptotically `O(Nat.size (a + b))` under the `atTop`
filter pulled back along the combined input bit-length `fun p ↦ Nat.size (p.1 + p.2)`. -/
theorem isBigO_binaryGcdSteps_comap_size_atTop :
    (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
      Filter.comap (fun p ↦ Nat.size (p.1 + p.2)) Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ)) :=
  isBigO_binaryGcdSteps_size_add _

/-- Instrumented binary GCD step count is asymptotically `O(Nat.size (a + b))`
with respect to an arbitrary filter `l` on `ℕ × ℕ`. -/
theorem isBigO_binaryGcdWithSteps_snd_size_add (l : Filter (ℕ × ℕ)) :
    (fun p : ℕ × ℕ ↦ (((binaryGcdWithSteps p.1 p.2).2 : ℕ) : ℝ)) =O[l]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ)) := by
  have heq : (fun p : ℕ × ℕ ↦ (((binaryGcdWithSteps p.1 p.2).2 : ℕ) : ℝ)) =
      (fun p : ℕ × ℕ ↦ ((binaryGcdSteps p.1 p.2 : ℕ) : ℝ)) := by
    funext ⟨a, b⟩
    rw [binaryGcdWithSteps_snd]
  rw [heq]
  exact isBigO_binaryGcdSteps_size_add l

/-- Euclidean GCD step count is asymptotically `O(Nat.size (min a b))` under `Filter.atTop`
on `ℕ × ℕ`. -/
theorem isBigO_euclideanGcdSteps_atTop :
    (fun p : ℕ × ℕ ↦ ((euclideanGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (min p.1 p.2) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (3 : ℝ) ?_
  have hev : ∀ᶠ (p : ℕ × ℕ) in Filter.atTop, (1, 1) ≤ p := Filter.eventually_ge_atTop (1, 1)
  refine hev.mono ?_
  intro ⟨a, b⟩ ⟨ha, hb⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := euclideanGcdSteps_le_two_mul_size_min a b
  have hmin_pos : 0 < min a b := by
    rw [Nat.lt_min]
    exact ⟨ha, hb⟩
  have hsz_pos : 1 ≤ Nat.size (min a b) := Nat.size_pos.mpr hmin_pos
  have h3 : euclideanGcdSteps a b ≤ 3 * Nat.size (min a b) := by omega
  exact_mod_cast h3

/-- Euclidean GCD step count is asymptotically `O(Nat.size (min a b))` under the `atTop`
filter pulled back along the minimum input measure `fun p ↦ min p.1 p.2`. -/
theorem isBigO_euclideanGcdSteps_comap_min_atTop :
    (fun p : ℕ × ℕ ↦ ((euclideanGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
      Filter.comap (fun p ↦ min p.1 p.2) Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (min p.1 p.2) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (3 : ℝ) ?_
  rw [Filter.eventually_comap]
  have hev : ∀ᶠ n in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  refine hev.mono ?_
  intro n hn ⟨a, b⟩ (hab : min a b = n)
  subst hab
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := euclideanGcdSteps_le_two_mul_size_min a b
  have hsz_pos : 1 ≤ Nat.size (min a b) := by
    have : 0 < min a b := by omega
    exact Nat.size_pos.mpr this
  have h3 : euclideanGcdSteps a b ≤ 3 * Nat.size (min a b) := by omega
  exact_mod_cast h3

/-- Euclidean GCD step count is asymptotically `O(Nat.size (a + b))` under the `atTop`
filter pulled back along the combined input sum `fun p ↦ p.1 + p.2`. -/
theorem isBigO_euclideanGcdSteps_comap_add_atTop :
    (fun p : ℕ × ℕ ↦ ((euclideanGcdSteps p.1 p.2 : ℕ) : ℝ)) =O[
      Filter.comap (fun p ↦ p.1 + p.2) Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (p.1 + p.2) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (3 : ℝ) ?_
  rw [Filter.eventually_comap]
  have hev : ∀ᶠ n in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  refine hev.mono ?_
  intro n hn ⟨a, b⟩ (hab : a + b = n)
  subst hab
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := euclideanGcdSteps_le_two_mul_size_add a b
  have hsz_pos : 1 ≤ Nat.size (a + b) := by
    have : 0 < a + b := by omega
    exact Nat.size_pos.mpr this
  have h3 : euclideanGcdSteps a b ≤ 3 * Nat.size (a + b) := by omega
  exact_mod_cast h3

end Nat
