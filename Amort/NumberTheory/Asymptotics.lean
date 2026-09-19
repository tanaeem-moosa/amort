/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.NumberTheory.ModExp
import Amort.NumberTheory.ExtendedGCD
import Amort.NumberTheory.Sieve
import Amort.Recurrence.Halving
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Number Theoretic Algorithms

This module connects the concrete operational step bounds for number theoretic algorithms
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework:
- Fast Modular Exponentiation ($O(\log b)$ multiplications via repeated squaring).
- Extended Euclidean Algorithm ($O(\log(\min(a, b)))$ division steps).
- Sieve of Eratosthenes ($O(n \log n)$ harmonic composite markings).

## Key Definitions and Theorems
- `Amort.NumberTheory.isBigO_modExpMulSteps_size`: ModExp multiplications $O(\text{size } b)$.
- `Amort.NumberTheory.isBigO_modExpMulSteps_log`: ModExp multiplications $O(\log b)$.
- `Amort.NumberTheory.isBigO_extGCDSteps_comap_min_atTop`: Extended GCD $O(\text{size}(\min a\ b))$.
- `Amort.NumberTheory.isBigO_sieveWork_mul_size`: Sieve work $O(n \cdot \text{size } n)$.
-/

namespace Amort.NumberTheory

open Asymptotics

/-- Multiplications in fast modular exponentiation are asymptotically $O(\text{Nat.size } b)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_modExpMulSteps_size :
    (fun b : ℕ ↦ ((modExpMulSteps b : ℕ) : ℝ)) =O[Filter.atTop]
      (fun b : ℕ ↦ ((Nat.size b : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (2 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨0, fun b _ ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := modExpMulSteps_le b
  have h_real : (((modExpMulSteps b : ℕ) : ℝ) ≤ ((2 * Nat.size b : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((2 * Nat.size b : ℕ) : ℝ) = 2 * ((Nat.size b : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

/-- Multiplications in fast modular exponentiation are asymptotically $O(\log b)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_modExpMulSteps_log :
    (fun b : ℕ ↦ ((modExpMulSteps b : ℕ) : ℝ)) =O[Filter.atTop]
      (fun b : ℕ ↦ Real.log (b : ℝ)) :=
  isBigO_modExpMulSteps_size.trans Amort.Recurrence.isBigO_size_log

/-- Extended Euclidean division steps are asymptotically $O(\text{Nat.size}(\min a\ b))$
under `Filter.comap` towards `Filter.atTop` on the minimum input. -/
theorem isBigO_extGCDSteps_comap_min_atTop :
    (fun p : ℕ × ℕ ↦ ((extGCDSteps p.1 p.2 : ℕ) : ℝ)) =O[
      Filter.comap (fun p ↦ min p.1 p.2) Filter.atTop]
    (fun p : ℕ × ℕ ↦ ((Nat.size (min p.1 p.2) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (3 : ℝ) ?_
  rw [Filter.eventually_comap]
  have hev : ∀ᶠ n in Filter.atTop, 1 ≤ n := Filter.eventually_ge_atTop 1
  refine hev.mono ?_
  intro n hn ⟨a, b⟩ (hab : min a b = n)
  subst hab
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := extGCDSteps_le a b
  have hsz_pos : 1 ≤ Nat.size (min a b) := by
    have : 0 < min a b := by omega
    exact Nat.size_pos.mpr this
  have h3 : extGCDSteps a b ≤ 3 * Nat.size (min a b) := by omega
  exact_mod_cast h3

/-- Sieve of Eratosthenes work is asymptotically $O(n \cdot \text{Nat.size } n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_sieveWork_mul_size :
    (fun n : ℕ ↦ ((sieveWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (2 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := sieveWork_le n hn
  have h_real : (((sieveWork n : ℕ) : ℝ) ≤ ((2 * n * Nat.size n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((2 * n * Nat.size n : ℕ) : ℝ) = 2 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

end Amort.NumberTheory
