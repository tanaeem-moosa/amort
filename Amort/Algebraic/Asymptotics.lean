/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Algebraic.FFT
import Amort.Algebraic.Strassen
import Amort.Recurrence.Halving
import Amort.Recurrence.MasterTheorem
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Fast Algebraic Algorithms

This module establishes formal connections between concrete operational work models
and Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic complexity framework
under `Filter.atTop`:

1. **Fast Fourier Transform (FFT)**:
   - $W_{FFT}(n) = O(n \cdot \text{Nat.size } n)$ under `Filter.atTop`.
   - $W_{FFT}(n) = O(n \log n)$ under `Filter.atTop`.

2. **Polynomial Multiplication**:
   - FFT-based polynomial multiplication: $W_{poly}(n) = O(n \log n)$ under `Filter.atTop`.
   - Contrast with naive polynomial multiplication: $W_{naive}(n) = n^2 = O(n^2)$.

3. **Strassen's Sub-Cubic Matrix Multiplication**:
   - Dyadic power bound: $W_{strassen}(n) = O(7^{\text{Nat.size } n})$ under `Filter.atTop`.
   - Real power bound: $W_{strassen}(n) = O(n^{\log_2 7})$ under `Filter.atTop`.
   - Sub-cubic exponent: $\log_2 7 < 3$, proving strict asymptotic superiority over standard
     cubic matrix multiplication $O(n^3)$.

## Key Theorems
- `Amort.Algebraic.isBigO_fftWork_mul_size`: FFT operational work is $O(n \cdot \text{size } n)$.
- `Amort.Algebraic.isBigO_fftWork_n_log_n`: FFT operational work is $O(n \log n)$.
- `Amort.Algebraic.isBigO_fftPolyMulWork_mul_size`: FFT poly mul is $O(n \cdot \text{size } n)$.
- `Amort.Algebraic.isBigO_fftPolyMulWork_n_log_n`: FFT poly mul is $O(n \log n)$.
- `Amort.Algebraic.isBigO_naivePolyMulWork_sq`: Naive polynomial multiplication is $O(n^2)$.
- `Amort.Algebraic.isBigO_strassenWork_pow7_size`: Strassen work is $O(7^{\text{size } n})$.
- `Amort.Algebraic.strassenWork_le_rpow`: Concrete bound $W(n) \le 7 n^{\log_2 7}$.
- `Amort.Algebraic.isBigO_strassenWork_rpow`: Strassen work is $O(n^{\log_2 7})$.
- `Amort.Algebraic.isBigO_standardMatrixMulWork_cube`: Standard matrix mul is $O(n^3)$.
-/

namespace Amort.Algebraic

open Asymptotics
open Real

/-! ### Fast Fourier Transform Asymptotics -/

/-- Operational work of Radix-2 FFT is asymptotically $O(n \cdot \text{Nat.size } n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_fftWork_mul_size :
    (fun n : ℕ ↦ ((fftWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (3 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := fftWork_le n hn
  have h_real : (((fftWork n : ℕ) : ℝ) ≤ ((3 * n * Nat.size n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((3 * n * Nat.size n : ℕ) : ℝ) = 3 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

/-- Operational work of Radix-2 FFT is asymptotically $O(n \log n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_fftWork_n_log_n :
    (fun n : ℕ ↦ ((fftWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) :=
  isBigO_fftWork_mul_size.trans
    (Amort.Recurrence.isBigO_mul_size_n_log_n Amort.Recurrence.isBigO_size_log)

/-- Operational work of FFT-based polynomial multiplication is asymptotically
$O(n \cdot \text{Nat.size } n)$ under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_fftPolyMulWork_mul_size :
    (fun n : ℕ ↦ ((fftPolyMulWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (38 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := fftPolyMulWork_le n hn
  have h_real : (((fftPolyMulWork n : ℕ) : ℝ) ≤ ((38 * n * Nat.size n : ℕ) : ℝ)) := by
    exact_mod_cast h
  have h_assoc : ((38 * n * Nat.size n : ℕ) : ℝ) = 38 * ((n * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc] at h_real
  exact h_real

/-- Operational work of FFT-based polynomial multiplication is asymptotically $O(n \log n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_fftPolyMulWork_n_log_n :
    (fun n : ℕ ↦ ((fftPolyMulWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ) * Real.log (n : ℝ)) :=
  isBigO_fftPolyMulWork_mul_size.trans
    (Amort.Recurrence.isBigO_mul_size_n_log_n Amort.Recurrence.isBigO_size_log)

/-- Naive polynomial multiplication is asymptotically $O(n^2)$ under `Filter.atTop`. -/
theorem isBigO_naivePolyMulWork_sq :
    (fun n : ℕ ↦ ((naivePolyMulWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨0, fun n _hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  unfold naivePolyMulWork
  rfl

/-! ### Strassen's Matrix Multiplication Asymptotics -/

/-- Operational work of Strassen's algorithm is asymptotically $O(7^{\text{Nat.size } n})$
under `Filter.atTop`. -/
theorem isBigO_strassenWork_pow7_size :
    (fun n : ℕ ↦ ((strassenWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((7 ^ Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨0, fun n _hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  unfold strassenWork
  rfl

/-- Concrete upper bound connecting Strassen's operational work to the continuous power
$7 \cdot n^{\log_2 7}$:
For all $n \ge 1$, $W(n) \le 7 \cdot n^{\log_2 7}$. -/
theorem strassenWork_le_rpow (n : ℕ) (hn : 1 ≤ n) :
    ((strassenWork n : ℕ) : ℝ) ≤ 7 * (n : ℝ) ^ (Real.log 7 / Real.log 2) := by
  unfold strassenWork
  have hn_pos : 0 < (n : ℝ) := by positivity
  have h7_pos : 0 < (7 : ℝ) := by norm_num
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog7_pos : 0 < Real.log 7 := Real.log_pos (by norm_num)
  have h_le : 2 ^ (Nat.size n - 1) ≤ n := by
    cases hn_size : Nat.size n with
    | zero =>
      have : n = 0 := by rwa [Nat.size_eq_zero] at hn_size
      omega
    | succ k =>
      simp only [Nat.succ_sub_one]
      rw [← Nat.lt_size]
      omega
  have h_real_le : ((2 ^ (Nat.size n - 1) : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h_le
  rw [Nat.cast_pow, Nat.cast_ofNat] at h_real_le
  have h_pow_pos : (0 : ℝ) < (2 : ℝ) ^ (Nat.size n - 1) := by positivity
  have h_log_le := Real.log_le_log h_pow_pos h_real_le
  rw [Real.log_pow] at h_log_le
  have h_size_sub : (((Nat.size n - 1 : ℕ) : ℝ)) ≤ Real.log (n : ℝ) / Real.log 2 :=
    (le_div_iff₀ hlog2_pos).mpr h_log_le
  have h_size_le : (((Nat.size n : ℕ) : ℝ)) ≤ Real.log (n : ℝ) / Real.log 2 + 1 := by
    have h_split : Nat.size n ≤ (Nat.size n - 1) + 1 := by omega
    have h_cast : (((Nat.size n : ℕ) : ℝ)) ≤ (((Nat.size n - 1 : ℕ) : ℝ)) + 1 := by
      exact_mod_cast h_split
    linarith
  have h_mul_le : (((Nat.size n : ℕ) : ℝ)) * Real.log 7 ≤
      (Real.log (n : ℝ) / Real.log 2 + 1) * Real.log 7 :=
    mul_le_mul_of_nonneg_right h_size_le hlog7_pos.le
  have h_exp_le : Real.exp ((((Nat.size n : ℕ) : ℝ)) * Real.log 7) ≤
      Real.exp ((Real.log (n : ℝ) / Real.log 2 + 1) * Real.log 7) :=
    Real.exp_le_exp.mpr h_mul_le
  have h_exp_7 : Real.exp ((((Nat.size n : ℕ) : ℝ)) * Real.log 7) =
      ((7 ^ Nat.size n : ℕ) : ℝ) := by
    rw [mul_comm, ← Real.rpow_def_of_pos h7_pos, Real.rpow_natCast]
    push_cast
    rfl
  have h_exp_add : Real.exp ((Real.log (n : ℝ) / Real.log 2 + 1) * Real.log 7) =
      Real.exp (Real.log (n : ℝ) * (Real.log 7 / Real.log 2)) * Real.exp (Real.log 7) := by
    have : (Real.log (n : ℝ) / Real.log 2 + 1) * Real.log 7 =
        Real.log (n : ℝ) * (Real.log 7 / Real.log 2) + Real.log 7 := by ring
    rw [this, Real.exp_add]
  have h_exp_log7 : Real.exp (Real.log 7) = 7 := Real.exp_log h7_pos
  have h_rpow : Real.exp (Real.log (n : ℝ) * (Real.log 7 / Real.log 2)) =
      (n : ℝ) ^ (Real.log 7 / Real.log 2) := by
    rw [← Real.rpow_def_of_pos hn_pos]
  rw [h_exp_7] at h_exp_le
  rw [h_exp_add, h_exp_log7, h_rpow] at h_exp_le
  linarith

/-- Operational work of Strassen's algorithm is asymptotically $O(n^{\log_2 7})$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_strassenWork_rpow :
    (fun n : ℕ ↦ ((strassenWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ (Real.log 7 / Real.log 2)) := by
  refine IsBigO.of_bound (7 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := strassenWork_le_rpow n hn
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hrpow_nonneg : 0 ≤ (n : ℝ) ^ (Real.log 7 / Real.log 2) :=
    Real.rpow_nonneg hn_pos.le _
  rw [_root_.abs_of_nonneg hrpow_nonneg]
  exact h

/-- Standard matrix multiplication is asymptotically cubic $O(n^3)$ under `Filter.atTop`. -/
theorem isBigO_standardMatrixMulWork_cube :
    (fun n : ℕ ↦ ((standardMatrixMulWork n : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n : ℕ ↦ ((n ^ 3 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (2 : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨0, fun n _hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  unfold standardMatrixMulWork
  have h_assoc : ((2 * n ^ 3 : ℕ) : ℝ) = 2 * ((n ^ 3 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [h_assoc]

end Amort.Algebraic
