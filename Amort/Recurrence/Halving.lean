/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Halving Recurrences and Logarithmic Bounds

This module formalizes recurrence bounds for decrease-by-constant-factor algorithms satisfying
the halving inequality: $T(n) \le T(n / 2) + c$ for all $n \ge 2$.

## Mathematical Architecture

1. **Size-Halving Invariant**:
   For any natural number $n$, $\text{Nat.size}(n / 2) = \text{Nat.size } n - 1$.
   For $n \ge 2$, $\text{Nat.size } n \ge 2$, so each halving step reduces the bit size by 1.

2. **Concrete Halving Recurrence Bound**:
   By strong induction on $n$, any sequence satisfying $T(n) \le T(n / 2) + c$ for $n \ge 2$
   obeys:
   $$T(n) \le c \cdot \text{Nat.size } n + T(1) \quad (\forall n \ge 1)$$
   and globally for all $n \in \mathbb{N}$:
   $$T(n) \le c \cdot \text{Nat.size } n + T(0) + T(1)$$

3. **Bit-Length and Natural Logarithm Dominance**:
   Using the two-sided power bound $2^{\text{size } n - 1} \le n < 2^{\text{size } n}$,
   we establish:
   $$\text{Nat.size } n = O(\log n) \quad \text{under } \text{Filter.atTop}$$

4. **Asymptotic Complexity**:
   Combining the concrete bound with the logarithmic bridge yields:
   $$T(n) = O(\text{Nat.size } n) \quad \text{and} \quad T(n) = O(\log n)$$
   under `Filter.atTop`.

## Key Theorems
- `Amort.Recurrence.size_div_two`: Bit-length decreases by 1 under integer halving.
- `Amort.Recurrence.size_ge_two_of_ge_two`: Bit-length is at least 2 when $n \ge 2$.
- :
  Concrete bound (n) \le c \cdot 	ext{size } n + T(1)$.
- `Amort.Recurrence.halving_recurrence_bound_all`: Concrete global bound for all $n \in \mathbb{N}$.
- `Amort.Recurrence.isBigO_size_log`: $\text{Nat.size } n = O(\log n)$ under `Filter.atTop`.
- `Amort.Recurrence.halving_recurrence_isBigO_size`:
  $T(n) = O(\text{Nat.size } n)$ under `Filter.atTop`.
- `Amort.Recurrence.halving_recurrence_isBigO_log`:
  $T(n) = O(\log n)$ under `Filter.atTop`.
-/

namespace Amort.Recurrence

open Asymptotics

/-! ### Bit-Length and Halving Lemmas -/

/-- Halving a natural number decreases its bit size by exactly 1. -/
theorem size_div_two (n : ℕ) : Nat.size (n / 2) = Nat.size n - 1 := by
  apply Nat.le_antisymm
  · cases hn : Nat.size n with
    | zero =>
      have : n = 0 := by rwa [Nat.size_eq_zero] at hn
      subst this
      simp
    | succ k =>
      rw [Nat.succ_sub_one]
      rw [Nat.size_le]
      have h := Nat.lt_size_self n
      rw [hn] at h
      have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [h2] at h
      omega
  · cases hn : Nat.size n - 1 with
    | zero => simp
    | succ k =>
      have h_lt : k + 1 < Nat.size n := by omega
      rw [Nat.lt_size] at h_lt
      have h2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [h2] at h_lt
      have h_div : 2 ^ k ≤ n / 2 := by omega
      rw [← Nat.lt_size] at h_div
      omega

/-- For any $n \ge 2$, the bit size $\text{Nat.size } n$ is at least 2. -/
theorem size_ge_two_of_ge_two {n : ℕ} (h : 2 ≤ n) : 2 ≤ Nat.size n := by
  have : 1 < Nat.size n := by
    rw [Nat.lt_size]
    exact h
  omega

/-! ### Concrete Halving Recurrence Bounds -/

/-- Concrete upper bound for halving recurrence on positive inputs: if $T(n) \le T(n / 2) + c$
for $n \ge 2$, then $T(n) \le c \cdot \text{Nat.size } n + T(1)$ for all $n \ge 1$. -/
theorem halving_recurrence_bound (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) (n : ℕ) (hn : 1 ≤ n) :
    T n ≤ c * Nat.size n + T 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn2 : n < 2
    · have : n = 1 := by omega
      subst this
      simp
    · have h2le : 2 ≤ n := by omega
      have hdiv_lt : n / 2 < n := Nat.div_lt_self (by omega) (by decide)
      have hdiv_ge : 1 ≤ n / 2 := by omega
      have ih_div := ih (n / 2) hdiv_lt hdiv_ge
      have h_step := hrec n h2le
      have h_size : Nat.size (n / 2) = Nat.size n - 1 := size_div_two n
      have h_size_ge : 2 ≤ Nat.size n := size_ge_two_of_ge_two h2le
      have h_calc : c * Nat.size (n / 2) + c = c * Nat.size n := by
        rw [h_size]
        have : Nat.size n - 1 + 1 = Nat.size n := by omega
        calc c * (Nat.size n - 1) + c
          _ = c * (Nat.size n - 1 + 1) := by ring
          _ = c * Nat.size n := by rw [this]
      omega

/-- Concrete upper bound for halving recurrence valid on all natural numbers:
$T(n) \le c \cdot \text{Nat.size } n + T(0) + T(1)$. -/
theorem halving_recurrence_bound_all (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) (n : ℕ) :
    T n ≤ c * Nat.size n + T 0 + T 1 := by
  by_cases hn : n = 0
  · subst hn
    simp
  · have hn_pos : 1 ≤ n := by omega
    have h := halving_recurrence_bound T c hrec n hn_pos
    omega

/-! ### Asymptotic Complexity -/

/-- Bit size $\text{Nat.size } n$ is asymptotically bounded by $\text{Real.log } n$
under `Filter.atTop`. -/
theorem isBigO_size_log :
    (fun n : ℕ ↦ ((Nat.size n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  refine IsBigO.of_bound (2 / Real.log 2) ?_
  rw [Filter.eventually_atTop]
  refine ⟨4, ?_⟩
  intro n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have hn_pos : 0 < (n : ℝ) := by positivity
  have h_log_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_log_n_pos : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
  rw [_root_.abs_of_nonneg h_log_n_pos]
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
  have h_size_le : (((Nat.size n - 1 : ℕ) : ℝ)) ≤ Real.log (n : ℝ) / Real.log 2 := by
    exact (le_div_iff₀ h_log_pos).mpr h_log_le
  have h_one_le : (1 : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 := by
    rw [one_le_div₀ h_log_pos]
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
    exact Real.log_le_log (by norm_num) this
  have h_size_ge : 1 ≤ Nat.size n := by
    have : 0 < Nat.size n := by
      rw [Nat.size_pos]
      omega
    omega
  have h_cast_sub : (((Nat.size n : ℕ) : ℝ)) - 1 = (((Nat.size n - 1 : ℕ) : ℝ)) := by
    have : Nat.size n = (Nat.size n - 1) + 1 := by omega
    nth_rewrite 1 [this]
    push_cast
    ring
  have h_total : (((Nat.size n : ℕ) : ℝ)) ≤ 2 * (Real.log (n : ℝ) / Real.log 2) := by
    calc (((Nat.size n : ℕ) : ℝ))
      _ = (((Nat.size n - 1 : ℕ) : ℝ)) + 1 := by linarith [h_cast_sub]
      _ ≤ Real.log (n : ℝ) / Real.log 2 + Real.log (n : ℝ) / Real.log 2 :=
        by linarith [h_size_le, h_one_le]
      _ = 2 * (Real.log (n : ℝ) / Real.log 2) := by ring
  calc (((Nat.size n : ℕ) : ℝ))
    _ ≤ 2 * (Real.log (n : ℝ) / Real.log 2) := h_total
    _ = (2 / Real.log 2) * Real.log (n : ℝ) := by ring

/-- Halving recurrence complexity is $O(\text{Nat.size } n)$ under `Filter.atTop`. -/
theorem halving_recurrence_isBigO_size (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((Nat.size n : ℕ) : ℝ)) := by
  refine IsBigO.of_bound ((c + T 1 : ℕ) : ℝ) ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, ?_⟩
  intro n hn
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h_bound := halving_recurrence_bound T c hrec n hn
  have hsize_pos : 0 < Nat.size n := Nat.size_pos.mpr (by omega)
  have hsize_ge : 1 ≤ Nat.size n := by omega
  have h_T1 : T 1 ≤ T 1 * Nat.size n := Nat.le_mul_of_pos_right (T 1) hsize_ge
  have h_total : T n ≤ (c + T 1) * Nat.size n := by
    calc T n ≤ c * Nat.size n + T 1 := h_bound
      _ ≤ c * Nat.size n + T 1 * Nat.size n := Nat.add_le_add_left h_T1 _
      _ = (c + T 1) * Nat.size n := by ring
  exact_mod_cast h_total

/-- Halving recurrence complexity is $O(\log n)$ under `Filter.atTop`. -/
theorem halving_recurrence_isBigO_log (T : ℕ → ℕ) (c : ℕ)
    (hrec : ∀ n, 2 ≤ n → T n ≤ T (n / 2) + c) :
    (fun n : ℕ ↦ ((T n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ Real.log (n : ℝ)) :=
  (halving_recurrence_isBigO_size T c hrec).trans isBigO_size_log

end Amort.Recurrence
