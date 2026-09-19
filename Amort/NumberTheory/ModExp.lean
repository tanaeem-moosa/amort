/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Halving
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Fast Modular Exponentiation (Binary Exponentiation)

This module formalizes repeated squaring for modular exponentiation ($a^b \bmod m$):
- Correctness invariant: loop state preserves $(acc \cdot base^{exp}) \equiv a^b \pmod m$.
- Mathematical equivalence: `modExp a b m = (a ^ b) % m`.
- Multiplication step counter `modExpMulSteps`.
- Step bound: $\le 2 \cdot \text{Nat.size } b$, establishing $O(\log b)$ complexity.

## Key Definitions and Theorems
- `Amort.NumberTheory.modExpAux`: Core repeated squaring tail-recursive loop.
- `Amort.NumberTheory.modExp`: Complete modular exponentiation.
- `Amort.NumberTheory.modExpMulSteps`: Operation counter for multiplications.
- `Amort.NumberTheory.mul_pow_two`: Exponentiation algebra identity $(b^2)^k = b^{2k}$.
- `Amort.NumberTheory.mod_step_algebra`: Algebraic invariance of a single squaring step.
- `Amort.NumberTheory.modExpAux_correct`: Main loop state correctness invariant.
- `Amort.NumberTheory.modExp_correct`: Global correctness theorem $a^b \bmod m$.
- `Amort.NumberTheory.modExpMulSteps_le`: Logarithmic step bound $\le 2 \cdot \text{Nat.size } b$.
-/

namespace Amort.NumberTheory

lemma mul_pow_two (b k : ℕ) : (b * b) ^ k = b ^ (2 * k) := by
  have h1 : b * b = b ^ 2 := by ring
  rw [h1, ← pow_mul]

/-- Algebraic foundation of binary exponentiation:
preserving the value $acc \cdot base^{exp}$ under division by 2. -/
lemma mod_step_algebra (acc base exp : ℕ) :
    (if exp % 2 = 1 then acc * base else acc) * (base * base) ^ (exp / 2) =
      acc * base ^ exp := by
  by_cases hmod : exp % 2 = 1
  · simp only [hmod, ite_true]
    have hexp : exp = 2 * (exp / 2) + 1 := by omega
    conv_rhs => rw [hexp]
    rw [pow_succ, mul_pow_two]
    ring
  · have hmod0 : exp % 2 = 0 := by omega
    simp only [hmod, ite_false]
    have hexp : exp = 2 * (exp / 2) := by omega
    conv_rhs => rw [hexp]
    rw [mul_pow_two]

/-- Core repeated squaring loop computing $(acc \cdot base^{exp}) \bmod m$. -/
def modExpAux (m : ℕ) (acc base exp : ℕ) : ℕ :=
  if exp = 0 then
    acc % m
  else
    let acc' := if exp % 2 = 1 then (acc * base) % m else acc
    let base' := (base * base) % m
    modExpAux m acc' base' (exp / 2)
termination_by exp
decreasing_by omega

/-- Complete modular exponentiation: computes $a^b \bmod m$. -/
def modExp (a b m : ℕ) : ℕ :=
  if m = 0 then 0
  else modExpAux m (1 % m) (a % m) b

/-- Step counter tracking the number of scalar multiplications in binary exponentiation. -/
def modExpMulSteps : ℕ → ℕ
  | 0 => 0
  | n + 1 =>
    let exp := n + 1
    (if exp % 2 = 1 then 2 else 1) + modExpMulSteps (exp / 2)
termination_by n => n
decreasing_by omega

/-! ### Correctness Invariant and Theorems -/

/-- Loop state invariant preservation across a single squaring transition modulo $m$. -/
lemma modExp_step_modEq (m acc base exp : ℕ) :
    ((if exp % 2 = 1 then (acc * base) % m else acc) * ((base * base) % m) ^ (exp / 2)) ≡
      (acc * base ^ exp) [MOD m] := by
  have hbase_mod : ((base * base) % m) ≡ (base * base) [MOD m] := Nat.mod_modEq _ _
  have hpow_mod : (((base * base) % m) ^ (exp / 2)) ≡ ((base * base) ^ (exp / 2)) [MOD m] :=
    Nat.ModEq.pow (exp / 2) hbase_mod
  by_cases hmod : exp % 2 = 1
  · simp only [hmod, ite_true]
    have hacc_mod : (acc * base) % m ≡ acc * base [MOD m] := Nat.mod_modEq _ _
    have hmul := Nat.ModEq.mul hacc_mod hpow_mod
    have halg := mod_step_algebra acc base exp
    simp only [hmod, ite_true] at halg
    rw [halg] at hmul
    exact hmul
  · simp only [hmod, ite_false]
    have hmul := Nat.ModEq.mul (Nat.ModEq.refl acc) hpow_mod
    have halg := mod_step_algebra acc base exp
    simp only [hmod, ite_false] at halg
    rw [halg] at hmul
    exact hmul

/-- Main loop invariant: for any modulus $m > 0$, `modExpAux m acc base exp` computes
$(acc \cdot base^{exp}) \bmod m$. -/
theorem modExpAux_correct (m acc base exp : ℕ) (_hm : 0 < m) :
    modExpAux m acc base exp = (acc * base ^ exp) % m := by
  induction exp using Nat.strong_induction_on generalizing acc base with
  | _ exp ih =>
    unfold modExpAux
    split
    · rename_i hexp0
      subst hexp0
      simp
    · rename_i hexp_ne
      have hexp_pos : 0 < exp := by omega
      have hlt : exp / 2 < exp := by omega
      have hstep := ih (exp / 2) hlt
        (if exp % 2 = 1 then (acc * base) % m else acc) ((base * base) % m)
      rw [hstep]
      have hmodeq := modExp_step_modEq m acc base exp
      exact hmodeq

/-- Global correctness theorem: for any modulus $m > 1$,
$modExp a b m = (a ^ b) \bmod m$. -/
theorem modExp_correct (a b m : ℕ) (_hm : 1 < m) :
    modExp a b m = (a ^ b) % m := by
  unfold modExp
  have hm0 : m ≠ 0 := by omega
  simp only [hm0, ite_false]
  have hm_pos : 0 < m := by omega
  rw [modExpAux_correct m (1 % m) (a % m) b hm_pos]
  have h1 : 1 % m ≡ 1 [MOD m] := Nat.mod_modEq 1 m
  have ha : a % m ≡ a [MOD m] := Nat.mod_modEq a m
  have hpow : (a % m) ^ b ≡ a ^ b [MOD m] := Nat.ModEq.pow b ha
  have hmul : (1 % m) * (a % m) ^ b ≡ 1 * a ^ b [MOD m] := Nat.ModEq.mul h1 hpow
  rw [one_mul] at hmul
  exact hmul

/-! ### Step Bound -/

/-- Multiplication step bound: `modExpMulSteps b` is bounded by $2 \cdot \text{Nat.size } b$. -/
theorem modExpMulSteps_le (b : ℕ) :
    modExpMulSteps b ≤ 2 * Nat.size b := by
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    cases b with
    | zero =>
      rw [modExpMulSteps]
      simp
    | succ k =>
      rw [modExpMulSteps]
      have hpos : 0 < k + 1 := by omega
      have hlt : (k + 1) / 2 < k + 1 := by omega
      have hrec := ih ((k + 1) / 2) hlt
      have hsize : Nat.size ((k + 1) / 2) = Nat.size (k + 1) - 1 :=
        Amort.Recurrence.size_div_two (k + 1)
      have hpos_size : 1 ≤ Nat.size (k + 1) := Nat.size_pos.mpr hpos
      have hmults : (if (k + 1) % 2 = 1 then 2 else 1) ≤ 2 := by
        split <;> omega
      omega

end Amort.NumberTheory
