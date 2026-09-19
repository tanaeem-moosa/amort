/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.EuclideanGCD
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Extended Euclidean Algorithm & Bézout Invariants

This module formalizes the extended Euclidean algorithm computing Bézout coefficients
$x, y \in \mathbb{Z}$ satisfying $a \cdot x + b \cdot y = \gcd(a, b)$:
- Extended GCD implementation `extGCD` computing $(x, y, g)$.
- Correctness theorem: $a \cdot x + b \cdot y = g$ and $g = \text{Nat.gcd } a\ b$.
- Remainder halving theorem: $2 \cdot r_{k+2} < r_k$ across two consecutive quotient steps.
- Logarithmic step bound: $\le 2 \cdot \text{Nat.size}(\min a\ b) + 1$, establishing
  $O(\log(\min(a, b)))$ complexity.

## Key Definitions and Theorems
- `Amort.NumberTheory.extGCD`: Extended Euclidean algorithm computing Bézout coefficients.
- `Amort.NumberTheory.extGCD_bezout`: Proof that $a \cdot x + b \cdot y = g$.
- `Amort.NumberTheory.extGCD_gcd`: Proof that $g = \text{Nat.gcd } a\ b$.
- `Amort.NumberTheory.remainder_halving`: Two-step remainder halving $2 \cdot (a \bmod b) < a$.
- `Amort.NumberTheory.extGCDSteps`: Step counter tracking quotient division steps.
- `Amort.NumberTheory.extGCDSteps_le`: Logarithmic step bound.
-/

namespace Amort.NumberTheory

/-- Extended Euclidean algorithm:
Computes the triple $(x, y, g)$ where $x, y \in \mathbb{Z}$ are Bézout coefficients
satisfying $a \cdot x + b \cdot y = g$ and $g = \text{Nat.gcd } a\ b$. -/
def extGCD (a b : ℕ) : ℤ × ℤ × ℕ :=
  if hb : b = 0 then
    (1, 0, a)
  else
    have _hlt : a % b < b := Nat.mod_lt a (Nat.pos_of_ne_zero hb)
    let res := extGCD b (a % b)
    let s := res.1
    let t := res.2.1
    let g := res.2.2
    (t, s - t * ((a / b : ℕ) : ℤ), g)
termination_by b

/-- Bézout identity correctness:
For all $a, b \in \mathbb{N}$, the coefficients $(x, y, g)$ produced by `extGCD a b`
satisfy $a \cdot x + b \cdot y = g$. -/
theorem extGCD_bezout (a b : ℕ) :
    let res := extGCD a b
    (a : ℤ) * res.1 + (b : ℤ) * res.2.1 = (res.2.2 : ℤ) := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    unfold extGCD
    split
    · rename_i hb0
      subst hb0
      simp
    · rename_i hb_ne
      have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne
      have hlt : a % b < b := Nat.mod_lt a hb_pos
      have ih_rec := ih (a % b) hlt b
      dsimp only
      have h_nat : a = b * (a / b) + a % b := (Nat.div_add_mod a b).symm
      have hdiv : (a : ℤ) = (b : ℤ) * ((a / b : ℕ) : ℤ) + ((a % b : ℕ) : ℤ) := by
        exact_mod_cast h_nat
      have hcalc : (a : ℤ) * (extGCD b (a % b)).2.1 +
          (b : ℤ) * ((extGCD b (a % b)).1 - (extGCD b (a % b)).2.1 * ((a / b : ℕ) : ℤ)) =
          (b : ℤ) * (extGCD b (a % b)).1 + ((a % b : ℕ) : ℤ) * (extGCD b (a % b)).2.1 := by
        rw [hdiv]
        ring
      rw [hcalc, ih_rec]

/-- Greatest common divisor correctness:
The integer $g$ computed by `extGCD a b` equals $\text{Nat.gcd } a\ b$. -/
theorem extGCD_gcd (a b : ℕ) :
    (extGCD a b).2.2 = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    unfold extGCD
    split
    · rename_i hb0
      subst hb0
      simp
    · rename_i hb_ne
      have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne
      have hlt : a % b < b := Nat.mod_lt a hb_pos
      have ih_rec := ih (a % b) hlt b
      dsimp only
      rw [ih_rec]
      rw [Nat.gcd_comm b (a % b), ← Nat.gcd_rec b a, Nat.gcd_comm b a]

/-! ### Remainder Halving and Step Count -/

/-- The fundamental two-step remainder halving theorem:
For positive $b \le a$, the remainder $r = a \bmod b$ satisfies $2 \cdot r < a$.
Consequently, in any two successive division steps, the remainder strictly halves:
$2 \cdot r_{k+2} < r_k$. -/
theorem remainder_halving {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    2 * (a % b) < a :=
  Nat.mod_two_mul_lt hb hba

/-- Step counting for the extended Euclidean algorithm:
tracks the number of division/modulo steps until $b = 0$. -/
def extGCDSteps (a b : ℕ) : ℕ :=
  if hb : b = 0 then 0
  else 1 + extGCDSteps b (a % b)
termination_by b
decreasing_by
  exact Nat.mod_lt a (Nat.pos_of_ne_zero hb)

lemma extGCDSteps_eq_euclideanGcdSteps (a b : ℕ) :
    extGCDSteps a b = Nat.euclideanGcdSteps b a := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    unfold extGCDSteps Nat.euclideanGcdSteps
    by_cases hb : b = 0
    · subst hb
      simp
    · have hb_pos : 0 < b := Nat.pos_of_ne_zero hb
      have hlt : a % b < b := Nat.mod_lt a hb_pos
      have ih_rec := ih (a % b) hlt b
      simp only [hb]
      rw [ih_rec]

/-- Logarithmic step bound:
The number of division steps executed by `extGCD a b` is bounded by
$2 \cdot \text{Nat.size}(\min a\ b) + 1$. -/
theorem extGCDSteps_le (a b : ℕ) :
    extGCDSteps a b ≤ 2 * Nat.size (min a b) + 1 := by
  rw [extGCDSteps_eq_euclideanGcdSteps]
  have h := Nat.euclideanGcdSteps_le_two_mul_size_min b a
  rw [min_comm b a] at h
  exact h

end Amort.NumberTheory
