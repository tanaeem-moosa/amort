/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Size
import Amort.GCD.StepCount

/-!
# Step Counting and Complexity Bounds for Euclidean GCD

This module formalizes step counting for the standard Euclidean algorithm (`Nat.gcd`)
and establishes an explicit logarithmic upper bound on the number of division/modulo
steps in terms of the bit lengths of the inputs.

## Key Definitions
- `Nat.euclideanGcdSteps`: Companion function counting the division/modulo steps
  executed by `Nat.gcd a b`.

## Key Theorems & Lemmas
- `Nat.mod_two_mul_lt`: The halving property of the modulo operation:
  `2 * (a % b) < a` whenever `0 < b ≤ a`.
- `Nat.size_mod_add_one_le`: Bit-length reduction under modulo:
  `Nat.size (a % b) + 1 ≤ Nat.size a` whenever `0 < b ≤ a`.
- `Nat.euclideanGcdSteps_le_two_mul_size_of_le`: Upper bound `2 * Nat.size a`
  when `a ≤ b`.
- `Nat.euclideanGcdSteps_le_two_mul_size_min`: Upper bound
  `euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1`.
- `Nat.euclideanGcdSteps_le_two_mul_size_add`: Upper bound
  `euclideanGcdSteps a b ≤ 2 * Nat.size (a + b) + 1`.
-/

namespace Nat

/-- Companion step-counting function for `Nat.gcd`.
Counts the exact number of modulo transitions executed on inputs `a` and `b`.
Mirrors the reduction structure of `Nat.gcd.eq_def`: if `a = 0` then 0 steps,
otherwise 1 step plus the steps for `(b % a, a)`. -/
def euclideanGcdSteps (a b : ℕ) : ℕ :=
  if ha : a = 0 then 0
  else 1 + euclideanGcdSteps (b % a) a
termination_by a
decreasing_by
  exact Nat.mod_lt b (Nat.pos_of_ne_zero ha)

/-- The fundamental halving property of modulo: for positive `b ≤ a`,
the remainder satisfies `2 * (a % b) < a`. -/
lemma mod_two_mul_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : 2 * (a % b) < a := by
  have hdiv := Nat.div_add_mod a b
  have hmod := Nat.mod_lt a hb
  have hq0 : 0 < a / b := Nat.div_pos hba hb
  have hq_cases : a / b = 1 ∨ 2 ≤ a / b := by omega
  rcases hq_cases with hq1 | hq2
  · have h1 : b * (a / b) = b := by rw [hq1, Nat.mul_one]
    omega
  · have h2 : 2 * b ≤ b * (a / b) := by
      rw [Nat.mul_comm 2 b]
      exact Nat.mul_le_mul_left b hq2
    omega

/-- When `2 * r < a`, the bit size of `r` is strictly smaller than the bit size of `a`:
`Nat.size r + 1 ≤ Nat.size a`. -/
lemma size_add_one_le_of_two_mul_lt {r a : ℕ} (h : 2 * r < a) :
    Nat.size r + 1 ≤ Nat.size a := by
  have ha : 0 < a := by omega
  have hr : r ≤ a / 2 := by omega
  have hsz : Nat.size r ≤ Nat.size (a / 2) := Nat.size_le_size hr
  rw [← Nat.size_div_two a ha]
  omega

/-- Bit-length reduction under modulo: for positive `b ≤ a`, the bit length of `a % b`
is strictly less than that of `a`, that is, `Nat.size (a % b) + 1 ≤ Nat.size a`. -/
lemma size_mod_add_one_le {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    Nat.size (a % b) + 1 ≤ Nat.size a :=
  size_add_one_le_of_two_mul_lt (mod_two_mul_lt hb hba)

/-- Modulo halving inequality in division form: `a % b ≤ a / 2` whenever `0 < b ≤ a`. -/
lemma mod_le_div_two {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : a % b ≤ a / 2 := by
  have := mod_two_mul_lt hb hba
  omega

/-- Intermediate step bound when the first argument is bounded by the second:
`euclideanGcdSteps a b ≤ 2 * Nat.size a` whenever `a ≤ b`. -/
lemma euclideanGcdSteps_le_two_mul_size_of_le (a : ℕ) :
    ∀ b, a ≤ b → euclideanGcdSteps a b ≤ 2 * Nat.size a := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b hab
    by_cases ha : a = 0
    · rw [euclideanGcdSteps.eq_def, dif_pos ha]
      omega
    · rw [euclideanGcdSteps.eq_def, dif_neg ha]
      have ha_pos : 0 < a := Nat.pos_of_ne_zero ha
      have hr1_lt : b % a < a := Nat.mod_lt b ha_pos
      by_cases hr1 : b % a = 0
      · rw [euclideanGcdSteps.eq_def, dif_pos hr1]
        have : 0 < Nat.size a := Nat.size_pos.mpr ha_pos
        omega
      · have hr1_pos : 0 < b % a := Nat.pos_of_ne_zero hr1
        rw [euclideanGcdSteps.eq_def, dif_neg hr1]
        have hr2_lt : a % (b % a) < b % a := Nat.mod_lt a hr1_pos
        have hr2_le : a % (b % a) ≤ b % a := Nat.le_of_lt hr2_lt
        have hih := ih (a % (b % a)) (by omega) (b % a) hr2_le
        have hstep : Nat.size (a % (b % a)) + 1 ≤ Nat.size a :=
          size_mod_add_one_le hr1_pos (Nat.le_of_lt hr1_lt)
        omega

/-- Main upper bound for Euclidean GCD steps in terms of the minimum of the inputs:
`euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1`. -/
theorem euclideanGcdSteps_le_two_mul_size_min (a b : ℕ) :
    euclideanGcdSteps a b ≤ 2 * Nat.size (min a b) + 1 := by
  by_cases hab : a ≤ b
  · have h := euclideanGcdSteps_le_two_mul_size_of_le a b hab
    rw [min_eq_left hab]
    omega
  · have hba : b < a := by omega
    rw [min_eq_right (Nat.le_of_lt hba)]
    rw [euclideanGcdSteps.eq_def, dif_neg (by omega)]
    have hmod : b % a = b := Nat.mod_eq_of_lt hba
    rw [hmod]
    have h := euclideanGcdSteps_le_two_mul_size_of_le b a (Nat.le_of_lt hba)
    omega

/-- Upper bound for Euclidean GCD steps in terms of the sum of the inputs:
`euclideanGcdSteps a b ≤ 2 * Nat.size (a + b) + 1`. -/
theorem euclideanGcdSteps_le_two_mul_size_add (a b : ℕ) :
    euclideanGcdSteps a b ≤ 2 * Nat.size (a + b) + 1 := by
  have h := euclideanGcdSteps_le_two_mul_size_min a b
  have hmin : min a b ≤ a + b := by omega
  have hsz : Nat.size (min a b) ≤ Nat.size (a + b) := Nat.size_le_size hmin
  omega

end Nat
