/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.EuclideanGCD
import Amort.GCD.BinaryGCD

/-!
# Tutorial: Euclidean GCD

Companion file for `tutorial/euclid_gcd.md`.
Introduces:
- Classical Euclidean algorithm (`Nat.euclidGcd`)
- Cross-algorithm equivalence (`euclidGcd a b = binaryGcd a b`)
- Instrumented step-counting for modulo transitions (`Nat.euclidGcdWithSteps`)
- Halving property of modulo and logarithmic bounds
  (`Nat.euclidGcdWithSteps_snd_le_two_mul_size_min`)

This file allows learners to interact with definitions, evaluate examples,
and check theorem statements locally.
-/

namespace Tutorial.EuclideanGCD

/-! ### Step 3: Running the Executable Algorithm -/

-- Run `#eval` to compute greatest common divisors using repeated remainders:
#eval Nat.euclidGcd 48 18     -- 6
#eval Nat.euclidGcd 105 252   -- 21
#eval Nat.euclidGcd 0 7       -- 7
#eval Nat.euclidGcd 0 0       -- 0

/-! ### Step 4: Correctness Claims -/

-- Equivalence to Mathlib specification `Nat.gcd`:
#check Nat.euclidGcd_eq_gcd
-- ∀ (a b : ℕ), Nat.euclidGcd a b = Nat.gcd a b

/-- Cross-algorithm equivalence: Euclid and Binary GCD compute identical results. -/
theorem euclid_eq_binary (a b : ℕ) : Nat.euclidGcd a b = Nat.binaryGcd a b := by
  rw [Nat.euclidGcd_eq_gcd, Nat.binaryGcd_eq_gcd]

/-- Learner experiment: Zero left identity. -/
example (b : ℕ) : Nat.euclidGcd 0 b = b := by
  exact Nat.euclidGcd_eq_gcd 0 b ▸ Nat.gcd_zero_left b

/-! ### Step 5: Step Counting & Complexity Bounds -/

-- Compare execution steps between Euclid and Binary GCD:
#eval Nat.euclidGcdWithSteps 48 18    -- (6, 4): 4 modulo operations
#eval Nat.binaryGcdWithSteps 48 18   -- (6, 6): 6 binary transitions

-- Coupling theorems:
#check Nat.euclidGcdWithSteps_fst
-- ∀ (a b : ℕ), (Nat.euclidGcdWithSteps a b).1 = Nat.euclidGcd a b

#check Nat.euclidGcdWithSteps_snd
-- ∀ (a b : ℕ), (Nat.euclidGcdWithSteps a b).2 = Nat.euclideanGcdSteps a b

-- Key invariant: The modulo halving property:
#check Nat.mod_two_mul_lt
-- 0 < b → b ≤ a → 2 * (a % b) < a

-- Logarithmic upper bound in terms of the minimum input bit-length:
#check Nat.euclidGcdWithSteps_snd_le_two_mul_size_min
-- ∀ (a b : ℕ), (Nat.euclidGcdWithSteps a b).2 ≤ 2 * Nat.size (min a b) + 1

/-- Learner experiment: Check the bound on a concrete input. -/
example : (Nat.euclidGcdWithSteps 48 18).2 ≤ 2 * Nat.size (min 48 18) + 1 := by
  exact Nat.euclidGcdWithSteps_snd_le_two_mul_size_min 48 18

/-! ### Spot the Fake: Compiling Real vs Fake Claims -/

/-- Fake 1 (Linear bound): Provable, but hides the logarithmic efficiency of Euclid. -/
theorem euclid_steps_le_linear (a b : ℕ) :
    Nat.euclideanGcdSteps a b ≤ 2 * (min a b) + 1 := by
  have h := Nat.euclideanGcdSteps_le_two_mul_size_min a b
  have hsz : Nat.size (min a b) ≤ min a b := by
    induction min a b using Nat.strong_induction_on with
    | h n ih =>
      cases n with
      | zero => simp
      | succ n =>
        have hdiv : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
        rw [← Nat.size_div_two (n + 1) (by omega)]
        have := ih ((n + 1) / 2) hdiv
        omega
  omega

/-- Fake 2 (Spec renamed as algo): Does zero algorithmic work. -/
def fakeEuclidAlgo (a b : ℕ) : ℕ := Nat.gcd a b

/-- Fake 2 correctness is tautological. -/
theorem fakeEuclidAlgo_eq (a b : ℕ) : fakeEuclidAlgo a b = Nat.gcd a b := rfl

/-- Genuine result: Real recursive algorithm, coupled counter, logarithmic bound. -/
theorem genuine_euclid_result (a b : ℕ) :
    (Nat.euclidGcdWithSteps a b).1 = Nat.gcd a b ∧
    (Nat.euclidGcdWithSteps a b).2 ≤ 2 * Nat.size (min a b) + 1 :=
  ⟨Nat.euclidGcdWithSteps_fst_eq_gcd a b,
   Nat.euclidGcdWithSteps_snd_le_two_mul_size_min a b⟩

end Tutorial.EuclideanGCD
