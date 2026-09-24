/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.BinaryGCD
import Amort.GCD.StepCount

/-!
# Tutorial: Binary GCD (Stein's Algorithm)

Companion file for `tutorial/binary_gcd.md`.
Introduces:
- Algorithm formalization (`Nat.binaryGcd`)
- Verification against canonical specification (`Nat.binaryGcd_eq_gcd`)
- Instrumented step-counting pattern (`Nat.binaryGcdWithSteps`)
- Logarithmic bit-length bounds (`Nat.binaryGcdSteps_le_size_add_size`)

This file allows learners to interact with definitions, evaluate examples,
and check theorem statements locally.
-/

namespace Tutorial.BinaryGCD

/-! ### Step 3: Running the Executable Algorithm -/

-- Run `#eval` to compute greatest common divisors using Stein's algorithm:
#eval Nat.binaryGcd 48 18     -- 6
#eval Nat.binaryGcd 105 252   -- 21
#eval Nat.binaryGcd 0 7       -- 7
#eval Nat.binaryGcd 0 0       -- 0

/-! ### Step 4: Correctness Claims -/

-- Canonical equivalence to Mathlib's `Nat.gcd`:
#check Nat.binaryGcd_eq_gcd
-- ∀ (a b : ℕ), Nat.binaryGcd a b = Nat.gcd a b

/-- Learner experiment: Verify that binary GCD is commutative. -/
example (a b : ℕ) : Nat.binaryGcd a b = Nat.binaryGcd b a := by
  rw [Nat.binaryGcd_eq_gcd, Nat.binaryGcd_eq_gcd, Nat.gcd_comm]

/-- Learner experiment: Common factor extraction for even inputs. -/
example (a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 0) :
    Nat.binaryGcd a b = 2 * Nat.binaryGcd (a / 2) (b / 2) := by
  rw [Nat.binaryGcd_eq_gcd, Nat.binaryGcd_eq_gcd]
  exact Nat.gcd_even_even ha hb

/-! ### Step 5: Step Counting & Complexity Bounds -/

-- Run `#eval` on the instrumented function to see `(gcd, step_count)`:
#eval Nat.binaryGcdWithSteps 48 18    -- (6, 6)
#eval Nat.binaryGcdWithSteps 105 252  -- (21, 9)

-- Coupling theorems:
#check Nat.binaryGcdWithSteps_fst
-- ∀ (a b : ℕ), (Nat.binaryGcdWithSteps a b).1 = Nat.binaryGcd a b

#check Nat.binaryGcdWithSteps_snd
-- ∀ (a b : ℕ), (Nat.binaryGcdWithSteps a b).2 = Nat.binaryGcdSteps a b

-- Complexity upper bounds in terms of bit lengths (Nat.size):
#check Nat.binaryGcdSteps_le_size_add_size
-- ∀ (a b : ℕ), Nat.binaryGcdSteps a b ≤ Nat.size a + Nat.size b

#check Nat.binaryGcdWithSteps_snd_le_two_mul_size_add
-- ∀ (a b : ℕ), (Nat.binaryGcdWithSteps a b).2 ≤ 2 * Nat.size (a + b)

/-- Learner experiment: At least one step bound check on concrete values. -/
example : (Nat.binaryGcdWithSteps 48 18).2 ≤ Nat.size 48 + Nat.size 18 := by
  exact Nat.binaryGcdWithSteps_snd_le_size_add_size 48 18

/-! ### Spot the Fake: Compiling Real vs Fake Claims -/

/-- Fake 1 (Formula stand-in): True and provable, but completely vacuous because
`fakeCost` has no connection to any execution of `binaryGcd`. -/
def fakeCost (a b : ℕ) : ℕ := Nat.size a + Nat.size b

/-- Fake 1 bound theorem: Proves a bound on `fakeCost`, not the algorithm. -/
theorem fakeCost_le (a b : ℕ) : fakeCost a b ≤ Nat.size a + Nat.size b :=
  le_refl _

/-- Auxiliary lemma: Bit size of a natural number is bounded by its value. -/
lemma size_le_self (n : ℕ) : Nat.size n ≤ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simp
    | succ n =>
      have hdiv : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by decide)
      rw [← Nat.size_div_two (n + 1) (by omega)]
      have := ih ((n + 1) / 2) hdiv
      omega

/-- Fake 2 (Value bound): True and tied to the algorithm, but exponentially weak
compared to logarithmic bit bounds. -/
theorem binaryGcdSteps_le_val_add (a b : ℕ) :
    Nat.binaryGcdSteps a b ≤ a + b := by
  have h := Nat.binaryGcdSteps_le_size_add_size a b
  have ha : Nat.size a ≤ a := size_le_self a
  have hb : Nat.size b ≤ b := size_le_self b
  omega

/-- Genuine complexity result: Ties the actual instrumented execution output to
a logarithmic bit-length bound. -/
theorem genuine_complexity (a b : ℕ) :
    (Nat.binaryGcdWithSteps a b).1 = Nat.gcd a b ∧
    (Nat.binaryGcdWithSteps a b).2 ≤ Nat.size a + Nat.size b :=
  ⟨Nat.binaryGcdWithSteps_eq_gcd a b, Nat.binaryGcdWithSteps_snd_le_size_add_size a b⟩

end Tutorial.BinaryGCD
