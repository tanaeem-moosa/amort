/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.BinaryGCD
import Amort.GCD.StepCount
import Amort.GCD.EuclideanGCD

/-!
# Euclid's GCD: companion file

Companion to `tutorial/euclid_gcd.md`. Every Lean snippet the chapter quotes is either here or
in the reference file `Amort/GCD/EuclideanGCD.lean`, so Lean checks all of it on every build.
-/

set_option linter.hashCommand false
set_option linter.style.header false

namespace Tutorial.EuclideanGCD

/-! ## Step 3: running the algorithm -/

#guard Nat.euclidGcd 48 18 = 6
#guard Nat.euclidGcd 105 252 = 21
#guard Nat.euclidGcd 0 7 = 7
#guard Nat.euclidGcd 0 0 = 0

/-! ## Step 4: two algorithms, one specification -/

theorem euclid_eq_binary (a b : ℕ) : Nat.euclidGcd a b = Nat.binaryGcd a b := by
  rw [Nat.euclidGcd_eq_gcd, Nat.binaryGcd_eq_gcd]

/-! ## Step 5: counting calls -/

#guard Nat.euclidGcdWithSteps 48 18 = (6, 4)
#guard Nat.binaryGcdWithSteps 48 18 = (6, 6)

/-! ## Spot the fake: "euclidGcd is correct" -/

/-- Option A: the "algorithm" is the specification under another name. -/
def fakeEuclidAlgo (a b : ℕ) : ℕ := Nat.gcd a b

theorem fakeEuclidAlgo_eq (a b : ℕ) : fakeEuclidAlgo a b = Nat.gcd a b := rfl

/-- Option B: a third of the specification. -/
theorem euclidGcd_dvd_left (a b : ℕ) : Nat.euclidGcd a b ∣ a := by
  rw [Nat.euclidGcd_eq_gcd]
  exact Nat.gcd_dvd_left a b

/-! ## Exercises -/

#guard Nat.euclidGcdWithSteps 105 252 = (21, 3)
#guard Nat.euclidGcdWithSteps 252 105 = (21, 4)

/-- With an extra hypothesis that is not needed. -/
theorem euclidGcd_eq_left_of_pos_of_dvd (a b : ℕ) (_ha : 0 < a) (h : a ∣ b) :
    Nat.euclidGcd a b = a := by
  rw [Nat.euclidGcd_eq_gcd]
  exact Nat.gcd_eq_left h

/-- The stronger version: the same conclusion without `0 < a`. -/
theorem euclidGcd_eq_left_of_dvd (a b : ℕ) (h : a ∣ b) : Nat.euclidGcd a b = a := by
  rw [Nat.euclidGcd_eq_gcd]
  exact Nat.gcd_eq_left h

end Tutorial.EuclideanGCD
