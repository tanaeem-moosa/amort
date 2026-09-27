/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.BinaryGCD
import Amort.GCD.StepCount

/-!
# Binary GCD: companion file

Companion to `tutorial/binary_gcd.md`. Every Lean snippet the chapter quotes is either here or
in the reference files (`Amort/GCD/BinaryGCD.lean`, `Amort/GCD/StepCount.lean`), so Lean
checks all of it on every build.
-/

set_option linter.hashCommand false
set_option linter.style.header false

namespace Tutorial.BinaryGCD

/-! ## Step 2: the specification -/

example : ∀ a b : ℕ, Nat.gcd a b ∣ a := Nat.gcd_dvd_left
example : ∀ a b : ℕ, Nat.gcd a b ∣ b := Nat.gcd_dvd_right
example : ∀ {a b d : ℕ}, d ∣ a → d ∣ b → d ∣ Nat.gcd a b := Nat.dvd_gcd

/-! ## Step 3: running the algorithm -/

#guard Nat.binaryGcd 48 18 = 6
#guard Nat.binaryGcd 105 252 = 21
#guard Nat.binaryGcd 0 7 = 7
#guard Nat.binaryGcd 0 0 = 0

/-! ## Step 5: counting calls -/

#guard Nat.binaryGcdWithSteps 48 18 = (6, 6)
#guard Nat.binaryGcdWithSteps 105 252 = (21, 5)

/-! ## Spot the fake, round 1: "binaryGcd is correct" -/

/-- Option A: true, but only half the specification. -/
theorem binaryGcd_dvd_both (a b : ℕ) :
    Nat.binaryGcd a b ∣ a ∧ Nat.binaryGcd a b ∣ b := by
  rw [Nat.binaryGcd_eq_gcd]
  exact ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩

/-- A function that ignores its inputs. -/
def alwaysOne (_ _ : ℕ) : ℕ := 1

/-- `alwaysOne` passes option A's specification too. -/
theorem alwaysOne_dvd_both (a b : ℕ) :
    alwaysOne a b ∣ a ∧ alwaysOne a b ∣ b :=
  ⟨one_dvd a, one_dvd b⟩

/-- Option B: one test case. -/
theorem binaryGcd_48_18 : Nat.binaryGcd 48 18 = 6 := by
  rw [Nat.binaryGcd_eq_gcd]
  rfl

/-! ## Spot the fake, round 2: "binaryGcd makes at most bits(a) + bits(b) calls" -/

/-- Option A: a cost defined as its own bound. -/
def gcdCost (a b : ℕ) : ℕ := Nat.size a + Nat.size b

theorem gcdCost_le (a b : ℕ) :
    gcdCost a b ≤ Nat.size a + Nat.size b :=
  le_refl _

/-- The number of bits of `n` is at most `n`. -/
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

/-- Option C: about the real counter, but bounded by the size of the numbers, not their bits. -/
theorem binaryGcdSteps_le_val_add (a b : ℕ) :
    Nat.binaryGcdSteps a b ≤ a + b := by
  have h := Nat.binaryGcdSteps_le_size_add_size a b
  have ha : Nat.size a ≤ a := size_le_self a
  have hb : Nat.size b ≤ b := size_le_self b
  omega

/-! ## Exercises -/

#guard Nat.binaryGcd 60 24 = 12
#guard Nat.binaryGcdWithSteps 60 24 = (12, 6)

theorem binaryGcd_comm (a b : ℕ) : Nat.binaryGcd a b = Nat.binaryGcd b a := by
  rw [Nat.binaryGcd_eq_gcd, Nat.binaryGcd_eq_gcd, Nat.gcd_comm]

end Tutorial.BinaryGCD
