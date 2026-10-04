/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.NumberTheory.ModExp

/-!
# Modular exponentiation: companion file

Companion to `tutorial/mod_exp.md`. Every Lean snippet the chapter quotes is either here or in
the reference file `Amort/NumberTheory/ModExp.lean`, so Lean checks all of it on every build.
-/

set_option linter.hashCommand false
set_option linter.style.header false

open Amort.NumberTheory

namespace Tutorial.ModExp

/-! ## Step 3: running the algorithm -/

#guard modExp 3 13 100 = 23
#guard modExp 2 10 1000 = 24
#guard modExp 7 1000000 13 = 9

/-! ## Step 4: the modulus 0 -/

#guard modExp 5 3 0 = 0
#guard 5 ^ 3 % 0 = 125

/-! ## Step 5: counting multiplications -/

#guard modExpWithCount 3 13 100 = (23, 7)
#guard modExpWithCount 7 1000000 13 = (9, 27)

/-! ## Spot the fake: "modExp is correct" -/

/-- Option B: true of any function that returns a remainder. -/
theorem modExp_lt (a b m : ℕ) (hm : 0 < m) : modExp a b m < m := by
  unfold modExp
  rw [if_neg (by omega), modExpAux_correct m (1 % m) (a % m) b hm]
  exact Nat.mod_lt _ hm

/-- The "specification", defined as the algorithm. -/
def powMod (a b m : ℕ) : ℕ := modExp a b m

/-- Option C: the algorithm equals itself under another name. -/
theorem modExp_eq_powMod (a b m : ℕ) : modExp a b m = powMod a b m := rfl

/-! ## Exercises -/

theorem modExp_correct_of_pos (a b m : ℕ) (hm : 0 < m) :
    modExp a b m = (a ^ b) % m := by
  unfold modExp
  rw [if_neg (by omega), modExpAux_correct m (1 % m) (a % m) b hm]
  have h := Nat.ModEq.mul (Nat.mod_modEq 1 m) (Nat.ModEq.pow b (Nat.mod_modEq a m))
  rw [one_mul] at h
  exact h

end Tutorial.ModExp
