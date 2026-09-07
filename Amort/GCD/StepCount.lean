/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.GCD.BinaryGCD
import Mathlib.Data.Nat.Size

/-!
# Step Counting and Complexity Bounds for Binary GCD

This module formalizes step counting for Stein's binary GCD algorithm and proves
explicit upper bounds on the number of recursive transitions in terms of the bit
lengths of the inputs.

## Key Definitions
- `Nat.binaryGcdSteps`: Companion function counting the recursive steps of `binaryGcd`.
- `Nat.binaryGcdWithSteps`: Instrumented representation returning `(gcd, steps)`.

## Key Theorems
- `Nat.binaryGcdWithSteps_fst`: The result of `binaryGcdWithSteps` matches `binaryGcd`.
- `Nat.binaryGcdWithSteps_snd`: The step count of `binaryGcdWithSteps` matches `binaryGcdSteps`.
- `Nat.binaryGcdWithSteps_eq_gcd`: The result of `binaryGcdWithSteps` equals `Nat.gcd a b`.
- `Nat.binaryGcdSteps_le_size_add_size`: `binaryGcdSteps a b ≤ Nat.size a + Nat.size b`.
- `Nat.binaryGcdSteps_le_two_mul_size_add`: `binaryGcdSteps a b ≤ 2 * Nat.size (a + b)`.
-/

namespace Nat

/-- Companion step-counting function for `binaryGcd`.
Counts the exact number of recursive transitions executed on inputs `a` and `b`. -/
def binaryGcdSteps (a b : ℕ) : ℕ :=
  if _ha : a = 0 then 0
  else if _hb : b = 0 then 0
  else if _ha_even : a % 2 = 0 then
    if _hb_even : b % 2 = 0 then
      1 + binaryGcdSteps (a / 2) (b / 2)
    else
      1 + binaryGcdSteps (a / 2) b
  else if _hb_even : b % 2 = 0 then
    1 + binaryGcdSteps a (b / 2)
  else
    if _h_le : b ≤ a then
      1 + binaryGcdSteps ((a - b) / 2) b
    else
      1 + binaryGcdSteps a ((b - a) / 2)
termination_by a + b
decreasing_by
  all_goals omega

/-- Instrumented representation of binary GCD that computes both the GCD
and the total number of recursive transitions in a single pass. -/
def binaryGcdWithSteps (a b : ℕ) : ℕ × ℕ :=
  if _ha : a = 0 then (b, 0)
  else if _hb : b = 0 then (a, 0)
  else if ha_even : a % 2 = 0 then
    if hb_even : b % 2 = 0 then
      let r := binaryGcdWithSteps (a / 2) (b / 2)
      (2 * r.1, r.2 + 1)
    else
      let r := binaryGcdWithSteps (a / 2) b
      (r.1, r.2 + 1)
  else if hb_even : b % 2 = 0 then
    let r := binaryGcdWithSteps a (b / 2)
    (r.1, r.2 + 1)
  else
    if h_le : b ≤ a then
      let r := binaryGcdWithSteps ((a - b) / 2) b
      (r.1, r.2 + 1)
    else
      let r := binaryGcdWithSteps a ((b - a) / 2)
      (r.1, r.2 + 1)
termination_by a + b
decreasing_by
  all_goals omega

/-- The computed GCD in `binaryGcdWithSteps` matches `binaryGcd`. -/
@[simp]
theorem binaryGcdWithSteps_fst (a b : ℕ) :
    (binaryGcdWithSteps a b).1 = binaryGcd a b := by
  induction a, b using binaryGcd.induct with
  | case1 b =>
    rw [binaryGcdWithSteps.eq_def, binaryGcd.eq_def, dif_pos rfl, dif_pos rfl]
  | case2 a ha =>
    rw [binaryGcdWithSteps.eq_def, binaryGcd.eq_def, dif_neg ha, dif_pos rfl,
      dif_neg ha, dif_pos rfl]
  | case3 a b ha hb ha_even hb_even ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even]
  | case4 a b ha hb ha_even hb_odd ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd]
  | case5 a b ha hb ha_odd hb_even ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even]
  | case6 a b ha hb ha_odd hb_odd hba ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_pos hba]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_pos hba]
  | case7 a b ha hb ha_odd hb_odd hnba ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_neg hnba]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_neg hnba]

/-- The step counter in `binaryGcdWithSteps` matches `binaryGcdSteps`. -/
@[simp]
theorem binaryGcdWithSteps_snd (a b : ℕ) :
    (binaryGcdWithSteps a b).2 = binaryGcdSteps a b := by
  induction a, b using binaryGcdSteps.induct with
  | case1 b =>
    rw [binaryGcdWithSteps.eq_def, binaryGcdSteps.eq_def, dif_pos rfl, dif_pos rfl]
  | case2 a ha =>
    rw [binaryGcdWithSteps.eq_def, binaryGcdSteps.eq_def, dif_neg ha, dif_pos rfl,
      dif_neg ha, dif_pos rfl]
  | case3 a b ha hb ha_even hb_even ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even]
    omega
  | case4 a b ha hb ha_even hb_odd ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd]
    omega
  | case5 a b ha hb ha_odd hb_even ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even]
    omega
  | case6 a b ha hb ha_odd hb_odd hba ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_pos hba]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_pos hba]
    omega
  | case7 a b ha hb ha_odd hb_odd hnba ih =>
    rw [binaryGcdWithSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_neg hnba]
    dsimp
    rw [ih]
    conv_rhs => rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_neg hnba]
    omega

/-- Combined product equality for the instrumented binary GCD. -/
@[simp]
theorem binaryGcdWithSteps_eq (a b : ℕ) :
    binaryGcdWithSteps a b = (binaryGcd a b, binaryGcdSteps a b) :=
  Prod.ext (binaryGcdWithSteps_fst a b) (binaryGcdWithSteps_snd a b)

/-- The instrumented function computes `Nat.gcd a b`. -/
theorem binaryGcdWithSteps_eq_gcd (a b : ℕ) :
    (binaryGcdWithSteps a b).1 = Nat.gcd a b := by
  rw [binaryGcdWithSteps_fst, binaryGcd_eq_gcd]

/-- Halving a strictly positive natural number decrements its bit size by 1. -/
lemma size_div_two (a : ℕ) (ha : 0 < a) : Nat.size (a / 2) + 1 = Nat.size a := by
  induction a using Nat.binaryRec' with
  | zero => omega
  | bit b n _ _ =>
    rw [Nat.size_bit (by omega), Nat.bit_div_two]

/-- Subtraction and halving bounded by bit size: for positive `a`,
`size ((a - b) / 2) + 1 ≤ size a`. -/
lemma size_sub_div_two_le (a b : ℕ) (ha : 0 < a) :
    Nat.size ((a - b) / 2) + 1 ≤ Nat.size a := by
  rw [← size_div_two a ha]
  exact Nat.add_le_add_right (Nat.size_le_size (by omega)) 1

/-- The number of recursive steps of `binaryGcd` is bounded above by the sum of the
bit lengths (logarithmic sizes) of the two arguments:
`binaryGcdSteps a b ≤ Nat.size a + Nat.size b`. -/
theorem binaryGcdSteps_le_size_add_size (a b : ℕ) :
    binaryGcdSteps a b ≤ Nat.size a + Nat.size b := by
  induction a, b using binaryGcdSteps.induct with
  | case1 b =>
    rw [binaryGcdSteps.eq_def, dif_pos rfl]
    omega
  | case2 a ha =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_pos rfl]
    omega
  | case3 a b ha hb ha_even hb_even ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even]
    have := size_div_two a (by omega)
    have := size_div_two b (by omega)
    omega
  | case4 a b ha hb ha_even hb_odd ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd]
    have := size_div_two a (by omega)
    omega
  | case5 a b ha hb ha_odd hb_even ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even]
    have := size_div_two b (by omega)
    omega
  | case6 a b ha hb ha_odd hb_odd hba ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_pos hba]
    have := size_sub_div_two_le a b (by omega)
    omega
  | case7 a b ha hb ha_odd hb_odd hnba ih =>
    rw [binaryGcdSteps.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd,
      dif_neg hnba]
    have := size_sub_div_two_le b a (by omega)
    omega

/-- Step bound in terms of the bit length of the sum:
`binaryGcdSteps a b ≤ 2 * Nat.size (a + b)`. -/
theorem binaryGcdSteps_le_two_mul_size_add (a b : ℕ) :
    binaryGcdSteps a b ≤ 2 * Nat.size (a + b) := by
  have h := binaryGcdSteps_le_size_add_size a b
  have ha : Nat.size a ≤ Nat.size (a + b) := Nat.size_le_size (Nat.le_add_right a b)
  have hb : Nat.size b ≤ Nat.size (a + b) := Nat.size_le_size (Nat.le_add_left b a)
  omega

/-- Upper bound for the instrumented step counter:
`(binaryGcdWithSteps a b).2 ≤ Nat.size a + Nat.size b`. -/
theorem binaryGcdWithSteps_snd_le_size_add_size (a b : ℕ) :
    (binaryGcdWithSteps a b).2 ≤ Nat.size a + Nat.size b := by
  rw [binaryGcdWithSteps_snd]
  exact binaryGcdSteps_le_size_add_size a b

/-- Upper bound for the instrumented step counter in terms of the sum:
`(binaryGcdWithSteps a b).2 ≤ 2 * Nat.size (a + b)`. -/
theorem binaryGcdWithSteps_snd_le_two_mul_size_add (a b : ℕ) :
    (binaryGcdWithSteps a b).2 ≤ 2 * Nat.size (a + b) := by
  rw [binaryGcdWithSteps_snd]
  exact binaryGcdSteps_le_two_mul_size_add a b

end Nat
