/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.GCD.Basic

/-!
# Binary GCD (Stein's Algorithm) in Lean 4

This module formalizes the binary GCD algorithm (also known as Stein's algorithm)
over the natural numbers (`ℕ`).

## Key Results
- `binaryGcd`: Executable definition of binary GCD with termination proven by `a + b`.
- `binaryGcd_eq_gcd`: Proof of equivalence `∀ a b, binaryGcd a b = Nat.gcd a b`.

## Invariant Lemmas
- `coprime_two_of_odd`: An odd natural number is coprime to 2.
- `gcd_even_odd`: `gcd(a, b) = gcd(a / 2, b)` when `a` is even and `b` is odd.
- `gcd_odd_even`: `gcd(a, b) = gcd(a, b / 2)` when `a` is odd and `b` is even.
- `gcd_even_even`: `gcd(a, b) = 2 * gcd(a / 2, b / 2)` when `a` and `b` are even.
- `gcd_odd_odd_sub_div2`: `gcd(a, b) = gcd((a - b) / 2, b)` when `a, b` are odd and `b ≤ a`.
- `gcd_odd_odd_sub_div2_right`: `gcd(a, b) = gcd(a, (b - a) / 2)` when `a, b` are odd and `a ≤ b`.
-/

/-- Stein's binary GCD algorithm computing the greatest common divisor of `a` and `b`.
The recursion terminates because the measure `a + b` strictly decreases at every step. -/
def binaryGcd (a b : ℕ) : ℕ :=
  if _ha : a = 0 then b
  else if _hb : b = 0 then a
  else if ha_even : a % 2 = 0 then
    if hb_even : b % 2 = 0 then
      2 * binaryGcd (a / 2) (b / 2)
    else
      binaryGcd (a / 2) b
  else if hb_even : b % 2 = 0 then
    binaryGcd a (b / 2)
  else
    if h_le : b ≤ a then
      binaryGcd ((a - b) / 2) b
    else
      binaryGcd a ((b - a) / 2)
termination_by a + b
decreasing_by
  all_goals omega

/-- Any odd natural number is coprime to 2. -/
theorem coprime_two_of_odd {b : ℕ} (hb : b % 2 = 1) : Nat.Coprime 2 b := by
  dsimp [Nat.Coprime]
  rw [Nat.gcd_rec, hb]
  exact Nat.gcd_one_left 2

/-- Elimination of factor 2: if `a` is even and `b` is odd, `gcd a b = gcd (a / 2) b`. -/
theorem gcd_even_odd {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 1) :
    Nat.gcd a b = Nat.gcd (a / 2) b := by
  have h2 : a = 2 * (a / 2) := by omega
  nth_rw 1 [h2]
  have hcop : Nat.Coprime 2 b := coprime_two_of_odd hb
  exact Nat.Coprime.gcd_mul_left_cancel (a / 2) hcop

/-- Elimination of factor 2 (symmetric): if `a` is odd and `b` is even,
`gcd a b = gcd a (b / 2)`. -/
theorem gcd_odd_even {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 0) :
    Nat.gcd a b = Nat.gcd a (b / 2) := by
  rw [Nat.gcd_comm, gcd_even_odd hb ha, Nat.gcd_comm]

/-- Common factor of 2 extraction: if both `a` and `b` are even,
`gcd a b = 2 * gcd (a / 2) (b / 2)`. -/
theorem gcd_even_even {a b : ℕ} (ha : a % 2 = 0) (hb : b % 2 = 0) :
    Nat.gcd a b = 2 * Nat.gcd (a / 2) (b / 2) := by
  have ha2 : a = 2 * (a / 2) := by omega
  have hb2 : b = 2 * (b / 2) := by omega
  nth_rw 1 [ha2]
  nth_rw 1 [hb2]
  exact Nat.gcd_mul_left 2 (a / 2) (b / 2)

/-- Subtraction invariant combined with factor-of-2 elimination for two odd numbers:
if `a` and `b` are odd and `b ≤ a`, then `a - b` is even, so
`gcd a b = gcd (a - b) b = gcd ((a - b) / 2) b`. -/
theorem gcd_odd_odd_sub_div2 {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (h : b ≤ a) :
    Nat.gcd a b = Nat.gcd ((a - b) / 2) b := by
  have h_sub_even : (a - b) % 2 = 0 := by omega
  have h_step1 : Nat.gcd a b = Nat.gcd (a - b) b := by
    rw [Nat.gcd_sub_self_left h]
  rw [h_step1]
  exact gcd_even_odd h_sub_even hb

/-- Symmetric subtraction invariant for two odd numbers with `a ≤ b`:
`gcd a b = gcd a ((b - a) / 2)`. -/
theorem gcd_odd_odd_sub_div2_right {a b : ℕ} (ha : a % 2 = 1) (hb : b % 2 = 1) (h : a ≤ b) :
    Nat.gcd a b = Nat.gcd a ((b - a) / 2) := by
  rw [Nat.gcd_comm, gcd_odd_odd_sub_div2 hb ha h, Nat.gcd_comm]

/-- **Main Equivalence Theorem (R2)**:
The binary GCD algorithm computes the exact same mathematical function as `Nat.gcd`
for all natural numbers `a` and `b`. -/
theorem binaryGcd_eq_gcd (a b : ℕ) : binaryGcd a b = Nat.gcd a b := by
  induction a, b using binaryGcd.induct with
  | case1 b =>
    rw [binaryGcd.eq_def, dif_pos rfl, Nat.gcd_zero_left]
  | case2 a ha =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_pos rfl, Nat.gcd_zero_right]
  | case3 a b ha hb ha_even hb_even ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_pos hb_even]
    rw [ih]
    exact (gcd_even_even ha_even hb_even).symm
  | case4 a b ha hb ha_even hb_odd ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_pos ha_even, dif_neg hb_odd]
    rw [ih]
    exact (gcd_even_odd ha_even (by omega)).symm
  | case5 a b ha hb ha_odd hb_even ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_pos hb_even]
    rw [ih]
    exact (gcd_odd_even (by omega) hb_even).symm
  | case6 a b ha hb ha_odd hb_odd hba ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd, dif_pos hba]
    rw [ih]
    exact (gcd_odd_odd_sub_div2 (by omega) (by omega) hba).symm
  | case7 a b ha hb ha_odd hb_odd hnba ih =>
    rw [binaryGcd.eq_def, dif_neg ha, dif_neg hb, dif_neg ha_odd, dif_neg hb_odd, dif_neg hnba]
    rw [ih]
    exact (gcd_odd_odd_sub_div2_right (by omega) (by omega) (by omega)).symm
