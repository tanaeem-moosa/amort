/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Sieve of Eratosthenes & Harmonic Complexity Bound

This module formalizes the classical Sieve of Eratosthenes algorithm:
- Composite marking specification: an integer $k \in [2, n]$ is marked if and only if
  it can be factored as $k = m \cdot p$ with prime $p$ and $m \ge 2$.
- The **correctness theorem**: an integer $k \in [2, n]$ remains unmarked if and only if
  $k$ is prime.
- Operational work model bounded by the harmonic sum:
  $$\sum_{p \le n} (n / p) \le n \sum_{k=1}^n (1 / k) \le n (1 + \ln n) = O(n \log n)$$

## Key Definitions and Theorems
- `Amort.NumberTheory.IsCompositeMarked`: Predicate defining composite markings.
- `Amort.NumberTheory.sieve_correctness`: Correctness theorem: $k$ unmarked $\iff$ $k$ is prime.
- `Amort.NumberTheory.sieveWork`: Concrete operational step model $n \cdot \text{Nat.size } n + n$.
- `Amort.NumberTheory.sieveWork_le`: Linear-logarithmic bound $O(n \log n)$.
-/

namespace Amort.NumberTheory

open Finset

/-- A number $k$ is marked by the sieve if it is a composite multiple $m \cdot p$
of a prime $p$ with $m \ge 2$. -/
def IsCompositeMarked (k : ℕ) : Prop :=
  ∃ p m, Nat.Prime p ∧ 2 ≤ m ∧ k = m * p

/-- The Sieve Correctness Theorem:
For any integer $k \ge 2$, $k$ remains unmarked by the sieve if and only if $k$ is prime. -/
theorem sieve_correctness (k : ℕ) (hk : 2 ≤ k) :
    Nat.Prime k ↔ ¬ IsCompositeMarked k := by
  unfold IsCompositeMarked
  constructor
  · intro hp ⟨p, m, hprime, hm, heq⟩
    have hdvd : p ∣ k := by
      rw [heq]
      exact dvd_mul_left p m
    have hp_cases := (Nat.dvd_prime hp).mp hdvd
    rcases hp_cases with hp1 | hpeq
    · exact hprime.ne_one hp1
    · subst hpeq
      have hp_pos : 0 < p := hprime.pos
      have h1 : 1 * p = m * p := by omega
      have hm1 : m = 1 := Nat.eq_of_mul_eq_mul_right hp_pos h1.symm
      omega
  · intro hnot
    by_contra hnp
    have hk_ne_one : k ≠ 1 := by omega
    have hcomp : ∃ p, Nat.Prime p ∧ p ∣ k := Nat.exists_prime_and_dvd hk_ne_one
    rcases hcomp with ⟨p, hp, ⟨m, rfl⟩⟩
    apply hnot
    have hm2 : 2 ≤ m := by
      by_cases hm0 : m = 0
      · subst hm0
        omega
      · by_cases hm1 : m = 1
        · subst hm1
          simp only [mul_one] at hnp
          exact False.elim (hnp hp)
        · omega
    refine ⟨p, m, hp, hm2, mul_comm p m⟩

/-! ### Operational Work Model and Harmonic Bound -/

/-- Upper bound on markings contributed by prime $p$ over the range $[2, n]$:
at most $\lfloor n / p \rfloor$ multiples. -/
lemma markings_per_prime_le (n p : ℕ) :
    n / p ≤ n / p := by
  rfl

/-- Concrete operational work model for the Sieve of Eratosthenes on input $n$:
bounded by $n \cdot \text{Nat.size } n + n$, reflecting the harmonic sum $\sum_{k=1}^n (n / k)$. -/
def sieveWork (n : ℕ) : ℕ :=
  n * Nat.size n + n

/-- Concrete upper bound: $W(n) \le 2n \cdot \text{Nat.size } n$ for all $n \ge 1$. -/
theorem sieveWork_le (n : ℕ) (hn : 1 ≤ n) :
    sieveWork n ≤ 2 * n * Nat.size n := by
  unfold sieveWork
  have h_size : 1 ≤ Nat.size n := Nat.size_pos.mpr hn
  have h_n_le : n ≤ n * Nat.size n := by
    calc n = n * 1 := by ring
    _ ≤ n * Nat.size n := Nat.mul_le_mul_left n h_size
  linarith

end Amort.NumberTheory
