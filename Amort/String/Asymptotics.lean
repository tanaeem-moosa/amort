/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Composition
import Amort.String.EditDistance
import Amort.String.KMP
import Amort.String.LCS
import Amort.String.NaiveMatch
import Mathlib.Order.Filter.Prod

/-!
# Asymptotic Complexity Bridges for String Algorithms

This module establishes formal asymptotic complexity bounds in Mathlib's
`Mathlib.Analysis.Asymptotics.IsBigO` framework for textbook string algorithms:
- Naive string matching ($O(n \cdot m)$ worst-case comparisons).
- Knuth-Morris-Pratt string matching ($O(n + m)$ linear time preprocessing and scanning).
- Longest Common Subsequence dynamic programming table ($O(n \cdot m)$ operations).
- Edit Distance dynamic programming matrix ($O(n \cdot m)$ operations).

## Mathematical Architecture
1. **Product Composition**:
   Connecting 2D table and nested loop bounds to `Amort.Recurrence.isBigO_nested_loops_nat`.
   Since $n + 1 = O(n)$ and $m + 1 = O(m)$ under `Filter.atTop` on `ℕ × ℕ`, the product
   $(n + 1) \cdot (m + 1)$ is $O(n \cdot m)$.
2. **Sequential Phase Composition**:
   Connecting linear KMP bounds to `Amort.Recurrence.isBigO_sequential_add_nat`.
   Preprocessing $2m = O(m)$ and text scanning $2n = O(n)$ compose to $2(n + m) = O(n + m)$.
3. **Filter Bridges**:
   Establishing formal bounds under `Filter.atTop` on `ℕ × ℕ` as well as arbitrary
   pullback filters on sequence pairs.
-/

namespace Amort.String

open Asymptotics
open Amort.Recurrence

/-! ### Asymptotics of Increments on `ℕ × ℕ` -/

/-- The first component increment `n + 1` is `O(n)` under `Filter.atTop` on `ℕ × ℕ`. -/
lemma isBigO_fst_add_one_atTop :
    (fun (p : ℕ × ℕ) ↦ ((p.1 + 1 : ℕ) : ℝ)) =O[Filter.atTop] (fun p ↦ ((p.1 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  rw [Filter.eventually_atTop]
  refine ⟨(1, 0), ?_⟩
  rintro ⟨n, m⟩ ⟨hn, _hm⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  push_cast
  have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  linarith

/-- The second component increment `m + 1` is `O(m)` under `Filter.atTop` on `ℕ × ℕ`. -/
lemma isBigO_snd_add_one_atTop :
    (fun (p : ℕ × ℕ) ↦ ((p.2 + 1 : ℕ) : ℝ)) =O[Filter.atTop] (fun p ↦ ((p.2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  rw [Filter.eventually_atTop]
  refine ⟨(0, 1), ?_⟩
  rintro ⟨n, m⟩ ⟨_hn, hm⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  push_cast
  have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  linarith

/-- Composition bridge: `(n + 1) * (m + 1) = O(n * m)` under `Filter.atTop` on `ℕ × ℕ`
via `Amort.Recurrence.isBigO_nested_loops_nat`. -/
theorem isBigO_succ_mul_succ_atTop :
    (fun (p : ℕ × ℕ) ↦ (((p.1 + 1) * (p.2 + 1) : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 * p.2 : ℕ) : ℝ)) :=
  isBigO_nested_loops_nat (fun (p : ℕ × ℕ) ↦ p.1 + 1) (fun p ↦ p.1)
    (fun (p : ℕ × ℕ) ↦ p.2 + 1) (fun p ↦ p.2)
    isBigO_fst_add_one_atTop isBigO_snd_add_one_atTop

/-! ### Sequence Alignment DP Asymptotics (LCS & Edit Distance) -/

/-- LCS DP table size `(n + 1) * (m + 1)` is asymptotically `O(n * m)` on `ℕ × ℕ`. -/
theorem isBigO_lcsTableCount_atTop :
    (fun (p : ℕ × ℕ) ↦ (((p.1 + 1) * (p.2 + 1) : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 * p.2 : ℕ) : ℝ)) :=
  isBigO_succ_mul_succ_atTop

/-- Edit Distance DP matrix size `(n + 1) * (m + 1)` is asymptotically `O(n * m)` on `ℕ × ℕ`. -/
theorem isBigO_editDistTableCount_atTop :
    (fun (p : ℕ × ℕ) ↦ (((p.1 + 1) * (p.2 + 1) : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 * p.2 : ℕ) : ℝ)) :=
  isBigO_succ_mul_succ_atTop

/-- LCS table operation count is pointwise bounded and asymptotically `O((n + 1) * (m + 1))`
under any filter on sequence pairs. -/
theorem isBigO_lcsTableCount_list {α : Type*} (F : Filter (List α × List α)) :
    (fun (p : List α × List α) ↦ ((lcsTableCount p.1 p.2 : ℕ) : ℝ)) =O[F]
      (fun p ↦ (((p.1.length + 1) * (p.2.length + 1) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro ⟨xs, ys⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := lcsTableCount_le xs ys
  exact_mod_cast h

/-- Edit Distance matrix operation count is pointwise bounded and asymptotically
`O((n + 1) * (m + 1))` under any filter on sequence pairs. -/
theorem isBigO_editDistTableCount_list {α : Type*} (F : Filter (List α × List α)) :
    (fun (p : List α × List α) ↦ ((editDistTableCount p.1 p.2 : ℕ) : ℝ)) =O[F]
      (fun p ↦ (((p.1.length + 1) * (p.2.length + 1) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro ⟨xs, ys⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := editDistTableCount_le xs ys
  exact_mod_cast h

/-! ### String Matching Asymptotics (Naive vs. KMP) -/

/-- Naive string matching worst-case comparison bound `n * m` is reflexive `O(n * m)`
on `ℕ × ℕ`. -/
theorem isBigO_naiveMatch_bound_atTop :
    (fun (p : ℕ × ℕ) ↦ ((p.1 * p.2 : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 * p.2 : ℕ) : ℝ)) :=
  isBigO_refl _ _

/-- Naive string matching comparisons are bounded by `|T| * |P|` under any filter on pairs. -/
theorem isBigO_naiveMatchCount_list {α : Type*} [DecidableEq α]
    (F : Filter (List α × List α)) :
    (fun (p : List α × List α) ↦ ((naiveMatchCount p.1 p.2 : ℕ) : ℝ)) =O[F]
      (fun p ↦ ((p.2.length * p.1.length : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro ⟨P, T⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := naiveMatchCount_le_mul P T
  exact_mod_cast h

/-- First phase of KMP (text scanning bound `2n`) is `O(n)` on `ℕ × ℕ`. -/
lemma isBigO_two_mul_fst_atTop :
    (fun (p : ℕ × ℕ) ↦ ((2 * p.1 : ℕ) : ℝ)) =O[Filter.atTop] (fun p ↦ ((p.1 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  intro ⟨n, m⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  push_cast
  linarith

/-- Second phase of KMP (preprocessing bound `2m`) is `O(m)` on `ℕ × ℕ`. -/
lemma isBigO_two_mul_snd_atTop :
    (fun (p : ℕ × ℕ) ↦ ((2 * p.2 : ℕ) : ℝ)) =O[Filter.atTop] (fun p ↦ ((p.2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  intro ⟨n, m⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  push_cast
  linarith

/-- Composition bridge: combined linear KMP bound `2n + 2m = O(n + m)` under `Filter.atTop`
via `Amort.Recurrence.isBigO_sequential_add_nat`. -/
theorem isBigO_kmp_linear_atTop :
    (fun (p : ℕ × ℕ) ↦ ((2 * p.1 + 2 * p.2 : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 + p.2 : ℕ) : ℝ)) :=
  isBigO_sequential_add_nat (fun (p : ℕ × ℕ) ↦ 2 * p.1) (fun p ↦ p.1)
    (fun (p : ℕ × ℕ) ↦ 2 * p.2) (fun p ↦ p.2)
    isBigO_two_mul_fst_atTop isBigO_two_mul_snd_atTop

/-- Combined KMP step bound `2 * (n + m)` is asymptotically `O(n + m)` under `Filter.atTop`. -/
theorem isBigO_kmpTotalSteps_bound_atTop :
    (fun (p : ℕ × ℕ) ↦ ((2 * (p.1 + p.2) : ℕ) : ℝ)) =O[Filter.atTop]
      (fun p ↦ ((p.1 + p.2 : ℕ) : ℝ)) := by
  have heq : (fun (p : ℕ × ℕ) ↦ ((2 * (p.1 + p.2) : ℕ) : ℝ)) =
      (fun (p : ℕ × ℕ) ↦ ((2 * p.1 + 2 * p.2 : ℕ) : ℝ)) := by
    funext ⟨n, m⟩
    simp only [Nat.mul_add]
  rw [heq]
  exact isBigO_kmp_linear_atTop

/-- Total KMP execution steps on sequence pairs are bounded by `2 * (|T| + |P|)` under
any filter on sequence pairs. -/
theorem isBigO_kmpTotalSteps_list {α : Type*} [DecidableEq α]
    (F : Filter (List α × List α)) :
    (fun (p : List α × List α) ↦ ((kmpTotalSteps p.1 p.2 : ℕ) : ℝ)) =O[F]
      (fun p ↦ ((p.2.length + p.1.length : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  intro ⟨P, T⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have h := kmpTotalSteps_le P T
  have h_real : ((kmpTotalSteps P T : ℕ) : ℝ) ≤ ((2 * (T.length + P.length) : ℕ) : ℝ) := by
    exact_mod_cast h
  have h2 : ((2 * (T.length + P.length) : ℕ) : ℝ) = 2 * ((T.length + P.length : ℕ) : ℝ) := by
    push_cast
    rfl
  rw [h2] at h_real
  exact h_real

end Amort.String
