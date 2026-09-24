/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Halving
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Size
import Mathlib.Order.Basic
import Mathlib.Tactic.Ring

/-!
# Binary Search Recurrence and Complexity Bounds

This module formalizes step counting and asymptotic complexity for binary search algorithms.
Binary search decreases the problem search interval by a factor of 2 at each step,
satisfying the halving recurrence $T(n) \le T(n / 2) + 1$ for $n \ge 2$.

## Mathematical Architecture

1. **Representative Step Counter**:
   We define `binarySearchSteps : ℕ → ℕ` modeling the worst-case number of comparisons
   required to locate an element or determine its absence in a sorted range of size $n$:
   - $T(0) = 0$
   - $T(1) = 1$
   - $T(n) = 1 + T(n / 2)$ for $n \ge 2$

2. **Halving Recurrence Satisfaction**:
   For any $n \ge 2$, `binarySearchSteps n ≤ binarySearchSteps (n / 2) + 1`.
   Consequently, binary search directly instantiates the general halving recurrence
   with step cost $c = 1$.

3. **Concrete Bounds**:
   - `binarySearchSteps_le_bound`: $T(n) \le \text{Nat.size } n + 1$ for $n \ge 1$
     via the general halving theorem.
   - `binarySearchSteps_le_size`: $T(n) \le \text{Nat.size } n$ for all $n \in \mathbb{N}$
     by induction on bit length.

4. **Asymptotic Complexity**:
   - `binarySearchSteps_isBigO_size`: $T(n) = O(\text{Nat.size } n)$ under `Filter.atTop`.
   - `binarySearchSteps_isBigO_log`: $T(n) = O(\log n)$ under `Filter.atTop`.

## Key Theorems
- `Amort.Recurrence.binarySearchSteps_step`: Exact halving recurrence step relation.
- `Amort.Recurrence.binarySearchSteps_le_halving`: Halving recurrence inequality ($c = 1$).
- `Amort.Recurrence.binarySearchSteps_le_bound`: Bounded by $\text{Nat.size } n + 1$ for $n \ge 1$.
- `Amort.Recurrence.binarySearchSteps_le_size`:
  Exact bit-size upper bound for all $n \in \mathbb{N}$.
- `Amort.Recurrence.binarySearchSteps_isBigO_size`: $O(\text{Nat.size } n)$ under `Filter.atTop`.
- `Amort.Recurrence.binarySearchSteps_isBigO_log`: $O(\log n)$ under `Filter.atTop`.
-/

namespace Amort.Recurrence

open Asymptotics

/-! ### Binary Search Step Counter -/

/-- Worst-case comparison counter for binary search on an interval or list of size $n$. -/
def binarySearchSteps : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 => 1 + binarySearchSteps ((n + 2) / 2)

@[simp]
theorem binarySearchSteps_zero : binarySearchSteps 0 = 0 := by
  unfold binarySearchSteps
  rfl

@[simp]
theorem binarySearchSteps_one : binarySearchSteps 1 = 1 := by
  unfold binarySearchSteps
  rfl

/-- Binary search step count satisfies the exact halving recurrence for $n \ge 2$. -/
theorem binarySearchSteps_step (n : ℕ) (hn : 2 ≤ n) :
    binarySearchSteps n = binarySearchSteps (n / 2) + 1 := by
  match n with
  | 0 => omega
  | 1 => omega
  | n + 2 =>
    rw [binarySearchSteps]
    omega

/-- Binary search step count satisfies the halving recurrence inequality with $c = 1$. -/
theorem binarySearchSteps_le_halving (n : ℕ) (hn : 2 ≤ n) :
    binarySearchSteps n ≤ binarySearchSteps (n / 2) + 1 := by
  rw [binarySearchSteps_step n hn]

/-! ### Concrete Upper Bounds -/

/-- Concrete upper bound: binary search steps bounded by $\text{Nat.size } n + 1$
via the general halving recurrence theorem. -/
theorem binarySearchSteps_le_bound (n : ℕ) (hn : 1 ≤ n) :
    binarySearchSteps n ≤ Nat.size n + 1 := by
  have h := halving_recurrence_bound binarySearchSteps 1 binarySearchSteps_le_halving n hn
  have h1 := binarySearchSteps_one
  rw [h1, one_mul] at h
  exact h

/-- Concrete bit-size upper bound: binary search steps are at most $\text{Nat.size } n$
for all $n \in \mathbb{N}$. -/
theorem binarySearchSteps_le_size (n : ℕ) :
    binarySearchSteps n ≤ Nat.size n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 =>
      rw [binarySearchSteps_zero]
      simp
    | 1 =>
      rw [binarySearchSteps_one]
      simp
    | n + 2 =>
      rw [binarySearchSteps]
      have hdiv_lt : (n + 2) / 2 < n + 2 := by omega
      have ih_div := ih ((n + 2) / 2) hdiv_lt
      have h_size : Nat.size ((n + 2) / 2) = Nat.size (n + 2) - 1 := size_div_two (n + 2)
      have h_size_ge : 2 ≤ Nat.size (n + 2) := size_ge_two_of_ge_two (by omega)
      omega

/-! ### Asymptotic Complexity -/

/-- Binary search comparison count is asymptotically $O(\text{Nat.size } n)$
under `Filter.atTop`. -/
theorem binarySearchSteps_isBigO_size :
    (fun n : ℕ ↦ ((binarySearchSteps n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((Nat.size n : ℕ) : ℝ)) :=
  halving_recurrence_isBigO_size binarySearchSteps 1 binarySearchSteps_le_halving

/-- Binary search comparison count is asymptotically $O(\log n)$
under `Filter.atTop`. -/
theorem binarySearchSteps_isBigO_log :
    (fun n : ℕ ↦ ((binarySearchSteps n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ Real.log (n : ℝ)) :=
  halving_recurrence_isBigO_log binarySearchSteps 1 binarySearchSteps_le_halving

/-- Monotonicity: binary search steps increase weakly with input size. -/
theorem binarySearchSteps_mono {a b : ℕ} (h : a ≤ b) :
    binarySearchSteps a ≤ binarySearchSteps b := by
  induction b using Nat.strong_induction_on generalizing a with
  | h n ih =>
    match n with
    | 0 =>
      have : a = 0 := by omega
      subst this
      rfl
    | 1 =>
      cases a with
      | zero => simp
      | succ a =>
        have : a = 0 := by omega
        subst this
        rfl
    | n + 2 =>
      rw [binarySearchSteps]
      cases a with
      | zero => simp
      | succ a =>
        cases a with
        | zero =>
          rw [binarySearchSteps_one]
          omega
        | succ a =>
          have h2 : 2 ≤ a + 2 := by omega
          rw [binarySearchSteps_step (a + 2) h2]
          have h_div : (a + 2) / 2 ≤ (n + 2) / 2 := Nat.div_le_div_right h
          have h_lt : (n + 2) / 2 < n + 2 := by omega
          have ih_div := ih ((n + 2) / 2) h_lt h_div
          omega

/-! ### Executable Binary Search -/

variable {α : Type*} [LinearOrder α]

/-- Executable binary search on a sorted list returning the index if found. -/
def binarySearch (xs : List α) (x : α) : Option ℕ :=
  if h : xs.length = 0 then
    none
  else
    let mid := xs.length / 2
    have hmid : mid < xs.length := by omega
    let midVal := xs[mid]
    if x < midVal then
      binarySearch (xs.take mid) x
    else if midVal < x then
      (binarySearch (xs.drop (mid + 1)) x).map (· + mid + 1)
    else
      some mid
termination_by xs.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

/-- Instrumented binary search counting element comparisons (probes). -/
def binarySearchWithCount (xs : List α) (x : α) : Option ℕ × ℕ :=
  if h : xs.length = 0 then
    (none, 0)
  else
    let mid := xs.length / 2
    have hmid : mid < xs.length := by omega
    let midVal := xs[mid]
    if x < midVal then
      let res := binarySearchWithCount (xs.take mid) x
      (res.1, res.2 + 1)
    else if midVal < x then
      let res := binarySearchWithCount (xs.drop (mid + 1)) x
      (res.1.map (· + mid + 1), res.2 + 1)
    else
      (some mid, 1)
termination_by xs.length
decreasing_by
  · simp only [List.length_take]; omega
  · simp only [List.length_drop]; omega

/-- Instrumented binary search returns the same result as pure binary search. -/
theorem binarySearchWithCount_fst (xs : List α) (x : α) :
    (binarySearchWithCount xs x).1 = binarySearch xs x := by
  induction h_len : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    rw [binarySearchWithCount.eq_def, binarySearch.eq_def]
    dsimp only
    split_ifs with h0 h1 h2
    · rfl
    · have h_lt : (xs.take (xs.length / 2)).length < n := by
        simp only [List.length_take]; omega
      have ih_take := ih (xs.take (xs.length / 2)).length h_lt (xs.take (xs.length / 2)) rfl
      rw [ih_take]
    · have h_lt : (xs.drop (xs.length / 2 + 1)).length < n := by
        simp only [List.length_drop]; omega
      have ih_drop := ih (xs.drop (xs.length / 2 + 1)).length h_lt (xs.drop (xs.length / 2 + 1)) rfl
      rw [ih_drop]
    · rfl

/-- Any index returned by binary search points to the searched element. -/
theorem binarySearch_some_get (xs : List α) (x : α) (i : ℕ) (h : binarySearch xs x = some i) :
    xs[i]? = some x := by
  induction h_len : xs.length using Nat.strong_induction_on generalizing xs i with
  | h n ih =>
    rw [binarySearch.eq_def] at h
    dsimp only at h
    by_cases h0 : xs.length = 0
    · rw [dif_pos h0] at h
      contradiction
    · rw [dif_neg h0] at h
      let mid := xs.length / 2
      have hmid : mid < xs.length := by omega
      by_cases h1 : x < xs[mid]
      · rw [if_pos h1] at h
        have h_lt : (xs.take mid).length < n := by
          simp only [List.length_take]; omega
        have ih_take := ih (xs.take mid).length h_lt (xs.take mid) i h rfl
        rw [List.getElem?_take] at ih_take
        split_ifs at ih_take with hi
        exact ih_take
      · rw [if_neg h1] at h
        by_cases h2 : xs[mid] < x
        · rw [if_pos h2] at h
          rcases Option.map_eq_some_iff.mp h with ⟨j, hj, rfl⟩
          have h_lt : (xs.drop (mid + 1)).length < n := by
            simp only [List.length_drop]; omega
          have ih_drop := ih (xs.drop (mid + 1)).length h_lt (xs.drop (mid + 1)) j hj rfl
          rw [List.getElem?_drop] at ih_drop
          have h_idx : mid + 1 + j = j + mid + 1 := by omega
          rw [h_idx] at ih_drop
          exact ih_drop
        · rw [if_neg h2] at h
          simp only [Option.some.injEq] at h
          subst h
          have h_eq : xs[mid] = x := (le_antisymm (not_lt.mp h2) (not_lt.mp h1)).symm
          rw [List.getElem?_eq_getElem hmid, h_eq]

/-- Any index returned by binary search contains the searched element. -/
theorem binarySearch_mem (xs : List α) (x : α) (i : ℕ) (h : binarySearch xs x = some i) :
    x ∈ xs :=
  List.mem_of_getElem? (binarySearch_some_get xs x i h)

/-- If `x ∈ xs` and `xs` is sorted, binary search successfully finds `x`. -/
theorem mem_imp_binarySearch_isSome (xs : List α) (x : α) (hsort : xs.Pairwise (· ≤ ·))
    (hx : x ∈ xs) : (binarySearch xs x).isSome := by
  induction h_len : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    rw [binarySearch.eq_def]
    dsimp only
    by_cases h0 : xs.length = 0
    · subst h_len
      have : xs = [] := by
        cases xs
        · rfl
        · contradiction
      subst this
      contradiction
    · rw [dif_neg h0]
      let mid := xs.length / 2
      have hmid : mid < xs.length := by omega
      rcases List.mem_iff_getElem.mp hx with ⟨k, hk, rfl⟩
      have h_pw := List.pairwise_iff_getElem.mp hsort
      by_cases h1 : xs[k] < xs[mid]
      · rw [if_pos h1]
        have h_k_lt_mid : k < mid := by
          by_contra! hge
          rcases hge.eq_or_lt with rfl | hgt
          · exact (lt_irrefl _) h1
          · have h_le := h_pw mid k hmid hk hgt
            exact not_lt.mpr h_le h1
        have h_lt : (xs.take mid).length < n := by
          simp only [List.length_take]; omega
        have h_sort_take : (xs.take mid).Pairwise (· ≤ ·) :=
          List.Pairwise.sublist (List.take_sublist mid xs) hsort
        have h_mem_take : xs[k] ∈ xs.take mid := by
          rw [List.mem_iff_getElem]
          refine ⟨k, by simp only [List.length_take]; omega, ?_⟩
          rw [List.getElem_take]
        exact ih (xs.take mid).length h_lt (xs.take mid) h_sort_take h_mem_take rfl
      · rw [if_neg h1]
        by_cases h2 : xs[mid] < xs[k]
        · rw [if_pos h2]
          have h_mid_lt_k : mid < k := by
            by_contra! hle
            rcases hle.eq_or_lt with rfl | hlt
            · exact (lt_irrefl _) h2
            · have h_le := h_pw k mid hk hmid hlt
              exact not_lt.mpr h_le h2
          have h_lt : (xs.drop (mid + 1)).length < n := by
            simp only [List.length_drop]; omega
          have h_sort_drop : (xs.drop (mid + 1)).Pairwise (· ≤ ·) :=
            List.Pairwise.sublist (List.drop_sublist (mid + 1) xs) hsort
          have h_mem_drop : xs[k] ∈ xs.drop (mid + 1) := by
            rw [List.mem_iff_getElem]
            have hk_drop : k - (mid + 1) < (xs.drop (mid + 1)).length := by
              simp only [List.length_drop]; omega
            refine ⟨k - (mid + 1), hk_drop, ?_⟩
            have h_eq : (xs.drop (mid + 1))[k - (mid + 1)] = xs[mid + 1 + (k - (mid + 1))] :=
              List.getElem_drop
            have h_idx : xs[mid + 1 + (k - (mid + 1))] = xs[k] := by
              congr 1
              omega
            exact h_eq.trans h_idx
          have ih_drop := ih (xs.drop (mid + 1)).length h_lt (xs.drop (mid + 1))
            h_sort_drop h_mem_drop rfl
          rw [Option.isSome_map, ih_drop]
        · rw [if_neg h2]
          simp only [Option.isSome_some]

/-- Correctness: on a sorted list, binary search finds an element if and only if it is present. -/
theorem binarySearch_isSome_iff (xs : List α) (x : α) (hsort : xs.Pairwise (· ≤ ·)) :
    (binarySearch xs x).isSome ↔ x ∈ xs :=
  ⟨fun h => by
    rcases Option.isSome_iff_exists.mp h with ⟨i, hi⟩
    exact binarySearch_mem xs x i hi,
   mem_imp_binarySearch_isSome xs x hsort⟩

/-- Concrete probe bound: binary search probe count is bounded by `binarySearchSteps xs.length`. -/
theorem binarySearchWithCount_snd_le_steps (xs : List α) (x : α) :
    (binarySearchWithCount xs x).2 ≤ binarySearchSteps xs.length := by
  induction h_len : xs.length using Nat.strong_induction_on generalizing xs with
  | h n ih =>
    subst h_len
    cases hn : xs.length with
    | zero =>
      rw [binarySearchWithCount.eq_def]
      dsimp only
      rw [dif_pos hn]
      decide
    | succ n' =>
      cases n' with
      | zero =>
        rw [binarySearchWithCount.eq_def]
        dsimp only
        rw [dif_neg (by omega)]
        have h_take_len : (xs.take (xs.length / 2)).length = 0 := by
          simp only [List.length_take]; omega
        have h_drop_len : (xs.drop (xs.length / 2 + 1)).length = 0 := by
          simp only [List.length_drop]; omega
        have ih_take := ih 0 (by omega) (xs.take (xs.length / 2)) h_take_len
        have ih_drop := ih 0 (by omega) (xs.drop (xs.length / 2 + 1)) h_drop_len
        rw [binarySearchSteps_zero] at ih_take ih_drop
        rw [binarySearchSteps_one]
        split_ifs <;> dsimp only <;> omega
      | succ n'' =>
        rw [binarySearchWithCount.eq_def]
        dsimp only
        rw [dif_neg (by omega)]
        have hge : 2 ≤ n'' + 1 + 1 := by omega
        rw [binarySearchSteps_step (n'' + 1 + 1) hge]
        split_ifs with h1 h2
        · dsimp only
          have h_lt : (xs.take (xs.length / 2)).length < xs.length := by
            simp only [List.length_take]; omega
          have ih_take := ih (xs.take (xs.length / 2)).length h_lt (xs.take (xs.length / 2)) rfl
          have h_take_len : (xs.take (xs.length / 2)).length = (n'' + 1 + 1) / 2 := by
            simp only [List.length_take]; omega
          rw [h_take_len] at ih_take
          omega
        · dsimp only
          have h_lt : (xs.drop (xs.length / 2 + 1)).length < xs.length := by
            simp only [List.length_drop]; omega
          have ih_drop := ih (xs.drop (xs.length / 2 + 1)).length h_lt
            (xs.drop (xs.length / 2 + 1)) rfl
          have h_drop_le : (xs.drop (xs.length / 2 + 1)).length ≤ (n'' + 1 + 1) / 2 := by
            simp only [List.length_drop]; omega
          have h_mono := binarySearchSteps_mono h_drop_le
          have ih_bound := ih_drop.trans h_mono
          omega
        · dsimp only
          omega

/-- Concrete bit-size probe bound: binary search probe count is bounded by `Nat.size xs.length`. -/
theorem binarySearchWithCount_snd_le_size (xs : List α) (x : α) :
    (binarySearchWithCount xs x).2 ≤ Nat.size xs.length :=
  (binarySearchWithCount_snd_le_steps xs x).trans (binarySearchSteps_le_size xs.length)

/-- Executable binary search on an `Array α`. -/
def binarySearchArray (a : Array α) (x : α) : Option ℕ :=
  binarySearch a.toList x

/-- Instrumented binary search on an `Array α` returning index and probe count. -/
def binarySearchArrayWithCount (a : Array α) (x : α) : Option ℕ × ℕ :=
  binarySearchWithCount a.toList x

/-- Instrumented binary search on arrays preserves pure binary search output. -/
theorem binarySearchArrayWithCount_fst (a : Array α) (x : α) :
    (binarySearchArrayWithCount a x).1 = binarySearchArray a x :=
  binarySearchWithCount_fst a.toList x

/-- Array binary search probe count is bounded by `binarySearchSteps a.size`. -/
theorem binarySearchArrayWithCount_snd_le_steps (a : Array α) (x : α) :
    (binarySearchArrayWithCount a x).2 ≤ binarySearchSteps a.size := by
  dsimp [binarySearchArrayWithCount]
  exact binarySearchWithCount_snd_le_steps a.toList x

/-- Array binary search probe count is bounded by `Nat.size a.size`. -/
theorem binarySearchArrayWithCount_snd_le_size (a : Array α) (x : α) :
    (binarySearchArrayWithCount a x).2 ≤ Nat.size a.size := by
  dsimp [binarySearchArrayWithCount]
  exact binarySearchWithCount_snd_le_size a.toList x

/-- Correctness for array binary search. -/
theorem binarySearchArray_isSome_iff (a : Array α) (x : α)
    (hsort : a.toList.Pairwise (· ≤ ·)) :
    (binarySearchArray a x).isSome ↔ x ∈ a := by
  dsimp [binarySearchArray]
  rw [binarySearch_isSome_iff a.toList x hsort]
  simp

end Amort.Recurrence
