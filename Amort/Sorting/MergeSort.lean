/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring

/-!
# Comparison Counting and Complexity Bounds for Merge Sort

This module formalizes comparison counting for merge sort over lists, proving equivalence
to Mathlib / Lean's `List.mergeSort` and establishing concrete upper bounds:
- Merging two lists of lengths `m` and `k` takes at most `m + k` comparisons.
- Merge sort on a list of length `n` satisfies the recurrence
  `T(n) ≤ T((n + 1) / 2) + T(n / 2) + n`.
- For any `n ≤ 2 ^ k`, `T(n) ≤ n * k`.
- Setting `k = Nat.size n`, `T(n) ≤ n * Nat.size n`.
- Full merge sort comparison complexity on a list `xs` is bounded by
  `xs.length * Nat.size xs.length`.

## Key Definitions
- `List.mergeCount`: Counts comparisons when merging two sorted lists.
- `List.mergeWithCount`: Instrumented merge returning both merged list and comparison count.
- `List.mergeSortCount`: Counts comparisons executed by merge sort on a list.
- `List.mergeSortWithCount`: Instrumented merge sort returning both sorted list and
  comparison count.
- `List.mergeSortRecBound`: Arithmetic recurrence upper bound for merge sort comparisons.

## Key Theorems
- `List.mergeWithCount_fst`: Matches `List.merge`.
- `List.mergeWithCount_snd`: Matches `List.mergeCount`.
- `List.mergeCount_le`: Comparisons bounded by `xs.length + ys.length`.
- `List.mergeSortWithCount_fst`: Matches `List.mergeSort`.
- `List.mergeSortWithCount_snd`: Matches `List.mergeSortCount`.
- `List.mergeSortRecBound_le_mul_of_le_two_pow`: Bounded by `n * k` for `n ≤ 2 ^ k`.
- `List.mergeSortRecBound_le_mul_size`: Bounded by `n * Nat.size n`.
- `List.mergeSortCount_le_recBound`: Count is bounded by `mergeSortRecBound xs.length`.
- `List.mergeSortCount_le_mul_size`: Count is bounded by `xs.length * Nat.size xs.length`.
- `List.mergeSortWithCount_snd_le_mul_size`: Instrumented count bounded by `n * Nat.size n`.
- `List.mergeSortWithCount_fst_eq_insertionSort`: Connects to `List.insertionSort`.
-/

namespace List

/-! ### Recurrence Bound for Divide-and-Conquer -/

/-- Arithmetic recurrence bounding the comparisons of merge sort on input of size `n`. -/
def mergeSortRecBound : ℕ → ℕ
  | 0 => 0
  | 1 => 0
  | n + 2 =>
    mergeSortRecBound ((n + 3) / 2) + mergeSortRecBound ((n + 2) / 2) + (n + 2)

/-- Whenever `n ≤ 2 ^ k`, the merge sort recurrence bound satisfies
`mergeSortRecBound n ≤ n * k`. -/
theorem mergeSortRecBound_le_mul_of_le_two_pow :
    ∀ (k : ℕ) (n : ℕ), n ≤ 2 ^ k → mergeSortRecBound n ≤ n * k := by
  intro k
  induction k with
  | zero =>
    intro n hn
    have hn' : n = 0 ∨ n = 1 := by omega
    rcases hn' with rfl | rfl <;> simp [mergeSortRecBound]
  | succ k ih =>
    intro n hn
    match n with
    | 0 => simp [mergeSortRecBound]
    | 1 => simp [mergeSortRecBound]
    | n + 2 =>
      have h1 : (n + 3) / 2 ≤ 2 ^ k := by omega
      have h2 : (n + 2) / 2 ≤ 2 ^ k := by omega
      have ih1 := ih ((n + 3) / 2) h1
      have ih2 := ih ((n + 2) / 2) h2
      rw [mergeSortRecBound]
      have h_sum : (n + 3) / 2 + (n + 2) / 2 = n + 2 := by omega
      have : (n + 2) * (k + 1) = ((n + 3) / 2) * k + ((n + 2) / 2) * k + (n + 2) := by
        calc (n + 2) * (k + 1)
          _ = (n + 2) * k + (n + 2) := by ring
          _ = ((n + 3) / 2 + (n + 2) / 2) * k + (n + 2) := by rw [h_sum]
          _ = ((n + 3) / 2) * k + ((n + 2) / 2) * k + (n + 2) := by ring
      omega

/-- For any `n : ℕ`, `mergeSortRecBound n ≤ n * Nat.size n`. -/
theorem mergeSortRecBound_le_mul_size (n : ℕ) :
    mergeSortRecBound n ≤ n * Nat.size n := by
  have h_le : n ≤ 2 ^ (Nat.size n) := le_of_lt (Nat.lt_size_self n)
  exact mergeSortRecBound_le_mul_of_le_two_pow (Nat.size n) n h_le

/-! ### Comparison Counting for Merge -/

/-- Counts the number of comparisons made when merging two lists using boolean relation `le`. -/
def mergeCount {α : Type*} (le : α → α → Bool) : List α → List α → ℕ
  | [], _ => 0
  | _ :: _, [] => 0
  | x :: xs, y :: ys =>
    if le x y then
      1 + mergeCount le xs (y :: ys)
    else
      1 + mergeCount le (x :: xs) ys

/-- Instrumented version of `List.merge` returning both the merged list and the comparison count. -/
def mergeWithCount {α : Type*} (le : α → α → Bool) : List α → List α → List α × ℕ
  | [], ys => (ys, 0)
  | xs, [] => (xs, 0)
  | x :: xs, y :: ys =>
    if le x y then
      let res := mergeWithCount le xs (y :: ys)
      (x :: res.1, 1 + res.2)
    else
      let res := mergeWithCount le (x :: xs) ys
      (y :: res.1, 1 + res.2)

@[simp]
theorem mergeWithCount_fst {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    (mergeWithCount le xs ys).1 = merge xs ys le := by
  match xs, ys with
  | [], ys => simp [mergeWithCount]
  | x :: xs, [] => simp [mergeWithCount]
  | x :: xs, y :: ys =>
    simp only [mergeWithCount, merge]
    split
    · have ih := mergeWithCount_fst le xs (y :: ys)
      simp [ih]
    · have ih := mergeWithCount_fst le (x :: xs) ys
      simp [ih]
termination_by xs.length + ys.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    omega

@[simp]
theorem mergeWithCount_snd {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    (mergeWithCount le xs ys).2 = mergeCount le xs ys := by
  match xs, ys with
  | [], ys => simp [mergeWithCount, mergeCount]
  | x :: xs, [] => simp [mergeWithCount, mergeCount]
  | x :: xs, y :: ys =>
    simp only [mergeWithCount, mergeCount]
    split
    · have ih := mergeWithCount_snd le xs (y :: ys)
      simp [ih]
    · have ih := mergeWithCount_snd le (x :: xs) ys
      simp [ih]
termination_by xs.length + ys.length
decreasing_by
  all_goals
    simp only [List.length_cons]
    omega

/-- Merging two lists of lengths `m` and `k` takes at most `m + k` comparisons. -/
theorem mergeCount_le {α : Type*} (le : α → α → Bool) (xs ys : List α) :
    mergeCount le xs ys ≤ xs.length + ys.length := by
  match xs, ys with
  | [], ys =>
    simp [mergeCount]
  | x :: xs, [] =>
    simp [mergeCount]
  | x :: xs, y :: ys =>
    have : xs.length + (y :: ys).length < (x :: xs).length + (y :: ys).length := by
      simp only [List.length_cons]; omega
    have : (x :: xs).length + ys.length < (x :: xs).length + (y :: ys).length := by
      simp only [List.length_cons]; omega
    rw [mergeCount]
    split
    · have ih := mergeCount_le le xs (y :: ys)
      omega
    · have ih := mergeCount_le le (x :: xs) ys
      omega
termination_by xs.length + ys.length

/-! ### Comparison Counting for Merge Sort -/

/-- Counts the total number of comparisons performed by `List.mergeSort`. -/
def mergeSortCount {α : Type*} (le : α → α → Bool) : List α → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: xs =>
    let lr := List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩
    have : lr.1.1.length < (a :: b :: xs).length := by
      have := lr.1.2
      simp only [List.length_cons] at this ⊢
      omega
    have : lr.2.1.length < (a :: b :: xs).length := by
      have := lr.2.2
      simp only [List.length_cons] at this ⊢
      omega
    mergeSortCount le lr.1.1 + mergeSortCount le lr.2.1 +
      mergeCount le (List.mergeSort lr.1.1 le) (List.mergeSort lr.2.1 le)
termination_by xs => xs.length

/-- Instrumented version of `List.mergeSort` returning both the sorted list and
total comparisons performed. -/
def mergeSortWithCount {α : Type*} (le : α → α → Bool) : List α → List α × ℕ
  | [] => ([], 0)
  | [a] => ([a], 0)
  | a :: b :: xs =>
    let lr := List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩
    have : lr.1.1.length < (a :: b :: xs).length := by
      have := lr.1.2
      simp only [List.length_cons] at this ⊢
      omega
    have : lr.2.1.length < (a :: b :: xs).length := by
      have := lr.2.2
      simp only [List.length_cons] at this ⊢
      omega
    let res1 := mergeSortWithCount le lr.1.1
    let res2 := mergeSortWithCount le lr.2.1
    let res_m := mergeWithCount le res1.1 res2.1
    (res_m.1, res1.2 + res2.2 + res_m.2)
termination_by xs => xs.length

@[simp]
theorem mergeSortWithCount_fst {α : Type*} (le : α → α → Bool) :
    ∀ (xs : List α), (mergeSortWithCount le xs).1 = mergeSort xs le
  | [] => by simp [mergeSortWithCount]
  | [a] => by simp [mergeSortWithCount]
  | a :: b :: xs => by
    rw [mergeSortWithCount, mergeSort]
    dsimp
    have ih1 := mergeSortWithCount_fst le
      (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1
    have ih2 := mergeSortWithCount_fst le
      (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1
    rw [ih1, ih2, mergeWithCount_fst]
termination_by xs => xs.length
decreasing_by
  all_goals
    have : (a :: b :: xs).length = xs.length + 2 := rfl
    have := (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.2
    have := (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.2
    simp only [List.length_cons] at *
    omega

@[simp]
theorem mergeSortWithCount_snd {α : Type*} (le : α → α → Bool) :
    ∀ (xs : List α), (mergeSortWithCount le xs).2 = mergeSortCount le xs
  | [] => by simp [mergeSortWithCount, mergeSortCount]
  | [a] => by simp [mergeSortWithCount, mergeSortCount]
  | a :: b :: xs => by
    rw [mergeSortWithCount, mergeSortCount]
    dsimp
    have ih1 := mergeSortWithCount_snd le
      (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1
    have ih2 := mergeSortWithCount_snd le
      (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1
    have ih1_fst := mergeSortWithCount_fst le
      (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.1
    have ih2_fst := mergeSortWithCount_fst le
      (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.1
    rw [ih1, ih2, ih1_fst, ih2_fst, mergeWithCount_snd]
termination_by xs => xs.length
decreasing_by
  all_goals
    have : (a :: b :: xs).length = xs.length + 2 := rfl
    have := (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).1.2
    have := (List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩).2.2
    simp only [List.length_cons] at *
    omega

/-- Comparisons performed by `mergeSort` are bounded by the recurrence `mergeSortRecBound`. -/
lemma mergeSortCount_le_recBound {α : Type*} (le : α → α → Bool) :
    ∀ (xs : List α), mergeSortCount le xs ≤ mergeSortRecBound xs.length
  | [] => by simp [mergeSortCount, mergeSortRecBound]
  | [_] => by simp [mergeSortCount, mergeSortRecBound]
  | a :: b :: xs => by
    rw [mergeSortCount]
    rcases List.MergeSort.Internal.splitInTwo ⟨a :: b :: xs, rfl⟩ with ⟨⟨l1, hl1⟩, ⟨l2, hl2⟩⟩
    have ih1 := mergeSortCount_le_recBound le l1
    have ih2 := mergeSortCount_le_recBound le l2
    have hm := mergeCount_le le (List.mergeSort l1 le) (List.mergeSort l2 le)
    rw [List.length_mergeSort, List.length_mergeSort] at hm
    simp only []
    dsimp
    simp only [List.length_cons] at hl1 hl2
    have h3 : (xs.length + 1 + 1 + 1) / 2 = (xs.length + 3) / 2 := by omega
    have h2 : (xs.length + 1 + 1) / 2 = (xs.length + 2) / 2 := by omega
    rw [h3] at hl1
    rw [h2] at hl2
    rw [hl1] at ih1
    rw [hl2] at ih2
    have h_rec : mergeSortRecBound (xs.length + 2) =
        mergeSortRecBound ((xs.length + 3) / 2) + mergeSortRecBound ((xs.length + 2) / 2) +
          (xs.length + 2) := by
      rw [mergeSortRecBound]
    have h_two : xs.length + 1 + 1 = xs.length + 2 := by omega
    rw [h_two, h_rec]
    omega
termination_by xs => xs.length
decreasing_by
  all_goals
    have : (a :: b :: xs).length = xs.length + 2 := rfl
    omega

/-- Total comparisons in merge sort are bounded by `n * Nat.size n` where `n = xs.length`. -/
theorem mergeSortCount_le_mul_size {α : Type*} (le : α → α → Bool) (xs : List α) :
    mergeSortCount le xs ≤ xs.length * Nat.size xs.length :=
  (mergeSortCount_le_recBound le xs).trans (mergeSortRecBound_le_mul_size xs.length)

/-- Instrumented merge sort comparison count is bounded by `n * Nat.size n`. -/
theorem mergeSortWithCount_snd_le_mul_size {α : Type*} (le : α → α → Bool) (xs : List α) :
    (mergeSortWithCount le xs).2 ≤ xs.length * Nat.size xs.length := by
  rw [mergeSortWithCount_snd]
  exact mergeSortCount_le_mul_size le xs

/-- Instrumented merge sort produces the same result as Mathlib's `List.insertionSort`
when the relation is total, transitive, and antisymmetric. -/
theorem mergeSortWithCount_fst_eq_insertionSort {α : Type*} (r : α → α → Prop)
    [DecidableRel r] [Std.Total r] [IsTrans α r] [Std.Antisymm r] (xs : List α) :
    (mergeSortWithCount (r · ·) xs).1 = insertionSort r xs := by
  rw [mergeSortWithCount_fst]
  exact mergeSort_eq_insertionSort (r := r) xs

end List
