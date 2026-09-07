/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Sort
import Mathlib.Tactic.Ring

/-!
# Comparison Counting and Complexity Bounds for Insertion Sort

This module formalizes comparison counting for insertion sort over lists, proving
equivalence to Mathlib's `List.insertionSort` and establishing concrete upper bounds:
- Single insertion into a list of length `k` requires at most `k` comparisons.
- Full insertion sort on a list of length `n` requires at most `n * (n - 1) / 2` comparisons.
- Consequently, insertion sort comparison complexity is bounded by `n ^ 2`.

## Key Definitions
- `List.orderedInsertCount`: Counts comparisons when inserting an element into a sorted list.
- `List.orderedInsertWithCount`: Instrumented insertion returning both the resulting list
  and the comparison count.
- `List.insertionSortCount`: Counts total comparisons executed by insertion sort on a list.
- `List.insertionSortWithCount`: Instrumented insertion sort returning both the sorted list
  and total comparison count.

## Key Theorems
- `List.orderedInsertWithCount_fst`: The output list of instrumented insertion equals
  `List.orderedInsert`.
- `List.orderedInsertWithCount_snd`: The comparison count of instrumented insertion equals
  `List.orderedInsertCount`.
- `List.insertionSortWithCount_fst`: The output list of instrumented sort equals
  `List.insertionSort`.
- `List.insertionSortWithCount_snd`: The comparison count of instrumented sort equals
  `List.insertionSortCount`.
- `List.orderedInsertCount_le`: Single insertion comparison count is bounded by list length.
- `List.insertionSortCount_le_triangular`: Total comparisons bounded by `n * (n - 1) / 2`.
- `List.insertionSortCount_le_sq`: Total comparisons bounded by `n ^ 2`.
-/

namespace List

variable {α : Type*} (r : α → α → Prop) [DecidableRel r]

/-- Counts the number of comparisons made when inserting an element into a list. -/
def orderedInsertCount (a : α) : List α → ℕ
  | [] => 0
  | b :: l => if r a b then 1 else 1 + orderedInsertCount a l

/-- Instrumented version of `List.orderedInsert` returning both the new list and the
number of comparisons performed. -/
def orderedInsertWithCount (a : α) : List α → List α × ℕ
  | [] => ([a], 0)
  | b :: l =>
    if r a b then
      (a :: b :: l, 1)
    else
      let res := orderedInsertWithCount a l
      (b :: res.1, 1 + res.2)

@[simp]
lemma orderedInsertWithCount_fst (a : α) (l : List α) :
    (orderedInsertWithCount r a l).1 = List.orderedInsert r a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [orderedInsertWithCount, List.orderedInsert_cons]
    split <;> simp [ih]

@[simp]
lemma orderedInsertWithCount_snd (a : α) (l : List α) :
    (orderedInsertWithCount r a l).2 = orderedInsertCount r a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [orderedInsertWithCount, orderedInsertCount]
    split <;> simp [ih]

/-- Inserting an element into a list of length `k` requires at most `k` comparisons. -/
lemma orderedInsertCount_le (a : α) (l : List α) :
    orderedInsertCount r a l ≤ l.length := by
  induction l with
  | nil => simp [orderedInsertCount]
  | cons b l ih =>
    simp only [orderedInsertCount, List.length_cons]
    split
    · omega
    · omega

/-- Counts the total number of comparisons made by `List.insertionSort`. -/
def insertionSortCount : List α → ℕ
  | [] => 0
  | a :: l => orderedInsertCount r a (List.insertionSort r l) + insertionSortCount l

/-- Instrumented version of `List.insertionSort` returning both the sorted list and
the total number of comparisons performed. -/
def insertionSortWithCount : List α → List α × ℕ
  | [] => ([], 0)
  | a :: l =>
    let res := insertionSortWithCount l
    let ins := orderedInsertWithCount r a res.1
    (ins.1, res.2 + ins.2)

@[simp]
theorem insertionSortWithCount_fst (l : List α) :
    (insertionSortWithCount r l).1 = List.insertionSort r l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [insertionSortWithCount, List.insertionSort_cons]
    rw [ih, orderedInsertWithCount_fst]

@[simp]
theorem insertionSortWithCount_snd (l : List α) :
    (insertionSortWithCount r l).2 = insertionSortCount r l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [insertionSortWithCount, insertionSortCount]
    rw [ih, insertionSortWithCount_fst, orderedInsertWithCount_snd]
    omega

/-- Total comparisons in insertion sort are bounded by the triangular number
`n * (n - 1) / 2` where `n = l.length`. -/
theorem insertionSortCount_le_triangular (l : List α) :
    insertionSortCount r l ≤ l.length * (l.length - 1) / 2 := by
  induction l with
  | nil => simp [insertionSortCount]
  | cons a l ih =>
    simp only [insertionSortCount, List.length_cons]
    have h_ins := orderedInsertCount_le r a (List.insertionSort r l)
    have h_len : (List.insertionSort r l).length = l.length := List.length_insertionSort r l
    rw [h_len] at h_ins
    have h_arith : (l.length + 1) * (l.length + 1 - 1) =
        l.length * (l.length - 1) + l.length * 2 := by
      cases hl : l.length with
      | zero => simp
      | succ n =>
        have h_sub1 : n + 1 + 1 - 1 = n + 1 := by omega
        have h_sub2 : n + 1 - 1 = n := by omega
        rw [h_sub1, h_sub2]
        ring
    have h_div : (l.length * (l.length - 1) + l.length * 2) / 2 =
        l.length * (l.length - 1) / 2 + l.length := by
      rw [Nat.add_mul_div_right _ _ (by decide : 0 < 2)]
    rw [h_arith, h_div]
    omega

/-- Total comparisons in insertion sort are bounded by `n ^ 2` where `n = l.length`. -/
theorem insertionSortCount_le_sq (l : List α) :
    insertionSortCount r l ≤ l.length ^ 2 := by
  have h := insertionSortCount_le_triangular r l
  have h_div : l.length * (l.length - 1) / 2 ≤ l.length * (l.length - 1) := Nat.div_le_self _ 2
  have h_mul : l.length * (l.length - 1) ≤ l.length * l.length :=
    Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have h_sq : l.length * l.length = l.length ^ 2 := by ring
  omega

/-- Instrumented comparison count is bounded by `n * (n - 1) / 2`. -/
theorem insertionSortWithCount_snd_le_triangular (l : List α) :
    (insertionSortWithCount r l).2 ≤ l.length * (l.length - 1) / 2 := by
  rw [insertionSortWithCount_snd]
  exact insertionSortCount_le_triangular r l

/-- Instrumented comparison count is bounded by `n ^ 2`. -/
theorem insertionSortWithCount_snd_le_sq (l : List α) :
    (insertionSortWithCount r l).2 ≤ l.length ^ 2 := by
  rw [insertionSortWithCount_snd]
  exact insertionSortCount_le_sq r l

end List
