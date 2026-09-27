/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Sorting.InsertionSort

/-!
# Insertion sort: companion file

Companion to `tutorial/insertion_sort.md`. Every Lean snippet the chapter quotes is either here
or in the reference file `Amort/Sorting/InsertionSort.lean`, so Lean checks all of it on every
build.
-/

set_option linter.hashCommand false
set_option linter.style.header false

open List
open scoped List

namespace Tutorial.InsertionSort

variable {α : Type*}

/-! ## Step 3: what Mathlib's definitions do -/

example (r : α → α → Prop) [DecidableRel r] (a : α) :
    List.orderedInsert r a [] = [a] := rfl

example (r : α → α → Prop) [DecidableRel r] (a b : α) (l : List α) :
    List.orderedInsert r a (b :: l) =
      if r a b then a :: b :: l else b :: List.orderedInsert r a l := rfl

example (r : α → α → Prop) [DecidableRel r] (a : α) (l : List α) :
    List.insertionSort r (a :: l) = List.orderedInsert r a (List.insertionSort r l) := rfl

/-! ## Step 5: counting comparisons -/

#guard List.insertionSortWithCount (· ≤ ·) [5, 2, 4, 6, 1, 3] = ([1, 2, 3, 4, 5, 6], 13)
#guard List.insertionSortWithCount (· ≤ ·) [1, 2, 3, 4] = ([1, 2, 3, 4], 3)
#guard List.insertionSortWithCount (· ≤ ·) [4, 3, 2, 1] = ([1, 2, 3, 4], 6)

/-! ## Spot the fake: "sort is correct" -/

/-- Throws the input away. -/
def emptySort (_ : List ℕ) : List ℕ := []

/-- Option A: sortedness alone. `emptySort` passes it. -/
theorem emptySort_sorted (l : List ℕ) : (emptySort l).Pairwise (· ≤ ·) := by
  simp [emptySort]

/-- Replaces every element with 0. -/
def zeroSort (l : List ℕ) : List ℕ := List.replicate l.length 0

/-- Option B: sortedness and the right length. `zeroSort` passes it. -/
theorem zeroSort_length_sorted (l : List ℕ) :
    (zeroSort l).length = l.length ∧ (zeroSort l).Pairwise (· ≤ ·) :=
  ⟨List.length_replicate, List.pairwise_replicate.2 (Or.inr le_rfl)⟩

/-- Option C: a rearrangement of the input, and sorted. -/
theorem insertionSort_correct (l : List ℕ) :
    (List.insertionSortWithCount (· ≤ ·) l).1 ~ l ∧
    (List.insertionSortWithCount (· ≤ ·) l).1.Pairwise (· ≤ ·) :=
  ⟨List.insertionSortWithCount_perm (· ≤ ·) l,
   List.insertionSortWithCount_fst_sorted (· ≤ ·) l⟩

/-! ## Exercises -/

#guard List.insertionSortWithCount (· ≤ ·) [2, 1, 3] = ([1, 2, 3], 3)

theorem insertionSort_length (l : List ℕ) :
    (List.insertionSortWithCount (· ≤ ·) l).1.length = l.length :=
  (List.insertionSortWithCount_perm (· ≤ ·) l).length_eq

end Tutorial.InsertionSort
