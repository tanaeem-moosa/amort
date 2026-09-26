/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Sorting.InsertionSort

/-!
# Tutorial: Insertion Sort

Companion file for `tutorial/insertion_sort.md`.
Introduces:
- The two-part sorting specification: sortedness (`List.Pairwise`) and
  permutation preservation (`List.Perm` / `~`)
- Why "sorted" alone is a fake spec (the empty list is sorted)
- Instrumented comparison counting (`List.insertionSortWithCount`)
- Concrete triangular (`n * (n - 1) / 2`) and quadratic (`n ^ 2`) upper bounds

This file allows learners to interact with definitions, evaluate examples,
and check theorem statements locally.
-/

set_option linter.hashCommand false
set_option linter.style.header false

open List
open scoped List

namespace Tutorial.InsertionSort

/-! ### Step 3: Running the Executable Algorithm -/

-- Run `#eval` to sort lists and count comparisons:
#eval List.insertionSortWithCount (· ≤ ·) [5, 2, 4, 6, 1, 3]
#guard List.insertionSortWithCount (· ≤ ·) [5, 2, 4, 6, 1, 3] = ([1, 2, 3, 4, 5, 6], 13)

-- Best case: already sorted input (n - 1 comparisons):
#eval List.insertionSortWithCount (· ≤ ·) [1, 2, 3, 4]
#guard List.insertionSortWithCount (· ≤ ·) [1, 2, 3, 4] = ([1, 2, 3, 4], 3)

-- Worst case: reverse sorted input (n * (n - 1) / 2 comparisons):
#eval List.insertionSortWithCount (· ≤ ·) [4, 3, 2, 1]
#guard List.insertionSortWithCount (· ≤ ·) [4, 3, 2, 1] = ([1, 2, 3, 4], 6)

/-! ### Step 4: Correctness Claims -/

-- Specification Part 1: Permutation (all original elements preserved):
#check List.insertionSortWithCount_perm
-- ∀ {α : Type*} (r : α → α → Prop) [DecidableRel r] (l : List α),
--   (List.insertionSortWithCount r l).1 ~ l

-- Specification Part 2: Sortedness (adjacent elements satisfy relation):
#check List.insertionSortWithCount_fst_sorted
-- ∀ {α : Type*} (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r] (l : List α),
--   (List.insertionSortWithCount r l).1.Pairwise r

/-- Learner experiment: Demonstrating that empty list is trivially sorted. -/
example : ([ ] : List ℕ).Pairwise (· ≤ ·) := by
  simp

/-- Sorting preserves list length -/
example (l : List ℕ) : (List.insertionSortWithCount (· ≤ ·) l).1.length = l.length := by
  exact (List.insertionSortWithCount_perm (· ≤ ·) l).length_eq

/-! ### Step 5: Comparison Counting & Complexity Bounds -/

-- Coupling theorems:
#check List.insertionSortWithCount_fst
#check List.insertionSortWithCount_snd

-- Triangular comparison bound:
#check List.insertionSortWithCount_snd_le_triangular
-- ∀ (l : List α), (List.insertionSortWithCount r l).2 ≤ l.length * (l.length - 1) / 2

-- Quadratic comparison bound:
#check List.insertionSortWithCount_snd_le_sq
-- ∀ (l : List α), (List.insertionSortWithCount r l).2 ≤ l.length ^ 2

/-- Learner experiment: Concrete verification of the triangular bound on 4 elements. -/
example : (List.insertionSortWithCount (· ≤ ·) [4, 3, 2, 1]).2 ≤ 4 * (4 - 1) / 2 := by
  exact List.insertionSortWithCount_snd_le_triangular (· ≤ ·) [4, 3, 2, 1]

/-! ### Spot the Fake: Compiling Real vs Fake Claims -/

/-- Fake 1 (Empty list fake): Output is provably sorted, but completely drops
the input data. -/
def emptySort (_ : List ℕ) : List ℕ := []

/-- Fake 1 passes a "sorted-only" specification. -/
theorem emptySort_sorted (l : List ℕ) : (emptySort l).Pairwise (· ≤ ·) := by
  simp [emptySort]

/-- Fake 2 (Identity fake): Output is provably a permutation, but fails to sort. -/
def identitySort (l : List ℕ) : List ℕ := l

/-- Fake 2 passes a "permutation-only" specification. -/
theorem identitySort_perm (l : List ℕ) : identitySort l ~ l :=
  List.Perm.refl l

/-- Genuine sorting specification: Requires BOTH permutation and sortedness,
alongside an honest operational comparison upper bound. -/
theorem genuine_sort_result (l : List ℕ) :
    (List.insertionSortWithCount (· ≤ ·) l).1 ~ l ∧
    (List.insertionSortWithCount (· ≤ ·) l).1.Pairwise (· ≤ ·) ∧
    (List.insertionSortWithCount (· ≤ ·) l).2 ≤ l.length * (l.length - 1) / 2 :=
  ⟨List.insertionSortWithCount_perm (· ≤ ·) l,
   List.insertionSortWithCount_fst_sorted (· ≤ ·) l,
   List.insertionSortWithCount_snd_le_triangular (· ≤ ·) l⟩

end Tutorial.InsertionSort
