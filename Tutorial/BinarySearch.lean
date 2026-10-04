/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.BinarySearch

/-!
# Binary search: companion file

Companion to `tutorial/binary_search.md`. Every Lean snippet the chapter quotes is either here
or in the reference file `Amort/Recurrence/BinarySearch.lean`, so Lean checks all of it on every
build.
-/

set_option linter.hashCommand false
set_option linter.style.header false

open Amort.Recurrence

namespace Tutorial.BinarySearch

/-! ## Step 3: running the algorithm -/

#guard binarySearch [1, 3, 5, 7, 9, 11] 7 = some 3
#guard binarySearch [1, 3, 5, 7, 9, 11] 4 = none
#guard binarySearch [2, 3, 1] 1 = none

/-! ## Step 5: counting probes -/

#guard binarySearchWithCount [1, 3, 5, 7, 9, 11] 7 = (some 3, 1)
#guard binarySearchWithCount [1, 3, 5, 7, 9, 11] 4 = (none, 3)
#guard binarySearchWithCount (List.range 1000) 1000 = (none, 9)

/-! ## Spot the fake, round 1: "binary search is correct" -/

/-- Never finds anything. -/
def neverFound (_ : List ℕ) (_ : ℕ) : Option ℕ := none

/-- Option A's statement, for `neverFound`: it holds, because there is never a result to check. -/
theorem neverFound_some_get (xs : List ℕ) (x i : ℕ) (h : neverFound xs x = some i) :
    xs[i]? = some x := by
  simp [neverFound] at h

/-- Always answers "found, at index 0". -/
def alwaysZero (_ : List ℕ) (_ : ℕ) : Option ℕ := some 0

/-- Option B: assumes the target is in the list. -/
theorem binarySearch_isSome_iff_of_mem (xs : List ℕ) (x : ℕ) (_hsort : xs.Pairwise (· ≤ ·))
    (hx : x ∈ xs) : (binarySearch xs x).isSome ↔ x ∈ xs :=
  ⟨fun _ => hx, fun _ => mem_imp_binarySearch_isSome xs x _hsort hx⟩

/-- `alwaysZero` passes option B's statement too. -/
theorem alwaysZero_isSome_iff_of_mem (xs : List ℕ) (x : ℕ) (_hsort : xs.Pairwise (· ≤ ·))
    (hx : x ∈ xs) : (alwaysZero xs x).isSome ↔ x ∈ xs :=
  ⟨fun _ => hx, fun _ => rfl⟩

/-! ## Spot the fake, round 2: "binary search makes at most bits(n) probes" -/

/-- The number of bits of `n` is at most `n`. -/
lemma size_le_self (n : ℕ) : Nat.size n ≤ n :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-- Option C: the real counter, but a linear bound. -/
theorem binarySearchWithCount_snd_le_length (xs : List ℕ) (x : ℕ) :
    (binarySearchWithCount xs x).2 ≤ xs.length :=
  (binarySearchWithCount_snd_le_size xs x).trans (size_le_self xs.length)

/-! ## Exercises -/

#guard binarySearchWithCount [1, 3, 5, 7, 9, 11] 1 = (some 0, 3)

theorem binarySearch_lt_length (xs : List ℕ) (x i : ℕ) (h : binarySearch xs x = some i) :
    i < xs.length := by
  obtain ⟨hi, _⟩ := List.getElem?_eq_some_iff.mp (binarySearch_some_get xs x i h)
  exact hi

end Tutorial.BinarySearch
