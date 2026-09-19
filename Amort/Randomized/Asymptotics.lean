/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Randomized.Quicksort
import Amort.Randomized.KargerMinCut
import Amort.Randomized.UniversalHash
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Randomized Algorithms

This module connects concrete operational step bounds for randomized algorithms
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework under `Filter.atTop`:
1. Expected Randomized Quicksort comparison bound: $O(n \log n)$.
2. Amplified Karger Min-Cut contraction work: $O(n^4)$.
3. 2-Universal hash table lookup expected steps: $O(1)$.

## Key Theorems
- `Amort.Randomized.isBigO_quicksortWorkBound_atTop`: Quicksort $O(n \log n)$ in `IsBigO`.
- `Amort.Randomized.isBigO_kargerTotalWork_atTop`: Karger min-cut $O(n^4)$ in `IsBigO`.
- `Amort.Randomized.isBigO_hashLookupExpectedWork_atTop`: Hash lookup $O(1)$ in `IsBigO`.
-/

open Asymptotics

namespace Amort.Randomized

/-! ### Randomized Quicksort Asymptotics -/

/-- Expected randomized quicksort comparison bound is asymptotically $O(n \cdot \text{size } n)$
under `Filter.atTop`. -/
theorem isBigO_quicksortWorkBound_atTop :
    (fun (n : ℕ) ↦ (((quicksortWorkBound n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ (((2 * n * Nat.size n : ℕ) : ℝ))) :=
  isBigO_refl _ _

/-! ### Karger's Min-Cut Asymptotics -/

/-- Amplified Karger min-cut operational complexity is asymptotically $O(n^4)$
under `Filter.atTop`. -/
theorem isBigO_kargerTotalWork_atTop :
    (fun (n : ℕ) ↦ (((kargerTotalWork n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ (((n ^ 4 : ℕ) : ℝ))) :=
  isBigO_refl _ _

/-! ### Universal Hash Table Lookup Asymptotics -/

/-- Expected hash table lookup step count is asymptotically $O(1)$ under `Filter.atTop`. -/
theorem isBigO_hashLookupExpectedWork_atTop :
    (fun (_ : ℕ) ↦ (((hashLookupExpectedWork : ℕ) : ℝ))) =O[Filter.atTop]
      (fun _ ↦ (1 : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [hashLookupExpectedWork]
  norm_num

end Amort.Randomized
