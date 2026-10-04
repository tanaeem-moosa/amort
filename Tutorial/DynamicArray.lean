/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.DataStructure.DynamicArray

/-!
# Dynamic array: companion file

Companion to `tutorial/dynamic_array.md`. Every Lean snippet the chapter quotes is either here
or in the reference file `Amort/DataStructure/DynamicArray.lean`, so Lean checks all of it on
every build.
-/

set_option linter.hashCommand false
set_option linter.style.header false

open Amort.DataStructure

namespace Tutorial.DynamicArray

/-! ## Step 3: running pushes -/

#guard pushSeq 9 DynArrayState.initOne = ⟨9, 16⟩
#guard (List.range 9).map (fun k => pushActualCost (pushSeq k DynArrayState.initOne)) =
  [1, 2, 3, 1, 5, 1, 1, 1, 9]

/-! ## Step 5: total cost -/

#guard pushSeqCost 8 DynArrayState.initOne = 15
#guard pushSeqCost 9 DynArrayState.initOne = 24

/-! ## Spot the fake: "pushes cost O(1) amortized" -/

/-- A potential that only ever goes down. -/
def badPhi (s : DynArrayState) : ℤ := -((s.size : ℤ) * s.size)

/-- Amortized cost measured with `badPhi`. -/
def badAmortizedCost (s : DynArrayState) : ℤ :=
  (pushActualCost s : ℤ) + badPhi (pushState s) - badPhi s

/-- Option A: an amortized bound with the wrong potential. -/
theorem badAmortizedCost_le_three (s : DynArrayState) :
    badAmortizedCost s ≤ 3 := by
  dsimp [badAmortizedCost, badPhi, pushActualCost, pushState]
  split_ifs <;> push_cast <;> nlinarith

/-- Option C: the worst case of one push. -/
theorem pushActualCost_le_size_add_one (s : DynArrayState) :
    pushActualCost s ≤ s.size + 1 := by
  dsimp [pushActualCost]
  split_ifs <;> omega

/-! ## Exercises -/

theorem pushSeq_initOne_size (k : ℕ) :
    (pushSeq k DynArrayState.initOne).size = k := by
  rw [pushSeq_size]
  simp [DynArrayState.initOne]

end Tutorial.DynamicArray
