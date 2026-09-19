/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.String.SuffixTree.Ukkonen
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Ukkonen's Suffix Tree Construction

This module connects the operational step bounds for Ukkonen's online linear-time suffix tree
construction algorithm to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` framework under
`Filter.atTop` on $\mathbb{N}$:
1. Total operational work across all $n$ phases is $O(n)$ linear time.

## Key Theorems
- `Amort.String.isBigO_ukkonenWork_atTop`: Ukkonen suffix tree construction is $O(n)$ in `IsBigO`.
-/

open Asymptotics

namespace Amort.String

/-- Ukkonen's online suffix tree construction operational complexity is asymptotically $O(n)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_ukkonenWork_atTop :
    (fun (n : ℕ) ↦ (((ukkonenWork n : ℕ) : ℝ))) =O[Filter.atTop]
      (fun n ↦ ((n : ℝ))) := by
  refine IsBigO.of_bound 4 ?_
  apply Filter.Eventually.of_forall
  intro n
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [ukkonenWork]
  have h : ((4 * n : ℕ) : ℝ) = 4 * (n : ℝ) := by
    push_cast
    ring
  rw [h]

end Amort.String
