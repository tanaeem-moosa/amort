/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Composition
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod

/-!
# State-Space Dynamic Programming Complexity Framework

This module formalizes the general state-space (DAG / memoization) complexity framework for
Dynamic Programming (DP).

## Mathematical Overview

In dynamic programming, rather than manually analyzing nested loops of a bottom-up table,
the complexity of any memoized DP is governed by the state space:
1. **State Space $S$**: The set of distinct subproblem states (e.g. `Fin (n + 1) × Fin (m + 1)`).
2. **Local Work $c(s)$**: The non-recursive computation performed at state $s$
   (e.g., comparing elements, taking minimum/maximum over $k$ transitions).
3. **Uniform Local Bound**: $\forall s \in S,\; c(s) \le C$.

Any memoized algorithm visits/computes each reachable state at most once.
Consequently, the total work across all states satisfies:
$$\text{Total Work} = \sum_{s \in S} c(s) \le |S| \cdot C$$

For 2D grid DP (such as LCS, Edit Distance, Sequence Alignment), the state space
is `Fin (n + 1) × Fin (m + 1)` with cardinality $(n + 1)(m + 1)$. With $O(1)$ local transitions,
the total work is bounded by $(n + 1)(m + 1)$, yielding $O(n \cdot m)$ immediately.

## Key Definitions and Theorems
- `Amort.Recurrence.DPModel`: General finite state space DP specification.
- `Amort.Recurrence.DPModel.totalCost`: Sum of local work across all states.
- `Amort.Recurrence.DPModel.totalCost_le`: Proof that `totalCost ≤ |State| * costBound`.
- `Amort.Recurrence.GridDP`: Specialization to $(n + 1) \times (m + 1)$ 2D grid DP.
- `Amort.Recurrence.GridDP.card_grid_states`: State space cardinality is $(n + 1)(m + 1)$.
- `Amort.Recurrence.GridDP.totalCost_le`: Total cost bounded by $(n + 1)(m + 1) \cdot C$.
- `Amort.Recurrence.GridDP.totalCost_le_unit`: When $C = 1$, total cost $\le (n + 1)(m + 1)$.
- `Amort.Recurrence.isBigO_dp_totalCost`: Mathlib `IsBigO` bridge for state-space DP.
-/

namespace Amort.Recurrence

open Asymptotics

/-- Abstract specification of a Dynamic Programming problem on a finite state space.
* `State`: Type of subproblem states.
* `costPerState`: Local work performed when computing state `s` (excluding recursive subproblems).
* `costBound`: Uniform upper bound on local work per state.
-/
structure DPModel (State : Type*) [Fintype State] where
  costPerState : State → ℕ
  costBound : ℕ
  h_cost : ∀ s : State, costPerState s ≤ costBound

namespace DPModel

variable {State : Type*} [Fintype State]

/-- The total work performed across all states in the state space. -/
def totalCost (dp : DPModel State) : ℕ :=
  ∑ s : State, dp.costPerState s

/-- Fundamental state-space bound: The total work of evaluating all states
is bounded by the number of states times the maximum local cost per state. -/
theorem totalCost_le (dp : DPModel State) :
    dp.totalCost ≤ Fintype.card State * dp.costBound := by
  dsimp [totalCost]
  have h := Finset.sum_le_card_nsmul Finset.univ dp.costPerState dp.costBound
    (fun s _ ↦ dp.h_cost s)
  simp only [Finset.card_univ, smul_eq_mul] at h
  exact h

/-- Pointwise bound: Any cost bounded by `totalCost` is bounded by `|State| * costBound`. -/
theorem cost_le_card_mul_bound (dp : DPModel State) {c : ℕ} (hc : c ≤ dp.totalCost) :
    c ≤ Fintype.card State * dp.costBound :=
  hc.trans dp.totalCost_le

end DPModel

/-! ### 2D Grid Dynamic Programming -/

/-- Specialization to 2D grid DP problems of dimension `(n + 1) × (m + 1)`
(such as LCS, Edit Distance, and Sequence Alignment). -/
structure GridDP (n m : ℕ) where
  costPerCell : Fin (n + 1) → Fin (m + 1) → ℕ
  costBound : ℕ
  h_cost : ∀ i j, costPerCell i j ≤ costBound

namespace GridDP

variable {n m : ℕ}

/-- Embeds a 2D grid DP into the general `DPModel` on `Fin (n + 1) × Fin (m + 1)`. -/
def toDPModel (g : GridDP n m) : DPModel (Fin (n + 1) × Fin (m + 1)) where
  costPerState := fun ⟨i, j⟩ ↦ g.costPerCell i j
  costBound := g.costBound
  h_cost := fun ⟨i, j⟩ ↦ g.h_cost i j

/-- The state space cardinality of an `(n + 1) × (m + 1)` grid DP is `(n + 1) * (m + 1)`. -/
@[simp]
theorem card_grid_states (n m : ℕ) :
    Fintype.card (Fin (n + 1) × Fin (m + 1)) = (n + 1) * (m + 1) := by
  simp [Fintype.card_prod]

/-- The total cost of an `(n + 1) × (m + 1)` grid DP is bounded by
`(n + 1) * (m + 1) * costBound`. -/
theorem totalCost_le (g : GridDP n m) :
    g.toDPModel.totalCost ≤ (n + 1) * (m + 1) * g.costBound := by
  have h := g.toDPModel.totalCost_le
  rw [card_grid_states] at h
  exact h

/-- When local cost per cell is at most 1, total cost is at most `(n + 1) * (m + 1)`. -/
theorem totalCost_le_unit (g : GridDP n m) (h_unit : g.costBound ≤ 1) :
    g.toDPModel.totalCost ≤ (n + 1) * (m + 1) := by
  calc g.toDPModel.totalCost
    _ ≤ (n + 1) * (m + 1) * g.costBound := g.totalCost_le
    _ ≤ (n + 1) * (m + 1) * 1 := Nat.mul_le_mul_left _ h_unit
    _ = (n + 1) * (m + 1) := mul_one _

/-- Canonical unit-cost 2D grid DP where every cell incurs at most 1 step. -/
def unitGridDP (n m : ℕ) : GridDP n m where
  costPerCell := fun _ _ ↦ 1
  costBound := 1
  h_cost := fun _ _ ↦ Nat.le_refl 1

@[simp]
theorem unitGridDP_costBound (n m : ℕ) : (unitGridDP n m).costBound = 1 := rfl

theorem unitGridDP_totalCost (n m : ℕ) :
    (unitGridDP n m).toDPModel.totalCost = (n + 1) * (m + 1) := by
  dsimp [DPModel.totalCost, unitGridDP, toDPModel]
  simp

end GridDP

/-! ### Asymptotic Complexity Bridges -/

/-- State-space DP complexity bridge: If state space cardinality is $O(g_1)$ and
cost bound is $O(g_2)$, the total cost is $O(g_1 \cdot g_2)$ under any filter. -/
theorem isBigO_dp_totalCost {α : Type*} {l : Filter α}
    (State : α → Type*) [∀ a, Fintype (State a)]
    (dp : (a : α) → DPModel (State a))
    (g₁ g₂ : α → ℕ)
    (h_card : (fun a ↦ ((Fintype.card (State a) : ℕ) : ℝ)) =O[l] (fun a ↦ ((g₁ a : ℕ) : ℝ)))
    (h_bound : (fun a ↦ (((dp a).costBound : ℕ) : ℝ)) =O[l] (fun a ↦ ((g₂ a : ℕ) : ℝ))) :
    (fun a ↦ (((dp a).totalCost : ℕ) : ℝ)) =O[l] (fun a ↦ ((g₁ a * g₂ a : ℕ) : ℝ)) := by
  have h_le : ∀ᶠ a in l, (dp a).totalCost ≤ Fintype.card (State a) * (dp a).costBound := by
    apply Filter.Eventually.of_forall
    intro a
    exact (dp a).totalCost_le
  exact isBigO_of_le_mul_nat (fun a ↦ (dp a).totalCost) (fun a ↦ Fintype.card (State a)) g₁
    (fun a ↦ (dp a).costBound) g₂ h_le h_card h_bound

/-- Grid DP complexity bridge: An `(n + 1) × (m + 1)` grid DP with $O(1)$ cell cost
is $O((n + 1)(m + 1))$ under any filter. -/
theorem isBigO_gridDP_totalCost {α : Type*} {l : Filter α}
    (dim : α → ℕ × ℕ)
    (g : (a : α) → GridDP (dim a).1 (dim a).2)
    (h_bound : ∀ a, (g a).costBound ≤ 1) :
    (fun a ↦ (((g a).toDPModel.totalCost : ℕ) : ℝ)) =O[l]
    (fun a ↦ ((((dim a).1 + 1) * ((dim a).2 + 1) : ℕ) : ℝ)) := by
  refine IsBigO.of_bound (1 : ℝ) ?_
  apply Filter.Eventually.of_forall
  intro a
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := (g a).totalCost_le_unit (h_bound a)
  exact_mod_cast h

end Amort.Recurrence
