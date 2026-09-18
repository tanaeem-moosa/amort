/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Dynamic Array with Capacity Doubling

This module formalizes the classic dynamic array amortized analysis via the potential method:
- Array state: `(size, capacity)` with invariant `size ≤ capacity`.
- Capacity doubling: when `size = capacity`, capacity doubles to `2 * capacity`.
- Potential function: $\Phi(n, C) = 2n - C$.
- Actual costs:
  - If $n < C$, actual cost $c = 1$.
  - If $n = C$, actual cost $c = n + 1$ (copying $n$ elements plus 1 insertion).
- Amortized cost: $\hat{c} = c + \Phi' - \Phi = 3$ for all push operations.
- Non-negativity: $\Phi \ge 0$ whenever $C \le 2n$.
- Telescoping bound: total actual cost of $k$ pushes is bounded by $3k + \Phi_0$.

## Mathematical Architecture

1. **State & Transitions**:
   - `DynArrayState`: stores `size` and `capacity`.
   - `pushState`: updates state upon push. If full, capacity doubles (`2 * capacity`).
   - `pushActualCost`: returns 1 if not full, $n + 1$ if full.

2. **Potential Method (Tarjan)**:
   - `phi s = 2 * s.size - s.capacity` (in $\mathbb{Z}$).
   - `pushAmortizedCost s = pushActualCost s + phi (pushState s) - phi s`.
   - Milestone Theorem: `pushAmortizedCost_eq_three` proves $\hat{c} = 3$ identically.
   - Milestone Theorem: `pushAmortizedCost_le_three` proves $\hat{c} \le 3$.

3. **Multi-Operation Telescoping**:
   - `pushSeq k s`: state after $k$ pushes.
   - `pushSeqCost k s`: sum of actual costs across $k$ pushes.
   - Milestone Theorem: `pushSeqCost_telescope` establishes
     $\sum c_i = 3k - \Phi_k + \Phi_0 \le 3k + \Phi_0$.

## Key Definitions and Theorems
- `Amort.DataStructure.DynArrayState`: Structure storing `size` and `capacity`.
- `Amort.DataStructure.phi`: Potential function $\Phi = 2n - C$.
- `Amort.DataStructure.phi_nonneg`: Non-negativity when $C \le 2n$.
- `Amort.DataStructure.pushState`: State transition for push.
- `Amort.DataStructure.pushActualCost`: Actual operational cost.
- `Amort.DataStructure.pushAmortizedCost`: Amortized cost $\hat{c}$.
- `Amort.DataStructure.pushAmortizedCost_eq_three`: Exact amortized cost = 3.
- `Amort.DataStructure.pushAmortizedCost_le_three`: Amortized bound $\le 3$.
- `Amort.DataStructure.pushSeqCost_telescope`: Telescoping actual cost theorem.
-/

namespace Amort.DataStructure

/-- State of a dynamic array storing current element count and allocated capacity. -/
structure DynArrayState where
  size : ℕ
  capacity : ℕ
  deriving Repr, DecidableEq

namespace DynArrayState

/-- Initial dynamic array with 0 elements and initial capacity `c₀`. -/
def init (c₀ : ℕ) : DynArrayState :=
  ⟨0, c₀⟩

/-- Standard initial dynamic array with 0 elements and capacity 1. -/
def initOne : DynArrayState :=
  ⟨0, 1⟩

end DynArrayState

/-- Potential function for dynamic array: $\Phi(n, C) = 2n - C$. -/
def phi (s : DynArrayState) : ℤ :=
  2 * (s.size : ℤ) - (s.capacity : ℤ)

/-- Potential is non-negative whenever the array is at least half full ($C \le 2n$). -/
theorem phi_nonneg (s : DynArrayState) (h : s.capacity ≤ 2 * s.size) :
    0 ≤ phi s := by
  dsimp [phi]
  omega

/-- Dynamic array state transition upon pushing a new element:
if `size < capacity`, capacity is unchanged;
if `size = capacity`, capacity doubles to `2 * capacity`. -/
def pushState (s : DynArrayState) : DynArrayState :=
  if s.size < s.capacity then
    ⟨s.size + 1, s.capacity⟩
  else
    ⟨s.size + 1, 2 * s.capacity⟩

/-- Actual operational cost of push:
1 unit to insert element if space available,
$n + 1$ units (copying $n$ elements plus 1 insertion) if resizing. -/
def pushActualCost (s : DynArrayState) : ℕ :=
  if s.size < s.capacity then 1
  else s.size + 1

/-- Amortized cost of push via the potential method:
$\hat{c} = c + \Phi(s') - \Phi(s)$. -/
def pushAmortizedCost (s : DynArrayState) : ℤ :=
  (pushActualCost s : ℤ) + phi (pushState s) - phi s

/-- Milestone Theorem: the amortized cost of pushing into a dynamic array
is identically 3 for all valid configurations ($n \le C$). -/
theorem pushAmortizedCost_eq_three (s : DynArrayState)
    (hle : s.size ≤ s.capacity) :
    pushAmortizedCost s = 3 := by
  dsimp [pushAmortizedCost, pushActualCost, pushState, phi]
  split_ifs with h
  · push_cast
    ring
  · have heq : s.size = s.capacity := by omega
    push_cast
    omega

/-- Milestone Bound: amortized cost of push is bounded by 3 ($T_{\text{amortized}} \le 3$). -/
theorem pushAmortizedCost_le_three (s : DynArrayState)
    (hle : s.size ≤ s.capacity) :
    pushAmortizedCost s ≤ 3 := by
  rw [pushAmortizedCost_eq_three s hle]

/-! ### Multi-Operation Telescoping Sequences -/

/-- State after applying $k$ successive push operations. -/
def pushSeq : ℕ → DynArrayState → DynArrayState
  | 0, s => s
  | k + 1, s => pushState (pushSeq k s)

/-- Cumulative actual cost across $k$ successive push operations. -/
def pushSeqCost : ℕ → DynArrayState → ℕ
  | 0, _ => 0
  | k + 1, s => pushSeqCost k s + pushActualCost (pushSeq k s)

/-- Capacity remains strictly positive across pushes if initially positive. -/
theorem pushSeq_capacity_pos (k : ℕ) (s : DynArrayState) (hpos : 0 < s.capacity) :
    0 < (pushSeq k s).capacity := by
  induction k with
  | zero => exact hpos
  | succ k ih =>
    dsimp [pushSeq, pushState]
    split_ifs
    · exact ih
    · dsimp; omega

/-- Invariant that size remains bounded by capacity across pushes,
given an initial non-empty capacity. -/
theorem pushSeq_size_le_capacity (k : ℕ) (s : DynArrayState)
    (hle : s.size ≤ s.capacity) (hpos : 0 < s.capacity) :
    (pushSeq k s).size ≤ (pushSeq k s).capacity := by
  induction k with
  | zero => exact hle
  | succ k ih =>
    dsimp [pushSeq, pushState]
    have hcap := pushSeq_capacity_pos k s hpos
    split_ifs with h
    · dsimp; omega
    · dsimp; omega

/-- Telescoping theorem for dynamic array: cumulative actual cost across $k$ pushes
equals $3k - \Phi_k + \Phi_0$. -/
theorem pushSeqCost_telescope (k : ℕ) (s : DynArrayState)
    (hle : ∀ j < k, (pushSeq j s).size ≤ (pushSeq j s).capacity) :
    (pushSeqCost k s : ℤ) = 3 * (k : ℤ) - phi (pushSeq k s) + phi s := by
  induction k with
  | zero =>
    dsimp [pushSeqCost, pushSeq]
    ring
  | succ k ih =>
    dsimp [pushSeqCost, pushSeq]
    have ih_le : ∀ j < k, (pushSeq j s).size ≤ (pushSeq j s).capacity := by
      intro j hj
      exact hle j (by omega)
    have ih_eq := ih ih_le
    have h_last := hle k (by omega)
    have h_amort := pushAmortizedCost_eq_three (pushSeq k s) h_last
    dsimp [pushAmortizedCost] at h_amort
    linarith

/-- Concrete upper bound: if final potential is non-negative, total actual cost
of $k$ pushes is at most $3k + \Phi_0$. -/
theorem pushSeqCost_le_three_mul_add (k : ℕ) (s : DynArrayState)
    (hle : ∀ j < k, (pushSeq j s).size ≤ (pushSeq j s).capacity)
    (hphi : 0 ≤ phi (pushSeq k s)) :
    (pushSeqCost k s : ℤ) ≤ 3 * (k : ℤ) + phi s := by
  have h_tel := pushSeqCost_telescope k s hle
  linarith

end Amort.DataStructure
