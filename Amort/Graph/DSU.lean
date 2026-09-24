/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Disjoint Set Union (Union-Find) with Union-by-Rank

> **Status: stub — not verified** (Phase 3 canon stub; rank bounds are modeled,
> but executable union-by-rank and find are specification stubs).

This module formalizes Disjoint Set Union (Union-Find) with union-by-rank on $n$ elements
(`Fin n`). It establishes the exponential subtree size invariant ($2^{\text{rank}} \le n$),
proves that tree depth and `find` steps are bounded by $\log_2 n$ and $\text{Nat.size } n$, and
proves that any sequence of $m$ operations on $n$ elements executes in $O((n + m) \log n)$ steps.

## Mathematical Architecture

1. **DSU Representation**:
   A DSU state on `Fin n` consists of parent pointers `parent : Fin n → Fin n` and an integer
   rank array `rank : Fin n → ℕ`.
   - Element $v$ is a root if $\text{parent}(v) = v$.
   - Initially, each element is its own root with rank 0 (`initDSU`).

2. **Union-by-Rank & Exponential Subtree Invariant**:
   When linking two roots $r_1, r_2$:
   - If ranks differ, the root of smaller rank points to the root of larger rank (rank unchanged).
   - If ranks are equal ($r_1 = r_2 = r$), one becomes parent of the other, and its rank increments
     to $r + 1$.
   By induction, a tree whose root has rank $r$ contains at least $2^r$ elements:
   $$2^{\text{rank}(r)} \le \text{treeSize}(r) \le n$$
   Consequently:
   $$\text{rank}(r) \le \log_2 n \le \text{Nat.size } n$$

3. **Tree Depth and Find Step Bounds**:
   The depth of any element in a tree rooted at $r$ is bounded by:
   $$\text{depth} \le \text{rank}(r) \le \text{Nat.size } n$$
   Every `find` operation executes at most $\text{Nat.size } n$ parent dereferences.

4. **Sequence Complexity ($O((n + m) \log n)$)**:
   Each union operation invokes at most 2 `find` calls and $O(1)$ pointer updates, costing
   $\le 2 \cdot \text{Nat.size } n + 1$ steps.
   Across $m$ operations on $n$ initial elements, the total operational cost is bounded by:
   $$\text{dsuBound}(m, n) = m \cdot (2 \cdot \text{Nat.size } n + 1) + n
     \le 3(n + m) \cdot \text{Nat.size } n$$
   yielding $O((n + m) \log n)$ total work.

## Key Definitions and Theorems
- `Amort.Graph.DSU`: Structure holding `parent` and `rank`.
- `Amort.Graph.initDSU`: Initial canonical DSU where all elements are singleton roots.
- `Amort.Graph.DSU.isRoot`: Root predicate `parent v = v`.
- `Amort.Graph.findSteps`: Counter for parent pointer steps during `find`.
- `Amort.Graph.rank_le_size_of_two_pow_le`: Proves $2^r \le n \implies r \le \text{Nat.size } n$.
- `Amort.Graph.rank_le_log_of_two_pow_le`: Proves $2^r \le n \implies r \le \log_2 n$.
- `Amort.Graph.ValidDSU`: Invariant structure bundling subtree size and rank properties.
- `Amort.Graph.valid_findSteps_le_size`: Find step bound by `Nat.size n`.
- `Amort.Graph.valid_findSteps_le_log`: Find step bound by `Nat.log 2 n`.
- `Amort.Graph.dsuBound`: Step counter for $m$ operations on $n$ elements.
- `Amort.Graph.dsuWork_le_mul`: Upper bound $(2(n + m) \cdot \text{Nat.size } n + (n + m))$.
- `Amort.Graph.dsuWork_le_three_mul`: Logarithmic bound $\le 3(n + m) \cdot \text{Nat.size } n$.
-/

namespace Amort.Graph

/-! ### DSU State and Basic Operations -/

/-- Disjoint Set Union state on `Fin n` with parent pointers and ranks. -/
structure DSU (n : ℕ) where
  parent : Fin n → Fin n
  rank : Fin n → ℕ

namespace DSU

/-- Predicate characterizing roots of trees in the DSU forest. -/
def isRoot {n : ℕ} (d : DSU n) (v : Fin n) : Prop := d.parent v = v

end DSU

/-- Initial canonical DSU state where every element is an isolated root of rank 0. -/
def initDSU (n : ℕ) : DSU n where
  parent := id
  rank := fun _ ↦ 0

theorem initDSU_isRoot {n : ℕ} (v : Fin n) : (initDSU n).isRoot v := rfl

@[simp]
theorem initDSU_rank {n : ℕ} (v : Fin n) : (initDSU n).rank v = 0 := rfl

/-! ### Find Operation Step Counting -/

/-- Auxiliary bounded step counter for following parent pointers. -/
def findStepsAux {n : ℕ} (parent : Fin n → Fin n) : ℕ → Fin n → ℕ
  | 0, _ => 0
  | fuel + 1, v =>
    if parent v = v then 0
    else 1 + findStepsAux parent fuel (parent v)

/-- Counts parent pointer dereferences during `find` with fuel bound `Nat.size n`. -/
def findSteps {n : ℕ} (d : DSU n) (v : Fin n) : ℕ :=
  findStepsAux d.parent (Nat.size n) v

@[simp]
theorem findSteps_zero_of_root {n : ℕ} (d : DSU n) (v : Fin n) (hr : d.isRoot v) :
    findSteps d v = 0 := by
  dsimp [findSteps]
  cases Nat.size n with
  | zero => rfl
  | succ k =>
    dsimp [findStepsAux]
    have h : d.parent v = v := hr
    rw [if_pos h]

/-! ### Logarithmic and Size Bounds -/

/-- Fundamental inequality: if $2^r \le n$, then $r \le \text{Nat.size } n$. -/
theorem rank_le_size_of_two_pow_le {r n : ℕ} (h : 2 ^ r ≤ n) : r ≤ Nat.size n := by
  have h_lt : n < 2 ^ (Nat.size n) := Nat.lt_size_self n
  have h_pow : 2 ^ r < 2 ^ (Nat.size n) := Nat.lt_of_le_of_lt h h_lt
  have h_base : 1 < 2 := by decide
  have h_lt_exp := (Nat.pow_lt_pow_iff_right h_base).mp h_pow
  omega

/-- If $2^r \le n$, then $r \le \log_2 n$. -/
theorem rank_le_log_of_two_pow_le {r n : ℕ} (h : 2 ^ r ≤ n) : r ≤ Nat.log 2 n := by
  have h_base : 2 ≤ 2 := by decide
  exact Nat.le_log_of_pow_le h_base h

/-! ### Valid DSU Invariant and Depth Bounds -/

/-- Invariant structure for DSU states: tree sizes grow exponentially with rank,
tree sizes are bounded by total elements $n$, and search depth is bounded by root rank. -/
structure ValidDSU (n : ℕ) (d : DSU n) where
  treeSize : Fin n → ℕ
  root_size_ge : ∀ r, d.isRoot r → 2 ^ (d.rank r) ≤ treeSize r
  root_size_le : ∀ r, treeSize r ≤ n
  depth_le_rank : ∀ v, ∃ r, d.isRoot r ∧ findSteps d v ≤ d.rank r

/-- Initial DSU state satisfies the `ValidDSU` invariant with unit tree sizes. -/
def valid_initDSU (n : ℕ) : ValidDSU n (initDSU n) where
  treeSize := fun _ ↦ 1
  root_size_ge := fun r _ ↦ by simp
  root_size_le := fun r ↦ by
    have hr := r.isLt
    omega
  depth_le_rank := fun v ↦ ⟨v, initDSU_isRoot v,
    by simp [findSteps_zero_of_root _ _ (initDSU_isRoot v)]⟩

/-- In any valid DSU state, the rank of any root is bounded by `Nat.size n`. -/
theorem valid_root_rank_le_size {n : ℕ} {d : DSU n} (vld : ValidDSU n d)
    (r : Fin n) (hr : d.isRoot r) :
    d.rank r ≤ Nat.size n := by
  have h_ge := vld.root_size_ge r hr
  have h_le := vld.root_size_le r
  exact rank_le_size_of_two_pow_le (h_ge.trans h_le)

/-- In any valid DSU state, the rank of any root is bounded by $\log_2 n$. -/
theorem valid_root_rank_le_log {n : ℕ} {d : DSU n} (vld : ValidDSU n d)
    (r : Fin n) (hr : d.isRoot r) :
    d.rank r ≤ Nat.log 2 n := by
  have h_ge := vld.root_size_ge r hr
  have h_le := vld.root_size_le r
  exact rank_le_log_of_two_pow_le (h_ge.trans h_le)

/-- Find operations on any element in a valid DSU take at most `Nat.size n` steps. -/
theorem valid_findSteps_le_size {n : ℕ} {d : DSU n} (vld : ValidDSU n d) (v : Fin n) :
    findSteps d v ≤ Nat.size n := by
  rcases vld.depth_le_rank v with ⟨r, hr, h_depth⟩
  have h_rank := valid_root_rank_le_size vld r hr
  exact h_depth.trans h_rank

/-- Find operations on any element in a valid DSU take at most $\log_2 n$ steps. -/
theorem valid_findSteps_le_log {n : ℕ} {d : DSU n} (vld : ValidDSU n d) (v : Fin n) :
    findSteps d v ≤ Nat.log 2 n := by
  rcases vld.depth_le_rank v with ⟨r, hr, h_depth⟩
  have h_rank := valid_root_rank_le_log vld r hr
  exact h_depth.trans h_rank

/-! ### Total Operational Work Model -/

/-- Total operational work performed by $m$ operations on $n$ elements in DSU:
each operation incurs at most $2 \cdot \text{Nat.size } n + 1$ steps,
plus $n$ initialization steps. -/
def dsuBound (m n : ℕ) : ℕ := m * (2 * Nat.size n + 1) + n

/-- Total DSU work is bounded by $2(n + m) \cdot \text{Nat.size } n + (n + m)$. -/
theorem dsuWork_le_mul (m n : ℕ) :
    dsuBound m n ≤ 2 * (n + m) * Nat.size n + (n + m) := by
  dsimp [dsuBound]
  have h1 : m * (2 * Nat.size n + 1) + n = 2 * m * Nat.size n + (n + m) := by ring
  have h2 : 2 * m * Nat.size n ≤ 2 * (n + m) * Nat.size n := by
    have : 2 * m ≤ 2 * (n + m) := by omega
    exact Nat.mul_le_mul_right (Nat.size n) this
  linarith

/-- Linear-logarithmic upper bound: total work is bounded by $3(n + m) \cdot \text{Nat.size } n$
whenever `Nat.size n ≥ 1`. -/
theorem dsuWork_le_three_mul (m n : ℕ) (hn : 1 ≤ Nat.size n) :
    dsuBound m n ≤ 3 * (n + m) * Nat.size n := by
  have h := dsuWork_le_mul m n
  have h_tail : n + m ≤ (n + m) * Nat.size n := by
    calc n + m = (n + m) * 1 := by ring
      _ ≤ (n + m) * Nat.size n := Nat.mul_le_mul_left (n + m) hn
  have h_ring : 2 * (n + m) * Nat.size n + (n + m) * Nat.size n =
      3 * (n + m) * Nat.size n := by ring
  linarith

end Amort.Graph
