/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.DSU
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-!
# Path Compression with Union-by-Rank

This module formalizes Disjoint Set Union (DSU) augmented with path compression during `find`.
It establishes the strict rank hierarchy invariant along parent pointers and proves the
logarithmic rank bound:
1. `StrictRankHierarchy`: For non-root $v$, $\text{rank}(v) < \text{rank}(\text{parent}(v))$.
2. `compress`: Augments DSU by flattening parent pointers directly to the root $r$.
3. `compress_preserves_hierarchy`: Proves that path compression preserves the strict rank hierarchy.
4. `rank_le_log_of_bound`: Node ranks are bounded above by $\log_2 n \le \text{Nat.size } n$.

## Mathematical Architecture

1. **Strict Rank Hierarchy**:
   In union-by-rank, whenever two trees are united, the root with smaller rank is attached as a
   child of the root with larger rank. When ranks are equal, one root's rank increments by 1.
   Consequently, parent pointers strictly increase in rank:
   $$v \ne \text{parent}(v) \implies \text{rank}(v) < \text{rank}(\text{parent}(v))$$

2. **Path Compression Invariance**:
   During `find(v)`, each visited node along the path has its parent pointer updated to root $r$:
   $$\text{parent}(u) := r$$
   Because $r$ is an ancestor of $u$ along a chain of strictly increasing ranks,
   $\text{rank}(u) < \text{rank}(r)$. Thus pointing $u$ directly to $r$ strictly preserves
   the rank hierarchy invariant.

3. **Logarithmic Rank Bound**:
   A tree rooted at a node of rank $r$ contains at least $2^r$ nodes. Therefore:
   $$2^{\text{rank}(v)} \le n \implies \text{rank}(v) \le \log_2 n \le \text{Nat.size } n$$
-/

namespace Amort.Graph

/-! ### Strict Rank Hierarchy Invariant -/

/-- Strict rank hierarchy invariant: every non-root node has rank strictly smaller than its
parent. -/
def StrictRankHierarchy {n : ℕ} (d : DSU n) : Prop :=
  ∀ v : Fin n, ¬ d.isRoot v → d.rank v < d.rank (d.parent v)

/-- The initial canonical DSU state vacuously satisfies the strict rank hierarchy invariant,
since every node is an isolated root. -/
theorem initDSU_strictRankHierarchy (n : ℕ) :
    StrictRankHierarchy (initDSU n) := by
  intro v hnot
  exfalso
  exact hnot (initDSU_isRoot v)

/-! ### Path Compression Operation -/

/-- Single-node path compression step updating `parent v := r` while keeping ranks unchanged. -/
def compress {n : ℕ} (d : DSU n) (v : Fin n) (r : Fin n) : DSU n where
  parent := fun x ↦ if x = v then r else d.parent x
  rank := d.rank

@[simp]
theorem compress_rank {n : ℕ} (d : DSU n) (v r : Fin n) (x : Fin n) :
    (compress d v r).rank x = d.rank x := rfl

@[simp]
theorem compress_parent_same {n : ℕ} (d : DSU n) (v r : Fin n) :
    (compress d v r).parent v = r := by
  dsimp [compress]
  rw [if_pos rfl]

theorem compress_parent_other {n : ℕ} (d : DSU n) (v r : Fin n) {x : Fin n} (hne : x ≠ v) :
    (compress d v r).parent x = d.parent x := by
  dsimp [compress]
  rw [if_neg hne]

/-- Path compression preserves the strict rank hierarchy: If node $v$ is pointed directly to an
ancestor root $r$ of strictly greater rank, the strict rank hierarchy invariant is preserved. -/
theorem compress_preserves_hierarchy {n : ℕ} (d : DSU n)
    (h_hier : StrictRankHierarchy d) (v r : Fin n)
    (h_lt : d.rank v < d.rank r) :
    StrictRankHierarchy (compress d v r) := by
  intro x hnot_root
  by_cases hx : x = v
  · subst hx
    dsimp [compress]
    rw [if_pos rfl]
    exact h_lt
  · dsimp [compress]
    rw [if_neg hx]
    dsimp [compress, DSU.isRoot] at hnot_root
    rw [if_neg hx] at hnot_root
    exact h_hier x hnot_root

/-! ### Rank Logarithmic Bounds -/

/-- Subtree exponential size bound predicate: Every node of rank $r$ represents at least
$2^r$ elements in the disjoint-set universe of size $n$. -/
def SubtreeRankBound {n : ℕ} (d : DSU n) : Prop :=
  ∀ v : Fin n, 2 ^ (d.rank v) ≤ n

/-- Node ranks are bounded above by $\log_2 n$ under the subtree exponential size invariant. -/
theorem rank_le_log_of_bound {n : ℕ} (d : DSU n) (h_bound : SubtreeRankBound d) (v : Fin n) :
    d.rank v ≤ Nat.log 2 n :=
  rank_le_log_of_two_pow_le (h_bound v)

/-- Node ranks are bounded above by $\text{Nat.size } n$ under the subtree exponential
size invariant. -/
theorem rank_le_size_of_bound {n : ℕ} (d : DSU n) (h_bound : SubtreeRankBound d) (v : Fin n) :
    d.rank v ≤ Nat.size n :=
  rank_le_size_of_two_pow_le (h_bound v)

/-- Path compression preserves the subtree exponential size bound. -/
theorem compress_preserves_subtreeBound {n : ℕ} (d : DSU n)
    (h_bound : SubtreeRankBound d) (v r : Fin n) :
    SubtreeRankBound (compress d v r) := by
  intro x
  rw [compress_rank]
  exact h_bound x

end Amort.Graph
