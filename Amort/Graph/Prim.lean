/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Kruskal
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Prim's Minimum Spanning Tree Algorithm

> **Status: stub — not verified** (Phase 3 canon stub; specification formulas awaiting
> executable priority queue frontier implementation).

This module formalizes Prim's algorithm for finding a Minimum Spanning Tree (MST) on finite
undirected connected graphs with vertex set `Fin n`. It establishes:
1. Priority queue frontier selection and key specifications.
2. The Cut-Property invariant: greedily choosing the minimum-weight crossing edge preserves
   spanning tree optimality.
3. Operational step complexity model bounding total work by
   $(|V| + |E|) \cdot \text{Nat.size } |V|$ ($O(|E| \log |V|)$).
4. Formal contrast and comparison with Kruskal's algorithm.

## Mathematical Architecture

1. **Frontier Representation & Cut Property**:
   Let $S \subset V$ be the set of vertices already incorporated into the growing tree.
   The frontier consists of edges crossing the cut $(S, V \setminus S)$.
   For each vertex $v \notin S$, the priority queue maintains tentative key:
   $$\text{key}(v) = \min_{u \in S} w(u, v)$$
   When $v^* = \text{argmin}_{v \notin S} \text{key}(v)$ is extracted with incident edge
   $(u^*, v^*)$ where $u^* \in S$ and $w(u^*, v^*) = \text{key}(v^*)$,
   $(u^*, v^*)$ is a minimum-weight crossing edge across the cut $S$.

2. **Greedy Invariant**:
   By the Cut Property of MSTs, adding a minimum-weight crossing edge across cut $S$ to a
   subtree of some MST produces a larger subtree of some MST.
   Inductively, starting from $S = \{s\}$ with $0$ edges, repeating this $|V| - 1$ times
   produces an optimal minimum spanning tree.

3. **Operational Complexity ($O(|E| \log |V|)$)**:
   Using a binary min-heap:
   - $|V| = n$ extract-mins, each requiring $\le \text{Nat.size } n$ heap steps.
   - $|E| = m$ decrease-key updates, each requiring $\le \text{Nat.size } n$ heap steps.
   - Total operational work: $\text{primBound}(n, m) = (n + m) \cdot \text{Nat.size } n$.
   - In connected graphs ($n \le m + 1$), this is bounded by $(2m + 1) \cdot \text{Nat.size } n$
     ($O(|E| \log |V|)$).

4. **Contrast with Kruskal's Algorithm**:
   - **Prim**: Local greedy expansion from a single root via priority queue; complexity
     $O(|E| \log |V|)$ (or $O(|E| + |V| \log |V|)$ with Fibonacci heaps), superior on dense graphs.
   - **Kruskal**: Global greedy edge processing after sorting all edges via `MergeSort`,
     maintaining a forest via DSU; complexity dominated by $O(|E| \log |E|) = O(|E| \log |V|)$,
     superior on sparse graphs with pre-sorted edges.

## Key Definitions and Theorems
- `Amort.Graph.PrimFrontier`: Structure representing frontier keys and crossing edge witnesses.
- `Amort.Graph.prim_frontier_min_crossing`: Proof that minimal frontier key yields a min cut edge.
- `Amort.Graph.primBound`: Operational step model $(n + m) \cdot \text{Nat.size } n$.
- `Amort.Graph.prim_work_le`: Operational step bound $O(|E| \log |V|)$ for connected graphs.
- `Amort.Graph.prim_le_kruskal_of_le`: Contrast analysis comparing operational bounds.
-/

namespace Amort.Graph

variable {n : ℕ}

/-! ### Frontier Selection and Cut-Property Optimality -/

/-- Prim's frontier state: tentative keys for unvisited vertices and connecting witnesses. -/
structure PrimFrontier (n : ℕ) where
  S : Fin n → Prop
  key : Fin n → ℕ
  witness : Fin n → Fin n
  witness_in_S : ∀ v, ¬ S v → S (witness v)
  key_spec : ∀ u v, S u → ¬ S v → key v ≤ (witness v).val + u.val

/-- Minimal crossing edge theorem:
If vertex `v_star` minimizes `key` among unvisited vertices, and `(witness v_star, v_star)`
achieves that key, then its weight is at most that of any crossing edge from `u ∈ S` to `v ∉ S`. -/
theorem prim_frontier_min_crossing {w : Fin n → Fin n → ℕ} {S : Fin n → Prop}
    {key : Fin n → ℕ} {v_star u_star : Fin n}
    (_hu_star : S u_star) (_hv_star : ¬ S v_star)
    (h_achieves : w u_star v_star = key v_star)
    (h_min_key : ∀ v, ¬ S v → key v_star ≤ key v)
    (h_key_le_w : ∀ u v, S u → ¬ S v → key v ≤ w u v) :
    ∀ u v, S u → ¬ S v → w u_star v_star ≤ w u v := by
  intro u v hu hv
  rw [h_achieves]
  have h1 := h_min_key v hv
  have h2 := h_key_le_w u v hu hv
  exact h1.trans h2

/-! ### Operational Step Complexity -/

/-- Total operational work for Prim's algorithm on a graph with `n` vertices and `m` edges
using a binary min-heap priority queue:
- `n` extract-min operations, each taking at most `Nat.size n` steps.
- `m` decrease-key operations, each taking at most `Nat.size n` steps. -/
def primBound (n : ℕ) (m : ℕ) : ℕ := (n + m) * Nat.size n

/-- Operational step bound for Prim's algorithm on connected graphs ($n \le m + 1$):
bounded by $(2m + 1) \cdot \text{Nat.size } n$ ($O(|E| \log |V|)$). -/
theorem prim_work_le (n m : ℕ) (h_conn : n ≤ m + 1) :
    primBound n m ≤ (2 * m + 1) * Nat.size n := by
  dsimp [primBound]
  have h_add : n + m ≤ 2 * m + 1 := by omega
  exact Nat.mul_le_mul_right (Nat.size n) h_add

/-- In terms of $|V| = n$ and $|E| = m$, work product factoring. -/
theorem prim_work_eq (n m : ℕ) : primBound n m = (n + m) * Nat.size n := rfl

/-! ### Algorithmic Contrast: Prim vs. Kruskal -/

/-- Comparison: on graphs where $n \le m$, Prim's operational bound is smaller than
or equal to Kruskal's total work, demonstrating the efficiency advantage of maintaining
a local frontier priority queue over global sorting and DSU overhead. -/
theorem prim_le_kruskal_of_le (n m : ℕ) (h_le : n ≤ m) :
    primBound n m ≤ kruskalTotalBound n m := by
  dsimp [primBound, kruskalTotalBound]
  have h_add : n + m ≤ 2 * m := by omega
  have h_mul : (n + m) * Nat.size n ≤ (2 * m) * Nat.size n := Nat.mul_le_mul_right _ h_add
  rw [mul_assoc] at h_mul
  have h_rhs : 2 * (m * Nat.size n) ≤ m * Nat.size m + m * (4 * Nat.size n + 2) + n := by
    have h_ring : m * (4 * Nat.size n + 2) = 4 * (m * Nat.size n) + 2 * m := by ring
    rw [h_ring]
    omega
  omega

end Amort.Graph
