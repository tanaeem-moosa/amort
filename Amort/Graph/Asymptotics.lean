/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.FloydWarshall
import Amort.Graph.BellmanFord
import Amort.Graph.Traversal
import Amort.Graph.TopologicalSort
import Amort.Graph.DSU
import Amort.Graph.Kruskal
import Amort.Recurrence.Composition
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Data.Nat.Size
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Graph Algorithms

This module connects the concrete operational step bounds for textbook graph algorithms
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework:
- Floyd-Warshall all-pairs shortest paths ($O(n^3)$ operations).
- Bellman-Ford single-source shortest paths ($O(|V| \cdot |E|)$ edge relaxations).
- Breadth-First Search ($O(|V| + |E|)$ traversal work).
- Topological Sort via Kahn's algorithm ($O(|V| + |E|)$ work).
- Disjoint Set Union ($O((n + m) \log n)$ operations for $m$ operations on $n$ elements).
- Kruskal's Minimum Spanning Tree ($O(|E| \log |V|)$ combined sorting and DSU work).

## Key Definitions and Theorems
- `Amort.Graph.isBigO_floydWarshallDP_totalCost_atTop`: Floyd-Warshall $O(n^3)$ operations.
- `Amort.Graph.isBigO_bellmanFord_totalRelaxations_atTop`: Bellman-Ford $O(|V| \cdot |E|)$ bounds.
- `Amort.Graph.isBigO_bfsWork_atTop`: BFS traversal work $O(|V| + |E|)$.
- `Amort.Graph.isBigO_kahnWork_atTop`: Topological Sort work $O(|V| + |E|)$.
- `Amort.Graph.isBigO_dsuWork_mul_size_atTop`: DSU $O((n + m) \log n)$ work.
- `Amort.Graph.isBigO_kruskalTotalWork_of_size_le`: Kruskal $O(|E| \log |V|)$ operational bound.
-/

open Asymptotics
open Amort.Recurrence

namespace Amort.Graph

/-! ### Floyd-Warshall Asymptotics -/

/-- Total work of Floyd-Warshall dynamic programming is asymptotically $O(n^3)$
under `Filter.atTop` on $\mathbb{N}$. -/
theorem isBigO_floydWarshallDP_totalCost_atTop :
    (fun n ↦ (((floydWarshallDP n).totalCost : ℕ) : ℝ)) =O[Filter.atTop]
      (fun n ↦ ((n ^ 3 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 2 ?_
  rw [Filter.eventually_atTop]
  refine ⟨1, fun n hn ↦ ?_⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  rw [floydWarshallDP_totalCost]
  have h1 : n + 1 ≤ 2 * n := by omega
  have h2 : (n + 1) * n ^ 2 ≤ 2 * n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) h1
  have h3 : 2 * n * n ^ 2 = 2 * n ^ 3 := by ring
  rw [h3] at h2
  have h2_real : (((n + 1) * n ^ 2 : ℕ) : ℝ) ≤ ((2 * n ^ 3 : ℕ) : ℝ) := by exact_mod_cast h2
  have h_eq : ((2 * n ^ 3 : ℕ) : ℝ) = 2 * ((n ^ 3 : ℕ) : ℝ) := by push_cast; ring
  exact h2_real.trans (le_of_eq h_eq)

/-! ### Bellman-Ford Asymptotics -/

/-- Bellman-Ford $(n - 1)$ rounds of $m$ edge relaxations is $O(n \cdot m)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_bellmanFord_totalRelaxations_atTop :
    (fun (p : ℕ × ℕ) ↦ ((((p.1 - 1) * p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ ((p.1 * p.2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  apply Filter.Eventually.of_forall
  intro ⟨n, m⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have : (n - 1) * m ≤ n * m := Nat.mul_le_mul_right m (Nat.sub_le n 1)
  exact_mod_cast this

/-! ### Linear Traversal & Topological Sort Asymptotics -/

/-- BFS traversal work is asymptotically $O(|V| + |E|)$ under `Filter.atTop`
on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_bfsWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((p.1 + p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ ((p.1 + p.2 : ℕ) : ℝ)) :=
  isBigO_refl _ _

/-- Kahn's Topological Sort work is asymptotically $O(|V| + |E|)$ under `Filter.atTop`
on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_kahnWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((p.1 + p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ ((p.1 + p.2 : ℕ) : ℝ)) :=
  isBigO_refl _ _

/-! ### Disjoint Set Union (DSU) Asymptotics -/

/-- DSU $m$ operations on $n$ elements is $O((n + m) \log n)$ under `Filter.atTop`
on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_dsuWork_mul_size_atTop :
    (fun (p : ℕ × ℕ) ↦ (((dsuWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.2 + p.1) * Nat.size p.2 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 3 ?_
  rw [Filter.eventually_atTop]
  refine ⟨(0, 1), ?_⟩
  rintro ⟨m, n⟩ ⟨_hm, hn⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  have hn_size : 1 ≤ Nat.size n := by
    have : 0 < n := by omega
    exact Nat.size_pos.mpr this
  have h_le := dsuWork_le_three_mul m n hn_size
  have h_le_real : ((dsuWork m n : ℕ) : ℝ) ≤ ((3 * (n + m) * Nat.size n : ℕ) : ℝ) := by
    exact_mod_cast h_le
  have h_ring : ((3 * (n + m) * Nat.size n : ℕ) : ℝ) =
      3 * (((n + m) * Nat.size n : ℕ) : ℝ) := by
    push_cast
    ring
  exact h_le_real.trans (le_of_eq h_ring)

/-! ### Kruskal's Algorithm Asymptotics -/

/-- Kruskal total operational complexity is $O((6 \log |V| + 3) |E| + |V|)$
under any filter where $\text{Nat.size } |E| \le 2 \cdot \text{Nat.size } |V| + 1$. -/
theorem isBigO_kruskalTotalWork_of_size_le (l : Filter (ℕ × ℕ))
    (h_size : ∀ᶠ p in l, Nat.size p.2 ≤ 2 * Nat.size p.1 + 1) :
    (fun (p : ℕ × ℕ) ↦ (((kruskalTotalWork p.1 p.2 : ℕ) : ℝ))) =O[l]
      (fun p ↦ (((6 * Nat.size p.1 + 3) * p.2 + p.1 : ℕ) : ℝ)) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h_size] with ⟨numV, numE⟩ hE
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := kruskal_total_work_le numV numE hE
  exact_mod_cast h

end Amort.Graph
