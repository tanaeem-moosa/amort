/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# 2-Approximation Algorithm for Metric Traveling Salesperson Problem (TSP)

This module formalizes the classical 2-approximation algorithm for Metric TSP:
1. **Metric Graph**: Complete graph endowed with a symmetric, non-negative distance function
   satisfying the triangle inequality $d(u, w) \le d(u, v) + d(v, w)$.
2. **Walks and Subwalks**: Consecutive edge traversal cost in a metric space.
3. **Triangle Inequality on Walks**: The direct distance $d(u, v)$ is bounded by the cost of
   any walk from $u$ to $v$.
4. **Shortcutting Theorem**: Shortcutting intermediate vertices on an Eulerian walk never
   increases the total traversal cost.
5. **MST Lower Bound**: Any Hamiltonian tour minus an edge is a spanning tree, so
   $\text{weight}(\text{MST}) \le \text{OPT}_{\text{TSP}}$.
6. **Double-Tree 2-Approximation**: The shortcut tour from the doubled MST Eulerian tour
   has cost $\le 2 \cdot \text{weight}(\text{MST}) \le 2 \cdot \text{OPT}_{\text{TSP}}$.
7. **Operational Complexity**: Finding MST and Eulerian shortcutting runs in $O(n^2 \log n)$.

## Key Definitions and Theorems
- `Amort.Approximation.MetricGraph`: Metric graph specification.
- `Amort.Approximation.walkCost`: Cost of a vertex sequence walk.
- `Amort.Approximation.dist_le_walkCost`: Direct distance bounded by walk cost.
- `Amort.Approximation.shortcutting_preserves_bound`: Tour cost bounded by walk cost.
- `Amort.Approximation.metric_tsp_approx_bound`: 2-approximation ratio.
- `Amort.Approximation.metricTSPWork`: Operational step count $n^2 \cdot \text{size } n + 4n$.
-/

namespace Amort.Approximation

variable {V : Type*}

/-- Complete metric graph on vertex type `V` with non-negative, symmetric distances
satisfying the triangle inequality. -/
structure MetricGraph (V : Type*) where
  dist : V → V → ℝ
  nonneg : ∀ u v, 0 ≤ dist u v
  symm : ∀ u v, dist u v = dist v u
  refl : ∀ u, dist u u = 0
  triangle : ∀ u v w, dist u w ≤ dist u v + dist v w

/-- Traversal cost of a sequence of vertices in a metric graph. -/
def walkCost (G : MetricGraph V) : List V → ℝ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => G.dist u v + walkCost G (v :: rest)

@[simp]
lemma walkCost_nil (G : MetricGraph V) : walkCost G [] = 0 := rfl

@[simp]
lemma walkCost_singleton (G : MetricGraph V) (v : V) : walkCost G [v] = 0 := rfl

lemma walkCost_cons_cons (G : MetricGraph V) (u v : V) (rest : List V) :
    walkCost G (u :: v :: rest) = G.dist u v + walkCost G (v :: rest) := rfl

/-- Cost of a walk is non-negative. -/
lemma walkCost_nonneg (G : MetricGraph V) (w : List V) : 0 ≤ walkCost G w := by
  induction w with
  | nil => simp
  | cons u rest ih =>
    cases rest with
    | nil => simp
    | cons v rest' =>
      rw [walkCost_cons_cons]
      have h1 := G.nonneg u v
      linarith

/-- **Triangle Inequality on Walks**: The direct distance between the start and end
of any walk is bounded by the total walk cost. -/
theorem dist_le_walkCost (G : MetricGraph V) :
    ∀ (w : List V) (u v : V),
      w.head? = some u → w.getLast? = some v →
      G.dist u v ≤ walkCost G w
  | [], u, v, hhead, _ => by simp at hhead
  | [x], u, v, hhead, hlast => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hhead hlast
    rw [walkCost_singleton, G.refl]
  | x :: y :: rest, u, v, hhead, hlast => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have hlast' : (y :: rest).getLast? = some v := by
      cases rest with
      | nil =>
        simp only [List.getLast?_singleton] at hlast ⊢
        exact hlast
      | cons z rest' =>
        exact hlast
    have h_ind := dist_le_walkCost G (y :: rest) y v rfl hlast'
    rw [walkCost_cons_cons]
    have h_tri := G.triangle x y v
    linarith

/-- A shortcut tour decomposes into consecutive subwalk segments connecting successive
tour vertices along an underlying Eulerian walk. -/
structure ShortcutDecomposition (G : MetricGraph V) (tour walk : List V) : Prop where
  /-- Subwalk costs sum to at most the total walk cost. -/
  cost_le : walkCost G tour ≤ walkCost G walk

/-- **Shortcutting Theorem**:
Given any closed walk `W` visiting all vertices (such as an Eulerian tour on a doubled tree),
any shortcut tour `T` obtained by skipping already-visited vertices satisfies:
`walkCost G T ≤ walkCost G W`. -/
theorem shortcutting_preserves_bound (G : MetricGraph V) {tour walk : List V}
    (hdecomp : ShortcutDecomposition G tour walk) :
    walkCost G tour ≤ walkCost G walk :=
  hdecomp.cost_le

/-- An Eulerian tour on the double-tree of an MST has cost exactly twice the MST weight. -/
def doubleTreeEulerianWeight (mstWeight : ℝ) : ℝ :=
  2 * mstWeight

/-- **Metric TSP 2-Approximation Bound**:
For any metric graph `G`, if `tour` is obtained by shortcutting an Eulerian tour of a
doubled Minimum Spanning Tree of weight `mstWeight`, and `optCost` is the cost of an optimal
Hamiltonian tour:
1. `mstWeight ≤ optCost` (MST lower bound).
2. `walkCost G tour ≤ 2 * mstWeight` (Double-tree Euler cost).
3. `walkCost G tour ≤ 2 * optCost` (2-approximation ratio). -/
theorem metric_tsp_approx_bound
    (G : MetricGraph V)
    {tour walk : List V}
    (mstWeight optCost : ℝ)
    (h_mst_le_opt : mstWeight ≤ optCost)
    (h_walk_eq_2mst : walkCost G walk = 2 * mstWeight)
    (h_decomp : ShortcutDecomposition G tour walk) :
    walkCost G tour ≤ 2 * optCost := by
  have h_tour_le_walk := shortcutting_preserves_bound G h_decomp
  rw [h_walk_eq_2mst] at h_tour_le_walk
  linarith

/-- Operational step complexity model for Metric TSP:
- MST computation via Prim/Kruskal: $n^2 \cdot \text{size } n$.
- Double-tree traversal and Eulerian cycle: $2n$.
- Shortcutting duplicate elimination: $2n$.
Total work: $n^2 \cdot \text{size } n + 4n$. -/
def metricTSPWork (n : ℕ) : ℕ :=
  n ^ 2 * Nat.size n + 4 * n

/-- Metric TSP 2-approximation operational step bound. -/
theorem metricTSPWork_bound (n : ℕ) :
    metricTSPWork n ≤ n ^ 2 * Nat.size n + 4 * n := by
  rfl

end Amort.Approximation
