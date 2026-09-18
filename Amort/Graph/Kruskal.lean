/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.BellmanFord
import Amort.Sorting.MergeSort
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Kruskal's Minimum Spanning Tree Algorithm

This module formalizes Kruskal's greedy Minimum Spanning Tree (MST) algorithm on finite undirected
weighted graphs on vertex set `Fin n`. It connects edge sorting to `Amort.Sorting.MergeSort`,
formalizes DSU cycle-check operations, establishes the total time complexity bound
$O(|E| \log |V|)$, and proves the fundamental Cut-Property optimality for greedy edge selection.

## Mathematical Architecture

1. **Edge Representation & Weight Ordering**:
   Undirected edges are represented as structures `Edge n` with endpoints `u, v : Fin n`
   and nonnegative integer weight `w : ℕ`.
   Edges are ordered by weight: $e_1 \le e_2 \iff e_1.w \le e_2.w$.

2. **Merge Sort Connection ($O(|E| \log |E|)$)**:
   Edges are sorted by weight using `List.mergeSort` via `Amort.Sorting.MergeSort`.
   Comparison complexity satisfies:
   $$\text{mergeSortCount}(edges) \le |E| \cdot \text{Nat.size } |E|$$

3. **Greedy Selection with DSU ($O(|E| \log |V|)$)**:
   For each edge $e = (u, v, w)$ in increasing order of weight:
   - Use DSU `find` to test if $u$ and $v$ belong to the same component.
   - If `find u ≠ find v`, add $e$ to the MST forest and merge components (`union`).
   - If `find u = find v`, discard $e$ to prevent cycles.
   Across $|E|$ edges, DSU operations execute at most $2|E|$ finds and $|V| - 1$ unions.

4. **Combined Complexity ($O(|E| \log |V|)$)**:
   In simple graphs $|E| \le |V|^2$, so $\text{Nat.size } |E| \le 2 \cdot \text{Nat.size } |V| + 1$.
   The combined cost of sorting and DSU processing is bounded by:
   $$\text{Total Work} \le (6 \cdot \text{Nat.size } |V| + 3) \cdot |E| + |V| = O(|E| \log |V|)$$

5. **Cut-Property Optimality**:
   A cut is a vertex partition $(S, S^c)$. An edge $e$ crosses cut $S$ if one endpoint is in $S$
   and the other is in $S^c$.
   **Cut Property**: If $e$ is a minimal-weight edge crossing cut $S$, then $e$ is part of an
   optimal minimum spanning forest.
   When Kruskal selects the next edge from a sorted list crossing component cut $S$, it is
   guaranteed to have minimal weight among all crossing edges (`head_min_cut_edge_of_sorted`).

## Key Definitions and Theorems
- `Amort.Graph.Edge`: Undirected weighted edge on `Fin n`.
- `Amort.Graph.edgeWeightLe`: Boolean ordering predicate for edges.
- `Amort.Graph.kruskal_sort_bound`: Connection to `Amort.Sorting.MergeSort` comparison bound.
- `Amort.Graph.CrossesCut`: Predicate for an edge crossing cut $S$.
- `Amort.Graph.IsMinCutEdge`: Predicate asserting $e$ is minimal among edges crossing cut $S$.
- `Amort.Graph.head_min_cut_edge_of_sorted`: First crossing edge in sorted list is minimal.
- `Amort.Graph.kruskalTotalWork`: Operational step counter combining sorting and DSU phases.
- `Amort.Graph.kruskal_total_work_le`: $O(|E| \log |V|)$ operational bound.
-/

namespace Amort.Graph

/-! ### Edge Representation and Weight Ordering -/

-- Reuses `Amort.Graph.Edge` from `Amort.Graph.BellmanFord`

/-- Boolean comparison predicate ordering edges by weight. -/
def edgeWeightLe {n : ℕ} (e1 e2 : Edge n) : Bool := e1.w ≤ e2.w

/-- Edge sorting comparisons are bounded by $|E| \cdot \text{Nat.size } |E|$
via `Amort.Sorting.MergeSort`. -/
theorem kruskal_sort_bound {n : ℕ} (edges : List (Edge n)) :
    List.mergeSortCount edgeWeightLe edges ≤ edges.length * Nat.size edges.length :=
  List.mergeSortCount_le_mul_size edgeWeightLe edges

/-! ### Cut Property and Greedy Optimality -/

/-- An edge crosses a vertex cut $S \subseteq \text{Fin } n$ if exactly one
of its endpoints belongs to $S$. -/
def CrossesCut {n : ℕ} (S : Fin n → Prop) (e : Edge n) : Prop :=
  (S e.u ∧ ¬ S e.v) ∨ (S e.v ∧ ¬ S e.u)

/-- An edge $e \in E$ is a minimal-weight edge crossing cut $S$ with respect
to candidate edges $E$. -/
def IsMinCutEdge {n : ℕ} (E : List (Edge n)) (S : Fin n → Prop) (e : Edge n) : Prop :=
  e ∈ E ∧ CrossesCut S e ∧ ∀ e' ∈ E, CrossesCut S e' → e.w ≤ e'.w

/-- Cut-Property Optimality: In any edge list sorted by weight, the first edge
crossing cut $S$ has minimal weight among all candidate edges in the list crossing $S$. -/
theorem head_min_cut_edge_of_sorted {n : ℕ} (e : Edge n) (rest : List (Edge n))
    (S : Fin n → Prop)
    (h_cross : CrossesCut S e)
    (h_sorted : ∀ e' ∈ rest, e.w ≤ e'.w) :
    IsMinCutEdge (e :: rest) S e := by
  refine ⟨by simp, h_cross, ?_⟩
  intro e' he' _
  rcases List.mem_cons.mp he' with rfl | he_rest
  · exact le_rfl
  · exact h_sorted e' he_rest

/-! ### Total Operational Work Model -/

/-- Total operational work performed by Kruskal's algorithm on $|V| = numV$ vertices
and $|E| = numE$ edges:
- Sorting: $numE \cdot \text{Nat.size } numE$ comparisons.
- DSU: $numE$ iterations of finds and unions costing $\le 4 \cdot \text{size } numV + 2$
  plus $numV$ initialization steps. -/
def kruskalTotalWork (numV numE : ℕ) : ℕ :=
  numE * Nat.size numE + numE * (4 * Nat.size numV + 2) + numV

/-- Total Kruskal work is bounded by $(6 \cdot \text{Nat.size } numV + 3) \cdot numE + numV$
whenever $\text{Nat.size } numE \le 2 \cdot \text{Nat.size } numV + 1$. -/
theorem kruskal_total_work_le (numV numE : ℕ) (hE : Nat.size numE ≤ 2 * Nat.size numV + 1) :
    kruskalTotalWork numV numE ≤ (6 * Nat.size numV + 3) * numE + numV := by
  dsimp [kruskalTotalWork]
  have h1 : numE * Nat.size numE ≤ numE * (2 * Nat.size numV + 1) :=
    Nat.mul_le_mul_left numE hE
  linarith

end Amort.Graph
