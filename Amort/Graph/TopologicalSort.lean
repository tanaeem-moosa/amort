/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Traversal

/-!
# Topological Sort and Kahn's Algorithm

> **Status: stub — not verified** (Phase 3 canon stub; topological order acyclicity is
> proven, but Kahn queue algorithm execution is a specification stub).

This module formalizes Kahn's queue-based in-degree zero algorithm for topological sorting of
directed graphs on vertex set `Fin n`. It establishes the operational work bound
$\text{Work} \le |V| + |E|$ ($O(|V| + |E|)$) and proves mathematical correctness: any valid
topological sort strictly orders all directed edges forward and guarantees that the graph
contains no directed cycles (is a Directed Acyclic Graph, or DAG).

## Mathematical Architecture

1. **Kahn's Algorithm Work Model**:
   Kahn's algorithm maintains vertices with remaining in-degree zero in a queue.
   For each dequeued vertex $u$:
   - 1 step for outputting / dequeuing $u$.
   - $\text{outdeg}(u)$ steps for scanning outgoing edges and decrementing neighbors' in-degrees.
   Across any sequence of distinct visited vertices $L$ ($L.Nodup$):
   $$\text{kahnBound}(L) = |L| + \sum_{u \in L} \text{outdeg}(u) \le |V| + |E|$$

2. **Topological Sort Correctness**:
   A permutation $L$ of `Fin n` is a valid topological sort (`IsTopologicalSort`) if:
   - $L.Nodup \wedge L.length = n$
   - $\forall u, v,\; v \in adj(u) \implies \text{idxOf}(u, L) < \text{idxOf}(v, L)$
   From this definition, we prove that:
   - No backward edges can exist.
   - No self-loops $u \in adj(u)$ can exist.
   - No 2-cycles $u \to v \to u$ can exist.
   - No directed cycles of any length $\ge 2$ can exist (`toposort_no_cycle`).

## Key Definitions and Theorems
- `Amort.Graph.kahnBound`: Total work performed across vertex list $L$.
- `Amort.Graph.kahnWork_le`: Total Kahn work bounded by $|V| + |E|$.
- `Amort.Graph.IsTopologicalSort`: Correctness predicate for topological ordering.
- `Amort.Graph.toposort_no_backward_edge`: Forbids backward edges.
- `Amort.Graph.toposort_no_self_loop`: Forbids self-loops.
- `Amort.Graph.toposort_no_two_cycle`: Forbids 2-cycles.
- `Amort.Graph.toposort_no_cycle`: Forbids directed cycles of any length (DAG property).
-/

open BigOperators

namespace Amort.Graph

variable {n : ℕ}

/-! ### Kahn's Algorithm Work Model -/

/-- Work performed by Kahn's algorithm processing vertex sequence `L`:
1 step per dequeued vertex plus `outdeg u` steps to decrement neighbors' in-degrees. -/
def kahnBound (adj : Fin n → List (Fin n)) (L : List (Fin n)) : ℕ :=
  bfsBound adj L

/-- Kahn's algorithm total work on any distinct sequence of vertices is bounded by `|V| + |E|`. -/
theorem kahnWork_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) (_hL : L.Nodup) :
    kahnBound adj L ≤ n + edgeCount adj :=
  bfsWork_le adj L

/-! ### Topological Sort Definition and Correctness -/

/-- A permutation `L` of `Fin n` is a valid topological sort of `adj` if
for every directed edge `u → v`, `u` precedes `v` in `L`. -/
def IsTopologicalSort (adj : Fin n → List (Fin n)) (L : List (Fin n)) : Prop :=
  L.Nodup ∧ L.length = n ∧ ∀ u v, v ∈ adj u → List.idxOf u L < List.idxOf v L

/-- If `L` is a valid topological sort, no edge can go backward. -/
theorem toposort_no_backward_edge (adj : Fin n → List (Fin n)) (L : List (Fin n))
    (h_topo : IsTopologicalSort adj L) (u v : Fin n) (h_edge : v ∈ adj u) :
    ¬ (List.idxOf v L ≤ List.idxOf u L) := by
  have h_lt := h_topo.2.2 u v h_edge
  omega

/-- If `L` is a valid topological sort, the graph cannot have self-loops `u ∈ adj u`. -/
theorem toposort_no_self_loop (adj : Fin n → List (Fin n)) (L : List (Fin n))
    (h_topo : IsTopologicalSort adj L) (u : Fin n) :
    u ∉ adj u := by
  intro h_edge
  have h_lt := h_topo.2.2 u u h_edge
  omega

/-- If `L` is a valid topological sort, no 2-cycles `u → v → u` can exist. -/
theorem toposort_no_two_cycle (adj : Fin n → List (Fin n)) (L : List (Fin n))
    (h_topo : IsTopologicalSort adj L) (u v : Fin n)
    (h_uv : v ∈ adj u) (h_vu : u ∈ adj v) : False := by
  have h1 := h_topo.2.2 u v h_uv
  have h2 := h_topo.2.2 v u h_vu
  omega

/-! ### Cycle Freedom (DAG Property) -/

/-- Index strictly increases along any non-trivial path in a topologically sorted graph. -/
lemma path_idx_lt (adj : Fin n → List (Fin n)) (L : List (Fin n))
    (h_topo : IsTopologicalSort adj L) :
    ∀ (p : List (Fin n)) (u v : Fin n),
      2 ≤ p.length → p.head? = some u → p.getLast? = some v → IsPath adj p →
      List.idxOf u L < List.idxOf v L
  | [], _, _, hlen, _, _, _ => by contradiction
  | [_], _, _, hlen, _, _, _ => by simp at hlen
  | [x, y], u, v, _, hhead, hlast, hpath => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    simp only [List.getLast?_cons, Option.some.injEq] at hlast
    subst hhead hlast
    exact h_topo.2.2 x y hpath.1
  | x :: y :: z :: rest, u, v, _, hhead, hlast, hpath => by
    simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    have h_edge : y ∈ adj x := hpath.1
    have h_lt1 := h_topo.2.2 x y h_edge
    have h_len : 2 ≤ (y :: z :: rest).length := by simp
    have ih := path_idx_lt adj L h_topo (y :: z :: rest) y v h_len rfl hlast hpath.2
    exact lt_trans h_lt1 ih

/-- A directed cycle is a path of length at least 2 whose first and last vertices coincide. -/
def IsCycle (adj : Fin n → List (Fin n)) (p : List (Fin n)) : Prop :=
  2 ≤ p.length ∧ p.head? = p.getLast? ∧ IsPath adj p

/-- Fundamental Theorem: Any graph admitting a topological sort contains no directed cycles. -/
theorem toposort_no_cycle (adj : Fin n → List (Fin n)) (L : List (Fin n))
    (h_topo : IsTopologicalSort adj L) (p : List (Fin n))
    (h_cycle : IsCycle adj p) : False := by
  rcases p with _ | ⟨x, rest⟩
  · simp [IsCycle] at h_cycle
  · have h_head : (x :: rest).head? = some x := rfl
    have h_last : (x :: rest).getLast? = some x := by
      have := h_cycle.2.1
      rw [h_head] at this
      exact this.symm
    have h_lt := path_idx_lt adj L h_topo (x :: rest) x x h_cycle.1 h_head h_last h_cycle.2.2
    omega

end Amort.Graph
