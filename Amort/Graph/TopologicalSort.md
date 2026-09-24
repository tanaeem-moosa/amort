# Topological Sort and Kahn's Algorithm

> **Status: stub — not verified** (Phase 3 canon stub; topological order acyclicity is
> proven, but Kahn queue algorithm execution is a specification stub).


This document details the Lean 4 formalization of Kahn's in-degree zero algorithm for topological
sorting of directed graphs in `Amort.Graph.TopologicalSort`, establishing its $O(|V| + |E|)$
operational step bound and proving topological sort correctness and cycle-freedom (DAG property).

---

## 1. Kahn's Algorithm Work Model ($O(|V| + |E|)$)

Kahn's algorithm maintains a queue of vertices whose in-degree in the remaining graph has reached 0.
When vertex $u$ is processed:
- Outputting $u$: $1$ operation.
- Scanning out-edges and decrementing neighbors' in-degrees: $\text{outdeg}(u)$ operations.

For any ordered sequence $L$ of distinct vertices processed ($L.Nodup$):

```lean
def kahnWork (adj : Fin n → List (Fin n)) (L : List (Fin n)) : ℕ :=
  bfsWork adj L

theorem kahnWork_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) (hL : L.Nodup) :
    kahnWork adj L ≤ n + edgeCount adj
```

Because each vertex enters and leaves the zero-in-degree queue at most once ($L.Nodup$),
the total work is strictly bounded by $|V| + |E|$.

---

## 2. Topological Sort Correctness

A list $L$ of vertices is a valid topological sort if:
1. $L$ contains no duplicates ($L.Nodup$).
2. $L$ contains all $n$ vertices ($L.length = n$).
3. For every directed edge $u \to v$ ($v \in adj(u)$), $u$ precedes $v$ in $L$:

```lean
def IsTopologicalSort (adj : Fin n → List (Fin n)) (L : List (Fin n)) : Prop :=
  L.Nodup ∧ L.length = n ∧ ∀ u v, v ∈ adj u → List.idxOf u L < List.idxOf v L
```

### Invariant Theorems
From this characterization, the following structural theorems are proven:

1. **No Backward Edges**:
   ```lean
   theorem toposort_no_backward_edge (adj : Fin n → List (Fin n)) (L : List (Fin n))
       (h_topo : IsTopologicalSort adj L) (u v : Fin n) (h_edge : v ∈ adj u) :
       ¬ (List.idxOf v L ≤ List.idxOf u L)
   ```

2. **No Self-Loops**:
   ```lean
   theorem toposort_no_self_loop (adj : Fin n → List (Fin n)) (L : List (Fin n))
       (h_topo : IsTopologicalSort adj L) (u : Fin n) :
       u ∉ adj u
   ```

3. **No 2-Cycles**:
   ```lean
   theorem toposort_no_two_cycle (adj : Fin n → List (Fin n)) (L : List (Fin n))
       (h_topo : IsTopologicalSort adj L) (u v : Fin n)
       (h_uv : v ∈ adj u) (h_vu : u ∈ adj v) : False
   ```

---

## 3. General Cycle Freedom (DAG Property)

A directed cycle is defined as a path of length $\ge 2$ whose starting and ending vertices coincide:

```lean
def IsCycle (adj : Fin n → List (Fin n)) (p : List (Fin n)) : Prop :=
  2 ≤ p.length ∧ p.head? = p.getLast? ∧ IsPath adj p
```

### Monotonic Index Progression
Along any directed path in a topologically sorted graph, vertex positions strictly increase:

```lean
lemma path_idx_lt (adj : Fin n → List (Fin n)) (L : List (Fin n))
    (h_topo : IsTopologicalSort adj L) :
    ∀ (p : List (Fin n)) (u v : Fin n),
      2 ≤ p.length → p.head? = some u → p.getLast? = some v → IsPath adj p →
      List.idxOf u L < List.idxOf v L
```

### Cycle Freedom Theorem
```lean
theorem toposort_no_cycle (adj : Fin n → List (Fin n)) (L : List (Fin n))
    (h_topo : IsTopologicalSort adj L) (p : List (Fin n))
    (h_cycle : IsCycle adj p) : False
```

Proof Strategy:
If a cycle $p$ starting and ending at vertex $x$ existed, `path_idx_lt` would imply
`List.idxOf x L < List.idxOf x L`, an immediate arithmetic contradiction.
Thus, any graph admitting a topological sort is strictly a Directed Acyclic Graph (DAG).
