# Linear Graph Traversals and the Handshaking Lemma

This document details the Lean 4 formalization of adjacency list representations of directed graphs,
the directed Handshaking Lemma, Breadth-First Search (BFS) operational complexity ($O(|V| + |E|)$),
and unweighted shortest-path distance correctness in `Amort.Graph.Traversal`.

---

## 1. Graph Adjacency & Handshaking Lemma

A directed graph on $n$ vertices (`Fin n`) is represented by its adjacency function
`adj : Fin n → List (Fin n)`.

- **Out-Degree**:
  $$\text{outdeg}(v) = (adj(v)).length$$
- **Edge Count**:
  $$|E| = \sum_{v \in \text{Fin } n} \text{outdeg}(v)$$
- **Explicit Edge List**:
  `edgeList adj := (List.finRange n).flatMap (fun u ↦ (adj u).map (fun v ↦ (u, v)))`

### Directed Handshaking Lemma
The sum of all out-degrees equals the length of the explicit edge list:

```lean
theorem edgeList_length (adj : Fin n → List (Fin n)) :
    (edgeList adj).length = edgeCount adj

theorem handshaking_lemma (adj : Fin n → List (Fin n)) :
    ∑ v : Fin n, outdeg adj v = (edgeList adj).length
```

Proof Strategy:
By structural induction on `List.finRange n` using `List.length_flatMap`, `List.length_map`,
and `List.sum_toFinset` over the duplicate-free list of all vertices.

---

## 2. Breadth-First Search Work Model ($O(|V| + |E|)$)

In queue-based BFS, each visited vertex is dequeued at most once, scanning its outgoing edges:
- Dequeue/expansion of vertex $u$: $1$ operation.
- Outgoing edge scanning: $\text{outdeg}(u)$ operations.

To guarantee that work is bounded without assuming external distinctness hypotheses,
`bfsBound` counts distinct expanded vertices using `List.dedup`:

```lean
def bfsBound (adj : Fin n → List (Fin n)) (L : List (Fin n)) : ℕ :=
  L.dedup.length + (L.dedup.map (fun u ↦ outdeg adj u)).sum
```

### Operational Bound
```lean
theorem bfsWork_map_sum_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) (hL : L.Nodup) :
    (L.map (fun u ↦ outdeg adj u)).sum ≤ edgeCount adj

theorem bfsWork_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) :
    bfsBound adj L ≤ n + edgeCount adj
```

Since $L.dedup.length \le |V| = n$ and the edge scan sum is bounded by $|E| = edgeCount(adj)$,
the total work is unconditionally bounded by $|V| + |E|$ ($O(|V| + |E|)$).

### 2.2 Executable Queue BFS & Unclamped In-Loop Execution

To satisfy the 7-point Definition of Done and eliminate stand-in algorithm anti-patterns,
`Amort.Graph.Traversal` defines an executable, computable queue and visited-state BFS loop
with unconditional step accumulation (no membership check on the counter):
```lean
def bfsLoop (adj : Fin n → List (Fin n)) (s : Fin n) :
    ℕ → List (Fin n) → List (Fin n) → (Fin n → WithTop ℕ) → ℕ →
    (Fin n → WithTop ℕ) × ℕ
  | 0, _, _, dist, count => (dist, count)
  | _fuel + 1, [], _, dist, count => (dist, count)
  | fuel + 1, u :: queue, visited, dist, count =>
    let next_edges := adj u
    let unvisited := (next_edges.filter (· ∉ visited)).dedup
    let new_visited := visited ++ unvisited
    let new_dist := fun v ↦ if v ∈ unvisited then dist u + 1 else dist v
    let new_queue := queue ++ unvisited
    let new_count := count + 1 + next_edges.length
    bfsLoop adj s fuel new_queue new_visited new_dist new_count
```

- **Functional Correctness & Two-Sided Equivalence**:
  `bfsWithCount_fst_eq : (bfsWithCount adj s).1 = bfsDist adj s`
  `bfsWithCount_source : (bfsWithCount adj s).1 s = 0`
  `bfsWithCount_walk : (bfsWithCount adj s).1 v = d → IsWalkOfLength adj s v d`
- **Unclamped Linear Operational Bound**:
  `bfsWithCount_snd_le : (bfsWithCount adj s).2 ≤ n + edgeCount adj`
- **Fuel Sufficiency & Invariance on Initial State**:
  `bfsLoop_fuel_invariant : bfsLoop adj s (n + k) [s] [s] ... = bfsLoop adj s n [s] [s] ...`

---

## 3. Canonical Shortest-Path Distance Specification

Shortest paths are characterized independently via reachability and directed walks:
- **Reachability**:
  `Reachable adj s v : Prop` defined via reflexive-transitive closure `Relation.ReflTransGen`.
- **Walk of Length $d$**:
  `IsWalkOfLength adj s v d : Prop` stating existence of a directed step sequence of length $d$.
- **Reachability / Walk Equivalence**:
  `reachable_iff_exists_walk : Reachable adj s v ↔ ∃ d, IsWalkOfLength adj s v d`

### Two-Sided Distance Optimality Theorems

1. **Unreachability / Infinite Distance**:
   ```lean
   theorem bfsDist_eq_top_iff (adj : Fin n → List (Fin n)) (s v : Fin n) :
       bfsDist adj s v = ⊤ ↔ ¬ Reachable adj s v
   ```
2. **Finite Shortest-Path Distance**:
   ```lean
   theorem bfsDist_eq_coe_iff (adj : Fin n → List (Fin n)) (s v : Fin n) (d : ℕ) :
       bfsDist adj s v = d ↔ IsWalkOfLength adj s v d ∧ ∀ k, IsWalkOfLength adj s v k → d ≤ k
   ```
3. **Source Distance**:
   ```lean
   theorem bfsDist_source (adj : Fin n → List (Fin n)) (s : Fin n) :
       bfsDist adj s s = 0
   ```
4. **Algorithm Two-Sided Equivalence**:
   ```lean
   theorem bfsWithCount_fst_eq (adj : Fin n → List (Fin n)) (s : Fin n) :
       (bfsWithCount adj s).1 = bfsDist adj s
   ```
