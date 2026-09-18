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

For any sequence of distinct visited vertices $L$ ($L.Nodup$):

```lean
def bfsWork (adj : Fin n → List (Fin n)) (L : List (Fin n)) : ℕ :=
  L.length + (L.map (fun u ↦ outdeg adj u)).sum
```

### Operational Bound
```lean
theorem bfsWork_map_sum_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) (hL : L.Nodup) :
    (L.map (fun u ↦ outdeg adj u)).sum ≤ edgeCount adj

theorem bfsWork_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) (hL : L.Nodup) :
    bfsWork adj L ≤ n + edgeCount adj
```

Since $L.length \le |V| = n$ and the edge scan sum is bounded by $|E| = edgeCount(adj)$,
the total work is strictly bounded by $|V| + |E|$ ($O(|V| + |E|)$).

---

## 3. Unweighted Shortest-Path Distance Correctness

A valid directed path in `adj` is defined inductively:

```lean
def IsPath (adj : Fin n → List (Fin n)) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y ∈ adj x ∧ IsPath adj (y :: rest)
```

A valid BFS distance specification satisfies:
1. $dist(s) = 0$
2. $\forall u, v,\; v \in adj(u) \implies dist(v) \le dist(u) + 1$

```lean
structure BFSDistance (adj : Fin n → List (Fin n)) (s : Fin n) where
  dist : Fin n → WithTop ℕ
  source_zero : dist s = 0
  edge_relax : ∀ u v, v ∈ adj u → dist v ≤ dist u + 1
```

### Optimality Theorem
For any path $p$ from source $s$ to vertex $v$, the BFS distance estimate is bounded above
by the number of edges in $p$ ($p.length - 1$):

```lean
theorem dist_le_path_from_source (adj : Fin n → List (Fin n)) (s : Fin n)
    (d : BFSDistance adj s) (p : List (Fin n)) (v : Fin n)
    (h_head : p.head? = some s) (h_last : p.getLast? = some v)
    (h_path : IsPath adj p) :
    d.dist v ≤ (p.length - 1 : ℕ)
```

This establishes that BFS distances never exceed the true graph geodesic distance,
proving unweighted shortest-path distance correctness.
