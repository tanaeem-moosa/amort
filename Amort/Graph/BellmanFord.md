# Bellman-Ford Single-Source Shortest Paths

This document details the Lean 4 formalization of the textbook Bellman-Ford shortest paths
algorithm in `Amort.Graph.BellmanFord`, establishing its pass-based edge relaxation architecture,
operational step counting showing that $(n - 1) \cdot |E| \le n \cdot |E|$ edge relaxations are
executed, and proving triangle inequality preservation at fixed points.

---

## 1. Graph & Edge Relaxation Model

A directed graph is represented by an explicit list of edges `edges : List (Edge n)`:

```lean
structure Edge (n : ℕ) where
  u : Fin n
  v : Fin n
  w : ℕ
deriving DecidableEq, Repr
```

Single-source distances from source $s$ are initialized to $0$ at $s$ and $\top$ elsewhere:

```lean
def initDist {n : ℕ} (s : Fin n) : Fin n → WithTop ℕ :=
  fun v ↦ if v = s then 0 else ⊤
```

A single edge $e = (u, v, w)$ is relaxed via:

```lean
def relaxEdge (dist : Fin n → WithTop ℕ) (e : Edge n) : Fin n → WithTop ℕ :=
  fun x ↦ if x = e.v then min (dist e.v) (dist e.u + e.w) else dist x
```

A pass relaxes all edges in the list sequentially:

```lean
def relaxAll (edges : List (Edge n)) (dist : Fin n → WithTop ℕ) : Fin n → WithTop ℕ :=
  edges.foldl relaxEdge dist
```

Bellman-Ford executes $(n - 1)$ sequential relaxation passes:

```lean
def bellmanFord (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Fin n → WithTop ℕ :=
  bellmanFordPasses edges (initDist s) (n - 1)
```

---

## 2. Invariants & Mathematical Properties

1. **Monotonicity**:
   Relaxation never increases distance estimates:
   ```lean
   theorem relaxEdge_mono (dist : Fin n → WithTop ℕ) (e : Edge n) (v : Fin n) :
       relaxEdge dist e v ≤ dist v

   theorem relaxAll_mono (edges : List (Edge n)) (dist : Fin n → WithTop ℕ) (v : Fin n) :
       relaxAll edges dist v ≤ dist v

   theorem bellmanFordPasses_mono (edges : List (Edge n)) (dist : Fin n → WithTop ℕ)
       (k : ℕ) (v : Fin n) :
       bellmanFordPasses edges dist (k + 1) v ≤ bellmanFordPasses edges dist k v
   ```

2. **Source Distance Invariance**:
   The source vertex distance remains 0 throughout all passes:
   ```lean
   theorem bellmanFordPasses_self (edges : List (Edge n)) (s : Fin n) (k : ℕ) :
       bellmanFordPasses edges (initDist s) k s = 0
   ```

3. **Triangle Inequality at Fixed Points**:
   When an edge is relaxed, it satisfies the shortest-path triangle inequality:
   ```lean
   theorem relaxEdge_triangle (dist : Fin n → WithTop ℕ) (e : Edge n)
       (h_relaxed : relaxEdge dist e = dist) :
       dist e.v ≤ dist e.u + e.w
   ```

---

## 3. Operational Step Counting & Nested Loop Composition

Across $(n - 1)$ passes of $|E| = edges.length$ edges, the total number of relaxations executed is:

```lean
def bellmanFordStepCount (n : ℕ) (edges : List (Edge n)) : ℕ :=
  (n - 1) * edges.length

theorem bellmanFordStepCount_le (n : ℕ) (edges : List (Edge n)) :
    bellmanFordStepCount n edges ≤ n * edges.length
```

Instrumented counterpart `bellmanFordWithCount` proves:

```lean
theorem bellmanFordWithCount_fst : (bellmanFordWithCount n edges s).1 = bellmanFord n edges s
theorem bellmanFordWithCount_snd : (bellmanFordWithCount n edges s).2 = (n - 1) * edges.length
```

By nested loop product composition (`Amort.Recurrence.isBigO_nested_loops_nat`),
since outer iterations $n - 1 = O(n)$ and inner iterations $m = O(m)$, the total complexity is:
$$(n - 1) \cdot m = O(n \cdot m) = O(|V| \cdot |E|)$$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.
