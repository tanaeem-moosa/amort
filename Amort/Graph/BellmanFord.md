# Bellman-Ford Single-Source Shortest Paths

This document details the Lean 4 formalization of the textbook Bellman-Ford shortest paths
algorithm in `Amort.Graph.BellmanFord`, establishing its pass-based edge relaxation
architecture with integer edge weights `ℤ`, operational step counting showing that
$(n - 1) \cdot |E| \le n \cdot |E|$ edge relaxations are executed ($O(|V| \cdot |E|)$),
and proving shortest-path distance optimality.

---

## 1. Graph & Edge Relaxation Model

A directed graph is represented by an explicit list of edges `edges : List (Edge n)`
with weights in `ℤ`:

```lean
structure Edge (n : ℕ) where
  u : Fin n
  v : Fin n
  w : ℤ
deriving DecidableEq, Repr
```

Single-source distances from source $s$ are initialized to $0$ at $s$ and $\top$ elsewhere:

```lean
def initDist {n : ℕ} (s : Fin n) : Fin n → WithTop ℤ :=
  fun v ↦ if v = s then (0 : WithTop ℤ) else ⊤
```

A single edge $e = (u, v, w)$ is relaxed via:

```lean
def relaxEdge (dist : Fin n → WithTop ℤ) (e : Edge n) : Fin n → WithTop ℤ :=
  fun x ↦ if x = e.v then min (dist e.v) (dist e.u + (e.w : WithTop ℤ)) else dist x
```

A pass relaxes all edges in the list sequentially:

```lean
def relaxAll (edges : List (Edge n)) (dist : Fin n → WithTop ℤ) : Fin n → WithTop ℤ :=
  edges.foldl relaxEdge dist
```

Bellman-Ford executes $(n - 1)$ sequential relaxation passes:

```lean
def bellmanFord (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Fin n → WithTop ℤ :=
  bellmanFordPasses edges (initDist s) (n - 1)
```

---

## 2. Invariants & Mathematical Properties

1. **Monotonicity**:
   Relaxation never increases distance estimates:
   ```lean
   theorem relaxEdge_mono (dist : Fin n → WithTop ℤ) (e : Edge n) (v : Fin n) :
       relaxEdge dist e v ≤ dist v

   theorem relaxAll_mono (edges : List (Edge n)) (dist : Fin n → WithTop ℤ) (v : Fin n) :
       relaxAll edges dist v ≤ dist v

   theorem bellmanFordPasses_mono (edges : List (Edge n)) (dist : Fin n → WithTop ℤ)
       (k : ℕ) (v : Fin n) :
       bellmanFordPasses edges dist (k + 1) v ≤ bellmanFordPasses edges dist k v
   ```

2. **Source Distance Invariance**:
   The source vertex distance remains non-increasing and bounded above by 0 across all passes:
   ```lean
   theorem bellmanFordPasses_self (edges : List (Edge n)) (s : Fin n) (k : ℕ) :
       bellmanFordPasses edges (initDist s) k s ≤ 0
   ```

3. **Triangle Inequality at Fixed Points**:
   When an edge is relaxed, it satisfies the shortest-path triangle inequality:
   ```lean
   theorem relaxEdge_triangle (dist : Fin n → WithTop ℤ) (e : Edge n)
       (h_relaxed : relaxEdge dist e = dist) :
       dist e.v ≤ dist e.u + (e.w : WithTop ℤ)
   ```

---

## 3. Shortest-Path Soundness, Optimality & Negative Cycle Detection

A directed edge path from $s$ to $v$ is modeled as a list of edges:
```lean
def isEdgePath (s : Fin n) : List (Edge n) → Fin n → Prop
  | [], v => s = v
  | e :: es, v => e.u = s ∧ isEdgePath e.v es v

def edgePathWeight (p : List (Edge n)) : ℤ :=
  (p.map Edge.w).sum
```

### 3.1 Path Realizability (Soundness)
Every finite distance estimate produced by Bellman-Ford is realized by an explicit edge path
from $s$ whose weight matches the distance:

```lean
theorem bellmanFord_achieved (edges : List (Edge n)) (s v : Fin n) (d : ℤ)
    (h : bellmanFord n edges s v = d) :
    ∃ p, isEdgePath s p v ∧ (∀ e ∈ p, e ∈ edges) ∧ edgePathWeight p = d
```

### 3.2 Shortest-Path Optimality Under `NoNegCycle`
Induction on path length establishes that after $k$ passes, Bellman-Ford computes a distance
bounded above by any path of length at most $k$:

```lean
theorem bellmanFord_le_path_weight (edges : List (Edge n))
    (s v : Fin n) (p : List (Edge n))
    (h_path : isEdgePath s p v) (h_edges : ∀ e ∈ p, e ∈ edges)
    (h_len : p.length ≤ n - 1) :
    bellmanFord n edges s v ≤ ((edgePathWeight p : ℤ) : WithTop ℤ)
```

Under the independent `NoNegCycle` condition, the length bound is dropped:
```lean
def NoNegCycle (edges : List (Edge n)) : Prop :=
  ∀ (s v : Fin n) (p : List (Edge n)),
    isEdgePath s p v → (∀ e ∈ p, e ∈ edges) →
    ∃ (p' : List (Edge n)), isEdgePath s p' v ∧ (∀ e ∈ p', e ∈ edges) ∧
      p'.length ≤ n - 1 ∧ edgePathWeight p' ≤ edgePathWeight p

theorem bellmanFord_optimal (edges : List (Edge n)) (hneg : NoNegCycle edges)
    (s v : Fin n) (p : List (Edge n))
    (hpath : isEdgePath s p v) (hedges : ∀ e ∈ p, e ∈ edges) :
    bellmanFord n edges s v ≤ ((edgePathWeight p : ℤ) : WithTop ℤ)
```

### 3.3 Negative Cycle Detection ($n$-th Pass Relaxation Check)
The $n$-th pass relaxation check executes across all edges:
```lean
def canRelaxEdge (dist : Fin n → WithTop ℤ) (e : Edge n) : Bool
def hasNegCycleCheck (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Bool :=
  edges.any (canRelaxEdge (bellmanFord n edges s))
```

Equivalence theorem:
```lean
theorem hasNegCycleCheck_iff (n : ℕ) (edges : List (Edge n)) (s : Fin n) :
    hasNegCycleCheck n edges s = true ↔ HasReachableNegCycle n edges s

theorem noNegCycle_not_hasReachableNegCycle (edges : List (Edge n))
    (hneg : NoNegCycle edges) (s : Fin n) :
    ¬ HasReachableNegCycle n edges s

theorem hasReachableNegCycle_not_noNegCycle (edges : List (Edge n))
    (s : Fin n) (h : HasReachableNegCycle n edges s) :
    ¬ NoNegCycle edges
```

---

## 4. Operational Step Counting & Nested Loop Composition

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
theorem bellmanFordWithCount_snd : (bellmanFordWithCount n edges s).2 = bellmanFordStepCount n edges
```

By nested loop product composition (`Amort.Recurrence.isBigO_nested_loops_nat`),
since outer iterations $n - 1 = O(n)$ and inner iterations $m = O(m)$, the total complexity is:
$$(n - 1) \cdot m = O(n \cdot m) = O(|V| \cdot |E|)$$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$.
