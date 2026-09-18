# Textbook Graph Algorithms in Lean 4

This document synthesizes the formalization of classical graph algorithms in `Amort.Graph`,
spanning shortest paths, linear traversals, amortized data structures, and minimum spanning trees:
1. **Graph Dynamic Programming & Shortest Paths**:
   - Floyd-Warshall: 3D dynamic programming ($O(n^3)$ via `Amort.Recurrence.DP`).
   - Bellman-Ford: Single-source shortest paths via $(n - 1)$ relaxation rounds ($O(|V| \cdot |E|)$ via loop composition).
2. **Foundational Linear Traversals**:
   - Directed Handshaking Lemma: $\sum_{v \in V} \text{outdeg}(v) = |E|$.
   - Breadth-First Search (BFS): Queue traversal ($O(|V| + |E|)$) and unweighted shortest-path distance correctness.
   - Topological Sort: Kahn's in-degree zero queue algorithm ($O(|V| + |E|)$) and DAG cycle-freedom correctness.
3. **Amortized Data Structures & MST**:
   - Disjoint Set Union (DSU): Union-by-rank, exponential subtree size $2^{\text{rank}} \le n$, logarithmic depth and find bounds ($O((n + m) \log n)$).
   - Kruskal's MST Algorithm: Edge sorting via `Amort.Sorting.MergeSort`, DSU cycle checking ($O(|E| \log |V|)$), and greedy Cut-Property optimality.
4. **Asymptotic Complexity Bridges**:
   - Direct bridges connecting all operational bounds to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.

All proofs rely exclusively on standard foundational Lean 4 axioms with zero reliance on `sorryAx`.

---

## 1. Architectural Overview

```
Amort/
├── Amort.lean                  -- Library root re-exporting all modules
├── Sorting/
│   └── MergeSort.lean          -- Merge sort and comparison counting (used by Kruskal)
├── Recurrence/
│   ├── DP.lean                 -- State-space DPModel and asymptotic bridges
│   └── Composition.lean        -- Compositional complexity algebra (nested loops, sums)
└── Graph/
    ├── FloydWarshall.lean      -- 3D DP all-pairs shortest paths (O(n^3))
    ├── BellmanFord.lean        -- Single-source shortest paths (O(|V| * |E|))
    ├── Traversal.lean          -- Handshaking Lemma and BFS traversal (O(|V| + |E|))
    ├── TopologicalSort.lean    -- Kahn's algorithm and DAG cycle freedom (O(|V| + |E|))
    ├── DSU.lean                -- Disjoint Set Union with union-by-rank (O((n + m) log n))
    ├── Kruskal.lean            -- Kruskal's MST and Cut-Property optimality (O(|E| log |V|))
    ├── Asymptotics.lean        -- Unified Mathlib IsBigO asymptotic theorems
    ├── FloydWarshall.md        -- Floyd-Warshall documentation & proof notes
    ├── BellmanFord.md          -- Bellman-Ford documentation & proof notes
    ├── Traversal.md            -- Traversal & Handshaking documentation
    ├── TopologicalSort.md      -- Topological Sort documentation & proof notes
    ├── DSU.md                  -- DSU documentation & proof notes
    ├── Kruskal.md              -- Kruskal documentation & proof notes
    └── Graph.md                -- Architecture synthesis and comparison
```

---

## 2. Algorithm Summary and Complexity Matrix

| Algorithm | Paradigm | State / Data Representation | Operational Work Bound | Mathlib `IsBigO` Bound |
| :--- | :--- | :--- | :--- | :--- |
| **Floyd-Warshall** | 3D Dynamic Programming | `Fin (n + 1) × Fin n × Fin n` | $(n + 1) \cdot n^2 \le (n + 1)^3$ | $O(n^3)$ |
| **Bellman-Ford** | Edge Relaxation Passes | `edges : List (Edge n)` | $(n - 1) \cdot \|E\| \le n \cdot \|E\|$ | $O(\|V\| \cdot \|E\|)$ |
| **BFS Traversal** | Queue-Based Search | `adj : Fin n → List (Fin n)` | $|V| + \sum \text{outdeg}(u) \le \|V\| + \|E\|$ | $O(\|V\| + \|E\|)$ |
| **Topological Sort** | Zero In-Degree Queue | In-degree array & Queue | $|V| + \sum \text{outdeg}(u) \le \|V\| + \|E\|$ | $O(\|V\| + \|E\|)$ |
| **Disjoint Set Union** | Tree Union-by-Rank | `parent : Fin n → Fin n`, `rank` | $m(2 \cdot \text{size } n + 1) + n$ | $O((n + m) \log n)$ |
| **Kruskal's MST** | Greedy + DSU | Edge list + MergeSort + DSU | $(6 \cdot \text{size } \|V\| + 3)\|E\| + \|V\|$ | $O(\|E\| \log \|V\|)$ |

---

## 3. Mathematical Highlights

### 3.1 Handshaking Lemma
For any directed graph on $n$ vertices (`Fin n`), the sum of out-degrees equals the length of the explicit edge list:
$$\sum_{v \in \text{Fin } n} \text{outdeg}(v) = (edgeList adj).length = |E|$$
proven by induction over `List.finRange n` using `List.sum_toFinset`.

### 3.2 Floyd-Warshall 3D Dynamic Programming
Instantiates `Amort.Recurrence.DPModel` on `FWState n := Fin (n + 1) × Fin n × Fin n` with unit transition cost $C = 1$:
$$\text{Total Work} \le |FWState n| \cdot 1 = (n + 1) \cdot n^2 \le (n + 1)^3$$

### 3.3 Bellman-Ford Loop Product Composition
Nested loops of $(n - 1)$ outer passes and $|E|$ inner relaxations:
$$(n - 1) = O(n) \quad \text{and} \quad |E| = O(|E|) \implies (n - 1) \cdot |E| = O(n \cdot |E|)$$
connecting directly to `Amort.Recurrence.Composition.isBigO_nested_loops_nat`.

### 3.4 Disjoint Set Union Exponential Subtree Size
For every root $r$ in union-by-rank:
$$2^{\text{rank}(r)} \le \text{treeSize}(r) \le n \implies \text{rank}(r) \le \log_2 n \le \text{Nat.size } n$$
Consequently, every path followed during `find` executes at most $\text{Nat.size } n$ pointer dereferences.

### 3.5 Kruskal's Cut-Property Optimality
Greedy edge addition selects edges across component cuts:
Every edge added across a cut is proven to have minimal weight among all candidate edges crossing that cut (`head_min_cut_edge_of_sorted`).
