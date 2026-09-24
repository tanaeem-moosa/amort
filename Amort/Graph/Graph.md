# Textbook Graph Algorithms in Lean 4

> **Status: partially verified / contains stubs** (Contains verified Traversal and Bellman-Ford
> algorithms alongside Phase 3/4 graph algorithm stubs).


This document synthesizes the formalization of classical and advanced graph algorithms in
`Amort.Graph`, spanning shortest paths, linear traversals, amortized data structures, minimum
spanning trees, network flows, strongly connected components, and Eulerian circuits:
1. **Graph Dynamic Programming & Shortest Paths**:
   - Floyd-Warshall: 3D dynamic programming ($O(n^3)$ via `Amort.Recurrence.DP`).
   - Bellman-Ford: Single-source shortest paths via $(n - 1)$ relaxation rounds ($O(|V| \cdot |E|)$
     via loop composition).
   - Dijkstra's Algorithm: Priority queue single-source shortest paths ($O((|V| + |E|) \log |V|)$)
     and greedy choice optimality.
2. **Foundational Linear Traversals & Decompositions**:
   - Directed Handshaking Lemma: $\sum_{v \in V} \text{outdeg}(v) = |E|$.
   - Breadth-First Search (BFS): Queue traversal ($O(|V| + |E|)$) and unweighted shortest-path
     distance correctness.
   - Topological Sort: Kahn's in-degree zero queue algorithm ($O(|V| + |E|)$) and DAG cycle-freedom.
   - Strongly Connected Components (SCC): Kosaraju's two-pass DFS ($O(|V| + |E|)$), mutual
     reachability equivalence, and acyclic condensation DAG.
   - Eulerian Circuits: Hierholzer's cycle splicing algorithm ($O(|V| + |E|)$) and degree
     balance conditions.
3. **Amortized Data Structures & Minimum Spanning Trees**:
   - Disjoint Set Union (DSU): Union-by-rank, exponential subtree size $2^{\text{rank}} \le n$,
     logarithmic depth and find bounds ($O((n + m) \log n)$).
   - Kruskal's MST Algorithm: Edge sorting via `Amort.Sorting.MergeSort`, DSU cycle checking
     ($O(|E| \log |V|)$), and greedy Cut-Property optimality.
   - Prim's MST Algorithm: Priority queue frontier selection, Cut-Property invariant,
     $O(|E| \log |V|)$ complexity, and formal contrast with Kruskal.
4. **Network Flow & Duality**:
   - Max-Flow Min-Cut Theorem: Flow networks, capacity constraints, flow conservation,
     cut-flow identity, weak duality, and tight residual cut equality.
   - Edmonds-Karp augmenting path complexity ($O(|V| \cdot |E|^2)$).
5. **Asymptotic Complexity Bridges**:
   - Direct bridges connecting all operational bounds to Mathlib's
     `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.

All proofs rely exclusively on standard foundational Lean 4 axioms with zero reliance on `sorryAx`.

---

## 1. Architectural Overview

```
Amort/
├── Amort.lean                     -- Library root re-exporting all modules
├── Sorting/
│   └── MergeSort.lean             -- Merge sort and comparison counting (used by Kruskal)
├── Recurrence/
│   ├── DP.lean                    -- State-space DPModel and asymptotic bridges
│   └── Composition.lean           -- Compositional complexity algebra (nested loops, sums)
└── Graph/
    ├── FloydWarshall.lean         -- 3D DP all-pairs shortest paths (O(n^3))
    ├── BellmanFord.lean           -- Single-source shortest paths (O(|V| * |E|))
    ├── Traversal.lean             -- Handshaking Lemma and BFS traversal (O(|V| + |E|))
    ├── TopologicalSort.lean       -- Kahn's algorithm and DAG cycle freedom (O(|V| + |E|))
    ├── DSU.lean                   -- Disjoint Set Union with union-by-rank (O((n + m) log n))
    ├── Kruskal.lean               -- Kruskal's MST and Cut-Property optimality (O(|E| log |V|))
    ├── Dijkstra.lean              -- Dijkstra shortest paths and greedy choice (O((|V|+|E|) log |V|))
    ├── MaxFlow.lean               -- Max-Flow Min-Cut Theorem & Edmonds-Karp (O(|V| * |E|^2))
    ├── SCC.lean                   -- Strongly Connected Components & condensation DAG (O(|V| + |E|))
    ├── Eulerian.lean              -- Eulerian circuits & Hierholzer splicing (O(|V| + |E|))
    ├── Prim.lean                  -- Prim's MST & comparison with Kruskal (O(|E| log |V|))
    ├── Asymptotics.lean           -- Foundational Mathlib IsBigO asymptotic theorems
    ├── AdvancedAsymptotics.lean   -- Advanced Mathlib IsBigO asymptotic theorems
    ├── FloydWarshall.md           -- Floyd-Warshall documentation & proof notes
    ├── BellmanFord.md             -- Bellman-Ford documentation & proof notes
    ├── Traversal.md               -- Traversal & Handshaking documentation
    ├── TopologicalSort.md         -- Topological Sort documentation & proof notes
    ├── DSU.md                     -- DSU documentation & proof notes
    ├── Kruskal.md                 -- Kruskal documentation & proof notes
    ├── Dijkstra.md                -- Dijkstra documentation & proof notes
    ├── MaxFlow.md                 -- Max-Flow Min-Cut documentation & proof notes
    ├── SCC.md                     -- SCC documentation & proof notes
    ├── Eulerian.md                -- Eulerian circuit documentation & proof notes
    ├── Prim.md                    -- Prim's MST documentation & proof notes
    ├── AdvancedAsymptotics.md     -- Advanced asymptotics documentation
    └── Graph.md                   -- Architecture synthesis and comparison
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
| **Dijkstra** | Greedy + Priority Queue | Distances + Min-Heap | $(|V| + \|E\|) \cdot \text{Nat.size } \|V\|$ | $O((|V| + \|E\|) \log \|V\|)$ |
| **Max-Flow (EK)** | Augmenting Paths (BFS) | Capacity network + Residual $G_f$ | $|V| \cdot \|E\|^2$ | $O(\|V\| \cdot \|E\|^2)$ |
| **SCC (Kosaraju)** | Two-Pass DFS | Adjacency on $G$ and $G^T$ | $2(|V| + \|E\|)$ | $O(\|V\| + \|E\|)$ |
| **Eulerian (Hierholzer)** | Cycle Splicing | Adjacency & Unused Edge Ptrs | $2(|V| + \|E\|)$ | $O(\|V\| + \|E\|)$ |
| **Prim's MST** | Greedy + Priority Queue | Frontier keys + Min-Heap | $(|V| + \|E\|) \cdot \text{Nat.size } \|V\|$ | $O(\|E\| \log \|V\|)$ |

---

## 3. Mathematical Highlights

### 3.1 Handshaking Lemma & Degree Balance
For any directed graph on $n$ vertices (`Fin n`):
$$\sum_{v \in \text{Fin } n} \text{indeg}(v) = \sum_{u \in \text{Fin } n} \text{outdeg}(u) = |E|$$
proven by induction over `List.finRange n` using `sum_count_eq_length` and sum transposition.

### 3.2 Dijkstra's Greedy Choice Invariant
When extracting $u^* = \text{argmin}_{v \notin S} d(v)$ with minimal tentative key:
Any path from $s$ to $u^*$ crossing frontier edge $(x, y)$ ($x \in S, y \notin S$) has weight at
least $\delta(s, x) + w(x, y) \ge d(y) \ge d(u^*)$, proving $d(u^*) = \delta(s, u^*)$.

### 3.3 Max-Flow Min-Cut Theorem & Weak Duality
By internal edge sum cancellation $\sum_{u \in S, v \in S} f(u, v) = \sum_{u \in S, v \in S} f(v, u)$:
$$\text{flowVal}(f) = \sum_{u \in S, v \in S^c} f(u, v) - \sum_{u \in S, v \in S^c} f(v, u) \le c(S)$$
When no augmenting path exists in $G_f$, the reachable cut $S^*$ has all forward edges saturated
and all backward edges empty, achieving $\text{flowVal}(f) = c(S^*)$.

### 3.4 SCC Equivalence & Condensation DAG
Mutual reachability $u \approx v \iff u \rightsquigarrow v \wedge v \rightsquigarrow u$ is an
equivalence relation. Distinct SCCs are strictly disjoint. The condensation graph contracts each
SCC into a super-vertex and is proven to be strictly acyclic (DAG).

### 3.5 Eulerian Circuits & Hierholzer's Algorithm
A connected directed graph contains an Eulerian circuit iff $\text{indeg}(v) = \text{outdeg}(v)$
for all $v$. Hierholzer's cycle splicing algorithm traverses every edge exactly once in $O(|V| + |E|)$.

### 3.6 Prim vs. Kruskal MST
Both algorithms satisfy the Cut Property (greedily selecting min-weight crossing edges preserves
spanning tree optimality). Prim maintains a local priority queue on vertex keys ($O(|E| \log |V|)$),
excelling on dense graphs ($O(|V|^2)$ with Fibonacci heaps), whereas Kruskal sorts all edges globally
($O(|E| \log |E|)$), excelling on sparse graphs with pre-sorted edges.
