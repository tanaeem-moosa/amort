# Prim's Minimum Spanning Tree Algorithm

> **Status: stub — not verified** (Phase 3 canon stub; specification formulas awaiting
> executable priority queue frontier implementation).


## Overview
This module formalizes Prim's algorithm for finding a Minimum Spanning Tree (MST) on finite
undirected connected graphs with priority queue frontier selection. It provides:
1. Priority queue frontier specifications and key invariants.
2. The Cut-Property invariant: greedily selecting the minimum-weight crossing edge preserves
   spanning tree optimality.
3. Operational step complexity model bounding total operations by
   $(|V| + |E|) \cdot \text{Nat.size } |V|$ ($O(|E| \log |V|)$).
4. Rigorous mathematical and algorithmic comparison with Kruskal's algorithm.

## Mathematical Architecture

### 1. Frontier Selection and Cut-Property Optimality
Let $S \subset V$ be the set of vertices already incorporated into the MST tree.
For each vertex $v \notin S$, the priority queue maintains the minimum edge weight from $S$ to $v$:
$$\text{key}(v) = \min_{u \in S} w(u, v)$$
When $v^* = \text{argmin}_{v \notin S} \text{key}(v)$ is extracted with connecting edge $(u^*, v^*)$:
- Theorem `prim_frontier_min_crossing` formally proves that for any $u \in S$ and $v \notin S$:
  $$w(u^*, v^*) \le w(u, v)$$
  establishing that $(u^*, v^*)$ is a minimum-weight edge crossing the cut $(S, V \setminus S)$.
- By the Cut Property of Minimum Spanning Trees, adding this minimal crossing edge to the
  current tree maintains the invariant that the tree is a subgraph of some MST.

### 2. Operational Step Complexity
Using a binary min-heap priority queue over $|V| = n$ vertices and $|E| = m$ edges:
- $|V|$ extract-min operations, each taking $\le \text{Nat.size } n$ heap operations.
- $|E|$ decrease-key / relaxation operations, each taking $\le \text{Nat.size } n$ heap operations.
- Total operational work:
  $$\text{primWork}(n, m) = (n + m) \cdot \text{Nat.size } n$$
- On connected graphs ($n \le m + 1$), this is bounded by $(2m + 1) \cdot \text{Nat.size } n$
  ($O(|E| \log |V|)$).

### 3. Algorithmic Contrast: Prim vs. Kruskal
- **Prim's Algorithm**:
  - **Strategy**: Grows a single component from an arbitrary start vertex, maintaining a
    frontier priority queue of unvisited vertices.
  - **Data Structures**: Binary min-heap (or Fibonacci heap) over vertices.
  - **Complexity**: $O(|E| \log |V|)$ (or $O(|E| + |V| \log |V|)$ with Fibonacci heaps).
  - **Advantage**: Superior on dense graphs ($|E| = \Theta(|V|^2)$), where Fibonacci heaps
    achieve $O(|V|^2)$ vs. Kruskal's $O(|V|^2 \log |V|)$.
- **Kruskal's Algorithm**:
  - **Strategy**: Global edge-centric greedy processing; sorts all edges upfront and joins
    trees in a forest using Disjoint Set Union (DSU) to avoid cycles.
  - **Data Structures**: `MergeSort` on edge list + DSU with union-by-rank.
  - **Complexity**: Dominated by edge sorting: $O(|E| \log |E|) = O(|E| \log |V|)$.
  - **Advantage**: Superior on sparse graphs with pre-sorted edges ($O(|E| \alpha(|V|))$).
- Theorem `prim_le_kruskal_of_le` formally verifies that whenever $|V| \le |E|$, Prim's
  operational bound is bounded above by Kruskal's total operational work.

## Key Theorems

| Theorem / Definition | Type | Description |
| :--- | :--- | :--- |
| `PrimFrontier` | Structure | Frontier state maintaining keys and incident witnesses |
| `prim_frontier_min_crossing` | Theorem | Minimal frontier key yields a min cut crossing edge |
| `primWork` | Definition | Operational step model: $(n + m) \cdot \text{Nat.size } n$ |
| `prim_work_le` | Theorem | Operational bound $(2m + 1) \cdot \text{Nat.size } n$ on connected graphs |
| `prim_work_eq` | Theorem | Work product factoring |
| `prim_le_kruskal_of_le` | Theorem | Formal complexity comparison showing Prim $\le$ Kruskal for $|V| \le |E|$ |
