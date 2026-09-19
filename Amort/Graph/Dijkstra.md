# Dijkstra's Shortest Paths Algorithm

## Overview
This module formalizes Dijkstra's algorithm for single-source shortest paths on directed
graphs with non-negative edge weights using a priority queue. It provides:
1. Shortest path specifications, path weights, and the triangle inequality.
2. The fundamental greedy choice invariant: when a vertex $u$ is extracted with minimum
   tentative key from the unvisited set, its tentative distance equals the true shortest path
   distance $\delta(s, u)$.
3. Operational step complexity modeling bounding total operations by
   $(|V| + |E|) \cdot \text{Nat.size } |V|$ ($O((|V| + |E|) \log |V|)$).

## Mathematical Architecture

### 1. Path Weight and Distance Specification
Given a graph with $n$ vertices (`Fin n`) and non-negative edge weights
$w : \text{Fin } n \to \text{Fin } n \to \text{WithTop } \mathbb{N}$:
- Path weight `pathWeight w p` accumulates edge weights along sequence $p$.
- Shortest path distance `DijkstraSpec w s` satisfies:
  - $\text{dist}(s) = 0$
  - $\text{dist}(v) \le \text{dist}(u) + w(u, v)$ for all edges $(u, v)$.
- Theorem `dist_le_pathWeight_from_source`: For any path $p$ from source $s$ to vertex $v$,
  $\text{dist}(v) \le \text{pathWeight}(w, p)$.

### 2. Greedy Choice Invariant
Let $S \subset V$ be the set of visited/finalized vertices whose distances are known to be exact.
Let tentative distances for $v \notin S$ satisfy the relaxation condition from $S$:
$$d(y) \le d(x) + w(x, y) \quad (\forall x \in S, y \notin S)$$
When the vertex $u^* = \text{argmin}_{v \notin S} d(v)$ with minimal tentative key is extracted:
- Any path from $s$ to $u^*$ must cross the frontier from $S$ to $V \setminus S$ at some edge $(x, y)$.
- Because all edge weights $w \ge 0$, the path weight satisfies:
  $$\text{weight} \ge \delta(s, x) + w(x, y) \ge d(y) \ge d(u^*)$$
- Theorem `dijkstra_greedy_choice`: Formally establishes that $d(u^*) \le d(x) + w(x, y)$,
  guaranteeing that no shorter path can reach $u^*$ through unvisited vertices.

### 3. Operational Step Complexity
Using a binary min-heap priority queue over $|V| = n$ vertices:
- $|V|$ extract-min operations, each requiring $\le \text{Nat.size } n$ steps.
- $|E| = m$ decrease-key / relaxation operations, each requiring $\le \text{Nat.size } n$ steps.
- Total operational work:
  $$\text{dijkstraWork}(n, m) = (n + m) \cdot \text{Nat.size } n \le (|V| + |E|) \cdot \text{Nat.size } |V|$$

## Key Theorems

| Theorem / Definition | Type | Description |
| :--- | :--- | :--- |
| `pathWeight` | Definition | Weight of a sequence of vertices |
| `DijkstraSpec` | Structure | Specification of valid shortest path distances |
| `dist_le_pathWeight_from_source` | Theorem | Distance bounded by weight of any path from source |
| `greedy_choice_minimal` | Theorem | Minimal key among unvisited vertices |
| `dijkstra_greedy_choice` | Theorem | Greedy choice correctness across frontier |
| `dijkstraWork` | Definition | Operational step model: $(n + m) \cdot \text{Nat.size } n$ |
| `dijkstra_work_le` | Theorem | Concrete upper bound on operational steps |
| `dijkstra_work_graph_le` | Theorem | Operational steps in terms of graph edge count |
