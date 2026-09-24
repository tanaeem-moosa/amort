# Asymptotic Complexity Bridges for Advanced Graph Algorithms

> **Status: stub — not verified** (Phase 3/4 canon stub; asymptotic theorems bound specification
> formulas awaiting instrumented execution implementations).


## Overview
This module connects the concrete operational step bounds for advanced graph algorithms
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework:
- Dijkstra's Single-Source Shortest Paths ($O((|V| + |E|) \log |V|)$).
- Edmonds-Karp Network Flow & Augmenting Paths ($O(|V| \cdot |E|^2)$).
- Strongly Connected Components via Kosaraju's Algorithm ($O(|V| + |E|)$).
- Eulerian Circuits via Hierholzer's Cycle Splicing Algorithm ($O(|V| + |E|)$).
- Prim's Minimum Spanning Tree Algorithm ($O(|E| \log |V|)$).

## Mathematical Architecture

### 1. Dijkstra's Algorithm ($O((|V| + |E|) \log |V|)$)
Priority queue operational step count $\text{dijkstraWork}(n, m) = (n + m) \cdot \text{Nat.size } n$
satisfies:
$$\text{dijkstraWork}(|V|, |E|) = O((|V| + |E|) \cdot \text{Nat.size } |V|)$$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ via `isBigO_dijkstraWork_atTop`.

### 2. Network Flow: Edmonds-Karp ($O(|V| \cdot |E|^2)$)
Edmonds-Karp step model $\text{edmondsKarpWork}(n, m) = n \cdot m^2$ satisfies:
$$\text{edmondsKarpWork}(|V|, |E|) = O(|V| \cdot |E|^2)$$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ via `isBigO_edmondsKarpWork_atTop`.

### 3. Strongly Connected Components: Kosaraju's Algorithm ($O(|V| + |E|)$)
Kosaraju's two-pass DFS step model $\text{kosarajuWork}(n, m) = 2(n + m)$ satisfies:
$$\text{kosarajuWork}(|V|, |E|) = O(|V| + |E|)$$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ with bounding constant $C = 2$ via
`isBigO_kosarajuWork_atTop`.

### 4. Eulerian Circuits: Hierholzer's Algorithm ($O(|V| + |E|)$)
Hierholzer's cycle splicing step model $\text{hierholzerWork}(n, m) = 2(n + m)$ satisfies:
$$\text{hierholzerWork}(|V|, |E|) = O(|V| + |E|)$$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ with bounding constant $C = 2$ via
`isBigO_hierholzerWork_atTop`.

### 5. Prim's Minimum Spanning Tree Algorithm ($O(|E| \log |V|)$)
Prim's priority queue operational step count $\text{primWork}(n, m) = (n + m) \cdot \text{Nat.size } n$
satisfies:
$$\text{primWork}(|V|, |E|) = O((|V| + |E|) \cdot \text{Nat.size } |V|)$$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ via `isBigO_primWork_atTop`.
On connected graphs ($|V| \le |E| + 1$):
$$\text{primWork}(|V|, |E|) = O(|E| \log |V|)$$
under filter $l$ via `isBigO_primWork_connected`.

## Key Theorems

| Theorem | Complexity Class | Filter | Bound Constant |
| :--- | :--- | :--- | :--- |
| `isBigO_dijkstraWork_atTop` | $O((|V| + |E|) \log |V|)$ | `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ | 1 |
| `isBigO_edmondsKarpWork_atTop` | $O(|V| \cdot |E|^2)$ | `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ | 1 |
| `isBigO_kosarajuWork_atTop` | $O(|V| + |E|)$ | `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ | 2 |
| `isBigO_hierholzerWork_atTop` | $O(|V| + |E|)$ | `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ | 2 |
| `isBigO_primWork_atTop` | $O((|V| + |E|) \log |V|)$ | `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$ | 1 |
| `isBigO_primWork_connected` | $O(|E| \log |V|)$ | Any filter with $|V| \le |E| + 1$ | 1 |
