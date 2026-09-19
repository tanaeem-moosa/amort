# Strongly Connected Components and the Condensation DAG

## Overview
This module formalizes graph reachability, mutual reachability equivalence classes,
strongly connected components (SCC), the acyclic condensation DAG, and linear-time
operational complexity for SCC decomposition via Kosaraju's two-pass DFS algorithm.

## Mathematical Architecture

### 1. Reachability and Mutual Reachability
For directed graph `adj : Fin n → List (Fin n)`:
- Reachability $u \rightsquigarrow v$ is modeled by the reflexive-transitive closure
  `Relation.ReflTransGen` on directed edges.
- Mutual reachability:
  $$u \approx v \iff u \rightsquigarrow v \wedge v \rightsquigarrow u$$
- Theorems `mutuallyReachable_refl`, `mutuallyReachable_symm`, and `mutuallyReachable_trans`
  formally establish that $\approx$ is an equivalence relation.

### 2. Strongly Connected Components (SCC)
An SCC is an equivalence class under mutual reachability:
- Predicate `IsSCC adj C`:
  - `nonempty`: $C \ne \emptyset$.
  - `soundness`: $\forall u, v \in C, u \approx v$ (every component is strongly connected).
  - `completeness`: $\forall u \in C, \forall v, u \approx v \implies v \in C$ (maximality).
- Theorem `scc_disjoint_or_eq`: Two SCCs that share at least one vertex are identical:
  $$C_1 \cap C_2 \ne \emptyset \implies C_1 = C_2$$

### 3. Condensation Graph & Acyclicity
The condensation graph contracts each SCC into a single super-vertex:
- Condensation edges exist between distinct components:
  $$\text{CondensationEdge}(C_1, C_2) \iff C_1 \ne C_2 \wedge \exists u \in C_1, v \in C_2, (u, v) \in E$$
- Theorem `scc_edge_reach`: If an edge exists from $C_1$ to $C_2$, every vertex in $C_1$
  can reach every vertex in $C_2$.
- Theorem `condensation_acyclic`: No two distinct SCCs can mutually reach each other:
  $$C_1 \ne C_2 \implies \neg (u \rightsquigarrow v \wedge v \rightsquigarrow u) \quad (\forall u \in C_1, v \in C_2)$$
  proving that the condensation graph contains no cycles (it is a DAG).

### 4. Linear Operational Step Complexity (Kosaraju's Algorithm)
Kosaraju's two-pass DFS algorithm decomposes SCCs in linear time:
- Pass 1: DFS on $G$ visiting all vertices and scanning edges, bounded by $|V| + |E|$ steps.
- Pass 2: DFS on the transposed graph $G^T$, bounded by $|V| + |E|$ steps.
- Total operational complexity:
  $$\text{kosarajuWork}(n, m) = 2(n + m) \le 2(|V| + |E|) = O(|V| + |E|)$$

## Key Theorems

| Theorem / Definition | Type | Description |
| :--- | :--- | :--- |
| `Reachable` | Definition | Reflexive-transitive reachability relation |
| `MutuallyReachable` | Definition | Mutual reachability equivalence relation |
| `IsSCC` | Structure | Nonempty, strongly connected, and maximal component |
| `scc_disjoint_or_eq` | Theorem | Pairwise disjointness of distinct SCCs |
| `CondensationEdge` | Definition | Directed edge between distinct components |
| `scc_edge_reach` | Theorem | Inter-component edge implies all-pairs reachability |
| `condensation_acyclic` | Theorem | Acyclicity of the condensation DAG |
| `kosarajuWork` | Definition | Operational step model: $2(n + m)$ |
| `kosaraju_work_le` | Theorem | Linear operational step bound $O(|V| + |E|)$ |
