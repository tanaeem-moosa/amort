# Hopcroft-Karp Maximum Bipartite Matching Algorithm

> **Status: stub — not verified** (Phase 4 canon stub; alternating path structures are
> defined, but phased BFS/DFS execution is a specification stub).


## Theoretical Foundations
Given a bipartite graph $G = (L, R, E)$, a matching $M$ is a subset of edges with no shared endpoints. An alternating path alternates between edges in $E \setminus M$ and $M$. An augmenting path begins and ends at distinct free (unmatched) vertices.

By symmetric difference, if $P$ is an augmenting path with respect to $M$, then $M \oplus P$ is a valid matching with $|M \oplus P| = |M| + 1$.

Hopcroft and Karp (1973) partition the algorithm into phases:
1. Breadth-First Search (BFS) builds a layered DAG rooted at free vertices in $L$, finding the length $d$ of the shortest augmenting path.
2. Depth-First Search (DFS) extracts a maximal collection of vertex-disjoint shortest augmenting paths $\{P_1, \dots, P_k\}$ of length $d$.
3. Matching augmentation updates $M \leftarrow M \oplus P_1 \oplus \dots \oplus P_k$.

### Invariants and Phase Bound
- **Strictly Increasing Length**: In any phase where all vertex-disjoint shortest paths are augmented, the length of the shortest augmenting path in the next phase strictly increases by at least 2:
  $$d_{i+1} \ge d_i + 2$$
- **Phase Bound**: After $\lfloor \sqrt{|V|} \rfloor$ phases, the shortest augmenting path has length $\ge 2\sqrt{|V|} + 1$. In the symmetric difference $M \oplus M^*$ with an optimal matching $M^*$, each component augmenting path has $\ge 2\sqrt{|V|}$ vertices. Since these paths are vertex-disjoint, at most:
  $$\frac{|V|}{2\sqrt{|V|}} \le \sqrt{|V|}$$
  augmenting paths remain. Because each remaining phase adds at least one edge, at most $\sqrt{|V|}$ more phases can occur. Total phases $\le 2\sqrt{|V|}$.
- **Complexity**: Each phase traverses edges in $O(|E| + |V|)$ time. Overall worst-case complexity is $O(|E|\sqrt{|V|})$.
