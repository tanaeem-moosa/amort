# Vertex Cover 2-Approximation via Maximal Matching

> **Status: stub — not verified** (Phase 4 canon stub; matching lower bound and 2-approximation
> ratio are proven, but operational greedy edge selection is a specification stub).

## Theoretical Foundations
For an undirected simple graph $G = (V, E)$, the Minimum Vertex Cover problem seeks a subset $C \subseteq V$ of minimal cardinality such that every edge $e \in E$ has at least one endpoint in $C$.

A matching $M \subseteq E$ is a set of pairwise disjoint edges. Any vertex cover $C^*$ must contain at least one endpoint of each edge in $M$. Since edges in $M$ share no endpoints:
$$|M| \le |C^*|$$

The greedy algorithm constructs a maximal matching $M$ by repeatedly selecting an edge $(u, v)$ and removing all incident edges. The set of endpoints $C = \bigcup_{e \in M} \{e.1, e.2\}$ forms a valid vertex cover because $M$ is maximal. Its size is:
$$|C| = 2|M| \le 2|C^*|$$
proving a worst-case approximation factor of 2.

## Formalization Highlights
- `Amort.Approximation.IsMatching`: Formal predicate for pairwise disjoint edge sets.
- `Amort.Approximation.matching_card_endpoints`: Proves $|V(M)| = 2|M|$ via `Finset.card_biUnion`.
- `Amort.Approximation.matching_card_le_vertexCover`: Proves the lower bound $|M| \le |C^*|$ by bounding the sum of disjoint intersections.
- `Amort.Approximation.maximal_matching_isVertexCover`: Proves that endpoints of a maximal matching cover all edges.
- `Amort.Approximation.vertex_cover_approx_ratio`: Synthesizes the 2-approximation theorem.
