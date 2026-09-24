# Approximation Algorithms in Lean 4

> **Status: stub — not verified** (Phase 4 canon stubs; Set Cover, Metric TSP, and Vertex Cover
> algorithms are specification stubs awaiting full verification).


This directory formalizes foundational approximation algorithms for NP-hard optimization problems:

1. **Vertex Cover 2-Approximation** (`VertexCover.lean`):
   - Maximal matching greedy edge selection.
   - Lower bound: any vertex cover must select at least one endpoint from each disjoint matching edge ($|M| \le |C^*|$).
   - Approximation ratio: $|C| = 2|M| \le 2 \cdot |C^*|$.
   - Linear operational complexity $O(|V| + |E|)$.

2. **Metric TSP 2-Approximation** (`MetricTSP.lean`):
   - Complete metric graphs with triangle inequality $d(u, w) \le d(u, v) + d(v, w)$.
   - Minimum Spanning Tree (MST) weight lower bound: $\text{weight}(\text{MST}) \le \text{OPT}_{\text{TSP}}$.
   - Double-tree Eulerian tour with total weight $2 \cdot \text{weight}(\text{MST})$.
   - Shortcutting theorem: shortcut tour preserves cycle validity and never increases length.
   - Approximation ratio: $\text{cost}(\text{Tour}) \le 2 \cdot \text{weight}(\text{MST}) \le 2 \cdot \text{OPT}_{\text{TSP}}$.
   - Operational complexity $O(n^2 \log n)$.

3. **Greedy Set Cover $H(n)$-Approximation** (`SetCover.lean`):
   - Universe $U$ and subset collection $\mathcal{S}$.
   - Harmonic potential charging scheme: each element is charged $1/k$ when covered.
   - Per-set potential bound: elements in $S^* \in \mathcal{C}^*$ accumulate charge $\le H(|S^*|) \le H(n)$.
   - Harmonic approximation bound: $|\mathcal{C}_{\text{greedy}}| \le H(n) \cdot |\mathcal{C}^*| = H(n) \cdot \text{OPT}$.
   - Operational complexity $O(m \cdot n)$.

4. **Asymptotic Complexity Bridges** (`Asymptotics.lean`):
   - Connection of all operational step functions to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
