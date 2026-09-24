# Advanced Graph Algorithms & Bipartite Matching in Lean 4

> **Status: stub — not verified** (Phase 4 canon stubs; Hopcroft-Karp, Tarjan Bridge, and Hall
> Marriage algorithms are specification stubs awaiting full verification).


This module family formalizes advanced graph algorithms, matching theory, and DFS invariants:

1. **Hopcroft-Karp Maximum Bipartite Matching** (`HopcroftKarp.lean`):
   - Alternating and augmenting paths on bipartite graphs $G = (L, R, E)$.
   - Layered BFS phase identifying shortest augmenting paths and maximal DFS augmentation.
   - Strictly increasing augmenting path lengths across phases: $d_{i+1} \ge d_i + 2$.
   - Phase bound theorem: total phases $\le 2\sqrt{|V|}$.
   - Worst-case time complexity $O(|E|\sqrt{|V|})$.

2. **Hall's Marriage Theorem** (`HallMarriage.lean`):
   - Combinatorial neighborhood $N(S) = \bigcup_{u \in S} N(u)$ for $S \subseteq L$.
   - Hall's marriage condition: $\forall S \subseteq L, |S| \le |N(S)|$.
   - Max-flow reduction to unit network: min-cut capacity $(|L| - |S|) + |N(S)| \ge |L|$.
   - Equivalence theorem: $G$ admits an $L$-saturating matching if and only if Hall's condition holds.

3. **Tarjan's Bridge and Articulation Point Finding** (`BridgeTarjan.lean`):
   - DFS discovery order $\text{disc}[u]$ and low-link values $\text{low}[u]$.
   - Bridge characterization: tree edge $(u, v)$ is a bridge $\iff \text{low}[v] > \text{disc}[u]$.
   - Articulation point criteria for root ($\ge 2$ children) and non-root ($\text{low}[v] \ge \text{disc}[u]$).
   - Linear operational step bound $O(|V| + |E|)$.

4. **Asymptotic Complexity Bridges** (`Asymptotics.lean`):
   - Formal connection of Hopcroft-Karp and Tarjan step functions to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` under `Filter.atTop`.
