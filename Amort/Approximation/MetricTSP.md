# Metric TSP 2-Approximation via Double-Tree Shortcutting

## Theoretical Foundations
In the Metric Traveling Salesperson Problem (TSP), we are given a complete graph $G = (V, E)$ with non-negative edge costs satisfying the triangle inequality:
$$d(u, w) \le d(u, v) + d(v, w)$$

The algorithm computes a Minimum Spanning Tree $T$ of $G$. By deleting any edge from an optimal Hamiltonian tour $T^*$, we obtain a spanning path, which is a spanning tree:
$$\text{weight}(\text{MST}) \le \text{cost}(T^*) = \text{OPT}$$

Doubling every edge of $T$ yields an Eulerian multigraph where every vertex has even degree. An Eulerian circuit $W$ traverses every doubled edge exactly once:
$$\text{cost}(W) = 2 \cdot \text{weight}(\text{MST})$$

By shortcutting intermediate visited vertices in $W$, we obtain a simple Hamiltonian cycle $T_{\text{shortcut}}$. By the triangle inequality, direct traversal between endpoints of a subwalk is no longer than the subwalk itself:
$$\text{cost}(T_{\text{shortcut}}) \le \text{cost}(W) = 2 \cdot \text{weight}(\text{MST}) \le 2 \cdot \text{OPT}$$

## Formalization Highlights
- `Amort.Approximation.MetricGraph`: Complete metric graph with symmetric, reflexive triangle distances.
- `Amort.Approximation.walkCost`: Recursive cost of an arbitrary vertex walk.
- `Amort.Approximation.dist_le_walkCost`: Formal induction proving $d(u, v) \le \text{walkCost}(W)$ for any walk connecting $u$ to $v$.
- `Amort.Approximation.shortcutting_preserves_bound`: Formal bounding of shortcut tours by underlying Eulerian walks.
- `Amort.Approximation.metric_tsp_approx_bound`: Complete formal verification of the 2-approximation theorem.
