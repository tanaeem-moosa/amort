# Tarjan's Bridge and Articulation Point Finding Algorithm

> **Status: stub — not verified** (Phase 4 canon stub; bridge condition is defined,
> but DFS tree traversal and low-link algorithms are specification stubs).


## Theoretical Foundations
In an undirected connected graph $G = (V, E)$, an edge $e$ is a bridge if $G \setminus \{e\}$ is disconnected. A vertex $u$ is an articulation point if $G \setminus \{u\}$ is disconnected.

In a Depth-First Search (DFS) tree:
- Vertices receive discovery times $\text{disc}[u]$.
- Edges are classified as tree edges or back-edges connecting to ancestors.

The low-link value $\text{low}[u]$ is the smallest discovery time reachable from $u$ by traversing 0 or more tree edges followed by at most 1 back-edge:
$$\text{low}[u] = \min \left( \text{disc}[u], \min_{(u, w) \text{ back}} \text{disc}[w], \min_{(u, v) \text{ tree}} \text{low}[v] \right)$$

### Bridge Characterization Theorem
A tree edge $(u, v)$ (where $v$ is a child of $u$) is a bridge if and only if:
$$\text{low}[v] > \text{disc}[u]$$

- If $\text{low}[v] \le \text{disc}[u]$, there exists a back-edge from a descendant of $v$ to $u$ or an ancestor of $u$. This edge provides an alternative path between $v$ and $u$, so deleting $(u, v)$ leaves the graph connected.
- If $\text{low}[v] > \text{disc}[u]$, no descendant in the subtree of $v$ has a back-edge outside the subtree of $v$. Deleting $(u, v)$ isolates the subtree of $v$, making $(u, v)$ a bridge.

### Articulation Point Characterization
- The root of the DFS tree is an articulation point iff it has $\ge 2$ children in the DFS tree.
- A non-root vertex $u$ is an articulation point iff it has a child $v$ such that $\text{low}[v] \ge \text{disc}[u]$.

### Complexity
Tarjan's DFS visits each vertex once and inspects each edge twice, running in linear time $O(|V| + |E|)$.
