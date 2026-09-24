# Path Compression with Union-by-Rank

> **Status: stub — not verified** (Phase 4 canon stub; rank invariants are modeled,
> but operational sequence execution is a specification stub).


This document details the Lean 4 formalization of Disjoint Set Union with path compression in `Amort.Graph.Ackermann.PathCompression`.

## Mathematical Invariants

### Strict Rank Hierarchy
In any DSU tree produced by union-by-rank, parent pointers strictly increase in rank:
$$\forall v \in \text{Fin } n, \quad \neg \text{isRoot}(v) \implies \text{rank}(v) < \text{rank}(\text{parent}(v))$$

### Path Compression Operation
During a `find` operation, path compression redirects every traversed node $v$ directly to the root $r$:
$$\text{parent}(v) := r$$
Because $r$ is an ancestor reached via a sequence of strictly increasing ranks, $\text{rank}(v) < \text{rank}(r)$. Thus:
```lean
theorem compress_preserves_hierarchy {n : ℕ} (d : DSU n)
    (h_hier : StrictRankHierarchy d) (v r : Fin n)
    (h_lt : d.rank v < d.rank r) :
    StrictRankHierarchy (compress d v r)
```

### Logarithmic Rank Bound
Under union-by-rank, any node of rank $r$ roots a subtree of at least $2^r$ elements:
$$2^{\text{rank}(v)} \le n \implies \text{rank}(v) \le \log_2 n \le \text{Nat.size } n$$
