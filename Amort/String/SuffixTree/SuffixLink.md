# Suffix Links and Depth Invariants

This document details the Lean 4 formalization of suffix links in `Amort.String.SuffixTree.SuffixLink`.

## Suffix Link Definition and Invariants

### Definition
For an internal node $u$ representing path label $a \beta$ where $a \in \Sigma$ and $\beta \in \Sigma^*$, its suffix link points to the node representing path label $\beta$:
$$\text{suffixLink}(u) = v \quad \text{where } \text{path}(v) = \beta$$

### String Depth Invariant
```lean
theorem suffixLink_depth_invariant : ∀ u, u ≠ root → stringDepth (suffixLink u) = stringDepth u - 1
```

### Strict Monotonicity & Iteration
Following a suffix link strictly decreases string depth:
$$\text{stringDepth}(\text{suffixLink}(u)) < \text{stringDepth}(u)$$
Iterating $k$ suffix links yields depth $\text{stringDepth}(u) - k$:
```lean
theorem iterateLink_depth (k : ℕ) (u : Node) (h_bound : k ≤ T.stringDepth u)
    (h_chain : ∀ j < k, iterateLink T j u ≠ T.root) :
    T.stringDepth (iterateLink T k u) = T.stringDepth u - k
```
This guarantees that any suffix link traversal chain terminates at the root in at most $\text{stringDepth}(u) \le n$ steps.
