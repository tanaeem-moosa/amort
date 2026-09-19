# Potential Function Analysis and Amortized Bound for DSU

This document details the Lean 4 formalization of the amortized analysis of DSU with path compression in `Amort.Graph.Ackermann.PotentialBound`.

## Potential Function and Amortized Analysis

### Rank Intervals
For node $v$ with rank $r$ and parent rank $R$, the level $k(v)$ is the index such that:
$$A_k(r) \le R < A_{k+1}(r)$$
Since $R \le n \le A_{\alpha(n)}(1) \le A_{\alpha(n)}(r)$, the level $k(v)$ is between $0$ and $\alpha(n)$.

### Accounting Scheme
Along the path of length $L$ during `find(v)`:
- At most $\alpha(n) + 1$ nodes change level or reach the root. These are charged directly to the operation:
  $$\hat{c} \le 4(\alpha(n) + 1)$$
- Every other node shares a level with its parent and has its parent rank strictly increased by path compression, decreasing the potential by at least 1.

### Telescoping Summation Theorem
```lean
theorem amortized_telescoping_sum (m : ℕ) (c : ℕ → ℤ) (phi : ℕ → ℤ) (A : ℤ)
    (h_step : ∀ i, c i ≤ A + phi i - phi (i + 1))
    (h_nonneg : 0 ≤ phi m) :
    (∑ i ∈ Finset.range m, c i) ≤ (m : ℤ) * A + phi 0
```
With total initial potential bounded by $2n(\alpha(n) + 1)$, the total actual cost across $m$ operations is bounded by:
$$\text{dsuAckermannWork}(m, n) = 4m(\alpha(n) + 1) + 2n(\alpha(n) + 1) \le 6(m + n)(\alpha(n) + 1)$$
When $m \ge n$, this yields $O(m \cdot \alpha(n))$ time.
