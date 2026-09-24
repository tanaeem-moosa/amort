# Compact Suffix Tree Structure and Size Bounds

> **Status: stub — not verified** (Phase 4 canon stub; tree combinatorics are modeled,
> but construction algorithm is a specification stub).


This document details the Lean 4 formalization of the compact suffix tree representation and its structural bounds in `Amort.String.SuffixTree.CompactTree`.

## Mathematical Formulations

### Edge Slice Intervals
Rather than storing explicit substring characters on each tree edge, edges are labeled by slice intervals $[l, r]$ referencing text $S[l..r]$:
```lean
structure EdgeInterval (n : ℕ) where
  left : ℕ
  right : ℕ
  h_le : left ≤ right
  h_right : right ≤ n
```
This guarantees $O(1)$ space per edge, bounding total edge label storage by $O(n)$ overall.

### Tree Combinatorics & Node Bounds
In any rooted tree with $L \ge 1$ leaves where every internal node has out-degree $\ge 2$:
1. The total number of edges is $E = V - 1 = L + I - 1$.
2. The sum of out-degrees across all internal nodes is $\sum_{u \in I} d(u) = E = L + I - 1$.
3. Since $d(u) \ge 2$ for all $u \in I$:
   $$2I \le L + I - 1 \implies I \le L - 1$$
4. Since $L \le n$, the number of internal nodes satisfies $I \le n - 1$.
5. The total number of nodes is:
   $$V = L + I \le L + (L - 1) = 2L - 1 \le 2n - 1 \le 2n$$
