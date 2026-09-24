# Ukkonen's Online Linear-Time Suffix Tree Construction

> **Status: stub — not verified** (Phase 4 canon stub; operational bounds and online tree
> construction algorithms are specification stubs awaiting full Phase 4 implementation).

This document details the Lean 4 formalization of Ukkonen's algorithm in `Amort.String.SuffixTree.Ukkonen`.

## Algorithm Mechanics and Amortized $O(n)$ Bound

### Online Active Point
The location in the suffix tree where the next character insertion occurs is represented by the active point:
```lean
structure ActivePoint (n : ℕ) where
  node : ℕ
  edge : ℕ
  len : ℕ
  len_le : len ≤ n
```

### The Three Extension Rules
1. **Rule 1 (Leaf Extension)**:
   Leaves are represented by open interval edges $[l, e]$. When the global end pointer $e$ increments $e \mapsto e + 1$, all existing leaves are extended automatically in $O(1)$ time per phase. Across all $n$ phases, this incurs at most $n$ operations.
2. **Rule 2 (Branching Split)**:
   When a mismatch occurs, the current edge is split, a new internal node is created, and a new leaf edge is inserted. The active point then follows the suffix link. Since every split creates a distinct internal branching node, the total number of Rule 2 splits across the entire algorithm cannot exceed $n - 1 \le n$.
3. **Rule 3 (Extension Stop)**:
   When the next character is already present along the current edge, the active length increments and the current phase halts immediately without modifying the tree.

### Complexity Theorem
Accounting for:
- $n$ global end pointer updates (Rule 1)
- At most $n$ branching splits (Rule 2)
- At most $2n$ suffix link traversals
- $O(1)$ phase transitions
Total operational work is bounded by:
$$\text{ukkonenWork}(n) = 4n \le 4n$$
yielding $O(n)$ linear time.
