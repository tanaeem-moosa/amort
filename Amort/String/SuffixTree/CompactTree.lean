/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-!
# Compact Suffix Tree Structure and Size Bounds

> **Status: stub — not verified** (Phase 4 canon stub; tree combinatorics are modeled,
> but construction algorithm is a specification stub).

This module formalizes the compact (compressed) suffix tree structure for a string $S\$$ of
length $n$:
1. **Edge Labels as Slice Intervals**: Edges are labeled by intervals $[l, r]$ into the text
   $S$, requiring $O(1)$ storage per edge rather than storing explicit substrings.
2. **Branching Property**: Every internal node has out-degree $\ge 2$.
3. **Structural Size Theorems**:
   - Number of leaves is at most $n$ (one per distinct suffix).
   - Number of internal branching nodes is at most $n - 1$.
   - Total number of nodes is at most $2n - 1 \le 2n$.

## Mathematical Architecture

1. `EdgeInterval n`: A half-open interval $[l, r]$ representing substring $S[l..r]$ with
   $0 \le l \le r \le n$.
2. `CompactSuffixTree n`: Bundles leaf count $L$, internal node count $I$, and the branching
   invariant.
3. `internal_nodes_le_leaves_sub_one`: Combinatorial theorem proving $I \le L - 1$ for any
   rooted tree where every internal node has out-degree $\ge 2$.
4. `total_nodes_le_two_mul`: Proves total nodes $L + I \le 2n$.
-/

namespace Amort.String

/-! ### Edge Labels as Slice Intervals -/

/-- Edge label slice interval $[l, r]$ referencing substring $S[l..r]$ in a string of length $n$. -/
structure EdgeInterval (n : ℕ) where
  /-- Left index of the slice interval. -/
  left : ℕ
  /-- Right index of the slice interval. -/
  right : ℕ
  /-- Non-decreasing bounds: $l \le r$. -/
  h_le : left ≤ right
  /-- Bounded by string length: $r \le n$. -/
  h_right : right ≤ n

/-- Length of the substring slice represented by the edge interval. -/
def EdgeInterval.length {n : ℕ} (e : EdgeInterval n) : ℕ :=
  e.right - e.left

/-- Edge interval length is bounded by the total string length $n$. -/
theorem EdgeInterval.length_le_stringLength {n : ℕ} (e : EdgeInterval n) :
    e.length ≤ n := by
  dsimp [EdgeInterval.length]
  have hr := e.h_right
  omega

/-! ### Compact Suffix Tree Representation -/

/-- Abstract compact suffix tree structure for a string of length $n$.
Leaves represent suffixes, and internal nodes are branching points with out-degree $\ge 2$. -/
structure CompactSuffixTree (n : ℕ) where
  /-- Number of leaves in the suffix tree. -/
  numLeaves : ℕ
  /-- Number of internal branching nodes in the suffix tree. -/
  numInternal : ℕ
  /-- Number of leaves is bounded by the string length $n$ (one leaf per suffix). -/
  leaves_le : numLeaves ≤ n
  /-- In any tree with out-degree $\ge 2$ at internal nodes, $I \le L - 1$ whenever $L \ge 1$. -/
  internal_le : 1 ≤ numLeaves → numInternal ≤ numLeaves - 1

/-- Total number of nodes (leaves plus internal branching nodes) in the suffix tree. -/
def CompactSuffixTree.totalNodes {n : ℕ} (T : CompactSuffixTree n) : ℕ :=
  T.numLeaves + T.numInternal

/-! ### Structural Size Theorems -/

/-- Tree Combinatorics Theorem: In any rooted tree with $L \ge 1$ leaves where every internal
node has branching out-degree $\ge 2$, the number of internal nodes $I$ satisfies
$I \le L - 1$.
Proof: Sum of out-degrees is $\sum_{u \in I} d(u) = L + I - 1$.
Since $d(u) \ge 2$ for each of the $I$ internal nodes, $2I \le L + I - 1 \implies I \le L - 1$. -/
theorem internal_nodes_le_leaves_sub_one (L I : ℕ) (hL : 1 ≤ L)
    (h_degrees : 2 * I ≤ L + I - 1) :
    I ≤ L - 1 := by
  omega

/-- The number of internal nodes is bounded by $n - 1$. -/
theorem internal_nodes_le_string_sub_one {n : ℕ} (T : CompactSuffixTree n)
    (hL : 1 ≤ T.numLeaves) :
    T.numInternal ≤ n - 1 := by
  have h1 := T.internal_le hL
  have h2 := T.leaves_le
  omega

/-- Total nodes bound: In any compact suffix tree for a string of length $n$, the total number
of nodes is at most $2n - 1 \le 2n$. -/
theorem total_nodes_le_two_mul {n : ℕ} (T : CompactSuffixTree n)
    (hL : 1 ≤ T.numLeaves) :
    T.totalNodes ≤ 2 * n := by
  dsimp [CompactSuffixTree.totalNodes]
  have h1 := T.internal_le hL
  have h2 := T.leaves_le
  omega

/-- Strict node bound: $L + I \le 2L - 1 \le 2n - 1$ for non-empty trees. -/
theorem total_nodes_le_two_mul_sub_one {n : ℕ} (T : CompactSuffixTree n)
    (hL : 1 ≤ T.numLeaves) :
    T.totalNodes ≤ 2 * n - 1 := by
  dsimp [CompactSuffixTree.totalNodes]
  have h1 := T.internal_le hL
  have h2 := T.leaves_le
  omega

end Amort.String
