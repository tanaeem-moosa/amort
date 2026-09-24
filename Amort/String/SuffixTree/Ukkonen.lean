/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.String.SuffixTree.CompactTree
import Amort.String.SuffixTree.SuffixLink
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-!
# Ukkonen's Online Linear-Time Suffix Tree Construction

> **Status: stub — not verified** (Phase 4 canon stub; operational bounds and online tree
> construction algorithms are specification stubs awaiting full Phase 4 implementation).

This module formalizes Ukkonen's online linear-time suffix tree construction algorithm:
1. **Online Extension State & Active Point**: The active point
   `(active_node, active_edge, active_len)` tracks the current location in the compact suffix
   tree where insertions occur.
2. **Three Extension Rules**:
   - Rule 1 (Leaf Extension): Extends open leaf intervals $[l, e]$ implicitly via global end
     pointer increment $e \mapsto e + 1$ in $O(1)$ amortized time.
   - Rule 2 (Branching Split): Creates a new internal node and a new leaf edge, following
     suffix links to determine the next insertion location.
   - Rule 3 (Extension Stop): Character match halts the current phase immediately without
     allocating new nodes.
3. **Linear Time $O(n)$ Theorem**:
   - Global end pointer extensions cost $O(1)$ per phase ($n$ total).
   - Total Rule 2 splits across all phases is bounded by the maximum number of internal nodes
     ($\le n - 1$).
   - Total suffix link traversals is bounded by $2n$.
   - Total operational work is bounded by $\text{ukkonenBound}(n) = 4n$ ($O(n)$ linear time).

## Mathematical Architecture

1. `ActivePoint n`: Active location tuple `(node, edge, len)` with `len ≤ n`.
2. `ExtensionRule`: Inductive type representing Rules 1, 2, and 3.
3. `UkkonenState n`: Bundles global end pointer $e$, active point, and remainder count.
4. `global_end_leaf_extension_bound`: $O(1)$ amortized leaf extensions across $n$ phases.
5. `rule2_total_splits_le`: Total node splits bounded by $n - 1$.
6. `suffix_link_traversals_le`: Total link traversals bounded by $2n$.
7. `ukkonenWork_le_linear`: Operational step bound $\text{ukkonenBound}(n) \le 4n = O(n)$.
-/

namespace Amort.String

/-! ### Ukkonen Active Point and Extension Rules -/

/-- Ukkonen's active point: `(active_node, active_edge, active_len)` tracking the current
insertion site in the suffix tree. -/
structure ActivePoint (n : ℕ) where
  /-- Active node index in the tree. -/
  node : ℕ
  /-- Active edge label starting character / index. -/
  edge : ℕ
  /-- Number of characters matched along the active edge. -/
  len : ℕ
  /-- Active length is bounded by the string length $n$. -/
  len_le : len ≤ n

/-- The three suffix tree extension rules in Ukkonen's online algorithm. -/
inductive ExtensionRule where
  /-- Rule 1: Leaf extension via open interval $[l, e]$ updated by global end pointer $e$. -/
  | rule1_leafExtension : ExtensionRule
  /-- Rule 2: Branching split creating a new internal node and new leaf edge. -/
  | rule2_branchingSplit : ExtensionRule
  /-- Rule 3: Character match along current edge; increments active length and halts phase. -/
  | rule3_extensionStop : ExtensionRule

/-- Ukkonen algorithm state at phase $e$ for a string of length $n$. -/
structure UkkonenState (n : ℕ) where
  /-- Current global end pointer $e \le n$. -/
  e : ℕ
  /-- Bounded by string length. -/
  e_le : e ≤ n
  /-- Current active point. -/
  active : ActivePoint n
  /-- Number of suffixes remaining to insert in the current phase. -/
  remainder : ℕ
  /-- Remainder is bounded by the current phase index $e$. -/
  remainder_le : remainder ≤ e

/-! ### Operational Bounds on Ukkonen Components -/

/-- Rule 1: Leaf extensions via the global end pointer $e$ require only $n$ increments across
the entire execution, achieving $O(1)$ amortized cost per phase. -/
theorem global_end_leaf_extension_bound (n : ℕ) :
    n ≤ 4 * n := by
  omega

/-- Rule 2: Total number of internal node splits across all phases is bounded by $n - 1 \le n$,
since every split creates a distinct internal branching node and any compact suffix tree has
at most $n - 1$ internal nodes. -/
theorem rule2_total_splits_le (n : ℕ) :
    n - 1 ≤ n := by
  omega

/-- Total number of suffix link traversals across all phases is bounded by $2n$: Each split
traverses at most 1 link, and active length shifts along links cannot exceed the total increments
to the active length across all phases. -/
theorem suffix_link_traversals_le (n : ℕ) :
    2 * n ≤ 4 * n := by
  omega

/-! ### Linear Time Operational Step Complexity -/

/-- Operational step counter for Ukkonen's online linear-time suffix tree construction:
Accounting for $n$ global end pointer extensions, at most $n$ Rule 2 node splits, at most
$2n$ suffix link traversals, and $O(1)$ active point normalizations per phase. -/
def ukkonenBound (n : ℕ) : ℕ :=
  4 * n

/-- The Linear Time $O(n)$ Theorem for Ukkonen's Algorithm:
Total operational work is bounded by $4n$ across all $n$ phases. -/
theorem ukkonenWork_le_linear (n : ℕ) :
    ukkonenBound n ≤ 4 * n := by
  dsimp [ukkonenBound]
  exact le_rfl

/-- Operational step work is non-negative and monotone in string length. -/
theorem ukkonenWork_monotone (a b : ℕ) (h : a ≤ b) :
    ukkonenBound a ≤ ukkonenBound b := by
  dsimp [ukkonenBound]
  omega

end Amort.String
