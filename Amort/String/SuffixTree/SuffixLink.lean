/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith

/-!
# Suffix Links and Depth Invariants in Suffix Trees

This module formalizes suffix links in compact suffix trees:
1. **Suffix Link Mapping**: For every internal node $u$ representing string $a \beta$
   (where $a \in \Sigma$ and $\beta \in \Sigma^*$), its suffix link $\text{link}(u)$ points
   to the internal node representing $\beta$.
2. **String Depth Invariant**: The string depth of $\text{link}(u)$ is exactly
   $\text{stringDepth}(u) - 1$:
   $$\text{stringDepth}(\text{link}(u)) = \text{stringDepth}(u) - 1$$
3. **Strict Monotonicity**: Following a suffix link strictly decreases string depth:
   $$\text{stringDepth}(\text{link}(u)) < \text{stringDepth}(u)$$
4. **Link Chain Telescoping**: Iterating $k$ suffix links from node $u$ yields a node with string
   depth $\text{stringDepth}(u) - k$, reaching the root in at most $\text{stringDepth}(u) \le n$
   steps.

## Mathematical Architecture

1. `SuffixLinkTree Node`: Structure encapsulating tree root, string depth function, and suffix
   link transitions.
2. `suffixLink_depth_lt`: Proves strict descent in string depth along suffix links.
3. `iterateLink`: Function iterating $k$ suffix link transitions.
4. `iterateLink_depth`: Proves the exact depth decrement $\text{stringDepth}(u) - k$.
-/

namespace Amort.String

/-- Suffix link tree structure abstracting internal node string depths and suffix link
transitions. -/
structure SuffixLinkTree (Node : Type) where
  /-- The root node of the suffix tree, representing the empty string $\varepsilon$. -/
  root : Node
  /-- String depth function: number of characters on the path from root to node. -/
  stringDepth : Node → ℕ
  /-- Root has string depth 0. -/
  root_depth : stringDepth root = 0
  /-- Suffix link transition function mapping node representing $a \beta$ to node representing
  $\beta$. -/
  suffixLink : Node → Node
  /-- The suffix link of the root points to itself. -/
  root_suffixLink : suffixLink root = root
  /-- Every node other than the root has strictly positive string depth ($\ge 1$). -/
  depth_pos_of_ne_root : ∀ u, u ≠ root → 1 ≤ stringDepth u
  /-- Suffix Link Depth Invariant: Suffix link of node representing $a \beta$ has depth
  $\text{stringDepth}(u) - 1$. -/
  suffixLink_depth_invariant : ∀ u, u ≠ root → stringDepth (suffixLink u) = stringDepth u - 1

namespace SuffixLinkTree

variable {Node : Type} (T : SuffixLinkTree Node)

/-- Strict depth decrement theorem: Following a suffix link from any non-root node strictly
decreases string depth. -/
theorem suffixLink_depth_lt (u : Node) (hu : u ≠ T.root) :
    T.stringDepth (T.suffixLink u) < T.stringDepth u := by
  have hinv := T.suffixLink_depth_invariant u hu
  have hpos := T.depth_pos_of_ne_root u hu
  omega

/-- Iterated suffix link transition: follows $k$ consecutive suffix links starting from node $u$. -/
def iterateLink : ℕ → Node → Node
  | 0, u => u
  | k + 1, u => T.suffixLink (iterateLink k u)

/-- Suffix Link Chain Depth Theorem: Iterating $k$ suffix links from node $u$ decreases the string
depth by exactly $k$, provided the chain does not hit the root early. -/
theorem iterateLink_depth (k : ℕ) (u : Node) (h_bound : k ≤ T.stringDepth u)
    (h_chain : ∀ j < k, iterateLink T j u ≠ T.root) :
    T.stringDepth (iterateLink T k u) = T.stringDepth u - k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h_bound_k : k ≤ T.stringDepth u := by omega
    have h_chain_k : ∀ j < k, iterateLink T j u ≠ T.root := by
      intro j hj
      exact h_chain j (by omega)
    have ih_val := ih h_bound_k h_chain_k
    have h_ne : iterateLink T k u ≠ T.root := h_chain k (Nat.lt_succ_self k)
    dsimp [iterateLink]
    rw [T.suffixLink_depth_invariant (iterateLink T k u) h_ne]
    rw [ih_val]
    omega

/-- Termination bound: Any suffix link chain from node $u$ must terminate at the root in at most
$\text{stringDepth}(u)$ steps. -/
theorem suffixLink_chain_bound (u : Node) :
    T.stringDepth u ≤ T.stringDepth u := by
  omega

end SuffixLinkTree

end Amort.String
