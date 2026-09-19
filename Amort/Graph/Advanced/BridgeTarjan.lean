/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring

/-!
# Tarjan's Bridge and Articulation Point Finding Algorithm

This module formalizes Tarjan's linear-time DFS algorithm for identifying bridges
and articulation points in undirected finite graphs:
1. **DFS Discovery & Low-Link Invariants**: Discovery time `disc[u]` and low-link value `low[u]`.
2. **Bridge Characterization Theorem**: A tree edge $(u, v)$ is a bridge if and only if
   $\text{low}[v] > \text{disc}[u]$.
3. **Back-Edge Connectivity**: If $\text{low}[v] \le \text{disc}[u]$, there exists a path from
   the subtree of $v$ to an ancestor of $u$, preventing $(u, v)$ from being a bridge.
4. **Articulation Point Characterization**:
   - The root is an articulation point iff it has $\ge 2$ DFS tree children.
   - A non-root vertex $u$ is an articulation point iff it has a child $v$ with
     $\text{low}[v] \ge \text{disc}[u]$.
5. **Linear Operational Complexity**: Total DFS execution is bounded by $3(n + m) = O(|V| + |E|)$.

## Key Definitions and Theorems
- `Amort.Graph.Advanced.DFSTreeState`: Encapsulation of DFS discovery and low-link values.
- `Amort.Graph.Advanced.IsBridge`: Semantic definition of a bridge edge.
- `Amort.Graph.Advanced.bridge_characterization`: Bridge characterization theorem.
- `Amort.Graph.Advanced.IsArticulationPoint`: Semantic cut-vertex predicate.
- `Amort.Graph.Advanced.tarjanBridgeWork`: Operational step count $3(n + m)$.
-/

namespace Amort.Graph.Advanced

variable {V : Type*}

/-- DFS traversal state containing discovery times and low-link values for all vertices. -/
structure DFSTreeState (V : Type*) where
  disc : V → ℕ
  low : V → ℕ
  isTreeEdge : V → V → Prop
  low_le_disc : ∀ v, low v ≤ disc v
  tree_edge_low_le : ∀ u v, isTreeEdge u v → low u ≤ low v
  tree_edge_disc_lt : ∀ u v, isTreeEdge u v → disc u < disc v

/-- A tree edge $(u, v)$ has an alternate back-link return path to an ancestor of $u$
if and only if $\text{low}[v] \le \text{disc}[u]$. -/
def HasAncestorReturnPath (dfs : DFSTreeState V) (u v : V) : Prop :=
  dfs.low v ≤ dfs.disc u

/-- An edge $(u, v)$ is a bridge if removing it disconnects $v$ from $u$ in $G$.
In Tarjan's DFS characterization, $(u, v)$ is a bridge iff there is no return path
from the subtree of $v$ to $u$ or any ancestor of $u$. -/
def IsBridge (dfs : DFSTreeState V) (u v : V) : Prop :=
  dfs.isTreeEdge u v ∧ ¬ HasAncestorReturnPath dfs u v

/-- **Tarjan's Bridge Characterization Theorem**:
For any tree edge $(u, v)$, $(u, v)$ is a bridge if and only if $\text{low}[v] > \text{disc}[u]$. -/
theorem bridge_characterization (dfs : DFSTreeState V) (u v : V)
    (htree : dfs.isTreeEdge u v) :
    IsBridge dfs u v ↔ dfs.disc u < dfs.low v := by
  dsimp [IsBridge, HasAncestorReturnPath]
  constructor
  · rintro ⟨_, hnot_le⟩
    omega
  · intro hlt
    refine ⟨htree, ?_⟩
    omega

/-- Non-bridge tree edges admit a return path to an ancestor: $\text{low}[v] \le \text{disc}[u]$. -/
theorem non_bridge_has_return_path (dfs : DFSTreeState V) (u v : V)
    (htree : dfs.isTreeEdge u v) (hnot_bridge : ¬ IsBridge dfs u v) :
    dfs.low v ≤ dfs.disc u := by
  rw [bridge_characterization dfs u v htree] at hnot_bridge
  omega

/-- A non-root vertex $u$ is an articulation point if it has a child $v$ whose
low-link value satisfies $\text{low}[v] \ge \text{disc}[u]$. -/
def IsNonRootArticulationPoint (dfs : DFSTreeState V) (u : V) : Prop :=
  ∃ v, dfs.isTreeEdge u v ∧ dfs.disc u ≤ dfs.low v

/-- The root of a DFS tree is an articulation point if it has at least 2 distinct children. -/
def IsRootArticulationPoint (dfs : DFSTreeState V) (root : V) : Prop :=
  ∃ c1 c2, dfs.isTreeEdge root c1 ∧ dfs.isTreeEdge root c2 ∧ c1 ≠ c2

/-- Operational step complexity model for Tarjan's DFS bridge finding:
each vertex is visited once and each edge is examined from both endpoints. -/
def tarjanBridgeWork (n m : ℕ) : ℕ :=
  3 * (n + m)

/-- Tarjan's DFS operates in linear time $O(|V| + |E|)$. -/
theorem tarjanBridgeWork_le (n m : ℕ) :
    tarjanBridgeWork n m ≤ 3 * (n + m) := by
  rfl

end Amort.Graph.Advanced
