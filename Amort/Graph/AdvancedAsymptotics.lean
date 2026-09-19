/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Dijkstra
import Amort.Graph.MaxFlow
import Amort.Graph.SCC
import Amort.Graph.Eulerian
import Amort.Graph.Prim
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.Prod
import Mathlib.Tactic.Ring

/-!
# Asymptotic Complexity Bridges for Advanced Graph Algorithms

This module connects the concrete operational step bounds for advanced graph algorithms
to Mathlib's `Mathlib.Analysis.Asymptotics.IsBigO` asymptotic framework:
- Dijkstra's Single-Source Shortest Paths ($O((|V| + |E|) \log |V|)$).
- Edmonds-Karp Network Flow & Augmenting Paths ($O(|V| \cdot |E|^2)$).
- Strongly Connected Components via Kosaraju's Algorithm ($O(|V| + |E|)$).
- Eulerian Circuits via Hierholzer's Cycle Splicing Algorithm ($O(|V| + |E|)$).
- Prim's Minimum Spanning Tree Algorithm ($O(|E| \log |V|)$).

## Key Definitions and Theorems
- `Amort.Graph.isBigO_dijkstraWork_atTop`: Dijkstra $O((|V| + |E|) \log |V|)$ in `IsBigO`.
- `Amort.Graph.isBigO_edmondsKarpWork_atTop`: Edmonds-Karp $O(|V| \cdot |E|^2)$ in `IsBigO`.
- `Amort.Graph.isBigO_kosarajuWork_atTop`: Kosaraju linear $O(|V| + |E|)$ in `IsBigO`.
- `Amort.Graph.isBigO_hierholzerWork_atTop`: Hierholzer linear $O(|V| + |E|)$ in `IsBigO`.
- `Amort.Graph.isBigO_primWork_atTop`: Prim $O((|V| + |E|) \log |V|)$ in `IsBigO`.
- `Amort.Graph.isBigO_primWork_connected`: Prim $O(|E| \log |V|)$ on connected graphs.
-/

open Asymptotics

namespace Amort.Graph

/-! ### Dijkstra's Algorithm Asymptotics -/

/-- Dijkstra's algorithm priority queue operational complexity is asymptotically
$O((|V| + |E|) \log |V|)$ under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_dijkstraWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((dijkstraWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ ((((p.1 + p.2) * Nat.size p.1 : ℕ) : ℝ))) :=
  isBigO_refl _ _

/-! ### Network Flow & Edmonds-Karp Asymptotics -/

/-- Edmonds-Karp augmenting path operational complexity is asymptotically
$O(|V| \cdot |E|^2)$ under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_edmondsKarpWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((edmondsKarpWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 * p.2 ^ 2 : ℕ) : ℝ))) :=
  isBigO_refl _ _

/-! ### Strongly Connected Components Asymptotics -/

/-- Kosaraju's two-pass DFS SCC decomposition is asymptotically $O(|V| + |E|)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_kosarajuWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((kosarajuWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 + p.2 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  rintro ⟨n, m⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [kosarajuWork]
  have h : ((2 * (n + m) : ℕ) : ℝ) = 2 * ((n + m : ℕ) : ℝ) := by push_cast; ring
  rw [h]

/-! ### Eulerian Circuits Asymptotics -/

/-- Hierholzer's cycle splicing algorithm is asymptotically $O(|V| + |E|)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_hierholzerWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((hierholzerWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ (((p.1 + p.2 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 2 ?_
  apply Filter.Eventually.of_forall
  rintro ⟨n, m⟩
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  dsimp [hierholzerWork]
  have h : ((2 * (n + m) : ℕ) : ℝ) = 2 * ((n + m : ℕ) : ℝ) := by push_cast; ring
  rw [h]

/-! ### Prim's Minimum Spanning Tree Asymptotics -/

/-- Prim's MST operational complexity is asymptotically $O((|V| + |E|) \log |V|)$
under `Filter.atTop` on $\mathbb{N} \times \mathbb{N}$. -/
theorem isBigO_primWork_atTop :
    (fun (p : ℕ × ℕ) ↦ (((primWork p.1 p.2 : ℕ) : ℝ))) =O[Filter.atTop]
      (fun p ↦ ((((p.1 + p.2) * Nat.size p.1 : ℕ) : ℝ))) :=
  isBigO_refl _ _

/-- On connected graphs where $|V| \le |E| + 1$, Prim's MST complexity is
asymptotically $O(|E| \log |V|)$. -/
theorem isBigO_primWork_connected (l : Filter (ℕ × ℕ))
    (h_conn : ∀ᶠ p in l, p.1 ≤ p.2 + 1) :
    (fun (p : ℕ × ℕ) ↦ (((primWork p.1 p.2 : ℕ) : ℝ))) =O[l]
      (fun p ↦ ((((2 * p.2 + 1) * Nat.size p.1 : ℕ) : ℝ))) := by
  refine IsBigO.of_bound 1 ?_
  filter_upwards [h_conn] with ⟨n, m⟩ h_c
  simp only [Real.norm_eq_abs, Nat.abs_cast, one_mul]
  have h := prim_work_le n m h_c
  exact_mod_cast h

end Amort.Graph
