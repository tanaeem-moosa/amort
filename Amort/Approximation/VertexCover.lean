/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Complexity.KarpReductions
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Union
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring

/-!
# 2-Approximation for Minimum Vertex Cover via Maximal Matching

> **Status: stub — not verified** (Phase 4 canon stub; matching lower bound and 2-approximation
> ratio are proven, but operational greedy edge selection is a specification stub).

This module formalizes the classical 2-approximation algorithm for the Minimum Vertex Cover
problem on finite undirected graphs using greedy maximal matchings:
1. **Matchings**: A collection of disjoint edges in a simple graph.
2. **Matching Endpoints**: The set of vertices incident to edges of the matching, with
   cardinality exactly $2|M|$.
3. **Lower Bound Lemma**: For any matching $M$ and any vertex cover $C^*$, $|M| \le |C^*|$.
4. **Maximal Matching Cover**: A maximal matching's endpoints form a valid vertex cover.
5. **2-Approximation Ratio**: The resulting cover $C$ satisfies $|C| = 2|M| \le 2|C^*|$.
6. **Linear Operational Complexity**: Edge-scanning greedy selection operates in $O(|V| + |E|)$.

## Key Definitions and Theorems
- `Amort.Approximation.IsMatching`: Matching predicate on edge sets.
- `Amort.Approximation.matchingVertices`: Endpoint set of a matching.
- `Amort.Approximation.matching_card_endpoints`: $|V(M)| = 2|M|$.
- `Amort.Approximation.matching_card_le_vertexCover`: $|M| \le |C|$ for any vertex cover $C$.
- `Amort.Approximation.IsMaximalMatching`: Maximality predicate.
- `Amort.Approximation.maximal_matching_isVertexCover`: Endpoint set forms a vertex cover.
- `Amort.Approximation.vertex_cover_approx_ratio`: $|C| \le 2|C^*|$ approximation ratio.
- `Amort.Approximation.vertexCoverBound`: Operational step count $2(n + m)$.
-/

namespace Amort.Approximation

open Amort.Complexity

variable {V : Type*}

/-- Every edge in a graph has distinct endpoints. -/
lemma edge_endpoints_ne (G : SimpleGraph V) {u v : V} (h : G.Adj u v) : u ≠ v := by
  intro heq
  subst heq
  exact G.loopless u h

variable [DecidableEq V]

/-- A matching `M` in graph `G` is a set of directed pairs representing disjoint edges. -/
def IsMatching (G : SimpleGraph V) (M : Finset (V × V)) : Prop :=
  (∀ e ∈ M, G.Adj e.1 e.2) ∧
  (∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
    Disjoint ({e1.1, e1.2} : Finset V) ({e2.1, e2.2} : Finset V))

/-- The set of endpoint vertices incident to edges in matching `M`. -/
def matchingVertices (M : Finset (V × V)) : Finset V :=
  M.biUnion (fun e ↦ {e.1, e.2})

/-- For any matching `M`, the number of endpoint vertices is exactly `2 * M.card`. -/
theorem matching_card_endpoints {G : SimpleGraph V} {M : Finset (V × V)}
    (hM : IsMatching G M) :
    (matchingVertices M).card = 2 * M.card := by
  rw [matchingVertices]
  rw [Finset.card_biUnion]
  · have h_each : ∀ e ∈ M, ({e.1, e.2} : Finset V).card = 2 := by
      intro e he
      have hadj := hM.1 e he
      have hne := edge_endpoints_ne G hadj
      exact Finset.card_pair hne
    rw [Finset.sum_congr rfl h_each]
    simp [mul_comm]
  · intro e1 he1 e2 he2 hne
    exact hM.2 e1 he1 e2 he2 hne

/-- Every edge in a matching intersects any vertex cover in at least one vertex. -/
lemma edge_inter_cover_nonempty {G : SimpleGraph V} {C : Finset V}
    (hC : G.IsVertexCover C) {e : V × V} {M : Finset (V × V)}
    (hM : IsMatching G M) (he : e ∈ M) :
    1 ≤ (({e.1, e.2} : Finset V) ∩ C).card := by
  have hadj := hM.1 e he
  have hcov := hC e.1 e.2 hadj
  cases hcov with
  | inl h1 =>
    have hmem : e.1 ∈ ({e.1, e.2} : Finset V) ∩ C := by
      rw [Finset.mem_inter]
      exact ⟨Finset.mem_insert_self e.1 _, h1⟩
    exact Finset.card_pos.mpr ⟨e.1, hmem⟩
  | inr h2 =>
    have hmem : e.2 ∈ ({e.1, e.2} : Finset V) ∩ C := by
      rw [Finset.mem_inter]
      refine ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self e.2), h2⟩
    exact Finset.card_pos.mpr ⟨e.2, hmem⟩

/-- **Lower Bound Lemma**: The size of any matching is bounded by the size of any vertex cover.
In particular, `M.card ≤ OPT`. -/
theorem matching_card_le_vertexCover {G : SimpleGraph V} {M : Finset (V × V)}
    (hM : IsMatching G M) {C : Finset V} (hC : G.IsVertexCover C) :
    M.card ≤ C.card := by
  have h_sum_le : M.card ≤ ∑ e ∈ M, (({e.1, e.2} : Finset V) ∩ C).card := by
    have h_one : M.card = ∑ e ∈ M, 1 := by simp
    rw [h_one]
    apply Finset.sum_le_sum
    intro e he
    exact edge_inter_cover_nonempty hC hM he
  have h_disj : ∀ e1 ∈ M, ∀ e2 ∈ M, e1 ≠ e2 →
      Disjoint (({e1.1, e1.2} : Finset V) ∩ C) (({e2.1, e2.2} : Finset V) ∩ C) := by
    intro e1 he1 e2 he2 hne
    have hdisj_endpoints := hM.2 e1 he1 e2 he2 hne
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left hdisj_endpoints
  have h_union_card : (∑ e ∈ M, (({e.1, e.2} : Finset V) ∩ C).card) =
      (M.biUnion (fun e ↦ ({e.1, e.2} : Finset V) ∩ C)).card := by
    symm
    apply Finset.card_biUnion
    intro e1 he1 e2 he2 hne
    exact h_disj e1 he1 e2 he2 hne
  have h_sub : (M.biUnion (fun e ↦ ({e.1, e.2} : Finset V) ∩ C)) ⊆ C := by
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨e, -, hmem⟩
    exact (Finset.mem_inter.mp hmem).2
  have h_card_sub := Finset.card_le_card h_sub
  omega

/-- A matching `M` is maximal if every edge in `G` has at least one endpoint in `M`. -/
def IsMaximalMatching (G : SimpleGraph V) (M : Finset (V × V)) : Prop :=
  IsMatching G M ∧
  ∀ u v, G.Adj u v → u ∈ matchingVertices M ∨ v ∈ matchingVertices M

/-- The endpoints of a maximal matching form a valid vertex cover. -/
theorem maximal_matching_isVertexCover {G : SimpleGraph V} {M : Finset (V × V)}
    (hM : IsMaximalMatching G M) :
    G.IsVertexCover (matchingVertices M) := by
  intro u v hadj
  exact hM.2 u v hadj

/-- **2-Approximation Ratio Theorem**:
The vertex cover `C = matchingVertices M` generated by a maximal matching `M` satisfies:
`|C| = 2 * |M| ≤ 2 * |C^*|` for any vertex cover `C^*`. -/
theorem vertex_cover_approx_ratio {G : SimpleGraph V} {M : Finset (V × V)}
    (hM : IsMaximalMatching G M) {CStar : Finset V} (hCStar : G.IsVertexCover CStar) :
    (matchingVertices M).card ≤ 2 * CStar.card := by
  rw [matching_card_endpoints hM.1]
  have h_le := matching_card_le_vertexCover hM.1 hCStar
  omega

/-- Operational step model for greedy maximal matching vertex cover:
scanning $|E| = m$ edges and recording endpoints across $|V| = n$ vertices. -/
def vertexCoverBound (n m : ℕ) : ℕ :=
  2 * (n + m)

/-- The greedy maximal matching vertex cover algorithm operates in linear time $O(|V| + |E|)$. -/
theorem vertexCoverWork_le (n m : ℕ) :
    vertexCoverBound n m ≤ 2 * (n + m) := by
  rfl

end Amort.Approximation
