/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Linear Graph Traversals and the Handshaking Lemma

This module formalizes adjacency list representations of directed graphs on vertex set `Fin n`,
establishes the directed Handshaking Lemma relating degree sums to edge counts, and proves the
$O(|V| + |E|)$ work bound and unweighted shortest-path distance correctness for Breadth-First
Search (BFS).

## Mathematical Architecture

1. **Adjacency Representation & Degrees**:
   A directed graph is represented by an adjacency function `adj : Fin n → List (Fin n)`.
   - Out-degree of vertex $v$: $\text{outdeg}(v) = (adj(v)).length$.
   - Directed edge count: $|E| = \sum_{v \in \text{Fin } n} \text{outdeg}(v)$.
   - Explicit edge list: `edgeList adj = (List.finRange n).flatMap (...)`.

2. **Directed Handshaking Lemma**:
   $$\sum_{v \in \text{Fin } n} \text{outdeg}(v) = (edgeList adj).length = |E|$$

3. **Breadth-First Search (BFS) Work Model**:
   BFS expands a subset of distinct vertices $L \subseteq \text{Fin } n$ ($L.Nodup$).
   For each expanded vertex $u$, 1 unit of queue overhead and $\text{outdeg}(u)$ edge scans
   are performed:
   $$\text{Total Work}(L) = |L| + \sum_{u \in L} \text{outdeg}(u) \le |V| + |E|$$

4. **Unweighted Shortest-Path Correctness**:
   For any valid path $p = [s, \dots, v]$ in `adj`, the distance function satisfies:
   $$dist(v) \le pathEdges(p) = p.length - 1$$
   proving that BFS distance is bounded by the length of every directed path from the source.

## Key Definitions and Theorems
- `Amort.Graph.outdeg`: Out-degree of a vertex in `Fin n`.
- `Amort.Graph.edgeCount`: Sum of out-degrees across all vertices.
- `Amort.Graph.edgeList`: Explicit list of directed edges.
- `Amort.Graph.edgeList_length`: Edge list length equals `edgeCount`.
- `Amort.Graph.handshaking_lemma`: Directed Handshaking Lemma.
- `Amort.Graph.bfsWork`: Total work expanding vertex list $L$.
- `Amort.Graph.bfsWork_le`: Total BFS work is bounded by $|V| + |E|$.
- `Amort.Graph.IsPath`: Path validity predicate in `adj`.
- `Amort.Graph.BFSDistance`: Valid BFS distance specification.
- `Amort.Graph.dist_le_path_from_source`: BFS distance upper-bounded by path length.
-/

open BigOperators

namespace Amort.Graph

variable {n : ℕ}

/-! ### Graph Adjacency and Handshaking Lemma -/

/-- Out-degree of vertex `v` in adjacency representation `adj`. -/
def outdeg (adj : Fin n → List (Fin n)) (v : Fin n) : ℕ := (adj v).length

/-- Total number of directed edges, defined as the sum of out-degrees. -/
def edgeCount (adj : Fin n → List (Fin n)) : ℕ := ∑ v : Fin n, outdeg adj v

/-- Explicit list of directed edges constructed from the adjacency list. -/
def edgeList (adj : Fin n → List (Fin n)) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun u ↦ (adj u).map (fun v ↦ (u, v)))

/-- The length of the explicit edge list equals the sum of out-degrees. -/
theorem edgeList_length (adj : Fin n → List (Fin n)) :
    (edgeList adj).length = edgeCount adj := by
  dsimp [edgeList, edgeCount, outdeg]
  rw [List.length_flatMap]
  simp only [List.length_map]
  have h_nodup : (List.finRange n).Nodup := List.nodup_finRange n
  have h_toFinset : (List.finRange n).toFinset = Finset.univ := List.toFinset_finRange n
  rw [← List.sum_toFinset _ h_nodup, h_toFinset]

/-- Directed Handshaking Lemma: The sum of out-degrees equals the total number of edges. -/
theorem handshaking_lemma (adj : Fin n → List (Fin n)) :
    ∑ v : Fin n, outdeg adj v = (edgeList adj).length := by
  rw [edgeList_length, edgeCount]

/-! ### BFS Work Model and O(|V| + |E|) Bound -/

/-- Total work performed by BFS when expanding vertex sequence `L`:
1 unit per vertex dequeued plus `outdeg u` per edge scanned. -/
def bfsWork (adj : Fin n → List (Fin n)) (L : List (Fin n)) : ℕ :=
  L.length + (L.map (fun u ↦ outdeg adj u)).sum

/-- Distinct vertex list length is bounded by the cardinality of the vertex type. -/
theorem list_length_le_card_of_nodup {α : Type*} [Fintype α]
    (L : List α) (hL : L.Nodup) :
    L.length ≤ Fintype.card α := by
  classical
  have h_card := List.toFinset_card_of_nodup hL
  have h_le : L.toFinset.card ≤ Fintype.card α := Finset.card_le_univ L.toFinset
  omega

/-- Sum over a subset of a finite type is bounded by the sum over the entire type. -/
theorem sum_le_univ_sum {α : Type*} [Fintype α]
    (s : Finset α) (f : α → ℕ) :
    ∑ x ∈ s, f x ≤ ∑ x, f x := by
  classical
  have h_sub : s ⊆ Finset.univ := Finset.subset_univ s
  have h := (Finset.sum_sdiff h_sub (f := f)).symm
  omega

/-- Sum of out-degrees of visited vertices is bounded by total edges. -/
theorem bfsWork_map_sum_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) (hL : L.Nodup) :
    (L.map (fun u ↦ outdeg adj u)).sum ≤ edgeCount adj := by
  dsimp [edgeCount]
  rw [← List.sum_toFinset _ hL]
  exact sum_le_univ_sum L.toFinset (fun u ↦ outdeg adj u)

/-- Total BFS work across any sequence of distinct visited vertices is bounded by `|V| + |E|`. -/
theorem bfsWork_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) (hL : L.Nodup) :
    bfsWork adj L ≤ n + edgeCount adj := by
  dsimp [bfsWork]
  have h1 : L.length ≤ n := by
    have h := list_length_le_card_of_nodup L hL
    simp only [Fintype.card_fin] at h
    exact h
  have h2 := bfsWork_map_sum_le adj L hL
  omega

/-! ### Shortest-Path Distance Correctness -/

/-- Right monotonicity of addition on `WithTop ℕ`. -/
lemma withTop_add_le_add_right (a b c : WithTop ℕ) (h : a ≤ b) : a + c ≤ b + c := by
  cases c with
  | top => simp
  | coe c =>
    cases b with
    | top => simp
    | coe b =>
      cases a with
      | top => cases h
      | coe a =>
        simp only [WithTop.coe_le_coe] at h ⊢
        simp only [← WithTop.coe_add, WithTop.coe_le_coe]
        exact Nat.add_le_add_right h c

/-- A valid directed path in adjacency graph `adj`. -/
def IsPath (adj : Fin n → List (Fin n)) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y ∈ adj x ∧ IsPath adj (y :: rest)

/-- Specification of a valid BFS distance function from source `s`:
source distance is 0, and each edge satisfies the unit relaxation condition. -/
structure BFSDistance (adj : Fin n → List (Fin n)) (s : Fin n) where
  dist : Fin n → WithTop ℕ
  source_zero : dist s = 0
  edge_relax : ∀ u v, v ∈ adj u → dist v ≤ dist u + 1

/-- Inductive bound: distance between endpoints of any path is bounded by the path length. -/
theorem dist_le_path_edges (adj : Fin n → List (Fin n)) (s : Fin n)
    (d : BFSDistance adj s) :
    ∀ (p : List (Fin n)) (u v : Fin n),
      p.head? = some u → p.getLast? = some v → IsPath adj p →
      d.dist v ≤ d.dist u + (p.length - 1 : ℕ)
  | [], _, _, h1, _, _ => by simp at h1
  | [x], u, v, h1, h2, _ => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    simp only [List.getLast?_singleton, Option.some.injEq] at h2
    subst h1 h2
    simp
  | x :: y :: rest, u, v, h1, h2, hpath => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have h_edge : y ∈ adj x := hpath.1
    have h_subpath : IsPath adj (y :: rest) := hpath.2
    have ih := dist_le_path_edges adj s d (y :: rest) y v rfl h2 h_subpath
    have h_relax := d.edge_relax x y h_edge
    have h_len : (x :: y :: rest).length - 1 = (y :: rest).length := by simp
    have h_sublen : (y :: rest).length - 1 + 1 = (y :: rest).length := by
      have : 1 ≤ (y :: rest).length := by simp
      omega
    have h_step : d.dist y + ((y :: rest).length - 1 : ℕ) ≤
        (d.dist x + 1) + ((y :: rest).length - 1 : ℕ) :=
      withTop_add_le_add_right (d.dist y) (d.dist x + 1) ((y :: rest).length - 1 : ℕ) h_relax
    have h_assoc : (d.dist x + 1) + ((y :: rest).length - 1 : ℕ) =
        d.dist x + (1 + ((y :: rest).length - 1 : ℕ)) := add_assoc (d.dist x) 1 _
    have h_cast : (1 : WithTop ℕ) + ((y :: rest).length - 1 : ℕ) =
        ((y :: rest).length : ℕ) := by
      rw [add_comm]
      exact_mod_cast h_sublen
    have h_eq : d.dist x + (1 + ((y :: rest).length - 1 : ℕ)) =
        d.dist x + ((x :: y :: rest).length - 1 : ℕ) := by
      rw [h_cast, h_len]
    exact ih.trans (h_step.trans (h_assoc.trans_le (le_of_eq h_eq)))

/-- Shortest-path distance correctness: BFS distance to `v` is bounded above by
the length of any directed path from source `s` to `v`. -/
theorem dist_le_path_from_source (adj : Fin n → List (Fin n)) (s : Fin n)
    (d : BFSDistance adj s) (p : List (Fin n)) (v : Fin n)
    (h_head : p.head? = some s) (h_last : p.getLast? = some v)
    (h_path : IsPath adj p) :
    d.dist v ≤ (p.length - 1 : ℕ) := by
  have h := dist_le_path_edges adj s d p s v h_head h_last h_path
  rw [d.source_zero, zero_add] at h
  exact h

end Amort.Graph
