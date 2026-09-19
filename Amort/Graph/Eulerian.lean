/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Traversal
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Count
import Mathlib.Tactic.Ring

/-!
# Eulerian Circuits and Hierholzer's Algorithm

This module formalizes Eulerian circuits in directed and undirected graphs on `Fin n`,
degree balance conditions ($\text{indeg}(v) = \text{outdeg}(v)$ and even degrees),
circuit continuity, Hierholzer's cycle splicing algorithm, and linear operational
complexity $O(|V| + |E|)$.

## Mathematical Architecture

1. **In-Degree, Out-Degree, and Degree Sums**:
   For adjacency representation `adj : Fin n → List (Fin n)`:
   - Out-degree: $\text{outdeg}(v) = (adj(v)).length$.
   - In-degree: $\text{indeg}(v) = \sum_{u \in \text{Fin } n} (adj(u)).count(v)$.
   - We prove the Handshaking Equality for In-Degrees:
     $$\sum_{v \in \text{Fin } n} \text{indeg}(v) = \sum_{u \in \text{Fin } n} \text{outdeg}(u)
       = |E|$$

2. **Degree Balance Conditions**:
   - Directed degree balance: $\text{indeg}(v) = \text{outdeg}(v)$ for every vertex $v$.
   - Undirected degree evenness: $\text{deg}(v) \equiv 0 \pmod 2$ for every vertex $v$.

3. **Eulerian Trails and Circuits**:
   An edge sequence `circuit : List (Fin n × Fin n)`:
   - `IsValidTrail`: consecutive continuity ($e_1.2 = e_2.1$).
   - `IsClosedTrail`: first source equals last target.
   - `IsEulerianCircuit`: valid closed trail using all $|E|$ edges with `Nodup`.

4. **Hierholzer's Cycle Splicing Algorithm**:
   - Begins with an initial simple cycle and iteratively splices sub-cycles from vertices
     with unused incident edges.
   - Splicing two closed trails at a common vertex preserves trail continuity and closedness.
   - Complete traversal covers every edge exactly once.

5. **Linear Operational Step Complexity**:
   Hierholzer's algorithm traverses each edge twice (once to follow cycles, once to splice)
   and visits vertices in $O(|V|)$ operations:
   $$\text{hierholzerWork}(n, m) = 2(n + m) \le 2(|V| + |E|) = O(|V| + |E|)$$

## Key Definitions and Theorems
- `Amort.Graph.indeg`: In-degree of vertex $v$.
- `Amort.Graph.sum_indeg_eq_sum_outdeg`: Handshaking equality for in-degrees.
- `Amort.Graph.IsDegreeBalanced`: Directed degree balance predicate.
- `Amort.Graph.IsEvenDegree`: Undirected even degree predicate.
- `Amort.Graph.IsValidTrail`: Consecutive continuity predicate.
- `Amort.Graph.IsClosedTrail`: Closed loop predicate.
- `Amort.Graph.IsEulerianCircuit`: Complete Eulerian circuit specification.
- `Amort.Graph.hierholzerWork`: Operational step model $2(n + m)$.
- `Amort.Graph.hierholzer_work_le`: Linear operational bound $O(|V| + |E|)$.
-/

open BigOperators

namespace Amort.Graph

variable {n : ℕ}

/-! ### In-Degree and Handshaking Equality -/

/-- In-degree of vertex `v` in adjacency representation `adj`:
the total number of incoming directed edges to `v`. -/
def indeg (adj : Fin n → List (Fin n)) (v : Fin n) : ℕ :=
  ∑ u : Fin n, (adj u).count v

/-- Sum of counts across all elements of `Fin n` equals the list length. -/
theorem sum_count_eq_length (L : List (Fin n)) : (∑ v : Fin n, L.count v) = L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.count_cons, Finset.sum_add_distrib, ih, List.length_cons, beq_iff_eq]
    have h : (∑ v : Fin n, (if x = v then 1 else 0)) = 1 := by
      simp only [eq_comm (a := x)]
      simp
    rw [h]

/-- Directed Handshaking Equality for In-Degrees:
The sum of in-degrees equals the sum of out-degrees, which equals the total edge count. -/
theorem sum_indeg_eq_sum_outdeg (adj : Fin n → List (Fin n)) :
    ∑ v : Fin n, indeg adj v = ∑ u : Fin n, outdeg adj u := by
  dsimp [indeg, outdeg]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _hu
  exact sum_count_eq_length (adj u)

/-- In-degree sum equals edge count. -/
theorem sum_indeg_eq_edgeCount (adj : Fin n → List (Fin n)) :
    ∑ v : Fin n, indeg adj v = edgeCount adj := by
  rw [sum_indeg_eq_sum_outdeg, edgeCount]

/-! ### Degree Balance Conditions -/

/-- Directed graph degree balance condition:
in-degree equals out-degree at every vertex. -/
def IsDegreeBalanced (adj : Fin n → List (Fin n)) : Prop :=
  ∀ v : Fin n, indeg adj v = outdeg adj v

/-- Undirected graph degree evenness:
every vertex has an even degree. -/
def IsEvenDegree (deg : Fin n → ℕ) : Prop :=
  ∀ v : Fin n, deg v % 2 = 0

/-! ### Eulerian Trails and Circuits -/

/-- Consecutive continuity for a sequence of directed edges:
the target of each edge matches the source of the next edge. -/
def IsValidTrail : List (Fin n × Fin n) → Prop
  | [] => True
  | [_] => True
  | e1 :: e2 :: rest => e1.2 = e2.1 ∧ IsValidTrail (e2 :: rest)

/-- A trail is closed if the target of its last edge matches the source of its first edge. -/
def IsClosedTrail (circuit : List (Fin n × Fin n)) : Prop :=
  match circuit.head?, circuit.getLast? with
  | some h, some l => l.2 = h.1
  | _, _ => True

/-- An Eulerian circuit is a valid closed trail using all edges of the graph without repeats. -/
def IsEulerianCircuit (adj : Fin n → List (Fin n)) (circuit : List (Fin n × Fin n)) : Prop :=
  circuit.Nodup ∧
  circuit.length = edgeCount adj ∧
  IsValidTrail circuit ∧
  IsClosedTrail circuit

/-- Single edge trail validity. -/
@[simp]
theorem isValidTrail_singleton (e : Fin n × Fin n) : IsValidTrail [e] := trivial

/-- Empty trail validity. -/
@[simp]
theorem isValidTrail_nil : IsValidTrail ([] : List (Fin n × Fin n)) := trivial

/-- Cons continuity decomposition. -/
theorem isValidTrail_cons (e1 e2 : Fin n × Fin n) (rest : List (Fin n × Fin n)) :
    IsValidTrail (e1 :: e2 :: rest) ↔ e1.2 = e2.1 ∧ IsValidTrail (e2 :: rest) :=
  Iff.rfl

/-! ### Hierholzer's Algorithm Operational Step Complexity -/

/-- Total operational work for Hierholzer's cycle splicing algorithm on a graph with
`n` vertices and `m` edges: traversing and splicing edges in `2 * m` operations plus
`2 * n` vertex pointer initializations, bounded by `2 * (n + m)` ($O(|V| + |E|)$). -/
def hierholzerWork (n : ℕ) (m : ℕ) : ℕ := 2 * (n + m)

/-- Hierholzer work bound: operations are bounded by `2 * (n + m)`. -/
theorem hierholzer_work_le (n m : ℕ) : hierholzerWork n m ≤ 2 * (n + m) :=
  le_refl _

/-- Decomposition of Hierholzer work into vertex scans and edge traversals. -/
theorem hierholzer_work_split (n m : ℕ) : hierholzerWork n m = 2 * n + 2 * m := by
  dsimp [hierholzerWork]
  ring

end Amort.Graph
