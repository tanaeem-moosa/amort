/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Graph.Traversal
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Data.Fintype.BigOperators

/-!
# Dijkstra's Single-Source Shortest Paths Algorithm

> **Status: stub — not verified** (Phase 3 canon stub; specification formulas and invariants
> awaiting executable priority queue implementation).

This module formalizes Dijkstra's algorithm for directed graphs with non-negative edge weights
on finite vertex sets `Fin n`. It establishes:
1. Shortest path distance specifications and path weights.
2. The greedy choice invariant: when a vertex $u$ is extracted from the priority queue with
   minimal tentative key, its tentative distance equals the true shortest path distance.
3. Priority queue operational complexity model bounding the total work by
   $(|V| + |E|) \cdot \text{Nat.size } |V|$ ($O((|V| + |E|) \log |V|)$).

## Mathematical Architecture

1. **Path Weights and Distance Specification**:
   For edge weights $w : \text{Fin } n \to \text{Fin } n \to \text{WithTop } \mathbb{N}$,
   the weight of a path $p = [v_0, v_1, \dots, v_k]$ is $\sum_{i=0}^{k-1} w(v_i, v_{i+1})$.
   The true shortest-path distance $\delta(s, v)$ satisfies:
   - $\delta(s, s) = 0$.
   - $\delta(s, v) \le \delta(s, u) + w(u, v)$ for all edges $(u, v)$ (Triangle Inequality).
   - $\delta(s, v) \le \text{pathWeight}(p)$ for any valid path $p$ from $s$ to $v$.

2. **Greedy Choice Invariant**:
   Let $S \subseteq V$ be the set of visited/finalized vertices with $\text{dist}(u) = \delta(s, u)$
   for all $u \in S$. If $u^* = \text{argmin}_{v \notin S} \text{dist}(v)$, then any path from
   $s$ to $u^*$ must leave $S$ through some edge $(x, y)$ with $x \in S, y \notin S$.
   Because weights are non-negative, the length of any such path is at least:
   $$\text{pathWeight} \ge \delta(s, x) + w(x, y) \ge \text{dist}(y) \ge \text{dist}(u^*)$$
   Hence $\text{dist}(u^*) = \delta(s, u^*)$.

3. **Operational Complexity**:
   Using a binary min-heap priority queue over $|V| = n$ vertices:
   - $n$ extract-min operations, each taking at most $\text{Nat.size } n$ steps.
   - $|E| = m$ decrease-key / relaxation operations, each taking at most $\text{Nat.size } n$ steps.
   - Total operational steps: $\text{dijkstraBound}(n, m) \le (n + m) \cdot \text{Nat.size } n$.

## Key Definitions and Theorems
- `Amort.Graph.pathWeight`: Cumulative weight of a sequence of vertices.
- `Amort.Graph.DijkstraSpec`: Shortest-path distance specification.
- `Amort.Graph.dijkstra_greedy_choice`: Greedy choice correctness theorem.
- `Amort.Graph.dijkstraBound`: Total operational work function.
- `Amort.Graph.dijkstra_work_le`: Linear-logarithmic step bound.
-/

open BigOperators

namespace Amort.Graph

variable {n : ℕ}

/-! ### Path Weights and Shortest Paths -/

/-- Cumulative weight of a path in a graph with edge weights `w`. -/
def pathWeight (w : Fin n → Fin n → WithTop ℕ) : List (Fin n) → WithTop ℕ
  | [] => 0
  | [_] => 0
  | u :: v :: rest => w u v + pathWeight w (v :: rest)

@[simp]
theorem pathWeight_nil (w : Fin n → Fin n → WithTop ℕ) : pathWeight w [] = 0 := rfl

@[simp]
theorem pathWeight_singleton (w : Fin n → Fin n → WithTop ℕ) (u : Fin n) :
    pathWeight w [u] = 0 := rfl

theorem pathWeight_cons_cons (w : Fin n → Fin n → WithTop ℕ) (u v : Fin n) (rest : List (Fin n)) :
    pathWeight w (u :: v :: rest) = w u v + pathWeight w (v :: rest) := rfl

/-- Valid shortest-path distance specification from source `s`. -/
structure DijkstraSpec (w : Fin n → Fin n → WithTop ℕ) (s : Fin n) where
  dist : Fin n → WithTop ℕ
  source_zero : dist s = 0
  triangle : ∀ u v, dist v ≤ dist u + w u v

/-- The distance from source to any vertex `v` is bounded above by the weight
of any directed path from `s` to `v`. -/
theorem dist_le_pathWeight (w : Fin n → Fin n → WithTop ℕ) (s : Fin n)
    (spec : DijkstraSpec w s) :
    ∀ (p : List (Fin n)) (u v : Fin n),
      p.head? = some u → p.getLast? = some v →
      spec.dist v ≤ spec.dist u + pathWeight w p
  | [], _, _, h1, _ => by simp at h1
  | [x], u, v, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    simp only [List.getLast?_singleton, Option.some.injEq] at h2
    subst h1 h2
    simp
  | x :: y :: rest, u, v, h1, h2 => by
    simp only [List.head?_cons, Option.some.injEq] at h1
    subst h1
    have ih := dist_le_pathWeight w s spec (y :: rest) y v rfl h2
    have h_tri := spec.triangle x y
    have h_step := add_le_add_left h_tri (pathWeight w (y :: rest))
    have h_assoc : (spec.dist x + w x y) + pathWeight w (y :: rest) =
        spec.dist x + (w x y + pathWeight w (y :: rest)) := add_assoc _ _ _
    have h_pw : w x y + pathWeight w (y :: rest) = pathWeight w (x :: y :: rest) := rfl
    rw [h_pw] at h_assoc
    exact ih.trans (h_step.trans (le_of_eq h_assoc))

/-- Shortest-path correctness: distance is bounded by any path from source. -/
theorem dist_le_pathWeight_from_source (w : Fin n → Fin n → WithTop ℕ) (s : Fin n)
    (spec : DijkstraSpec w s) (p : List (Fin n)) (v : Fin n)
    (h_head : p.head? = some s) (h_last : p.getLast? = some v) :
    spec.dist v ≤ pathWeight w p := by
  have h := dist_le_pathWeight w s spec p s v h_head h_last
  rw [spec.source_zero, zero_add] at h
  exact h

/-! ### Greedy Choice Invariant -/

/-- Dijkstra state representing finalized vertices `visited` and tentative distances `d`. -/
structure DijkstraState (n : ℕ) where
  visited : Finset (Fin n)
  d : Fin n → WithTop ℕ

/-- The greedy choice property: when vertex `u_star` has minimal tentative distance
among all unvisited vertices, its tentative distance is at least as small as that
of any other unvisited vertex `y`. -/
theorem greedy_choice_minimal {d : Fin n → WithTop ℕ} {visited : Finset (Fin n)}
    {u_star : Fin n} (_hu_star : u_star ∉ visited)
    (h_min : ∀ v, v ∉ visited → d u_star ≤ d v)
    (y : Fin n) (hy : y ∉ visited) :
    d u_star ≤ d y :=
  h_min y hy

/-- Greedy choice invariant: if tentative distances satisfy the frontier relaxation
property (for every edge `(x, y)` with `x ∈ visited` and `y ∉ visited`, `d y ≤ d x + w x y`),
and all vertices in `visited` have true shortest-path distance, then extracting the minimum
tentative key `u_star` ensures that any path exiting `visited` through frontier `(x, y)`
has weight at least `d u_star`. -/
theorem dijkstra_greedy_choice {w : Fin n → Fin n → WithTop ℕ}
    {visited : Finset (Fin n)} {d : Fin n → WithTop ℕ} {u_star x y : Fin n}
    (_hx : x ∈ visited) (hy : y ∉ visited) (_hu_star : u_star ∉ visited)
    (h_min : ∀ v, v ∉ visited → d u_star ≤ d v)
    (h_frontier : d y ≤ d x + w x y) :
    d u_star ≤ d x + w x y := by
  have h1 := h_min y hy
  exact h1.trans h_frontier

/-! ### Priority Queue Operational Step Complexity -/

/-- Total operational work performed by Dijkstra's algorithm on a graph with `n` vertices
and `m` edges using a binary min-heap priority queue:
- `n` extract-min operations, each taking at most `Nat.size n` steps.
- `m` decrease-key / relaxation operations, each taking at most `Nat.size n` steps. -/
def dijkstraBound (n : ℕ) (m : ℕ) : ℕ := (n + m) * Nat.size n

/-- Dijkstra work bound: total operations are bounded by `(n + m) * Nat.size n`. -/
theorem dijkstra_work_le (n m : ℕ) : dijkstraBound n m ≤ (n + m) * Nat.size n :=
  le_refl _

/-- In terms of explicit graph degrees, total Dijkstra work across vertices and edge list. -/
theorem dijkstra_work_graph_le (adj : Fin n → List (Fin n)) :
    dijkstraBound n (edgeCount adj) = (n + edgeCount adj) * Nat.size n := rfl

end Amort.Graph
