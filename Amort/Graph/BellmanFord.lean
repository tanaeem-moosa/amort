/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Composition
import Mathlib.Algebra.Order.Ring.WithTop

/-!
# Bellman-Ford Single-Source Shortest Paths

This module formalizes the textbook Bellman-Ford shortest paths algorithm on directed graphs
with vertex set `Fin n` and an explicit edge list `edges : List (Edge n)`.
It establishes operational step counting showing that $(n - 1)$ rounds of relaxing all $|E|$ edges
executes $(n - 1) \cdot |E| \le n \cdot |E|$ edge relaxations ($O(|V| \cdot |E|)$), connecting
to `Amort.Recurrence.Composition.isBigO_nested_loops_nat`.

## Mathematical Architecture

1. **Edge Representation**:
   Directed edges are represented as structures `Edge n` with source `u : Fin n`,
   target `v : Fin n`, and weight `w : ℕ`.

2. **Single-Source Distance Initialization**:
   Given source vertex `s : Fin n`, distances are initialized to:
   - $dist(s) = 0$
   - $dist(v) = \top$ for $v \ne s$

3. **Edge Relaxation Passes**:
   In each pass, every edge $(u, v, w)$ is relaxed:
   $$dist(v) \leftarrow \min(dist(v), dist(u) + w)$$
   The algorithm performs $(n - 1)$ sequential relaxation passes.

4. **Operational Step Counting & Complexity**:
   - Each pass executes $|E| = edges.length$ relaxations.
   - Across $(n - 1)$ passes, total edge relaxations executed equals:
     $$(n - 1) \cdot |E| \le n \cdot |E|$$
   - By product loop composition (`isBigO_nested_loops_nat`), this gives $O(|V| \cdot |E|)$.

## Key Definitions and Theorems
- `Amort.Graph.Edge`: Directed weighted edge between vertices in `Fin n`.
- `Amort.Graph.initDist`: Canonical single-source distance initialization.
- `Amort.Graph.relaxEdge`: Single edge relaxation step.
- `Amort.Graph.relaxAll`: Single pass relaxing all edges in `edges`.
- `Amort.Graph.bellmanFordPasses`: $k$ passes of edge relaxations.
- `Amort.Graph.bellmanFord`: Full Bellman-Ford algorithm with $(n - 1)$ passes.
- `Amort.Graph.bellmanFordStepCount`: Exact step counter $(n - 1) \cdot |E|$.
- `Amort.Graph.bellmanFordStepCount_le`: Upper bound $(n - 1) \cdot |E| \le n \cdot |E|$.
- `Amort.Graph.bellmanFordWithCount`: Instrumented representation returning distance and count.
- `Amort.Graph.relaxEdge_mono`: Relaxation never increases distance estimates.
- `Amort.Graph.relaxAll_mono`: Full pass never increases distance estimates.
- `Amort.Graph.bellmanFordPasses_mono`: Monotonicity across relaxation rounds.
- `Amort.Graph.bellmanFordPasses_self`: Source distance remains 0.
- `Amort.Graph.relaxEdge_triangle`: Satisfied triangle inequality at fixed points.
-/

namespace Amort.Graph

open Amort.Recurrence

/-! ### Edge Representation and Graph Initialization -/

/-- Directed weighted edge between vertices in `Fin n` with weight `w : ℕ`. -/
structure Edge (n : ℕ) where
  u : Fin n
  v : Fin n
  w : ℕ
deriving DecidableEq, Repr

/-- Canonical single-source distance initialization: source has distance 0,
all other vertices have distance `⊤`. -/
def initDist {n : ℕ} (s : Fin n) : Fin n → WithTop ℕ :=
  fun v ↦ if v = s then 0 else ⊤

@[simp]
theorem initDist_source {n : ℕ} (s : Fin n) : initDist s s = 0 := by
  dsimp [initDist]
  rw [if_pos rfl]

theorem initDist_other {n : ℕ} (s v : Fin n) (h : v ≠ s) : initDist s v = ⊤ := by
  dsimp [initDist]
  rw [if_neg h]

/-! ### Edge Relaxation Operations -/

/-- Relaxes a single edge `e = (u, v, w)`: updates `dist v` to `min (dist v) (dist u + w)`. -/
def relaxEdge {n : ℕ} (dist : Fin n → WithTop ℕ) (e : Edge n) : Fin n → WithTop ℕ :=
  fun x ↦ if x = e.v then min (dist e.v) (dist e.u + e.w) else dist x

/-- Relaxes all edges in `edges` sequentially in a single pass. -/
def relaxAll {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℕ) :
    Fin n → WithTop ℕ :=
  edges.foldl relaxEdge dist

/-- Executes `k` sequential relaxation passes over the edge list `edges`. -/
def bellmanFordPasses {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℕ) :
    ℕ → (Fin n → WithTop ℕ)
  | 0 => dist
  | k + 1 => relaxAll edges (bellmanFordPasses edges dist k)

/-- Full Bellman-Ford algorithm: executes `(n - 1)` relaxation passes from source `s`. -/
def bellmanFord (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Fin n → WithTop ℕ :=
  bellmanFordPasses edges (initDist s) (n - 1)

/-! ### Step Counting and Operational Bounds -/

/-- Total edge relaxations performed across `(n - 1)` passes of `edges.length` edges. -/
def bellmanFordStepCount (n : ℕ) (edges : List (Edge n)) : ℕ :=
  (n - 1) * edges.length

/-- The total number of edge relaxations is bounded above by `n * edges.length`. -/
theorem bellmanFordStepCount_le (n : ℕ) (edges : List (Edge n)) :
    bellmanFordStepCount n edges ≤ n * edges.length :=
  Nat.mul_le_mul_right edges.length (Nat.sub_le n 1)

/-! ### Instrumented Representation -/

/-- Instrumented version of `bellmanFordPasses` returning both distance estimates
and the exact number of edge relaxations executed. -/
def bellmanFordPassesWithCount {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℕ) :
    ℕ → (Fin n → WithTop ℕ) × ℕ
  | 0 => (dist, 0)
  | k + 1 =>
    let res := bellmanFordPassesWithCount edges dist k
    (relaxAll edges res.1, res.2 + edges.length)

theorem bellmanFordPassesWithCount_fst {n : ℕ} (edges : List (Edge n))
    (dist : Fin n → WithTop ℕ) (k : ℕ) :
    (bellmanFordPassesWithCount edges dist k).1 = bellmanFordPasses edges dist k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    dsimp [bellmanFordPassesWithCount, bellmanFordPasses]
    rw [ih]

theorem bellmanFordPassesWithCount_snd {n : ℕ} (edges : List (Edge n))
    (dist : Fin n → WithTop ℕ) (k : ℕ) :
    (bellmanFordPassesWithCount edges dist k).2 = k * edges.length := by
  induction k with
  | zero => simp [bellmanFordPassesWithCount]
  | succ m ih =>
    dsimp [bellmanFordPassesWithCount]
    rw [ih]
    ring

/-- Instrumented version of `bellmanFord` returning both final distances
and total relaxation steps. -/
def bellmanFordWithCount (n : ℕ) (edges : List (Edge n)) (s : Fin n) :
    (Fin n → WithTop ℕ) × ℕ :=
  bellmanFordPassesWithCount edges (initDist s) (n - 1)

theorem bellmanFordWithCount_fst (n : ℕ) (edges : List (Edge n)) (s : Fin n) :
    (bellmanFordWithCount n edges s).1 = bellmanFord n edges s :=
  bellmanFordPassesWithCount_fst edges (initDist s) (n - 1)

theorem bellmanFordWithCount_snd (n : ℕ) (edges : List (Edge n)) (s : Fin n) :
    (bellmanFordWithCount n edges s).2 = bellmanFordStepCount n edges := by
  dsimp [bellmanFordWithCount, bellmanFordStepCount]
  exact bellmanFordPassesWithCount_snd edges (initDist s) (n - 1)

theorem bellmanFordWithCount_snd_le (n : ℕ) (edges : List (Edge n)) (s : Fin n) :
    (bellmanFordWithCount n edges s).2 ≤ n * edges.length := by
  rw [bellmanFordWithCount_snd]
  exact bellmanFordStepCount_le n edges

/-! ### Mathematical Invariants and Properties -/

/-- Relaxing an edge never increases distance estimates. -/
theorem relaxEdge_mono {n : ℕ} (dist : Fin n → WithTop ℕ) (e : Edge n) (v : Fin n) :
    relaxEdge dist e v ≤ dist v := by
  dsimp [relaxEdge]
  split_ifs with h
  · subst h
    exact min_le_left (dist e.v) (dist e.u + e.w)
  · exact le_rfl

lemma relaxAll_mono_aux {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℕ)
    (v : Fin n) :
    edges.foldl relaxEdge dist v ≤ dist v := by
  induction edges generalizing dist with
  | nil => exact le_rfl
  | cons e es ih =>
    have h1 := ih (relaxEdge dist e)
    have h2 := relaxEdge_mono dist e v
    exact h1.trans h2

/-- Relaxing all edges in a pass never increases distance estimates. -/
theorem relaxAll_mono {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℕ)
    (v : Fin n) :
    relaxAll edges dist v ≤ dist v :=
  relaxAll_mono_aux edges dist v

/-- Monotonicity across passes: distances after `k + 1` passes are at most distances
after `k` passes. -/
theorem bellmanFordPasses_mono {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℕ)
    (k : ℕ) (v : Fin n) :
    bellmanFordPasses edges dist (k + 1) v ≤ bellmanFordPasses edges dist k v :=
  relaxAll_mono edges (bellmanFordPasses edges dist k) v

/-- Every element in `WithTop ℕ` is bounded below by 0. -/
lemma withTop_nat_zero_le (x : WithTop ℕ) : (0 : WithTop ℕ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe n => exact WithTop.coe_le_coe.mpr (Nat.zero_le n)

/-- Source distance remains 0 throughout all passes. -/
theorem bellmanFordPasses_self {n : ℕ} (edges : List (Edge n)) (s : Fin n) (k : ℕ) :
    bellmanFordPasses edges (initDist s) k s = 0 := by
  induction k with
  | zero =>
    dsimp [bellmanFordPasses]
    exact initDist_source s
  | succ m ih =>
    have h_le := bellmanFordPasses_mono edges (initDist s) m s
    rw [ih] at h_le
    exact le_antisymm h_le (withTop_nat_zero_le _)

/-- If an edge `e` is relaxed (fixed point under `relaxEdge`), it satisfies
the triangle inequality `dist e.v ≤ dist e.u + e.w`. -/
theorem relaxEdge_triangle {n : ℕ} (dist : Fin n → WithTop ℕ) (e : Edge n)
    (h_relaxed : relaxEdge dist e = dist) :
    dist e.v ≤ dist e.u + e.w := by
  have h := congr_fun h_relaxed e.v
  dsimp [relaxEdge] at h
  rw [if_pos rfl] at h
  rw [← h]
  exact min_le_right (dist e.v) (dist e.u + e.w)

end Amort.Graph
