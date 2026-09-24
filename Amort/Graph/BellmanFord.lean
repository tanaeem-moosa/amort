/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Composition
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Order.WithBot
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Dedup

/-!
# Bellman-Ford Single-Source Shortest Paths

This module formalizes the textbook Bellman-Ford shortest paths algorithm on directed graphs
with vertex set `Fin n` and an explicit edge list `edges : List (Edge n)` with integer weights `ℤ`.
It establishes operational step counting showing that $(n - 1)$ rounds of relaxing all $|E|$ edges
executes $(n - 1) \cdot |E| \le n \cdot |E|$ edge relaxations ($O(|V| \cdot |E|)$), connecting
to `Amort.Recurrence.Composition.isBigO_nested_loops_nat`.
Furthermore, it establishes the shortest path property: after $(n - 1)$ passes, distance estimates
are bounded above by the weight of any valid edge path with length at most $(n - 1)$.

## Mathematical Architecture

1. **Edge Representation**:
   Directed edges are represented as structures `Edge n` with source `u : Fin n`,
   target `v : Fin n`, and weight `w : ℤ`.

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

5. **Shortest Path Optimality**:
   - Every path of length at most $k$ from $s$ to $v$ satisfies:
     `bellmanFordPasses edges (initDist s) k v ≤ edgePathWeight p`.
   - In particular, after $(n - 1)$ passes:
     `bellmanFord n edges s v ≤ edgePathWeight p` for any path of length $\le n - 1$.

## Key Definitions and Theorems
- `Amort.Graph.Edge`: Directed weighted edge between vertices in `Fin n` with integer weight.
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
- `Amort.Graph.bellmanFordPasses_self`: Source distance is bounded above by 0.
- `Amort.Graph.relaxEdge_triangle`: Satisfied triangle inequality at fixed points.
- `Amort.Graph.bellmanFordPasses_le_path_edges`: Distance is bounded by path weight for paths ≤ $k$.
- `Amort.Graph.bellmanFord_le_path_weight`: $(n - 1)$ passes bounded by simple path weight.
- `Amort.Graph.bellmanFord_achieved`: Realizability of finite distance estimates by concrete paths.
- `Amort.Graph.NoNegCycle`: Independent graph predicate stating paths can be reduced
  to length $\le n - 1$.
- `Amort.Graph.bellmanFord_optimal`: Shortest path optimality under `NoNegCycle` for paths of
  arbitrary length.
- `Amort.Graph.hasNegCycleCheck`: Executable boolean check running the $n$-th relaxation pass.
- `Amort.Graph.hasNegCycleCheck_iff`: Detection equivalence to `HasReachableNegCycle`.
- `Amort.Graph.noNegCycle_not_hasReachableNegCycle`: Soundness of negative cycle detection.
- `Amort.Graph.hasReachableNegCycle_not_noNegCycle`: Completeness of negative cycle certification.
-/

namespace Amort.Graph

open Amort.Recurrence

/-! ### Edge Representation and Graph Initialization -/

/-- Directed weighted edge between vertices in `Fin n` with integer weight `w : ℤ`. -/
structure Edge (n : ℕ) where
  u : Fin n
  v : Fin n
  w : ℤ
deriving DecidableEq, Repr

/-- Canonical single-source distance initialization: source has distance 0,
all other vertices have distance `⊤`. -/
def initDist {n : ℕ} (s : Fin n) : Fin n → WithTop ℤ :=
  fun v ↦ if v = s then (0 : WithTop ℤ) else ⊤

@[simp]
theorem initDist_source {n : ℕ} (s : Fin n) : initDist s s = (0 : WithTop ℤ) := by
  dsimp [initDist]
  rw [if_pos rfl]

theorem initDist_other {n : ℕ} (s v : Fin n) (h : v ≠ s) : initDist s v = ⊤ := by
  dsimp [initDist]
  rw [if_neg h]

/-! ### Edge Relaxation Operations -/

/-- Relaxes a single edge `e = (u, v, w)`: updates `dist v` to `min (dist v) (dist u + w)`. -/
def relaxEdge {n : ℕ} (dist : Fin n → WithTop ℤ) (e : Edge n) : Fin n → WithTop ℤ :=
  fun x ↦ if x = e.v then min (dist e.v) (dist e.u + (e.w : WithTop ℤ)) else dist x

/-- Relaxes all edges in `edges` sequentially in a single pass. -/
def relaxAll {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ) :
    Fin n → WithTop ℤ :=
  edges.foldl relaxEdge dist

/-- Executes `k` sequential relaxation passes over the edge list `edges`. -/
def bellmanFordPasses {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ) :
    ℕ → (Fin n → WithTop ℤ)
  | 0 => dist
  | k + 1 => relaxAll edges (bellmanFordPasses edges dist k)

/-- Full Bellman-Ford algorithm: executes `(n - 1)` relaxation passes from source `s`. -/
def bellmanFord (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Fin n → WithTop ℤ :=
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
def bellmanFordPassesWithCount {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ) :
    ℕ → (Fin n → WithTop ℤ) × ℕ
  | 0 => (dist, 0)
  | k + 1 =>
    let res := bellmanFordPassesWithCount edges dist k
    (relaxAll edges res.1, res.2 + edges.length)

theorem bellmanFordPassesWithCount_fst {n : ℕ} (edges : List (Edge n))
    (dist : Fin n → WithTop ℤ) (k : ℕ) :
    (bellmanFordPassesWithCount edges dist k).1 = bellmanFordPasses edges dist k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    dsimp [bellmanFordPassesWithCount, bellmanFordPasses]
    rw [ih]

theorem bellmanFordPassesWithCount_snd {n : ℕ} (edges : List (Edge n))
    (dist : Fin n → WithTop ℤ) (k : ℕ) :
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
    (Fin n → WithTop ℤ) × ℕ :=
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
theorem relaxEdge_mono {n : ℕ} (dist : Fin n → WithTop ℤ) (e : Edge n) (v : Fin n) :
    relaxEdge dist e v ≤ dist v := by
  dsimp [relaxEdge]
  split_ifs with h
  · subst h
    exact min_le_left (dist e.v) (dist e.u + (e.w : WithTop ℤ))
  · exact le_rfl

lemma relaxAll_mono_aux {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ)
    (v : Fin n) :
    edges.foldl relaxEdge dist v ≤ dist v := by
  induction edges generalizing dist with
  | nil => exact le_rfl
  | cons e es ih =>
    have h1 := ih (relaxEdge dist e)
    have h2 := relaxEdge_mono dist e v
    exact h1.trans h2

/-- Relaxing all edges in a pass never increases distance estimates. -/
theorem relaxAll_mono {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ)
    (v : Fin n) :
    relaxAll edges dist v ≤ dist v :=
  relaxAll_mono_aux edges dist v

/-- Monotonicity across passes: distances after `k + 1` passes are at most distances
after `k` passes. -/
theorem bellmanFordPasses_mono {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ)
    (k : ℕ) (v : Fin n) :
    bellmanFordPasses edges dist (k + 1) v ≤ bellmanFordPasses edges dist k v :=
  relaxAll_mono edges (bellmanFordPasses edges dist k) v

/-- Distance monotonicity for any `k ≤ m`. -/
theorem bellmanFordPasses_mono_le {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ)
    {k m : ℕ} (h : k ≤ m) (v : Fin n) :
    bellmanFordPasses edges dist m v ≤ bellmanFordPasses edges dist k v := by
  induction m, h using Nat.le_induction with
  | base => exact le_rfl
  | succ m' hle ih =>
    exact (bellmanFordPasses_mono edges dist m' v).trans ih

/-- Source distance is non-increasing and bounded above by 0 across all passes. -/
theorem bellmanFordPasses_self {n : ℕ} (edges : List (Edge n)) (s : Fin n) (k : ℕ) :
    bellmanFordPasses edges (initDist s) k s ≤ 0 := by
  have h_mono := bellmanFordPasses_mono_le edges (initDist s) (Nat.zero_le k) s
  have h_init : bellmanFordPasses edges (initDist s) 0 s = 0 := by
    dsimp [bellmanFordPasses]
    exact initDist_source s
  rw [h_init] at h_mono
  exact h_mono

/-- If an edge `e` is relaxed (fixed point under `relaxEdge`), it satisfies
the triangle inequality `dist e.v ≤ dist e.u + e.w`. -/
theorem relaxEdge_triangle {n : ℕ} (dist : Fin n → WithTop ℤ) (e : Edge n)
    (h_relaxed : relaxEdge dist e = dist) :
    dist e.v ≤ dist e.u + (e.w : WithTop ℤ) := by
  have h := congr_fun h_relaxed e.v
  dsimp [relaxEdge] at h
  rw [if_pos rfl] at h
  rw [← h]
  exact min_le_right (dist e.v) (dist e.u + (e.w : WithTop ℤ))

/-! ### Shortest Path Verification -/

/-- Inductive predicate specifying that `p` forms a directed edge path from `s` to `v`. -/
def isEdgePath {n : ℕ} (s : Fin n) : List (Edge n) → Fin n → Prop
  | [], v => s = v
  | e :: es, v => e.u = s ∧ isEdgePath e.v es v

/-- Total weight of an edge path: sum of edge weights in `ℤ`. -/
def edgePathWeight {n : ℕ} (p : List (Edge n)) : ℤ :=
  (p.map Edge.w).sum

/-- Appending an edge to a path connects from `s` to `e.v`. -/
theorem isEdgePath_append_singleton {n : ℕ} (s : Fin n) (p : List (Edge n))
    (e : Edge n) (v : Fin n) :
    isEdgePath s (p ++ [e]) v ↔ isEdgePath s p e.u ∧ e.v = v := by
  induction p generalizing s with
  | nil =>
    simp [isEdgePath, eq_comm]
  | cons head tail ih =>
    simp [isEdgePath, ih head.v, and_assoc]

/-- Appending an edge to an edge path adds its weight. -/
theorem edgePathWeight_append_singleton {n : ℕ} (p : List (Edge n)) (e : Edge n) :
    edgePathWeight (p ++ [e]) = edgePathWeight p + e.w := by
  dsimp [edgePathWeight]
  simp

/-- Addition with integer on the right is monotone on `WithTop ℤ`. -/
theorem withTop_int_add_le_add_right (a b : WithTop ℤ) (c : ℤ) (h : a ≤ b) :
    a + (c : WithTop ℤ) ≤ b + (c : WithTop ℤ) := by
  cases a with
  | top =>
    have : b = ⊤ := le_antisymm le_top h
    subst this
    exact le_rfl
  | coe a_val =>
    cases b with
    | top => simp
    | coe b_val =>
      simp only [← WithTop.coe_add]
      rw [WithTop.coe_le_coe] at h ⊢
      omega

/-- One pass of edge relaxations decreases the endpoint distance to at most `dist e.u + e.w`. -/
lemma relaxAll_edge_le {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ)
    (e : Edge n) (he : e ∈ edges) :
    relaxAll edges dist e.v ≤ dist e.u + (e.w : WithTop ℤ) := by
  induction edges generalizing dist with
  | nil => contradiction
  | cons e' es ih =>
    dsimp [relaxAll]
    cases he with
    | head =>
      have h1 := relaxAll_mono_aux es (relaxEdge dist e) e.v
      have h2 : relaxEdge dist e e.v ≤ dist e.u + (e.w : WithTop ℤ) := by
        dsimp [relaxEdge]
        rw [if_pos rfl]
        exact min_le_right _ _
      exact h1.trans h2
    | tail _ h_in =>
      have h_ih := ih (relaxEdge dist e') h_in
      have h_mono := relaxEdge_mono dist e' e.u
      have h_add := withTop_int_add_le_add_right (relaxEdge dist e' e.u) (dist e.u) e.w h_mono
      exact h_ih.trans h_add

/-- Helper induction principle from the back for lists. -/
lemma list_reverse_induction {α : Type*} {P : List α → Prop}
    (nil : P [])
    (snoc : ∀ (l : List α) (x : α), P l → P (l ++ [x]))
    (l : List α) : P l := by
  suffices ∀ (l' : List α), P l'.reverse by
    have h := this l.reverse
    rwa [List.reverse_reverse] at h
  intro l'
  induction l' with
  | nil => exact nil
  | cons x xs ih =>
    rw [List.reverse_cons]
    exact snoc xs.reverse x ih

/-- Shortest-path induction: distance estimate after `k` passes is bounded by
the weight of any path of length at most `k` using edges from `edges`. -/
theorem bellmanFordPasses_le_path_edges {n : ℕ} (edges : List (Edge n))
    (s : Fin n) (k : ℕ) (p : List (Edge n)) (v : Fin n)
    (h_path : isEdgePath s p v)
    (h_edges : ∀ e ∈ p, e ∈ edges)
    (h_len : p.length ≤ k) :
    bellmanFordPasses edges (initDist s) k v ≤ ((edgePathWeight p : ℤ) : WithTop ℤ) := by
  induction p using list_reverse_induction generalizing k v with
  | nil =>
    dsimp [isEdgePath] at h_path
    subst h_path
    dsimp [edgePathWeight]
    have h_mono := bellmanFordPasses_mono_le edges (initDist s) (Nat.zero_le k) s
    have h_init : bellmanFordPasses edges (initDist s) 0 s = 0 := by
      dsimp [bellmanFordPasses]
      exact initDist_source s
    rw [h_init] at h_mono
    exact h_mono
  | snoc p e ih =>
    rw [isEdgePath_append_singleton] at h_path
    rcases h_path with ⟨h_p, rfl⟩
    have he_in : e ∈ edges := h_edges e (List.mem_append_right _ (List.mem_singleton_self e))
    have hp_edges : ∀ e' ∈ p, e' ∈ edges := fun e' he' ↦
      h_edges e' (List.mem_append_left _ he')
    rw [edgePathWeight_append_singleton]
    simp only [List.length_append, List.length_singleton] at h_len
    cases k with
    | zero => omega
    | succ k' =>
      have h_len' : p.length ≤ k' := by omega
      have ih' := ih k' e.u h_p hp_edges h_len'
      dsimp [bellmanFordPasses]
      have h_relax := relaxAll_edge_le edges (bellmanFordPasses edges (initDist s) k') e he_in
      have h_add := withTop_int_add_le_add_right _ _ e.w ih'
      exact h_relax.trans h_add

/-- Full Bellman-Ford shortest-path theorem: after `(n - 1)` relaxation passes,
the distance estimate `bellmanFord n edges s v` is bounded above by the weight
of any path `p` from `s` to `v` of length at most `(n - 1)`. -/
theorem bellmanFord_le_path_weight {n : ℕ} (edges : List (Edge n))
    (s v : Fin n) (p : List (Edge n))
    (h_path : isEdgePath s p v)
    (h_edges : ∀ e ∈ p, e ∈ edges)
    (h_len : p.length ≤ n - 1) :
    bellmanFord n edges s v ≤ ((edgePathWeight p : ℤ) : WithTop ℤ) :=
  bellmanFordPasses_le_path_edges edges s (n - 1) p v h_path h_edges h_len

/-! ### Path Realizability (Soundness) -/

/-- Invariant: every finite distance estimate is realized by an explicit edge path
originating at the source `s` whose weight matches the distance estimate. -/
def Realizable {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (dist : Fin n → WithTop ℤ) : Prop :=
  ∀ (v : Fin n) (d : ℤ), dist v = (d : WithTop ℤ) →
    ∃ p, isEdgePath s p v ∧ (∀ e ∈ p, e ∈ edges) ∧ edgePathWeight p = d

lemma initDist_realizable {n : ℕ} (edges : List (Edge n)) (s : Fin n) :
    Realizable edges s (initDist s) := by
  intro v d hd
  dsimp [initDist] at hd
  split_ifs at hd with hv
  · subst hv
    have hd' : d = 0 := WithTop.coe_inj.mp hd.symm
    subst hd'
    refine ⟨[], ?_, ?_, ?_⟩
    · dsimp [isEdgePath]
    · intro e he; cases he
    · rfl
  · cases hd

lemma relaxEdge_realizable {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (dist : Fin n → WithTop ℤ) (e : Edge n) (he_in : e ∈ edges)
    (h_real : Realizable edges s dist) :
    Realizable edges s (relaxEdge dist e) := by
  intro v d hd
  dsimp [relaxEdge] at hd
  split_ifs at hd with hv
  · subst hv
    rcases min_choice (dist e.v) (dist e.u + (e.w : WithTop ℤ)) with hmin | hmin
    · rw [hmin] at hd
      exact h_real e.v d hd
    · rw [hmin] at hd
      cases hu : dist e.u with
      | top =>
        rw [hu] at hd
        simp only [WithTop.top_add] at hd
        cases hd
      | coe du =>
        rw [hu] at hd
        have h_add : ((du + e.w : ℤ) : WithTop ℤ) = (d : WithTop ℤ) := by
          have h_cast : (du : WithTop ℤ) + (e.w : WithTop ℤ) = ((du + e.w : ℤ) : WithTop ℤ) := by
            exact WithTop.coe_add du e.w
          rwa [← h_cast]
        have h_eq : du + e.w = d := WithTop.coe_inj.mp h_add
        have h_du : du = d - e.w := by omega
        rcases h_real e.u du hu with ⟨p, hp_path, hp_edges, hp_wt⟩
        refine ⟨p ++ [e], ?_, ?_, ?_⟩
        · rw [isEdgePath_append_singleton]
          exact ⟨hp_path, rfl⟩
        · intro e' he'
          simp only [List.mem_append, List.mem_singleton] at he'
          cases he' with
          | inl h_in => exact hp_edges e' h_in
          | inr h_in => subst h_in; exact he_in
        · rw [edgePathWeight_append_singleton, hp_wt, h_du]
          omega
  · exact h_real v d hd

lemma foldl_relaxEdge_realizable {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (es : List (Edge n)) (hes : ∀ e ∈ es, e ∈ edges)
    (dist : Fin n → WithTop ℤ) (h_real : Realizable edges s dist) :
    Realizable edges s (es.foldl relaxEdge dist) := by
  induction es generalizing dist with
  | nil => exact h_real
  | cons e rest ih =>
    have he_in : e ∈ edges := hes e (by simp)
    have hrest : ∀ e' ∈ rest, e' ∈ edges := fun e' he' ↦
      hes e' (List.mem_cons_of_mem e he')
    have h_step := relaxEdge_realizable edges s dist e he_in h_real
    exact ih hrest (relaxEdge dist e) h_step

lemma relaxAll_realizable {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (dist : Fin n → WithTop ℤ) (h_real : Realizable edges s dist) :
    Realizable edges s (relaxAll edges dist) :=
  foldl_relaxEdge_realizable edges s edges (fun _ he ↦ he) dist h_real

/-- Realizability invariant holds across any number `k` of relaxation passes. -/
theorem bellmanFordPasses_realizable {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (k : ℕ) :
    Realizable edges s (bellmanFordPasses edges (initDist s) k) := by
  induction k with
  | zero =>
    dsimp [bellmanFordPasses]
    exact initDist_realizable edges s
  | succ m ih =>
    dsimp [bellmanFordPasses]
    exact relaxAll_realizable edges s (bellmanFordPasses edges (initDist s) m) ih

/-- Every finite distance estimate produced by Bellman-Ford is realized by a concrete
edge path from the source `s` through the graph's edge list. -/
theorem bellmanFord_achieved {n : ℕ} (edges : List (Edge n)) (s v : Fin n) (d : ℤ)
    (h : bellmanFord n edges s v = d) :
    ∃ p, isEdgePath s p v ∧ (∀ e ∈ p, e ∈ edges) ∧ edgePathWeight p = d :=
  bellmanFordPasses_realizable edges s (n - 1) v d h

/-! ### Path Decomposition and Cycle Removal -/

/-- The sequence of vertices visited by an edge path starting from `s`. -/
def pathVertices {n : ℕ} (s : Fin n) : List (Edge n) → List (Fin n)
  | [] => [s]
  | e :: es => s :: pathVertices e.v es

theorem pathVertices_length {n : ℕ} (s : Fin n) (p : List (Edge n)) :
    (pathVertices s p).length = p.length + 1 := by
  induction p generalizing s with
  | nil => rfl
  | cons e es ih =>
    dsimp [pathVertices]
    simp [ih e.v]

theorem edgePathWeight_append {n : ℕ} (p1 p2 : List (Edge n)) :
    edgePathWeight (p1 ++ p2) = edgePathWeight p1 + edgePathWeight p2 := by
  dsimp [edgePathWeight]
  simp

lemma pathVertices_split {n : ℕ} (s : Fin n) (p : List (Edge n)) (v : Fin n)
    (h_path : isEdgePath s p v) (x : Fin n) (hx : x ∈ pathVertices s p) :
    ∃ p1 p2, p = p1 ++ p2 ∧ isEdgePath s p1 x ∧ isEdgePath x p2 v ∧
      (∀ e ∈ p1, e ∈ p) ∧ (∀ e ∈ p2, e ∈ p) := by
  induction p generalizing s with
  | nil =>
    dsimp [pathVertices] at hx
    simp only [List.mem_singleton] at hx
    subst hx
    dsimp [isEdgePath] at h_path
    subst h_path
    exact ⟨[], [], rfl, rfl, rfl, by simp, by simp⟩
  | cons e es ih =>
    dsimp [pathVertices] at hx
    simp only [List.mem_cons] at hx
    dsimp [isEdgePath] at h_path
    rcases h_path with ⟨rfl, hes⟩
    cases hx with
    | inl hx_eq =>
      subst hx_eq
      exact ⟨[], e :: es, rfl, rfl, ⟨rfl, hes⟩, by simp, fun _ he ↦ he⟩
    | inr hx_in =>
      rcases ih e.v hes hx_in with ⟨p1, p2, rfl, hp1, hp2, hp1_sub, hp2_sub⟩
      refine ⟨e :: p1, p2, rfl, ⟨rfl, hp1⟩, hp2, ?_, ?_⟩
      · intro e' he'
        simp only [List.mem_cons] at he' ⊢
        cases he' with
        | inl he'_eq => exact Or.inl he'_eq
        | inr he'_in => exact Or.inr (hp1_sub e' he'_in)
      · intro e' he'
        simp only [List.mem_cons]
        exact Or.inr (hp2_sub e' he')

lemma path_duplicate_cycle {n : ℕ} (s : Fin n) (p : List (Edge n)) (v : Fin n)
    (h_path : isEdgePath s p v) (h_not_nodup : ¬ (pathVertices s p).Nodup) :
    ∃ (u : Fin n) (p1 c p2 : List (Edge n)),
      p = p1 ++ c ++ p2 ∧ c ≠ [] ∧ isEdgePath s p1 u ∧ isEdgePath u c u ∧
      isEdgePath u p2 v ∧ isEdgePath s (p1 ++ p2) v ∧
      (∀ e ∈ p1 ++ p2, e ∈ p) ∧ (∀ e ∈ c, e ∈ p) ∧
      edgePathWeight p = edgePathWeight (p1 ++ p2) + edgePathWeight c := by
  induction p generalizing s with
  | nil =>
    dsimp [pathVertices] at h_not_nodup
    exact False.elim (h_not_nodup (List.nodup_singleton s))
  | cons e es ih =>
    dsimp [pathVertices] at h_not_nodup
    dsimp [isEdgePath] at h_path
    rcases h_path with ⟨rfl, hes⟩
    have h_cases : e.u ∈ pathVertices e.v es ∨ ¬ (pathVertices e.v es).Nodup := by
      by_contra! h_both
      have h_nd : (pathVertices e.u (e :: es)).Nodup := by
        dsimp [pathVertices]
        rw [List.nodup_cons]
        exact ⟨h_both.1, h_both.2⟩
      exact h_not_nodup h_nd
    cases h_cases with
    | inl hs_in =>
      rcases pathVertices_split e.v es v hes e.u hs_in with
        ⟨c, p2, rfl, hc_path, hp2_path, hc_sub, hp2_sub⟩
      refine ⟨e.u, [], e :: c, p2, rfl, by simp, rfl, ⟨rfl, hc_path⟩, hp2_path, hp2_path,
        ?_, ?_, ?_⟩
      · intro e' he'
        simp only [List.nil_append] at he'
        exact List.mem_cons_of_mem e (hp2_sub e' he')
      · intro e' he'
        simp only [List.mem_cons] at he' ⊢
        cases he' with
        | inl he'_eq => exact Or.inl he'_eq
        | inr he'_in => exact Or.inr (hc_sub e' he'_in)
      · dsimp [edgePathWeight]
        simp only [List.map_cons, List.sum_cons, List.map_append, List.sum_append]
        omega
    | inr hes_not_nodup =>
      rcases ih e.v hes hes_not_nodup with
        ⟨u, p1, c, p2, rfl, hc_ne, hp1_path, hc_cyc, hp2_path, hp12_path, hp12_sub, hc_sub, h_wt⟩
      refine ⟨u, e :: p1, c, p2, rfl, hc_ne, ⟨rfl, hp1_path⟩, hc_cyc, hp2_path, ⟨rfl, hp12_path⟩,
        ?_, ?_, ?_⟩
      · intro e' he'
        simp only [List.cons_append, List.mem_cons] at he' ⊢
        cases he' with
        | inl he'_eq => exact Or.inl he'_eq
        | inr he'_in => exact Or.inr (hp12_sub e' he'_in)
      · intro e' he'
        exact List.mem_cons_of_mem e (hc_sub e' he')
      · dsimp [edgePathWeight]
        simp only [List.map_cons, List.sum_cons]
        dsimp [edgePathWeight] at h_wt
        omega

/-- Distinct vertex list length is bounded by the cardinality of the vertex type. -/
theorem list_length_le_card_of_nodup {α : Type*} [Fintype α]
    (L : List α) (hL : L.Nodup) :
    L.length ≤ Fintype.card α := by
  classical
  have h_card := List.toFinset_card_of_nodup hL
  have h_le : L.toFinset.card ≤ Fintype.card α := Finset.card_le_univ L.toFinset
  omega

/-! ### Optimality Under No Negative Cycles -/

/-- Genuine negative cycle predicate: every directed cycle in `edges` has non-negative weight. -/
def NoNegCycle {n : ℕ} (edges : List (Edge n)) : Prop :=
  ∀ (v : Fin n) (c : List (Edge n)), isEdgePath v c v → (∀ e ∈ c, e ∈ edges) →
    0 ≤ edgePathWeight c

/-- Cycle removal: under `NoNegCycle`, every edge path can be shortened to length at most `n - 1`
without increasing its total weight. -/
theorem noNegCycle_path_le_len {n : ℕ} (edges : List (Edge n)) (hneg : NoNegCycle edges)
    (s v : Fin n) (p : List (Edge n))
    (hpath : isEdgePath s p v) (hedges : ∀ e ∈ p, e ∈ edges) :
    ∃ (p' : List (Edge n)), isEdgePath s p' v ∧ (∀ e ∈ p', e ∈ edges) ∧
      p'.length ≤ n - 1 ∧ edgePathWeight p' ≤ edgePathWeight p := by
  by_cases h_nodup : (pathVertices s p).Nodup
  · have hlen : (pathVertices s p).length ≤ n := by
      have h := list_length_le_card_of_nodup (pathVertices s p) h_nodup
      simp only [Fintype.card_fin] at h
      exact h
    rw [pathVertices_length] at hlen
    refine ⟨p, hpath, hedges, by omega, le_rfl⟩
  · rcases path_duplicate_cycle s p v hpath h_nodup with
      ⟨u, p1, c, p2, hp_eq, hc_ne, _, hc_cyc, _, hp12_path, hp12_edges, hc_edges, h_wt⟩
    have hc_in : ∀ e ∈ c, e ∈ edges := fun e he ↦ hedges e (hc_edges e he)
    have h_c_ge : 0 ≤ edgePathWeight c := hneg u c hc_cyc hc_in
    have hp12_in : ∀ e ∈ p1 ++ p2, e ∈ edges := fun e he ↦ hedges e (hp12_edges e he)
    have ih := noNegCycle_path_le_len edges hneg s v (p1 ++ p2) hp12_path hp12_in
    rcases ih with ⟨p', hp'_path, hp'_edges, hp'_len, hp'_wt⟩
    refine ⟨p', hp'_path, hp'_edges, hp'_len, ?_⟩
    have : edgePathWeight (p1 ++ p2) ≤ edgePathWeight p := by
      rw [h_wt]
      omega
    exact hp'_wt.trans this
termination_by p.length
decreasing_by
  have : c.length > 0 := List.length_pos_of_ne_nil hc_ne
  rw [hp_eq]
  simp only [List.length_append]
  omega

/-- Bellman-Ford optimality under the `NoNegCycle` condition: for any edge path
from `s` to `v` of arbitrary length, `bellmanFord n edges s v` is bounded above
by its weight. -/
theorem bellmanFord_optimal {n : ℕ} (edges : List (Edge n)) (hneg : NoNegCycle edges)
    (s v : Fin n) (p : List (Edge n))
    (hpath : isEdgePath s p v) (hedges : ∀ e ∈ p, e ∈ edges) :
    bellmanFord n edges s v ≤ ((edgePathWeight p : ℤ) : WithTop ℤ) := by
  rcases noNegCycle_path_le_len edges hneg s v p hpath hedges with
    ⟨p', hp'_path, hp'_edges, hp'_len, hp'_wt⟩
  have h_bf := bellmanFord_le_path_weight edges s v p' hp'_path hp'_edges hp'_len
  have h_le : ((edgePathWeight p' : ℤ) : WithTop ℤ) ≤ ((edgePathWeight p : ℤ) : WithTop ℤ) := by
    rw [WithTop.coe_le_coe]
    exact hp'_wt
  exact h_bf.trans h_le

/-! ### Negative Cycle Detection -/

/-- Checks whether an edge `e` can be relaxed further given current distance estimates `dist`. -/
def canRelaxEdge {n : ℕ} (dist : Fin n → WithTop ℤ) (e : Edge n) : Bool :=
  match dist e.u with
  | ⊤ => false
  | some du =>
    match dist e.v with
    | ⊤ => true
    | some dv => du + e.w < dv

/-- Propositional characterization of an edge being relaxable. -/
def CanRelax {n : ℕ} (dist : Fin n → WithTop ℤ) (e : Edge n) : Prop :=
  dist e.u ≠ ⊤ ∧ dist e.u + (e.w : WithTop ℤ) < dist e.v

lemma canRelaxEdge_iff {n : ℕ} (dist : Fin n → WithTop ℤ) (e : Edge n) :
    canRelaxEdge dist e = true ↔ CanRelax dist e := by
  dsimp [canRelaxEdge, CanRelax]
  cases hu : dist e.u with
  | top =>
    simp
  | coe du =>
    constructor
    · intro h
      refine ⟨by simp, ?_⟩
      cases hv : dist e.v with
      | top =>
        have h_cast : (du : WithTop ℤ) + (e.w : WithTop ℤ) = ((du + e.w : ℤ) : WithTop ℤ) :=
          WithTop.coe_add du e.w
        rw [h_cast]
        exact WithTop.coe_lt_top (du + e.w)
      | coe dv =>
        have h_cast : (du : WithTop ℤ) + (e.w : WithTop ℤ) = ((du + e.w : ℤ) : WithTop ℤ) :=
          WithTop.coe_add du e.w
        rw [h_cast, WithTop.coe_lt_coe]
        revert h
        dsimp
        rw [hv]
        simp
    · intro ⟨_, hlt⟩
      cases hv : dist e.v with
      | top =>
        dsimp
      | coe dv =>
        dsimp
        have h_cast : (du : WithTop ℤ) + (e.w : WithTop ℤ) = ((du + e.w : ℤ) : WithTop ℤ) :=
          WithTop.coe_add du e.w
        rw [hv, h_cast, WithTop.coe_lt_coe] at hlt
        exact decide_eq_true hlt

/-- Genuine reachable negative cycle condition: a directed cycle `c` at `v` reachable from `s`
via path `p` having strictly negative total weight. -/
def HasReachableNegCycle (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Prop :=
  ∃ (v : Fin n) (p c : List (Edge n)), isEdgePath s p v ∧ isEdgePath v c v ∧
    (∀ e ∈ p ++ c, e ∈ edges) ∧ edgePathWeight c < 0

/-- Full Bellman-Ford negative cycle check: returns `true` if any edge can be relaxed
on the `n`-th pass after `n - 1` relaxation rounds. -/
def hasNegCycleCheck (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Bool :=
  let dist := bellmanFord n edges s
  edges.any (canRelaxEdge dist)

/-- Cycle removal on reachable paths when no reachable negative cycles exist. -/
theorem reachable_path_le_len {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (h_no_neg : ¬ HasReachableNegCycle n edges s)
    (v : Fin n) (p : List (Edge n))
    (hpath : isEdgePath s p v) (hedges : ∀ e ∈ p, e ∈ edges) :
    ∃ (p' : List (Edge n)), isEdgePath s p' v ∧ (∀ e ∈ p', e ∈ edges) ∧
      p'.length ≤ n - 1 ∧ edgePathWeight p' ≤ edgePathWeight p := by
  by_cases h_nodup : (pathVertices s p).Nodup
  · have hlen : (pathVertices s p).length ≤ n := by
      have h := list_length_le_card_of_nodup (pathVertices s p) h_nodup
      simp only [Fintype.card_fin] at h
      exact h
    rw [pathVertices_length] at hlen
    refine ⟨p, hpath, hedges, by omega, le_rfl⟩
  · rcases path_duplicate_cycle s p v hpath h_nodup with
      ⟨u, p1, c, p2, hp_eq, hc_ne, hp1_path, hc_cyc, _, hp12_path, hp12_edges, hc_edges, h_wt⟩
    have hp1_c_edges : ∀ e ∈ p1 ++ c, e ∈ edges := by
      intro e he
      simp only [List.mem_append] at he
      cases he with
      | inl hin =>
        have : e ∈ p1 ++ p2 := List.mem_append_left p2 hin
        exact hedges e (hp12_edges e this)
      | inr hin => exact hedges e (hc_edges e hin)
    have h_c_ge : 0 ≤ edgePathWeight c := by
      by_contra! hlt
      have : HasReachableNegCycle n edges s := ⟨u, p1, c, hp1_path, hc_cyc, hp1_c_edges, hlt⟩
      exact h_no_neg this
    have hp12_in : ∀ e ∈ p1 ++ p2, e ∈ edges := fun e he ↦ hedges e (hp12_edges e he)
    have ih := reachable_path_le_len edges s h_no_neg v (p1 ++ p2) hp12_path hp12_in
    rcases ih with ⟨p', hp'_path, hp'_edges, hp'_len, hp'_wt⟩
    refine ⟨p', hp'_path, hp'_edges, hp'_len, ?_⟩
    have : edgePathWeight (p1 ++ p2) ≤ edgePathWeight p := by
      rw [h_wt]
      omega
    exact hp'_wt.trans this
termination_by p.length
decreasing_by
  have : c.length > 0 := List.length_pos_of_ne_nil hc_ne
  rw [hp_eq]
  simp only [List.length_append]
  omega

lemma no_hasReachableNegCycle_not_canRelax {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (h_no_neg : ¬ HasReachableNegCycle n edges s) (e : Edge n) (he : e ∈ edges) :
    ¬ CanRelax (bellmanFord n edges s) e := by
  intro ⟨hu_ne, hlt⟩
  cases hu : bellmanFord n edges s e.u with
  | top => exact hu_ne hu
  | coe du =>
    rcases bellmanFord_achieved edges s e.u du hu with ⟨p, hp_path, hp_edges, hp_wt⟩
    have h_pe_path : isEdgePath s (p ++ [e]) e.v := by
      rw [isEdgePath_append_singleton]
      exact ⟨hp_path, rfl⟩
    have h_pe_edges : ∀ e' ∈ p ++ [e], e' ∈ edges := by
      intro e' he'
      simp only [List.mem_append, List.mem_singleton] at he'
      cases he' with
      | inl hin => exact hp_edges e' hin
      | inr hin => subst hin; exact he
    rcases reachable_path_le_len edges s h_no_neg e.v (p ++ [e]) h_pe_path h_pe_edges with
      ⟨p', hp'_path, hp'_edges, hp'_len, hp'_wt⟩
    have h_bf := bellmanFord_le_path_weight edges s e.v p' hp'_path hp'_edges hp'_len
    rw [edgePathWeight_append_singleton, hp_wt] at hp'_wt
    rw [hu] at hlt
    have h_cast : ((du + e.w : ℤ) : WithTop ℤ) = (du : WithTop ℤ) + (e.w : WithTop ℤ) :=
      WithTop.coe_add du e.w
    have hp'_wt_top : ((edgePathWeight p' : ℤ) : WithTop ℤ) ≤
        (du : WithTop ℤ) + (e.w : WithTop ℤ) := by
      rw [← h_cast, WithTop.coe_le_coe]
      exact hp'_wt
    have h_le := h_bf.trans hp'_wt_top
    have h_contra := h_le.trans_lt hlt
    exact lt_irrefl _ h_contra

lemma no_hasReachableNegCycle_hasNegCycleCheck_false {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (h : ¬ HasReachableNegCycle n edges s) :
    hasNegCycleCheck n edges s = false := by
  dsimp [hasNegCycleCheck]
  rw [List.any_eq_false]
  intro e he
  rw [canRelaxEdge_iff]
  exact no_hasReachableNegCycle_not_canRelax edges s h e he

lemma dist_le_of_no_relax {n : ℕ} (edges : List (Edge n)) (dist : Fin n → WithTop ℤ)
    (h_no_relax : ∀ e ∈ edges, ¬ CanRelax dist e)
    (x y : Fin n) (p : List (Edge n))
    (hp : isEdgePath x p y) (hedges : ∀ e ∈ p, e ∈ edges)
    (hx : dist x ≠ ⊤) :
    dist y ≤ dist x + (edgePathWeight p : WithTop ℤ) := by
  induction p generalizing x with
  | nil =>
    dsimp [isEdgePath] at hp
    subst hp
    dsimp [edgePathWeight]
    simp
  | cons e es ih =>
    dsimp [isEdgePath] at hp
    rcases hp with ⟨rfl, hes⟩
    have he_in : e ∈ edges := hedges e (List.mem_cons.mpr (Or.inl rfl))
    have hes_in : ∀ e' ∈ es, e' ∈ edges := fun e' he' ↦ hedges e' (List.mem_cons_of_mem e he')
    have h_nr := h_no_relax e he_in
    dsimp [CanRelax] at h_nr
    have he_le : dist e.v ≤ dist e.u + (e.w : WithTop ℤ) := by
      by_contra! hlt
      exact h_nr ⟨hx, hlt⟩
    have hev_ne_top : dist e.v ≠ ⊤ := by
      intro h_top
      rw [h_top] at he_le
      cases h_eu : dist e.u with
      | top => exact hx h_eu
      | coe du =>
        rw [h_eu] at he_le
        have : (du : WithTop ℤ) + (e.w : WithTop ℤ) = ((du + e.w : ℤ) : WithTop ℤ) :=
          WithTop.coe_add du e.w
        rw [this] at he_le
        exact WithTop.not_top_le_coe (du + e.w) he_le
    have ih_res := ih e.v hes hes_in hev_ne_top
    dsimp [edgePathWeight]
    simp only [List.map_cons, List.sum_cons]
    have h_cast : ((e.w + (es.map Edge.w).sum : ℤ) : WithTop ℤ) =
        (e.w : WithTop ℤ) + ((es.map Edge.w).sum : WithTop ℤ) := WithTop.coe_add _ _
    rw [h_cast, ← add_assoc]
    have h_mono : dist e.v + ((es.map Edge.w).sum : WithTop ℤ) ≤
        dist e.u + (e.w : WithTop ℤ) + ((es.map Edge.w).sum : WithTop ℤ) := by
      exact withTop_int_add_le_add_right _ _ _ he_le
    exact ih_res.trans h_mono

lemma hasReachableNegCycle_hasNegCycleCheck_true {n : ℕ} (edges : List (Edge n)) (s : Fin n)
    (h : HasReachableNegCycle n edges s) :
    hasNegCycleCheck n edges s = true := by
  by_contra h_not_true
  have h_false : hasNegCycleCheck n edges s = false := by
    revert h_not_true; cases hasNegCycleCheck n edges s <;> simp
  dsimp [hasNegCycleCheck] at h_false
  rw [List.any_eq_false] at h_false
  have h_no_relax : ∀ e ∈ edges, ¬ CanRelax (bellmanFord n edges s) e := by
    intro e he
    have := h_false e he
    rwa [canRelaxEdge_iff] at this
  rcases h with ⟨v, p, c, hp_path, hc_path, hedges, hc_wt⟩
  have hp_edges : ∀ e ∈ p, e ∈ edges := fun e he ↦ hedges e (List.mem_append_left c he)
  have hc_edges : ∀ e ∈ c, e ∈ edges := fun e he ↦ hedges e (List.mem_append_right p he)
  have hs_ne_top : bellmanFord n edges s s ≠ ⊤ := by
    have h_self := bellmanFordPasses_self edges s (n - 1)
    intro h_top
    dsimp [bellmanFord] at h_top
    rw [h_top] at h_self
    contradiction
  have hv_le := dist_le_of_no_relax edges (bellmanFord n edges s) h_no_relax
    s v p hp_path hp_edges hs_ne_top
  have hv_ne_top : bellmanFord n edges s v ≠ ⊤ := by
    intro h_top
    rw [h_top] at hv_le
    cases hs : bellmanFord n edges s s with
    | top => exact hs_ne_top hs
    | coe ds =>
      rw [hs] at hv_le
      have : (ds : WithTop ℤ) + (edgePathWeight p : WithTop ℤ) =
          ((ds + edgePathWeight p : ℤ) : WithTop ℤ) := WithTop.coe_add _ _
      rw [this] at hv_le
      exact WithTop.not_top_le_coe _ hv_le
  have hc_le := dist_le_of_no_relax edges (bellmanFord n edges s) h_no_relax
    v v c hc_path hc_edges hv_ne_top
  cases hv : bellmanFord n edges s v with
  | top => exact hv_ne_top hv
  | coe dv =>
    have h_add : (dv : WithTop ℤ) + (edgePathWeight c : WithTop ℤ) =
        ((dv + edgePathWeight c : ℤ) : WithTop ℤ) := WithTop.coe_add dv (edgePathWeight c)
    rw [hv, h_add, WithTop.coe_le_coe] at hc_le
    omega

/-- The `n`-th pass relaxation check returns `true` if and only if there exists
a reachable negative cycle. -/
theorem hasNegCycleCheck_iff (n : ℕ) (edges : List (Edge n)) (s : Fin n) :
    hasNegCycleCheck n edges s = true ↔ HasReachableNegCycle n edges s := by
  constructor
  · intro h
    by_contra h_not
    have h_false := no_hasReachableNegCycle_hasNegCycleCheck_false edges s h_not
    rw [h_false] at h
    contradiction
  · exact hasReachableNegCycle_hasNegCycleCheck_true edges s

/-- Under the `NoNegCycle` property, no reachable negative cycle exists in the graph. -/
theorem noNegCycle_not_hasReachableNegCycle {n : ℕ} (edges : List (Edge n))
    (hneg : NoNegCycle edges) (s : Fin n) :
    ¬ HasReachableNegCycle n edges s := by
  intro ⟨v, p, c, _, hc_path, hedges, hc_wt⟩
  have hc_edges : ∀ e ∈ c, e ∈ edges := fun e he ↦ hedges e (List.mem_append_right p he)
  have hge := hneg v c hc_path hc_edges
  omega

/-- Detecting a reachable negative cycle certifies that the graph does not satisfy `NoNegCycle`. -/
theorem hasReachableNegCycle_not_noNegCycle {n : ℕ} (edges : List (Edge n))
    (s : Fin n) (h : HasReachableNegCycle n edges s) :
    ¬ NoNegCycle edges := fun hneg ↦
  noNegCycle_not_hasReachableNegCycle edges hneg s h

end Amort.Graph
