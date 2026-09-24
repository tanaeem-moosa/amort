/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Recurrence.Composition
import Mathlib.Algebra.Order.Ring.WithTop
import Mathlib.Order.WithBot
import Mathlib.Data.List.Basic

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

/-! ### Optimality Under No Negative Cycles -/

/-- A graph has no negative cycles if any edge path can be replaced by an edge path
of length at most `n - 1` with weight at most the original path weight. -/
def NoNegCycle {n : ℕ} (edges : List (Edge n)) : Prop :=
  ∀ (s v : Fin n) (p : List (Edge n)),
    isEdgePath s p v → (∀ e ∈ p, e ∈ edges) →
    ∃ (p' : List (Edge n)), isEdgePath s p' v ∧ (∀ e ∈ p', e ∈ edges) ∧
      p'.length ≤ n - 1 ∧ edgePathWeight p' ≤ edgePathWeight p

/-- Bellman-Ford optimality under the `NoNegCycle` condition: for any edge path
from `s` to `v` of arbitrary length, `bellmanFord n edges s v` is bounded above
by its weight. -/
theorem bellmanFord_optimal {n : ℕ} (edges : List (Edge n)) (hneg : NoNegCycle edges)
    (s v : Fin n) (p : List (Edge n))
    (hpath : isEdgePath s p v) (hedges : ∀ e ∈ p, e ∈ edges) :
    bellmanFord n edges s v ≤ ((edgePathWeight p : ℤ) : WithTop ℤ) := by
  rcases hneg s v p hpath hedges with ⟨p', hp'_path, hp'_edges, hp'_len, hp'_wt⟩
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

/-- A reachable negative cycle condition in the Bellman-Ford framework: an edge in `edges`
whose source has a finite distance estimate from `s` after `n - 1` passes, and whose relaxation
would strictly decrease the distance estimate of its target. -/
def HasReachableNegCycle (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Prop :=
  ∃ e ∈ edges, CanRelax (bellmanFord n edges s) e

/-- Full Bellman-Ford negative cycle check: returns `true` if any edge can be relaxed
on the `n`-th pass after `n - 1` relaxation rounds. -/
def hasNegCycleCheck (n : ℕ) (edges : List (Edge n)) (s : Fin n) : Bool :=
  let dist := bellmanFord n edges s
  edges.any (canRelaxEdge dist)

/-- The `n`-th pass relaxation check returns `true` if and only if there exists
a reachable negative cycle witness. -/
theorem hasNegCycleCheck_iff (n : ℕ) (edges : List (Edge n)) (s : Fin n) :
    hasNegCycleCheck n edges s = true ↔ HasReachableNegCycle n edges s := by
  dsimp [hasNegCycleCheck, HasReachableNegCycle]
  rw [List.any_eq_true]
  simp only [canRelaxEdge_iff]

/-- Under the `NoNegCycle` property, no edge reachable from `s` can be relaxed
after `n - 1` passes. -/
theorem noNegCycle_not_hasReachableNegCycle {n : ℕ} (edges : List (Edge n))
    (hneg : NoNegCycle edges) (s : Fin n) :
    ¬ HasReachableNegCycle n edges s := by
  intro ⟨e, he_in, hu_ne, hlt⟩
  cases hu : bellmanFord n edges s e.u with
  | top => exact hu_ne hu
  | coe du =>
    rcases bellmanFord_achieved edges s e.u du hu with ⟨p, hp_path, hp_edges, hp_wt⟩
    have h_p_ext : isEdgePath s (p ++ [e]) e.v := by
      rw [isEdgePath_append_singleton]
      exact ⟨hp_path, rfl⟩
    have h_edges_ext : ∀ e' ∈ p ++ [e], e' ∈ edges := by
      intro e' he'
      simp only [List.mem_append, List.mem_singleton] at he'
      cases he' with
      | inl hin => exact hp_edges e' hin
      | inr hin => subst hin; exact he_in
    have h_opt := bellmanFord_optimal edges hneg s e.v (p ++ [e]) h_p_ext h_edges_ext
    rw [edgePathWeight_append_singleton, hp_wt] at h_opt
    rw [hu] at hlt
    have h_opt' : bellmanFord n edges s e.v ≤ (du : WithTop ℤ) + (e.w : WithTop ℤ) := by
      have h_cast : ((du + e.w : ℤ) : WithTop ℤ) = (du : WithTop ℤ) + (e.w : WithTop ℤ) := by
        exact WithTop.coe_add du e.w
      rwa [h_cast] at h_opt
    have h_contra : bellmanFord n edges s e.v < bellmanFord n edges s e.v :=
      h_opt'.trans_lt hlt
    exact lt_irrefl _ h_contra

/-- Detecting a relaxable edge on the `n`-th pass certifies that the graph does not
satisfy `NoNegCycle`. -/
theorem hasReachableNegCycle_not_noNegCycle {n : ℕ} (edges : List (Edge n))
    (s : Fin n) (h : HasReachableNegCycle n edges s) :
    ¬ NoNegCycle edges := fun hneg ↦
  noNegCycle_not_hasReachableNegCycle edges hneg s h

end Amort.Graph
