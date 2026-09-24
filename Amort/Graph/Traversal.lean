/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Dedup
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
3. Executable linear queue traversal with deduplicated visited tracking,
   proving total work bounded unconditionally by $|V| + |E|$.

## Key Definitions and Theorems
- `Amort.Graph.outdeg`: Out-degree of a vertex in `Fin n`.
- `Amort.Graph.edgeCount`: Sum of out-degrees across all vertices.
- `Amort.Graph.edgeList`: Explicit list of directed edges.
- `Amort.Graph.edgeList_length`: Edge list length equals `edgeCount`.
- `Amort.Graph.handshaking_lemma`: Directed Handshaking Lemma.
- `Amort.Graph.bfsBound`: Total work expanding vertex list $L$.
- `Amort.Graph.bfsWork_le`: Total BFS work is bounded unconditionally by $|V| + |E|$.
- `Amort.Graph.bfsDist`: Canonical unweighted shortest-path distance specification.
- `Amort.Graph.bfsDist_eq_top_iff`: Specification distance is ⊤ iff unreachable.
- `Amort.Graph.bfsDist_eq_coe_iff`: Two-sided specification distance characterization.
- `Amort.Graph.bfsWithCount`: Instrumented BFS returning distances and step count.
- `Amort.Graph.bfsWithCount_fst_eq`: Algorithm distance equals canonical shortest-path distance.
- `Amort.Graph.bfsWithCount_snd_le`: In-loop accumulated operations bounded by $|V| + |E|$.
- `Amort.Graph.bfsLoop_fuel_invariant`: Fuel sufficiency on initial queue state.
- `Amort.Graph.IsPath`: Path validity predicate in `adj`.
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
1 unit per distinct vertex dequeued plus `outdeg u` per edge scanned. -/
def bfsBound (adj : Fin n → List (Fin n)) (L : List (Fin n)) : ℕ :=
  L.dedup.length + (L.dedup.map (fun u ↦ outdeg adj u)).sum

/-- Distinct vertex list length is bounded by the cardinality of the vertex type. -/
theorem list_length_le_card_of_nodup {α : Type*} [Fintype α]
    (L : List α) (hL : L.Nodup) :
    L.length ≤ Fintype.card α := by
  classical
  have h_card := List.toFinset_card_of_nodup hL
  have h_le : L.toFinset.card ≤ Fintype.card α := Finset.card_le_univ L.toFinset
  omega

/-- Distinct vertex list length in `Fin n` is bounded by `n`. -/
theorem list_length_le_n (L : List (Fin n)) (hL : L.Nodup) : L.length ≤ n := by
  have h := list_length_le_card_of_nodup L hL
  simp only [Fintype.card_fin] at h
  exact h

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

/-- Total BFS work across any sequence of visited vertices is bounded
unconditionally by `|V| + |E|`. -/
theorem bfsWork_le (adj : Fin n → List (Fin n)) (L : List (Fin n)) :
    bfsBound adj L ≤ n + edgeCount adj := by
  dsimp [bfsBound]
  have h_nodup := List.nodup_dedup L
  have h1 : L.dedup.length ≤ n := list_length_le_n L.dedup h_nodup
  have h2 := bfsWork_map_sum_le adj L.dedup h_nodup
  omega

/-! ### Reachability and Directed Walks -/

/-- A single directed edge step in adjacency graph `adj`. -/
def Step (adj : Fin n → List (Fin n)) (u v : Fin n) : Prop :=
  v ∈ adj u

/-- Reachability defined as the reflexive-transitive closure of directed edge steps. -/
def Reachable (adj : Fin n → List (Fin n)) (u v : Fin n) : Prop :=
  Relation.ReflTransGen (fun x y ↦ y ∈ adj x) u v

/-- Inductive predicate for a directed walk of length `k` from `s` to `v` in `adj`. -/
inductive IsWalkOfLength (adj : Fin n → List (Fin n)) (s : Fin n) : Fin n → ℕ → Prop
  | zero : IsWalkOfLength adj s s 0
  | step {u v : Fin n} {k : ℕ} :
      IsWalkOfLength adj s u k → v ∈ adj u → IsWalkOfLength adj s v (k + 1)

/-- Equivalence between reachability and existence of a directed walk of some length. -/
theorem reachable_iff_exists_walk (adj : Fin n → List (Fin n)) (u v : Fin n) :
    Reachable adj u v ↔ ∃ k, IsWalkOfLength adj u v k := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨0, IsWalkOfLength.zero⟩
    | tail _ h_edge ih =>
      rcases ih with ⟨k, hk⟩
      exact ⟨k + 1, IsWalkOfLength.step hk h_edge⟩
  · rintro ⟨k, hk⟩
    induction hk with
    | zero => exact Relation.ReflTransGen.refl
    | step _ h_edge ih =>
      exact ih.tail h_edge

/-! ### Breadth-First Search Distance and Two-Sided Correctness -/

/-- Canonical Breadth-First Search shortest-path distance from `s` to `v`. -/
noncomputable def bfsDist (adj : Fin n → List (Fin n)) (s v : Fin n) : WithTop ℕ :=
  open Classical in
  if h : Reachable adj s v then
    have hex : ∃ k, IsWalkOfLength adj s v k := (reachable_iff_exists_walk adj s v).mp h
    (Nat.find hex : WithTop ℕ)
  else ⊤

/-- BFS distance is `⊤` if and only if `v` is unreachable from `s`. -/
theorem bfsDist_eq_top_iff (adj : Fin n → List (Fin n)) (s v : Fin n) :
    bfsDist adj s v = ⊤ ↔ ¬ Reachable adj s v := by
  classical
  dsimp [bfsDist]
  split_ifs with h
  · constructor
    · intro htop
      contradiction
    · intro hnot
      exact (hnot h).elim
  · simp [h]

/-- BFS distance equals `d` if and only if there is a walk of length `d` and no shorter walk. -/
theorem bfsDist_eq_coe_iff (adj : Fin n → List (Fin n)) (s v : Fin n) (d : ℕ) :
    bfsDist adj s v = d ↔ IsWalkOfLength adj s v d ∧ ∀ k, IsWalkOfLength adj s v k → d ≤ k := by
  classical
  dsimp [bfsDist]
  split_ifs with h
  · have hex : ∃ k, IsWalkOfLength adj s v k := (reachable_iff_exists_walk adj s v).mp h
    constructor
    · intro h_eq
      injection h_eq with h_nat
      subst h_nat
      exact ⟨Nat.find_spec hex, fun k hk ↦ Nat.find_le hk⟩
    · rintro ⟨hwalk, hmin⟩
      have h1 : Nat.find hex ≤ d := Nat.find_le hwalk
      have h2 : d ≤ Nat.find hex := hmin (Nat.find hex) (Nat.find_spec hex)
      have h_eq : Nat.find hex = d := by omega
      rw [h_eq]
  · constructor
    · intro h_eq
      contradiction
    · rintro ⟨hwalk, _⟩
      have : Reachable adj s v := (reachable_iff_exists_walk adj s v).mpr ⟨d, hwalk⟩
      exact (h this).elim

/-- BFS distance to source vertex is 0. -/
theorem bfsDist_source (adj : Fin n → List (Fin n)) (s : Fin n) :
    bfsDist adj s s = 0 := by
  change bfsDist adj s s = (0 : ℕ)
  rw [bfsDist_eq_coe_iff]
  exact ⟨IsWalkOfLength.zero, fun k _ ↦ Nat.zero_le k⟩

/-! ### Executable BFS Traversal and Unclamped In-Loop Counting -/

/-- Initial BFS distance state: 0 at source `s`, and `⊤` elsewhere. -/
def bfsInitDist (s : Fin n) : Fin n → WithTop ℕ :=
  fun v ↦ if v = s then 0 else ⊤

@[simp]
theorem bfsInitDist_self (s : Fin n) : bfsInitDist s s = 0 := by
  dsimp [bfsInitDist]
  rw [if_pos rfl]

/-- Queue-based Breadth-First Search traversal loop.
Carries fuel, queue of pending vertices, list of visited vertices, distance map, and
operational counter accumulated directly in-loop (1 tick per dequeue + 1 tick per edge scanned)
unconditionally without any membership clamping. -/
def bfsLoop (adj : Fin n → List (Fin n)) (s : Fin n) :
    ℕ → List (Fin n) → List (Fin n) → (Fin n → WithTop ℕ) → ℕ →
    (Fin n → WithTop ℕ) × ℕ
  | 0, _, _, dist, count => (dist, count)
  | _fuel + 1, [], _, dist, count => (dist, count)
  | fuel + 1, u :: queue, visited, dist, count =>
    let next_edges := adj u
    let unvisited := (next_edges.filter (· ∉ visited)).dedup
    let new_visited := visited ++ unvisited
    let new_dist := fun v ↦ if v ∈ unvisited then dist u + 1 else dist v
    let new_queue := queue ++ unvisited
    let new_count := count + 1 + next_edges.length
    bfsLoop adj s fuel new_queue new_visited new_dist new_count

/-- Invariant: in-loop counter is bounded by `count + |rem| + ∑ v ∈ rem, outdeg adj v`
over any candidate set `rem` covering the pending queue and unvisited vertices. -/
theorem bfsLoop_count_le (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ) :
    ∀ (queue visited : List (Fin n)) (dist : Fin n → WithTop ℕ) (count : ℕ)
      (rem : Finset (Fin n)),
      queue.Nodup →
      (∀ x ∈ queue, x ∈ visited) →
      (∀ x ∈ queue, x ∈ rem) →
      (∀ x, x ∉ visited → x ∈ rem) →
      (bfsLoop adj s fuel queue visited dist count).2 ≤
        count + rem.card + ∑ v ∈ rem, outdeg adj v := by
  induction fuel with
  | zero =>
    intro queue visited dist count rem _ _ _ _
    dsimp [bfsLoop]
    omega
  | succ fuel ih =>
    intro queue visited dist count rem hq_nodup hq_vis hq_rem hvert_rem
    cases queue with
    | nil =>
      dsimp [bfsLoop]
      omega
    | cons u queue =>
      dsimp [bfsLoop]
      have hu_in : u ∈ u :: queue := List.mem_cons_self
      have hu_rem : u ∈ rem := hq_rem u hu_in
      have hu_vis : u ∈ visited := hq_vis u hu_in
      have hq_nodup' : queue.Nodup := (List.nodup_cons.mp hq_nodup).2
      have hu_not_in_q : u ∉ queue := (List.nodup_cons.mp hq_nodup).1
      set next_edges := adj u
      set unvisited := (next_edges.filter (· ∉ visited)).dedup
      set new_visited := visited ++ unvisited
      set new_queue := queue ++ unvisited
      set rem' := rem.erase u
      have hcard : rem'.card + 1 = rem.card := Finset.card_erase_add_one hu_rem
      have hsum_eq : ∑ x ∈ rem', outdeg adj x + outdeg adj u = ∑ x ∈ rem, outdeg adj x :=
        Finset.sum_erase_add rem (fun v ↦ outdeg adj v) hu_rem
      have hsum : (∑ v ∈ rem, outdeg adj v) = outdeg adj u + ∑ v ∈ rem', outdeg adj v := by
        omega
      have hdeg : next_edges.length = outdeg adj u := rfl
      have hnew_q_nodup : new_queue.Nodup := by
        rw [List.nodup_append]
        refine ⟨hq_nodup', List.nodup_dedup _, ?_⟩
        intro x hx y hy
        rw [List.mem_dedup, List.mem_filter] at hy
        have hy_not_vis : y ∉ visited := of_decide_eq_true hy.2
        have hx_vis : x ∈ visited := hq_vis x (List.mem_cons_of_mem u hx)
        rintro rfl
        exact hy_not_vis hx_vis
      have hnew_q_vis : ∀ x ∈ new_queue, x ∈ new_visited := by
        intro x hx
        rw [List.mem_append] at hx ⊢
        cases hx with
        | inl h1 => exact Or.inl (hq_vis x (List.mem_cons_of_mem u h1))
        | inr h2 => exact Or.inr h2
      have hnew_q_rem : ∀ x ∈ new_queue, x ∈ rem' := by
        intro x hx
        rw [List.mem_append] at hx
        cases hx with
        | inl hq =>
          have hx_rem : x ∈ rem := hq_rem x (List.mem_cons_of_mem u hq)
          have hx_ne_u : x ≠ u := by
            rintro rfl
            exact hu_not_in_q hq
          exact Finset.mem_erase.mpr ⟨hx_ne_u, hx_rem⟩
        | inr hunvis =>
          rw [List.mem_dedup, List.mem_filter] at hunvis
          have hx_not_vis : x ∉ visited := of_decide_eq_true hunvis.2
          have hx_rem : x ∈ rem := hvert_rem x hx_not_vis
          have hx_ne_u : x ≠ u := by
            rintro rfl
            exact hx_not_vis hu_vis
          exact Finset.mem_erase.mpr ⟨hx_ne_u, hx_rem⟩
      have hnew_vert_rem : ∀ x, x ∉ new_visited → x ∈ rem' := by
        intro x hx
        have hx_not_vis : x ∉ visited := fun h ↦ hx (List.mem_append_left _ h)
        have hx_rem : x ∈ rem := hvert_rem x hx_not_vis
        have hx_ne_u : x ≠ u := by
          rintro rfl
          exact hx_not_vis hu_vis
        exact Finset.mem_erase.mpr ⟨hx_ne_u, hx_rem⟩
      have ih_step := ih new_queue new_visited
        (fun v ↦ if v ∈ unvisited then dist u + 1 else dist v)
        (count + 1 + next_edges.length) rem'
        hnew_q_nodup hnew_q_vis hnew_q_rem hnew_vert_rem
      omega

/-- Invariant: Source vertex distance remains 0 throughout BFS traversal. -/
theorem bfsLoop_dist_source (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ)
    (queue visited : List (Fin n))
    (dist : Fin n → WithTop ℕ) (count : ℕ) (hs : s ∈ visited) (h_dist_s : dist s = 0) :
    (bfsLoop adj s fuel queue visited dist count).1 s = 0 := by
  induction fuel generalizing queue visited dist count with
  | zero =>
    dsimp [bfsLoop]
    exact h_dist_s
  | succ fuel ih =>
    cases queue with
    | nil =>
      dsimp [bfsLoop]
      exact h_dist_s
    | cons u queue =>
      dsimp [bfsLoop]
      set unvisited := ((adj u).filter (· ∉ visited)).dedup
      have hnot : s ∉ unvisited := by
        intro h
        rw [List.mem_dedup, List.mem_filter] at h
        have := of_decide_eq_true h.2
        exact this hs
      have hdist : (fun v ↦ if v ∈ unvisited then dist u + 1 else dist v) s = 0 := by
        dsimp
        rw [if_neg hnot]
        exact h_dist_s
      have hvis : s ∈ visited ++ unvisited := List.mem_append_left _ hs
      exact ih (queue ++ unvisited) (visited ++ unvisited) _ _ hvis hdist

/-- Invariant: Every finite distance produced by `bfsLoop` corresponds to a genuine walk. -/
theorem bfsLoop_dist_walk (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ)
    (queue visited : List (Fin n))
    (dist : Fin n → WithTop ℕ) (count : ℕ)
    (h_dist : ∀ w (d : ℕ), dist w = (d : WithTop ℕ) → IsWalkOfLength adj s w d)
    (h_queue : ∀ u ∈ queue, ∃ (d : ℕ), dist u = (d : WithTop ℕ)) :
    ∀ w (d : ℕ), (bfsLoop adj s fuel queue visited dist count).1 w = (d : WithTop ℕ) →
      IsWalkOfLength adj s w d := by
  induction fuel generalizing queue visited dist count with
  | zero =>
    dsimp [bfsLoop]
    exact h_dist
  | succ fuel ih =>
    cases queue with
    | nil =>
      dsimp [bfsLoop]
      exact h_dist
    | cons u queue =>
      dsimp [bfsLoop]
      have hu_q : u ∈ u :: queue := List.mem_cons_self
      rcases h_queue u hu_q with ⟨du, hdu⟩
      have hu_walk : IsWalkOfLength adj s u du := h_dist u du hdu
      set unvisited := ((adj u).filter (· ∉ visited)).dedup
      have h_new_dist : ∀ w (d : ℕ),
          (if w ∈ unvisited then dist u + 1 else dist w) = (d : WithTop ℕ) →
          IsWalkOfLength adj s w d := by
        intro w d hw
        split_ifs at hw with hw_in
        · rw [List.mem_dedup, List.mem_filter] at hw_in
          have h_edge : w ∈ adj u := hw_in.1
          have hd : dist u + 1 = ((du + 1 : ℕ) : WithTop ℕ) := by
            rw [hdu]
            rfl
          rw [hd] at hw
          have : du + 1 = d := WithTop.coe_inj.mp hw
          subst this
          exact IsWalkOfLength.step hu_walk h_edge
        · exact h_dist w d hw
      have h_new_queue : ∀ x ∈ queue ++ unvisited,
          ∃ (d : ℕ),
            (if x ∈ unvisited then dist u + 1 else dist x) =
              (d : WithTop ℕ) := by
        intro x hx
        rw [List.mem_append] at hx
        cases hx with
        | inl hq =>
          have hq' : x ∈ u :: queue := List.mem_cons_of_mem u hq
          rcases h_queue x hq' with ⟨dx, hdx⟩
          split_ifs with hx_in
          · exact ⟨du + 1, by rw [hdu]; rfl⟩
          · exact ⟨dx, hdx⟩
        | inr h_unvis =>
          rw [if_pos h_unvis]
          exact ⟨du + 1, by rw [hdu]; rfl⟩
      exact ih (queue ++ unvisited) (visited ++ unvisited) _ _ h_new_dist h_new_queue

/-- Any fuel with empty queue immediately terminates. -/
theorem bfsLoop_nil (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ)
    (visited : List (Fin n)) (dist : Fin n → WithTop ℕ) (count : ℕ) :
    bfsLoop adj s fuel [] visited dist count = (dist, count) := by
  cases fuel <;> rfl

/-- Fuel addition lemma: When fuel exceeds remaining queue elements plus unvisited vertices,
any extra fuel produces the identical result. -/
theorem bfsLoop_fuel_add (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ) :
    ∀ (queue visited : List (Fin n)) (dist : Fin n → WithTop ℕ) (count : ℕ) (k : ℕ),
      visited.Nodup →
      queue.Nodup →
      (∀ x ∈ queue, x ∈ visited) →
      queue.length + n ≤ visited.length + fuel →
      bfsLoop adj s (fuel + k) queue visited dist count =
        bfsLoop adj s fuel queue visited dist count := by
  induction fuel with
  | zero =>
    intro queue visited dist count k hvis_nodup hq_nodup hq_vis hq
    cases queue with
    | nil =>
      rw [bfsLoop_nil, bfsLoop_nil]
    | cons u q =>
      have hvis_le := list_length_le_n visited hvis_nodup
      dsimp at hq
      omega
  | succ fuel ih =>
    intro queue visited dist count k hvis_nodup hq_nodup hq_vis hq
    cases queue with
    | nil =>
      rw [bfsLoop_nil, bfsLoop_nil]
    | cons u q =>
      dsimp [bfsLoop]
      have hq_nodup' : q.Nodup := (List.nodup_cons.mp hq_nodup).2
      set next_edges := adj u
      set unvisited := (next_edges.filter (· ∉ visited)).dedup
      set new_visited := visited ++ unvisited
      set new_queue := q ++ unvisited
      set new_dist := fun v ↦ if v ∈ unvisited then dist u + 1 else dist v
      set new_count := count + 1 + next_edges.length
      have h_fuel_k : fuel + 1 + k = (fuel + k) + 1 := by omega
      have h_step : bfsLoop adj s (fuel + 1 + k) (u :: q) visited dist count =
          bfsLoop adj s (fuel + k) new_queue new_visited new_dist new_count := by
        conv => lhs; rw [h_fuel_k]
        rfl
      rw [h_step]
      have h_unvis_not_vis : ∀ x ∈ unvisited, x ∉ visited := by
        intro x hx
        rw [List.mem_dedup, List.mem_filter] at hx
        exact of_decide_eq_true hx.2
      have hnew_vis_nodup : new_visited.Nodup := by
        rw [List.nodup_append]
        refine ⟨hvis_nodup, List.nodup_dedup _, ?_⟩
        intro x hx y hy
        have hy_not_vis := h_unvis_not_vis y hy
        rintro rfl
        exact hy_not_vis hx
      have hnew_q_nodup : new_queue.Nodup := by
        rw [List.nodup_append]
        refine ⟨hq_nodup', List.nodup_dedup _, ?_⟩
        intro x hx y hy
        have hy_not_vis := h_unvis_not_vis y hy
        have hx_vis : x ∈ visited := hq_vis x (List.mem_cons_of_mem u hx)
        rintro rfl
        exact hy_not_vis hx_vis
      have hnew_q_vis : ∀ x ∈ new_queue, x ∈ new_visited := by
        intro x hx
        rw [List.mem_append] at hx ⊢
        cases hx with
        | inl h1 => exact Or.inl (hq_vis x (List.mem_cons_of_mem u h1))
        | inr h2 => exact Or.inr h2
      have h_len : new_queue.length + n ≤ new_visited.length + fuel := by
        dsimp [new_queue, new_visited]
        simp only [List.length_append]
        dsimp at hq
        omega
      exact ih new_queue new_visited new_dist new_count k
        hnew_vis_nodup hnew_q_nodup hnew_q_vis h_len

/-- Real fuel invariance: Any extra fuel beyond `n` produces the identical result on `[s]`. -/
theorem bfsLoop_fuel_invariant (adj : Fin n → List (Fin n)) (s : Fin n) (k : ℕ) :
    bfsLoop adj s (n + k) [s] [s] (bfsInitDist s) 0 =
    bfsLoop adj s n [s] [s] (bfsInitDist s) 0 := by
  have hvis_nodup : ([s] : List (Fin n)).Nodup := List.nodup_singleton s
  have hq_nodup : ([s] : List (Fin n)).Nodup := List.nodup_singleton s
  have hq_vis : ∀ x ∈ ([s] : List (Fin n)), x ∈ ([s] : List (Fin n)) := fun _ h ↦ h
  have h_len : ([s] : List (Fin n)).length + n ≤ ([s] : List (Fin n)).length + n := le_rfl
  exact bfsLoop_fuel_add adj s n [s] [s] (bfsInitDist s) 0 k
    hvis_nodup hq_nodup hq_vis h_len

/-- Instrumented BFS returning distance map and operational step count accumulated in-loop. -/
def bfsWithCount (adj : Fin n → List (Fin n)) (s : Fin n) :
    (Fin n → WithTop ℕ) × ℕ :=
  bfsLoop adj s n [s] [s] (bfsInitDist s) 0

/-- Distance to source vertex is 0 in the returned distance map. -/
theorem bfsWithCount_source (adj : Fin n → List (Fin n)) (s : Fin n) :
    (bfsWithCount adj s).1 s = 0 := by
  dsimp [bfsWithCount]
  have hs : s ∈ [s] := List.mem_singleton_self s
  have hd : bfsInitDist s s = 0 := bfsInitDist_self s
  exact bfsLoop_dist_source adj s n [s] [s] (bfsInitDist s) 0 hs hd

/-- Distance soundness: every finite distance produced by `bfsWithCount` is achieved by a walk. -/
theorem bfsWithCount_walk (adj : Fin n → List (Fin n)) (s v : Fin n) (d : ℕ)
    (h : (bfsWithCount adj s).1 v = (d : WithTop ℕ)) :
    IsWalkOfLength adj s v d := by
  dsimp [bfsWithCount] at h
  have h_init_dist :
      ∀ w (dw : ℕ), bfsInitDist s w = (dw : WithTop ℕ) → IsWalkOfLength adj s w dw := by
    intro w dw hdw
    dsimp [bfsInitDist] at hdw
    split_ifs at hdw with hws
    · subst hws
      have : (0 : WithTop ℕ) = (dw : WithTop ℕ) := hdw
      have hdw0 : dw = 0 := (WithTop.coe_inj.mp this).symm
      subst hdw0
      exact IsWalkOfLength.zero
    · contradiction
  have h_init_q : ∀ u ∈ ([s] : List (Fin n)), ∃ (du : ℕ), bfsInitDist s u = (du : WithTop ℕ) := by
    intro u hu
    simp only [List.mem_singleton] at hu
    rw [hu]
    exact ⟨0, bfsInitDist_self s⟩
  exact bfsLoop_dist_walk adj s n [s] [s] (bfsInitDist s) 0 h_init_dist h_init_q v d h

/-- Total BFS operations accumulated inside the loop are bounded by `|V| + |E|`. -/
theorem bfsWithCount_snd_le (adj : Fin n → List (Fin n)) (s : Fin n) :
    (bfsWithCount adj s).2 ≤ n + edgeCount adj := by
  dsimp [bfsWithCount]
  have hq_nodup : ([s] : List (Fin n)).Nodup := List.nodup_singleton s
  have hq_vis : ∀ x ∈ ([s] : List (Fin n)), x ∈ ([s] : List (Fin n)) := fun _ h ↦ h
  have hq_rem : ∀ x ∈ ([s] : List (Fin n)), x ∈ (Finset.univ : Finset (Fin n)) :=
    fun _ _ ↦ Finset.mem_univ _
  have hvert_rem : ∀ x : Fin n, x ∉ ([s] : List (Fin n)) → x ∈ (Finset.univ : Finset (Fin n)) :=
    fun _ _ ↦ Finset.mem_univ _
  have h := bfsLoop_count_le adj s n [s] [s] (bfsInitDist s) 0
    Finset.univ hq_nodup hq_vis hq_rem hvert_rem
  have hcard : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
  have hsum : ∑ v ∈ (Finset.univ : Finset (Fin n)), outdeg adj v = edgeCount adj := rfl
  omega

/-! ### Two-Sided Equivalence: (bfsWithCount adj s).1 = bfsDist adj s -/

/-- Induction helper: Closed distance map on empty queue bounds all directed walk lengths. -/
lemma dist_le_walk_of_empty_queue
    (adj : Fin n → List (Fin n)) (s : Fin n)
    (visited : List (Fin n)) (dist : Fin n → WithTop ℕ)
    (hs_vis : s ∈ visited) (hs_dist : dist s = 0)
    (h_step : ∀ u ∈ visited, ∀ w ∈ adj u, w ∈ visited ∧ dist w ≤ dist u + 1) :
    ∀ w k, IsWalkOfLength adj s w k → w ∈ visited ∧ dist w ≤ (k : WithTop ℕ) := by
  intro w k h_walk
  induction h_walk with
  | zero =>
    refine ⟨hs_vis, by rw [hs_dist]; exact le_rfl⟩
  | @step u v k h_walk_u h_edge ih =>
    rcases ih with ⟨hu_vis, hu_dist⟩
    have h_next := h_step u hu_vis v h_edge
    refine ⟨h_next.1, ?_⟩
    have h_le := h_next.2
    have : dist u + 1 ≤ (k + 1 : WithTop ℕ) := by
      have hk : (k + 1 : WithTop ℕ) = (k : WithTop ℕ) + 1 := rfl
      rw [hk]
      exact add_le_add hu_dist le_rfl
    exact le_trans h_le this

/-- Queue distance invariant: queue vertices have distance d or d+1, visited distances ≤ d+1,
and all dequeued vertices have closed neighbor distances. -/
def BFSInv (adj : Fin n → List (Fin n)) (s : Fin n)
    (queue visited : List (Fin n)) (dist : Fin n → WithTop ℕ) : Prop :=
  visited.Nodup ∧
  queue.Nodup ∧
  (∀ x ∈ queue, x ∈ visited) ∧
  s ∈ visited ∧ dist s = 0 ∧
  (∀ x ∈ visited, dist x ≠ ⊤) ∧
  (∀ u ∈ visited, u ∉ queue → ∀ w ∈ adj u, w ∈ visited ∧ dist w ≤ dist u + 1) ∧
  ∃ (d : ℕ),
    (∀ x ∈ visited, dist x ≤ (d + 1 : WithTop ℕ)) ∧
    ∃ (q1 q2 : List (Fin n)), queue = q1 ++ q2 ∧
      (∀ x ∈ q1, dist x = (d : WithTop ℕ)) ∧
      (∀ x ∈ q2, dist x = (d + 1 : WithTop ℕ))

/-- Base case: The initial BFS state satisfies `BFSInv` with level `d = 0`. -/
theorem BFSInv_init (adj : Fin n → List (Fin n)) (s : Fin n) :
    BFSInv adj s [s] [s] (bfsInitDist s) := by
  refine ⟨List.nodup_singleton s, List.nodup_singleton s, fun _ h ↦ h,
    List.mem_singleton_self s, bfsInitDist_self s, ?_, ?_, 0, ?_, [s], [], rfl, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [bfsInitDist_self]
    intro h
    contradiction
  · intro u hu hnot
    exact (hnot hu).elim
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [bfsInitDist_self]
    exact WithTop.coe_le_coe.mpr (by omega)
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst hx
    rw [bfsInitDist_self]
    rfl
  · intro x hx
    cases hx

/-- Inductive step: Each step of `bfsLoop` preserves `BFSInv`. -/
theorem BFSInv_step (adj : Fin n → List (Fin n)) (s : Fin n)
    (u : Fin n) (q visited : List (Fin n)) (dist : Fin n → WithTop ℕ)
    (hinv : BFSInv adj s (u :: q) visited dist) :
    let unvisited := ((adj u).filter (· ∉ visited)).dedup
    let new_visited := visited ++ unvisited
    let new_dist := fun v ↦ if v ∈ unvisited then dist u + 1 else dist v
    let new_queue := q ++ unvisited
    BFSInv adj s new_queue new_visited new_dist := by
  intro unvisited new_visited new_dist new_queue
  rcases hinv with ⟨hvis_nodup, hq_nodup, hq_vis, hs_vis, hs_dist,
    hvis_ne_top, h_closed, d, hvis_le_d, q1, q2, hq_eq, hq1_dist, hq2_dist⟩
  have hq_nodup' : q.Nodup := (List.nodup_cons.mp hq_nodup).2
  have hu_not_in_q : u ∉ q := (List.nodup_cons.mp hq_nodup).1
  have hu_vis : u ∈ visited := hq_vis u List.mem_cons_self
  have h_unvis_not_vis : ∀ x ∈ unvisited, x ∉ visited := by
    intro x hx
    rw [List.mem_dedup, List.mem_filter] at hx
    exact of_decide_eq_true hx.2
  have hnew_vis_nodup : new_visited.Nodup := by
    rw [List.nodup_append]
    refine ⟨hvis_nodup, List.nodup_dedup _, ?_⟩
    intro x hx y hy
    have hy_not_vis := h_unvis_not_vis y hy
    rintro rfl
    exact hy_not_vis hx
  have hnew_q_nodup : new_queue.Nodup := by
    rw [List.nodup_append]
    refine ⟨hq_nodup', List.nodup_dedup _, ?_⟩
    intro x hx y hy
    have hy_not_vis := h_unvis_not_vis y hy
    have hx_vis : x ∈ visited := hq_vis x (List.mem_cons_of_mem u hx)
    rintro rfl
    exact hy_not_vis hx_vis
  have hnew_q_vis : ∀ x ∈ new_queue, x ∈ new_visited := by
    intro x hx
    rw [List.mem_append] at hx ⊢
    cases hx with
    | inl h1 => exact Or.inl (hq_vis x (List.mem_cons_of_mem u h1))
    | inr h2 => exact Or.inr h2
  have hs_new_vis : s ∈ new_visited := List.mem_append_left _ hs_vis
  have hs_not_unvis : s ∉ unvisited := fun h ↦ h_unvis_not_vis s h hs_vis
  have hs_new_dist : new_dist s = 0 := by
    dsimp [new_dist]
    rw [if_neg hs_not_unvis, hs_dist]
  have hnew_vis_ne_top : ∀ x ∈ new_visited, new_dist x ≠ ⊤ := by
    intro x hx
    rw [List.mem_append] at hx
    dsimp [new_dist]
    split_ifs with hx_unvis
    · have hu_ne_top := hvis_ne_top u hu_vis
      cases h : dist u with
      | top => contradiction
      | coe val =>
        change ((val + 1 : ℕ) : WithTop ℕ) ≠ ⊤
        exact WithTop.coe_ne_top
    · cases hx with
      | inl h_vis => exact hvis_ne_top x h_vis
      | inr h_unvis => exact (hx_unvis h_unvis).elim
  have hu_dist_ge_d : (d : WithTop ℕ) ≤ dist u := by
    have hu_in_q : u ∈ u :: q := List.mem_cons_self
    rw [hq_eq, List.mem_append] at hu_in_q
    cases hu_in_q with
    | inl h1 =>
      rw [hq1_dist u h1]
    | inr h2 =>
      rw [hq2_dist u h2]
      have : (d : WithTop ℕ) ≤ (d : WithTop ℕ) + 1 := le_self_add
      exact this
  have h_queue_cases :
      (∃ (q1' : List (Fin n)), q1 = u :: q1' ∧ dist u = d) ∨
      (q1 = [] ∧ dist u = d + 1) := by
    cases q1 with
    | nil =>
      have hu_q2 : u ∈ q2 := by
        have : u ∈ [] ++ q2 := by rw [← hq_eq]; exact List.mem_cons_self
        exact this
      exact Or.inr ⟨rfl, by rw [hq2_dist u hu_q2]⟩
    | cons u' q1' =>
      have hu_eq : u = u' := by
        have : u :: q = (u' :: q1') ++ q2 := hq_eq
        injection this
      subst hu_eq
      have hu_q1 : u ∈ u :: q1' := List.mem_cons_self
      exact Or.inl ⟨q1', rfl, by rw [hq1_dist u hu_q1]⟩
  have h_levels :
      ∃ (d_new : ℕ),
        (∀ x ∈ new_visited, new_dist x ≤ (d_new + 1 : WithTop ℕ)) ∧
        ∃ (q1_new q2_new : List (Fin n)), new_queue = q1_new ++ q2_new ∧
          (∀ x ∈ q1_new, new_dist x = (d_new : WithTop ℕ)) ∧
          (∀ x ∈ q2_new, new_dist x = (d_new + 1 : WithTop ℕ)) := by
    cases h_queue_cases with
    | inl h_case1 =>
      rcases h_case1 with ⟨q1', rfl, hdu⟩
      use d
      have hq_split : q = q1' ++ q2 := by
        have : u :: q = (u :: q1') ++ q2 := hq_eq
        injection this
      constructor
      · intro x hx
        rw [List.mem_append] at hx
        dsimp [new_dist]
        split_ifs with hx_unvis
        · rw [hdu]
        · cases hx with
          | inl hx_vis => exact hvis_le_d x hx_vis
          | inr hx_unvis' => exact (hx_unvis hx_unvis').elim
      · use q1', (q2 ++ unvisited)
        refine ⟨by dsimp [new_queue]; rw [hq_split, List.append_assoc], ?_, ?_⟩
        · intro x hx
          dsimp [new_dist]
          have hx_vis : x ∈ visited := by
            have : x ∈ u :: q := by
              rw [hq_eq, List.mem_append]
              exact Or.inl (List.mem_cons_of_mem u hx)
            exact hq_vis x this
          have hx_not_unvis := fun h ↦ h_unvis_not_vis x h hx_vis
          rw [if_neg hx_not_unvis]
          exact hq1_dist x (List.mem_cons_of_mem u hx)
        · intro x hx
          rw [List.mem_append] at hx
          dsimp [new_dist]
          cases hx with
          | inl hx_q2 =>
            have hx_vis : x ∈ visited := by
              have : x ∈ u :: q := by rw [hq_eq, List.mem_append]; exact Or.inr hx_q2
              exact hq_vis x this
            have hx_not_unvis := fun h ↦ h_unvis_not_vis x h hx_vis
            rw [if_neg hx_not_unvis]
            exact hq2_dist x hx_q2
          | inr hx_unvis =>
            rw [if_pos hx_unvis, hdu]
    | inr h_case2 =>
      rcases h_case2 with ⟨rfl, hdu⟩
      use d + 1
      have hq_q2 : q2 = u :: q := by
        have : u :: q = [] ++ q2 := hq_eq
        exact this.symm
      constructor
      · intro x hx
        rw [List.mem_append] at hx
        dsimp [new_dist]
        split_ifs with hx_unvis
        · rw [hdu]
          exact le_rfl
        · cases hx with
          | inl hx_vis =>
            have := hvis_le_d x hx_vis
            have hd_le : (d + 1 : WithTop ℕ) ≤ ((d + 1) + 1 : WithTop ℕ) := le_self_add
            exact le_trans this hd_le
          | inr hx_unvis' => exact (hx_unvis hx_unvis').elim
      · use q, unvisited
        refine ⟨rfl, ?_, ?_⟩
        · intro x hx
          dsimp [new_dist]
          have hx_vis : x ∈ visited := hq_vis x (List.mem_cons_of_mem u hx)
          have hx_not_unvis := fun h ↦ h_unvis_not_vis x h hx_vis
          rw [if_neg hx_not_unvis]
          have hx_q2 : x ∈ q2 := by rw [hq_q2]; exact List.mem_cons_of_mem u hx
          exact hq2_dist x hx_q2
        · intro x hx
          dsimp [new_dist]
          rw [if_pos hx, hdu]
          norm_cast
  have h_closed_new :
      ∀ u' ∈ new_visited, u' ∉ new_queue →
        ∀ w ∈ adj u', w ∈ new_visited ∧ new_dist w ≤ new_dist u' + 1 := by
    intro u' hu' h_not_in_new_q w hw
    rw [List.mem_append] at hu'
    have hu'_not_unvis : u' ∉ unvisited := by
      intro h
      have : u' ∈ new_queue := by dsimp [new_queue]; rw [List.mem_append]; exact Or.inr h
      exact h_not_in_new_q this
    have hu'_vis : u' ∈ visited := by
      cases hu' with
      | inl h => exact h
      | inr h => exact (hu'_not_unvis h).elim
    have hu'_not_q : u' ∉ q := by
      intro h
      have : u' ∈ new_queue := by dsimp [new_queue]; rw [List.mem_append]; exact Or.inl h
      exact h_not_in_new_q this
    have hnew_dist_u' : new_dist u' = dist u' := by
      dsimp [new_dist]
      rw [if_neg hu'_not_unvis]
    by_cases hu'_eq_u : u' = u
    · have hw_case : w ∈ visited ∨ w ∉ visited := Classical.em (w ∈ visited)
      cases hw_case with
      | inl hw_vis =>
        have hw_not_unvis := fun h ↦ h_unvis_not_vis w h hw_vis
        have hnew_dist_w : new_dist w = dist w := by
          dsimp [new_dist]
          rw [if_neg hw_not_unvis]
        refine ⟨List.mem_append_left _ hw_vis, ?_⟩
        rw [hnew_dist_w, hnew_dist_u', hu'_eq_u]
        have hw_le := hvis_le_d w hw_vis
        have hd_le_du := hu_dist_ge_d
        have : (d + 1 : WithTop ℕ) ≤ dist u + 1 := by
          have : (d + 1 : WithTop ℕ) = (d : WithTop ℕ) + 1 := rfl
          rw [this]
          exact add_le_add hd_le_du le_rfl
        exact le_trans hw_le this
      | inr hw_not_vis =>
        have hw_adj_u : w ∈ adj u := by rwa [hu'_eq_u] at hw
        have hw_unvis : w ∈ unvisited := by
          dsimp [unvisited]
          rw [List.mem_dedup, List.mem_filter]
          exact ⟨hw_adj_u, decide_eq_true hw_not_vis⟩
        refine ⟨List.mem_append_right _ hw_unvis, ?_⟩
        dsimp [new_dist]
        rw [if_pos hw_unvis, if_neg hu'_not_unvis, hu'_eq_u]
    · have hu'_not_in_old_q : u' ∉ u :: q := by
        intro h
        cases List.mem_cons.mp h with
        | inl heq => exact hu'_eq_u heq
        | inr hq_mem => exact hu'_not_q hq_mem
      have h_old := h_closed u' hu'_vis hu'_not_in_old_q w hw
      rcases h_old with ⟨hw_vis, hw_dist_le⟩
      have hw_not_unvis := fun h ↦ h_unvis_not_vis w h hw_vis
      have hnew_dist_w : new_dist w = dist w := by
        dsimp [new_dist]
        rw [if_neg hw_not_unvis]
      refine ⟨List.mem_append_left _ hw_vis, ?_⟩
      rw [hnew_dist_w, hnew_dist_u']
      exact hw_dist_le
  exact ⟨hnew_vis_nodup, hnew_q_nodup, hnew_q_vis,
    hs_new_vis, hs_new_dist, hnew_vis_ne_top, h_closed_new, h_levels⟩

/-- Distance optimality: `bfsLoop` returns distances bounded by any genuine walk length. -/
theorem bfsLoop_dist_le_walk (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ) :
    ∀ (queue visited : List (Fin n)) (dist : Fin n → WithTop ℕ) (count : ℕ),
      queue.length + n ≤ visited.length + fuel →
      BFSInv adj s queue visited dist →
      ∀ w k, IsWalkOfLength adj s w k →
        (bfsLoop adj s fuel queue visited dist count).1 w ≤ (k : WithTop ℕ) := by
  induction fuel with
  | zero =>
    intro queue visited dist count h_len hinv w k h_walk
    cases queue with
    | nil =>
      dsimp [bfsLoop]
      rcases hinv with ⟨_, _, _, hs_vis, hs_dist, _, h_closed, _⟩
      have h_empty_closed : ∀ u ∈ visited, ∀ x ∈ adj u, x ∈ visited ∧ dist x ≤ dist u + 1 := by
        intro u hu x hx
        exact h_closed u hu (fun h ↦ nomatch h) x hx
      have h_bound := dist_le_walk_of_empty_queue adj s visited dist hs_vis hs_dist h_empty_closed
      exact (h_bound w k h_walk).2
    | cons u q =>
      have hvis_le := list_length_le_n visited hinv.1
      dsimp at h_len
      omega
  | succ fuel ih =>
    intro queue visited dist count h_len hinv w k h_walk
    cases queue with
    | nil =>
      dsimp [bfsLoop]
      rcases hinv with ⟨_, _, _, hs_vis, hs_dist, _, h_closed, _⟩
      have h_empty_closed : ∀ u ∈ visited, ∀ x ∈ adj u, x ∈ visited ∧ dist x ≤ dist u + 1 := by
        intro u hu x hx
        exact h_closed u hu (fun h ↦ nomatch h) x hx
      have h_bound := dist_le_walk_of_empty_queue adj s visited dist hs_vis hs_dist h_empty_closed
      exact (h_bound w k h_walk).2
    | cons u q =>
      dsimp [bfsLoop]
      set unvisited := ((adj u).filter (· ∉ visited)).dedup
      set new_visited := visited ++ unvisited
      set new_dist := fun v ↦ if v ∈ unvisited then dist u + 1 else dist v
      set new_queue := q ++ unvisited
      set new_count := count + 1 + (adj u).length
      have hinv' := BFSInv_step adj s u q visited dist hinv
      have h_len' : new_queue.length + n ≤ new_visited.length + fuel := by
        dsimp [new_queue, new_visited]
        simp only [List.length_append]
        dsimp at h_len
        omega
      exact ih new_queue new_visited new_dist new_count h_len' hinv' w k h_walk

/-- Distance optimality of `bfsWithCount`: distance is bounded by every directed walk length. -/
theorem bfsWithCount_dist_le_walk (adj : Fin n → List (Fin n)) (s w : Fin n) (k : ℕ)
    (h_walk : IsWalkOfLength adj s w k) :
    (bfsWithCount adj s).1 w ≤ (k : WithTop ℕ) := by
  dsimp [bfsWithCount]
  have h_len : ([s] : List (Fin n)).length + n ≤ ([s] : List (Fin n)).length + n := le_rfl
  have hinv := BFSInv_init adj s
  exact bfsLoop_dist_le_walk adj s n [s] [s] (bfsInitDist s) 0
    h_len hinv w k h_walk

/-- Two-sided distance equivalence: Executable `bfsWithCount` distance map equals canonical
shortest-path distance `bfsDist` everywhere (completeness and optimality). -/
theorem bfsWithCount_fst_eq (adj : Fin n → List (Fin n)) (s : Fin n) :
    (bfsWithCount adj s).1 = bfsDist adj s := by
  funext v
  classical
  by_cases hr : Reachable adj s v
  · have hex : ∃ k, IsWalkOfLength adj s v k := (reachable_iff_exists_walk adj s v).mp hr
    have h_spec : bfsDist adj s v = (Nat.find hex : WithTop ℕ) := by
      dsimp [bfsDist]
      rw [dif_pos hr]
    have h_walk : IsWalkOfLength adj s v (Nat.find hex) := Nat.find_spec hex
    have h_le : (bfsWithCount adj s).1 v ≤ (Nat.find hex : WithTop ℕ) :=
      bfsWithCount_dist_le_walk adj s v (Nat.find hex) h_walk
    cases h_val : (bfsWithCount adj s).1 v with
    | top =>
      rw [h_val] at h_le
      have : ¬ (⊤ : WithTop ℕ) ≤ (Nat.find hex : WithTop ℕ) := by simp
      exact (this h_le).elim
    | coe d =>
      have hd_le : d ≤ Nat.find hex := by
        rw [h_val] at h_le
        exact WithTop.coe_le_coe.mp h_le
      have h_walk_d := bfsWithCount_walk adj s v d h_val
      have hd_ge : Nat.find hex ≤ d := Nat.find_le h_walk_d
      have hd_eq : d = Nat.find hex := by omega
      rw [hd_eq, h_spec]
      rfl
  · have h_spec : bfsDist adj s v = ⊤ := (bfsDist_eq_top_iff adj s v).mpr hr
    rw [h_spec]
    cases h_val : (bfsWithCount adj s).1 v with
    | top => rfl
    | coe d =>
      have h_walk_d := bfsWithCount_walk adj s v d h_val
      have : Reachable adj s v := (reachable_iff_exists_walk adj s v).mpr ⟨d, h_walk_d⟩
      exact (hr this).elim

/-! ### Path Validity -/

/-- A valid directed path in adjacency graph `adj`. -/
def IsPath (adj : Fin n → List (Fin n)) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y ∈ adj x ∧ IsPath adj (y :: rest)

end Amort.Graph
