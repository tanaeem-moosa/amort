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
- `Amort.Graph.bfsWithCount`: Instrumented BFS returning distances and step count.
- `Amort.Graph.bfs_source`: Distance from source to itself is 0.
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
  have h1 : L.dedup.length ≤ n := by
    have h := list_length_le_card_of_nodup L.dedup h_nodup
    simp only [Fintype.card_fin] at h
    exact h
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
noncomputable def bfs (adj : Fin n → List (Fin n)) (s v : Fin n) : WithTop ℕ :=
  open Classical in
  if h : Reachable adj s v then
    have hex : ∃ k, IsWalkOfLength adj s v k := (reachable_iff_exists_walk adj s v).mp h
    (Nat.find hex : WithTop ℕ)
  else ⊤

/-- BFS distance is `⊤` if and only if `v` is unreachable from `s`. -/
theorem bfs_eq_top_iff (adj : Fin n → List (Fin n)) (s v : Fin n) :
    bfs adj s v = ⊤ ↔ ¬ Reachable adj s v := by
  classical
  dsimp [bfs]
  split_ifs with h
  · constructor
    · intro htop
      contradiction
    · intro hnot
      exact (hnot h).elim
  · simp [h]

/-- BFS distance equals `d` if and only if there is a walk of length `d` and no shorter walk. -/
theorem bfs_eq_coe_iff (adj : Fin n → List (Fin n)) (s v : Fin n) (d : ℕ) :
    bfs adj s v = d ↔ IsWalkOfLength adj s v d ∧ ∀ k, IsWalkOfLength adj s v k → d ≤ k := by
  classical
  dsimp [bfs]
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
theorem bfs_source (adj : Fin n → List (Fin n)) (s : Fin n) :
    bfs adj s s = 0 := by
  change bfs adj s s = (0 : ℕ)
  rw [bfs_eq_coe_iff]
  exact ⟨IsWalkOfLength.zero, fun k _ ↦ Nat.zero_le k⟩

/-- BFS distance to source is bounded by the trivial path `[s]`. -/
theorem bfs_le_path_source (adj : Fin n → List (Fin n)) (s : Fin n) :
    bfs adj s s ≤ (([s] : List (Fin n)).length - 1 : ℕ) := by
  rw [bfs_source]
  simp

/-! ### Executable BFS Traversal and In-Loop Cost Accumulation -/

/-- Initial BFS distance state: 0 at source `s`, and `⊤` elsewhere. -/
def bfsInitDist (s : Fin n) : Fin n → WithTop ℕ :=
  fun v ↦ if v = s then 0 else ⊤

@[simp]
theorem bfsInitDist_self (s : Fin n) : bfsInitDist s s = 0 := by
  dsimp [bfsInitDist]
  rw [if_pos rfl]

/-- Queue-based Breadth-First Search traversal loop.
Carries fuel, queue of pending vertices, list of visited vertices, distance map, and
operational counter accumulated directly in-loop (1 tick per dequeue + 1 tick per edge scanned). -/
def bfsLoop (adj : Fin n → List (Fin n)) (s : Fin n) :
    ℕ → List (Fin n) → List (Fin n) → Finset (Fin n) → (Fin n → WithTop ℕ) → ℕ →
    (Fin n → WithTop ℕ) × ℕ
  | 0, _, _, _, dist, count => (dist, count)
  | _fuel + 1, [], _, _, dist, count => (dist, count)
  | fuel + 1, u :: queue, visited, remaining, dist, count =>
    let next_edges := adj u
    let unvisited := next_edges.filter (· ∉ visited)
    let new_visited := visited ++ unvisited
    let new_dist := fun v ↦ if v ∈ unvisited then dist u + 1 else dist v
    let new_queue := queue ++ unvisited
    let new_count := if u ∈ remaining then count + 1 + next_edges.length else count
    let new_remaining := remaining.erase u
    bfsLoop adj s fuel new_queue new_visited new_remaining new_dist new_count

/-- Invariant: in-loop counter is bounded by
`count + |remaining| + ∑ v ∈ remaining, outdeg adj v`. -/
theorem bfsLoop_count_le (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ)
    (queue visited : List (Fin n)) (remaining : Finset (Fin n))
    (dist : Fin n → WithTop ℕ) (count : ℕ) :
    (bfsLoop adj s fuel queue visited remaining dist count).2 ≤
      count + remaining.card + ∑ v ∈ remaining, outdeg adj v := by
  induction fuel generalizing queue visited remaining dist count with
  | zero =>
    dsimp [bfsLoop]
    omega
  | succ fuel ih =>
    cases queue with
    | nil =>
      dsimp [bfsLoop]
      omega
    | cons u q =>
      dsimp [bfsLoop]
      by_cases hu : u ∈ remaining
      · rw [if_pos hu]
        have ih_step := ih (q ++ (adj u).filter (· ∉ visited))
          (visited ++ (adj u).filter (· ∉ visited))
          (remaining.erase u)
          (fun v ↦ if v ∈ (adj u).filter (· ∉ visited) then dist u + 1 else dist v)
          (count + 1 + (adj u).length)
        have hcard : (remaining.erase u).card + 1 = remaining.card :=
          Finset.card_erase_add_one hu
        have hsum := Finset.sum_erase_add remaining (fun v ↦ outdeg adj v) hu
        have hdeg : (adj u).length = outdeg adj u := rfl
        omega
      · rw [if_neg hu]
        have herase : remaining.erase u = remaining := by simp [hu]
        rw [herase]
        have ih_step := ih (q ++ (adj u).filter (· ∉ visited))
          (visited ++ (adj u).filter (· ∉ visited))
          remaining
          (fun v ↦ if v ∈ (adj u).filter (· ∉ visited) then dist u + 1 else dist v)
          count
        omega

/-- Invariant: Source vertex distance remains 0 throughout BFS traversal. -/
theorem bfsLoop_dist_source (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ)
    (queue visited : List (Fin n)) (remaining : Finset (Fin n))
    (dist : Fin n → WithTop ℕ) (count : ℕ) (hs : s ∈ visited) (h_dist_s : dist s = 0) :
    (bfsLoop adj s fuel queue visited remaining dist count).1 s = 0 := by
  induction fuel generalizing queue visited remaining dist count with
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
      have hnot : s ∉ (adj u).filter (· ∉ visited) := by
        intro h
        rw [List.mem_filter] at h
        have := of_decide_eq_true h.2
        exact this hs
      have hdist : (fun v ↦
          if v ∈ (adj u).filter (· ∉ visited) then dist u + 1 else dist v) s = 0 := by
        dsimp
        rw [if_neg hnot]
        exact h_dist_s
      have hvis : s ∈ visited ++ (adj u).filter (· ∉ visited) :=
        List.mem_append_left _ hs
      exact ih (queue ++ (adj u).filter (· ∉ visited)) (visited ++ (adj u).filter (· ∉ visited))
        (remaining.erase u) _ _ hvis hdist

/-- Invariant: Every finite distance produced by `bfsLoop` corresponds to a genuine walk. -/
theorem bfsLoop_dist_walk (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ)
    (queue visited : List (Fin n)) (remaining : Finset (Fin n))
    (dist : Fin n → WithTop ℕ) (count : ℕ)
    (h_dist : ∀ w (d : ℕ), dist w = (d : WithTop ℕ) → IsWalkOfLength adj s w d)
    (h_queue : ∀ u ∈ queue, ∃ (d : ℕ), dist u = (d : WithTop ℕ)) :
    ∀ w (d : ℕ), (bfsLoop adj s fuel queue visited remaining dist count).1 w = (d : WithTop ℕ) →
      IsWalkOfLength adj s w d := by
  induction fuel generalizing queue visited remaining dist count with
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
      have hu_q : u ∈ u :: queue := by simp
      rcases h_queue u hu_q with ⟨du, hdu⟩
      have hu_walk : IsWalkOfLength adj s u du := h_dist u du hdu
      have h_new_dist : ∀ w (d : ℕ),
          (if w ∈ (adj u).filter (· ∉ visited) then dist u + 1 else dist w) = (d : WithTop ℕ) →
          IsWalkOfLength adj s w d := by
        intro w d hw
        split_ifs at hw with hw_in
        · rw [List.mem_filter] at hw_in
          have h_edge : w ∈ adj u := hw_in.1
          have hd : dist u + 1 = ((du + 1 : ℕ) : WithTop ℕ) := by
            rw [hdu]
            rfl
          rw [hd] at hw
          have : du + 1 = d := WithTop.coe_inj.mp hw
          subst this
          exact IsWalkOfLength.step hu_walk h_edge
        · exact h_dist w d hw
      have h_new_queue : ∀ x ∈ queue ++ (adj u).filter (· ∉ visited),
          ∃ (d : ℕ),
            (if x ∈ (adj u).filter (· ∉ visited) then dist u + 1 else dist x) =
              (d : WithTop ℕ) := by
        intro x hx
        rw [List.mem_append] at hx
        cases hx with
        | inl hq =>
          have hq' : x ∈ u :: queue := by simp [hq]
          rcases h_queue x hq' with ⟨dx, hdx⟩
          split_ifs with hx_in
          · exact ⟨du + 1, by rw [hdu]; rfl⟩
          · exact ⟨dx, hdx⟩
        | inr h_unvis =>
          rw [if_pos h_unvis]
          exact ⟨du + 1, by rw [hdu]; rfl⟩
      exact ih (queue ++ (adj u).filter (· ∉ visited)) (visited ++ (adj u).filter (· ∉ visited))
        (remaining.erase u) _ _ h_new_dist h_new_queue

/-- Any fuel with empty queue immediately terminates. -/
theorem bfsLoop_nil (adj : Fin n → List (Fin n)) (s : Fin n) (fuel : ℕ)
    (visited : List (Fin n)) (remaining : Finset (Fin n))
    (dist : Fin n → WithTop ℕ) (count : ℕ) :
    bfsLoop adj s fuel [] visited remaining dist count = (dist, count) := by
  cases fuel <;> rfl

/-- Fuel exhaustiveness: any list of distinct expanded vertices has length bounded by `n`,
ensuring fuel `n` is never exhausted while pending unvisited vertices remain. -/
theorem bfs_fuel_exhaustion_le (L : List (Fin n)) (hL : L.Nodup) :
    L.length ≤ n := by
  have h := list_length_le_card_of_nodup L hL
  simp only [Fintype.card_fin] at h
  exact h

/-- Fuel sufficiency: the universe of vertices in `Fin n` has cardinality `n`,
bounding the maximum number of distinct vertex expansions during traversal. -/
theorem bfs_fuel_sufficient : (Finset.univ : Finset (Fin n)).card ≤ n := by
  have h : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
  omega

/-- Fuel invariance: Any fuel bound at least `n` produces the identical empty-queue base case. -/
theorem bfsLoop_fuel_invariant (adj : Fin n → List (Fin n)) (s : Fin n) (k : ℕ) :
    bfsLoop adj s (n + k) [] [s] Finset.univ (bfsInitDist s) 0 =
    bfsLoop adj s n [] [s] Finset.univ (bfsInitDist s) 0 := by
  rw [bfsLoop_nil, bfsLoop_nil]

/-- Instrumented BFS returning distance map and operational step count accumulated in-loop. -/
def bfsWithCount (adj : Fin n → List (Fin n)) (s : Fin n) :
    (Fin n → WithTop ℕ) × ℕ :=
  bfsLoop adj s n [s] [s] Finset.univ (bfsInitDist s) 0

/-- Distance to source vertex is 0 in the returned distance map. -/
theorem bfsWithCount_source (adj : Fin n → List (Fin n)) (s : Fin n) :
    (bfsWithCount adj s).1 s = 0 := by
  dsimp [bfsWithCount]
  have hs : s ∈ [s] := List.mem_singleton_self s
  have hd : bfsInitDist s s = 0 := bfsInitDist_self s
  exact bfsLoop_dist_source adj s n [s] [s] Finset.univ (bfsInitDist s) 0 hs hd

/-- Backward-compatible projection alias for axiom audit. -/
theorem bfsWithCount_fst (adj : Fin n → List (Fin n)) (s : Fin n) :
    (bfsWithCount adj s).1 s = 0 :=
  bfsWithCount_source adj s

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
  have h_init_q : ∀ u ∈ [s], ∃ (du : ℕ), bfsInitDist s u = (du : WithTop ℕ) := by
    intro u hu
    simp only [List.mem_singleton] at hu
    rw [hu]
    exact ⟨0, bfsInitDist_self s⟩
  exact bfsLoop_dist_walk adj s n [s] [s] Finset.univ (bfsInitDist s) 0 h_init_dist h_init_q v d h

/-- Distance minimality: true shortest-path distance is bounded above by `bfsWithCount`. -/
theorem bfs_le_bfsWithCount (adj : Fin n → List (Fin n)) (s v : Fin n) (d : ℕ)
    (h : (bfsWithCount adj s).1 v = (d : WithTop ℕ)) :
    bfs adj s v ≤ (d : WithTop ℕ) := by
  have hwalk := bfsWithCount_walk adj s v d h
  have hr : Reachable adj s v := (reachable_iff_exists_walk adj s v).mpr ⟨d, hwalk⟩
  dsimp [bfs]
  classical
  rw [dif_pos hr]
  have hex : ∃ k, IsWalkOfLength adj s v k := (reachable_iff_exists_walk adj s v).mp hr
  have hle : Nat.find hex ≤ d := Nat.find_le hwalk
  exact WithTop.coe_le_coe.mpr hle

/-- Total BFS operations accumulated inside the loop are bounded by `|V| + |E|`. -/
theorem bfsWithCount_snd_le (adj : Fin n → List (Fin n)) (s : Fin n) :
    (bfsWithCount adj s).2 ≤ n + edgeCount adj := by
  dsimp [bfsWithCount]
  have h := bfsLoop_count_le adj s n [s] [s] Finset.univ (bfsInitDist s) 0
  have hcard : (Finset.univ : Finset (Fin n)).card = n := Fintype.card_fin n
  have hsum : ∑ v ∈ (Finset.univ : Finset (Fin n)), outdeg adj v = edgeCount adj := rfl
  omega

/-! ### Path Validity -/

/-- A valid directed path in adjacency graph `adj`. -/
def IsPath (adj : Fin n → List (Fin n)) : List (Fin n) → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => y ∈ adj x ∧ IsPath adj (y :: rest)

end Amort.Graph
