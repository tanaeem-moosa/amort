/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Amort.Sorting.MergeSort
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interval Scheduling / Activity Selection

This module formalizes the classical greedy interval scheduling algorithm:
- Interval representation with valid positive duration $[start, finish)$.
- Pairwise and chain compatibility predicates.
- Greedy earliest-finish-time selection algorithm.
- Formal proof of the exchange argument: any valid schedule can be transformed
  without reducing cardinality into one beginning with the greedy choice.
- Cardinality optimality: greedy selection achieves maximum schedule size.
- Operational step bound $O(n \log n)$ dominated by sorting.

## Key Definitions and Theorems
- `Amort.Greedy.Interval`: Structure for an interval with $start < finish$.
- `Amort.Greedy.Compatible`: Binary non-overlapping predicate.
- `Amort.Greedy.ChainCompatible`: Inductive sequence compatibility.
- `Amort.Greedy.greedySelect`: Greedy selection given finish threshold.
- `Amort.Greedy.greedyIntervalSchedule`: Complete greedy selection.
- `Amort.Greedy.chainCompatible_pairwise`: Chain compatibility implies pairwise compatibility.
- `Amort.Greedy.greedySelect_chainCompatible`: Greedy schedule is chain-compatible.
- `Amort.Greedy.SortedByFinish`: Predicate that intervals are ordered by finish time.
- `Amort.Greedy.intervalSchedule_valid`: Validity of schedule from unsorted input.
- `Amort.Greedy.intervalSchedule_optimal`: Global optimality of end-to-end pipeline.
-/

namespace Amort.Greedy

/-- A continuous time interval $[start, finish)$ with strictly positive duration. -/
structure Interval where
  start : ℕ
  finish : ℕ
  start_lt_finish : start < finish
  deriving DecidableEq, Repr

/-- Two intervals are compatible if they do not overlap in time. -/
def Compatible (i1 i2 : Interval) : Prop :=
  i1.finish ≤ i2.start ∨ i2.finish ≤ i1.start

lemma compatible_comm (i1 i2 : Interval) : Compatible i1 i2 ↔ Compatible i2 i1 := by
  unfold Compatible
  omega

/-- A list of intervals is chain-compatible if each interval finishes before or at
the start of the subsequent interval. -/
def ChainCompatible : List Interval → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x.finish ≤ y.start ∧ ChainCompatible (y :: rest)

/-- Pairwise compatibility of a schedule. -/
def PairwiseCompatible (L : List Interval) : Prop :=
  L.Pairwise Compatible

lemma chainCompatible_cons {x : Interval} :
    ∀ {rest : List Interval}, ChainCompatible (x :: rest) → ChainCompatible rest
  | [], _ => trivial
  | _ :: _, h => h.2

lemma chainCompatible_all_start_ge {x : Interval} :
    ∀ {rest : List Interval}, ChainCompatible (x :: rest) →
      ∀ y ∈ rest, x.finish ≤ y.start
  | [], _, _, hmem => by contradiction
  | y :: rest, h, z, hmem => by
    rcases List.mem_cons.mp hmem with rfl | hmem_rest
    · exact h.1
    · have h_rec := chainCompatible_all_start_ge h.2 z hmem_rest
      have hy : y.start < y.finish := y.start_lt_finish
      have hxy : x.finish ≤ y.start := h.1
      omega

theorem chainCompatible_pairwise :
    ∀ {L : List Interval}, ChainCompatible L → PairwiseCompatible L
  | [] => by intro _; simp [PairwiseCompatible]
  | [_] => by intro _; simp [PairwiseCompatible]
  | x :: y :: rest => by
    intro h
    rw [PairwiseCompatible, List.pairwise_cons]
    refine ⟨?_, ?_⟩
    · intro z hz
      have hle := chainCompatible_all_start_ge h z hz
      exact Or.inl hle
    · exact chainCompatible_pairwise h.2

/-- An interval list is sorted by finish time. -/
def SortedByFinish (L : List Interval) : Prop :=
  L.Pairwise (fun a b ↦ a.finish ≤ b.finish)

lemma sortedByFinish_cons {x : Interval} {xs : List Interval} (h : SortedByFinish (x :: xs)) :
    SortedByFinish xs :=
  List.Pairwise.of_cons h

lemma sortedByFinish_head_le {x : Interval} {xs : List Interval} (h : SortedByFinish (x :: xs)) :
    ∀ y ∈ xs, x.finish ≤ y.finish := by
  intro y hy
  exact (List.pairwise_cons.mp h).1 y hy

/-- Greedy selection from a list of intervals: picks intervals with earliest finish time
that start after or at `lastFinish`. -/
def greedySelect (lastFinish : ℕ) : List Interval → List Interval
  | [] => []
  | x :: xs =>
    if lastFinish ≤ x.start then
      x :: greedySelect x.finish xs
    else
      greedySelect lastFinish xs

/-- Total greedy interval scheduling: selects compatible intervals starting from time 0. -/
def greedyIntervalSchedule (L : List Interval) : List Interval :=
  greedySelect 0 L

lemma greedySelect_mem_all_start_ge (lastFinish : ℕ) :
    ∀ {L : List Interval} {x : Interval},
      x ∈ greedySelect lastFinish L → lastFinish ≤ x.start
  | [], x, h => by contradiction
  | y :: ys, x, h => by
    unfold greedySelect at h
    split at h
    · rcases List.mem_cons.mp h with rfl | hmem
      · rename_i hge
        exact hge
      · have hrec := greedySelect_mem_all_start_ge y.finish hmem
        have hy : y.start < y.finish := y.start_lt_finish
        omega
    · exact greedySelect_mem_all_start_ge lastFinish h

lemma greedySelect_chainCompatible_aux (lastFinish : ℕ) :
    ∀ (L : List Interval), ChainCompatible (greedySelect lastFinish L)
  | [] => by simp [greedySelect, ChainCompatible]
  | x :: xs => by
    unfold greedySelect
    split
    · rename_i hge
      cases hres : greedySelect x.finish xs with
      | nil => simp [ChainCompatible]
      | cons y ys =>
        have hy_mem : y ∈ greedySelect x.finish xs := by
          rw [hres]
          exact List.mem_cons_self ..
        have hy_ge : x.finish ≤ y.start := greedySelect_mem_all_start_ge x.finish hy_mem
        have hrec := greedySelect_chainCompatible_aux x.finish xs
        rw [hres] at hrec
        exact ⟨hy_ge, hrec⟩
    · exact greedySelect_chainCompatible_aux lastFinish xs

/-- The greedy schedule is always chain-compatible. -/
theorem greedySelect_chainCompatible (lastFinish : ℕ) (L : List Interval) :
    ChainCompatible (greedySelect lastFinish L) :=
  greedySelect_chainCompatible_aux lastFinish L

/-- The greedy schedule is always pairwise compatible. -/
theorem greedyIntervalSchedule_pairwiseCompatible (L : List Interval) :
    PairwiseCompatible (greedyIntervalSchedule L) :=
  chainCompatible_pairwise (greedySelect_chainCompatible 0 L)

/-- An interval schedule is valid with respect to a threshold `lastFinish` and
candidate pool `L` if it is chain-compatible, its intervals come from `L`,
and all its intervals start at or after `lastFinish`. -/
def ValidSchedule (lastFinish : ℕ) (L : List Interval) (S : List Interval) : Prop :=
  ChainCompatible S ∧ (∀ x ∈ S, x ∈ L ∧ lastFinish ≤ x.start)

/-- Suffix inclusion helper: if `s ∈ L` and `lastFinish ≤ s.start`, but `x.start < lastFinish`,
then `s ∈ xs`. -/
lemma mem_of_mem_cons_of_not_ge {x : Interval} {xs : List Interval} {lastFinish : ℕ}
    (hx : ¬(lastFinish ≤ x.start)) {s : Interval} (hs_start : lastFinish ≤ s.start)
    (hs_mem : s ∈ x :: xs) : s ∈ xs := by
  rcases List.mem_cons.mp hs_mem with rfl | hs_xs
  · omega
  · exact hs_xs

/-- The greedy exchange optimality theorem:
Given a list `L` sorted by finish time, any valid schedule `S` from `L`
respecting `lastFinish` satisfies `S.length ≤ (greedySelect lastFinish L).length`. -/
theorem greedy_exchange_optimality (L : List Interval) (hsort : SortedByFinish L) :
    ∀ (lastFinish : ℕ) (S : List Interval),
      ValidSchedule lastFinish L S →
      S.length ≤ (greedySelect lastFinish L).length := by
  induction L with
  | nil =>
    intro lastFinish S hvalid
    rcases hvalid with ⟨_, hall⟩
    cases S with
    | nil => simp
    | cons s rest =>
      have hs_mem := (hall s (List.mem_cons_self ..)).1
      contradiction
  | cons x xs ih =>
    intro lastFinish S hvalid
    rcases hvalid with ⟨hchain, hall⟩
    cases S with
    | nil => simp
    | cons s0 rest =>
      have hs0_mem : s0 ∈ s0 :: rest := List.mem_cons_self ..
      have hs0_spec := hall s0 hs0_mem
      have hs0_in_L : s0 ∈ x :: xs := hs0_spec.1
      have hs0_start : lastFinish ≤ s0.start := hs0_spec.2
      have hsort_xs : SortedByFinish xs := sortedByFinish_cons hsort
      unfold greedySelect
      split
      · rename_i hx_ge
        have hx_fin_le_s0_fin : x.finish ≤ s0.finish := by
          rcases List.mem_cons.mp hs0_in_L with rfl | hs0_xs
          · rfl
          · exact sortedByFinish_head_le hsort s0 hs0_xs
        have h_rest_valid : ValidSchedule x.finish xs rest := by
          refine ⟨chainCompatible_cons hchain, ?_⟩
          intro z hz
          have hz_in_S : z ∈ s0 :: rest := List.mem_cons_of_mem s0 hz
          have hz_spec := hall z hz_in_S
          have hz_start_ge_s0_fin : s0.finish ≤ z.start :=
            chainCompatible_all_start_ge hchain z hz
          have hz_ge_x_fin : x.finish ≤ z.start := by omega
          have hz_in_xs : z ∈ xs := by
            rcases List.mem_cons.mp hz_spec.1 with rfl | hz_xs
            · have hx_lt := z.start_lt_finish
              omega
            · exact hz_xs
          exact ⟨hz_in_xs, hz_ge_x_fin⟩
        have h_rest_len := ih hsort_xs x.finish rest h_rest_valid
        simp only [List.length_cons]
        omega
      · rename_i hx_not_ge
        have hs0_in_xs : s0 ∈ xs :=
          mem_of_mem_cons_of_not_ge hx_not_ge hs0_start hs0_in_L
        have h_S_valid : ValidSchedule lastFinish xs (s0 :: rest) := by
          refine ⟨hchain, ?_⟩
          intro z hz
          have hz_spec := hall z hz
          have hz_in_xs : z ∈ xs := by
            rcases List.mem_cons.mp hz_spec.1 with rfl | hz_xs
            · omega
            · exact hz_xs
          exact ⟨hz_in_xs, hz_spec.2⟩
        exact ih hsort_xs lastFinish (s0 :: rest) h_S_valid

/-- Global optimality: for any list of intervals `L` sorted by finish time,
the greedy interval schedule produces a schedule of maximum cardinality. -/
theorem greedyIntervalSchedule_optimal (L : List Interval) (hsort : SortedByFinish L) :
    ∀ (S : List Interval), ValidSchedule 0 L S →
      S.length ≤ (greedyIntervalSchedule L).length := by
  intro S hvalid
  exact greedy_exchange_optimality L hsort 0 S hvalid

/-! ### Step Count and Asymptotic Complexity -/

/-- Step counter for the greedy selection pass: each candidate interval is examined
at most once. -/
def greedyScanSteps : List Interval → ℕ
  | [] => 0
  | _ :: xs => 1 + greedyScanSteps xs

lemma greedyScanSteps_eq_length (L : List Interval) :
    greedyScanSteps L = L.length := by
  induction L with
  | nil => rfl
  | cons _ xs ih => simp [greedyScanSteps, ih, Nat.add_comm]

lemma greedySelect_subset (lastFinish : ℕ) : ∀ {L : List Interval} {x : Interval},
    x ∈ greedySelect lastFinish L → x ∈ L
  | [], _, h => by contradiction
  | y :: ys, x, h => by
    unfold greedySelect at h
    split at h
    · rcases List.mem_cons.mp h with rfl | hmem
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem y (greedySelect_subset _ hmem)
    · exact List.mem_cons_of_mem y (greedySelect_subset _ h)

/-! ### Executable Full Pipeline with Instrumented Operation Counting -/

/-- Boolean comparison by finish time. -/
def intervalLe (i1 i2 : Interval) : Bool :=
  i1.finish <= i2.finish

lemma intervalLe_trans (a b c : Interval) (h1 : intervalLe a b = true)
    (h2 : intervalLe b c = true) : intervalLe a c = true := by
  dsimp [intervalLe] at *
  rw [decide_eq_true_iff] at *
  omega

lemma intervalLe_total (a b : Interval) : (intervalLe a b || intervalLe b a) = true := by
  dsimp [intervalLe]
  rw [Bool.or_eq_true, decide_eq_true_iff, decide_eq_true_iff]
  omega

theorem sortedByFinish_mergeSort (L : List Interval) :
    SortedByFinish (L.mergeSort intervalLe) := by
  have h := List.pairwise_mergeSort intervalLe_trans intervalLe_total L
  unfold SortedByFinish
  refine List.Pairwise.imp ?_ h
  intro a b hab
  dsimp [intervalLe] at hab
  exact of_decide_eq_true hab

lemma chainCompatible_of_pairwise_of_sorted : ∀ {S : List Interval},
    PairwiseCompatible S → SortedByFinish S → ChainCompatible S
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | x :: y :: rest, hcompat, hsort => by
    rw [PairwiseCompatible, List.pairwise_cons] at hcompat
    rw [SortedByFinish, List.pairwise_cons] at hsort
    have h_rec := chainCompatible_of_pairwise_of_sorted hcompat.2 hsort.2
    have hxy_compat : Compatible x y := hcompat.1 y (List.mem_cons_self ..)
    have hxy_le : x.finish ≤ y.finish := hsort.1 y (List.mem_cons_self ..)
    have hx_lt := x.start_lt_finish
    have hxy_start : x.finish ≤ y.start := by
      rcases hxy_compat with h1 | h2
      · exact h1
      · omega
    exact ⟨hxy_start, h_rec⟩

/-- Complete interval scheduling algorithm:
first sorts intervals by finish time, then runs the greedy linear scan. -/
def intervalSchedule (L : List Interval) : List Interval :=
  greedyIntervalSchedule (L.mergeSort intervalLe)

/-- The schedule produced by `intervalSchedule` is pairwise compatible and consists of
intervals from the input list `L`. -/
theorem intervalSchedule_valid (L : List Interval) :
    PairwiseCompatible (intervalSchedule L) ∧ ∀ x ∈ intervalSchedule L, x ∈ L := by
  refine ⟨greedyIntervalSchedule_pairwiseCompatible (L.mergeSort intervalLe), ?_⟩
  intro x hx
  have h_sub := greedySelect_subset 0 hx
  exact (List.mergeSort_perm L intervalLe).mem_iff.mp h_sub

/-- Global optimality of `intervalSchedule`: produces a schedule of maximum cardinality
from arbitrary (unsorted) input `L`. -/
theorem intervalSchedule_optimal (L S : List Interval)
    (hS : PairwiseCompatible S) (hsub : ∀ x ∈ S, x ∈ L) (_hnd : S.Nodup) :
    S.length ≤ (intervalSchedule L).length := by
  let S' := S.mergeSort intervalLe
  have hperm : S'.Perm S := List.mergeSort_perm S intervalLe
  have hS'_compat : PairwiseCompatible S' :=
    List.Pairwise.perm hS hperm.symm (fun h => (compatible_comm _ _).mp h)
  have hS'_sort : SortedByFinish S' := sortedByFinish_mergeSort S
  have hS'_chain : ChainCompatible S' :=
    chainCompatible_of_pairwise_of_sorted hS'_compat hS'_sort
  have h_valid : ValidSchedule 0 (L.mergeSort intervalLe) S' := by
    refine ⟨hS'_chain, ?_⟩
    intro z hz
    have hz_in_S : z ∈ S := hperm.mem_iff.mp hz
    have hz_in_L : z ∈ L := hsub z hz_in_S
    have hz_in_sortedL : z ∈ L.mergeSort intervalLe :=
      (List.mergeSort_perm L intervalLe).mem_iff.mpr hz_in_L
    exact ⟨hz_in_sortedL, Nat.zero_le _⟩
  have h_opt := greedy_exchange_optimality (L.mergeSort intervalLe)
    (sortedByFinish_mergeSort L) 0 S' h_valid
  have hlen : S'.length = S.length := hperm.length_eq
  rw [hlen] at h_opt
  exact h_opt

/-- Instrumented interval scheduling: sorts intervals with comparison counter,
then scans with step counter, returning the schedule and total operations. -/
def intervalScheduleWithCount (L : List Interval) : List Interval × ℕ :=
  let res := List.mergeSortWithCount intervalLe L
  let schedule := greedyIntervalSchedule res.1
  (schedule, res.2 + res.1.length)

/-- First projection of instrumented pipeline matches pure `intervalSchedule`. -/
theorem intervalScheduleWithCount_fst (L : List Interval) :
    (intervalScheduleWithCount L).1 = intervalSchedule L := by
  dsimp [intervalScheduleWithCount, intervalSchedule]
  rw [List.mergeSortWithCount_fst]

/-- Operational cost of interval scheduling is bounded by sorting comparisons
plus scan steps. -/
theorem intervalScheduleWithCount_snd_le (L : List Interval) :
    (intervalScheduleWithCount L).2 ≤ L.length * Nat.size L.length + L.length := by
  dsimp [intervalScheduleWithCount]
  have _hsort := List.mergeSortWithCount_snd_le_mul_size intervalLe L
  have hlen : (List.mergeSortWithCount intervalLe L).1.length = L.length := by
    have hperm := List.mergeSortWithCount_perm intervalLe L
    exact hperm.length_eq
  rw [hlen]
  omega

/-- Concrete upper bound for instrumented interval scheduling:
at most $2n \cdot \text{Nat.size } n$ total operations for $n \ge 1$. -/
theorem intervalScheduleWithCount_snd_le_mul (L : List Interval) (hn : 1 ≤ L.length) :
    (intervalScheduleWithCount L).2 ≤ 2 * L.length * Nat.size L.length := by
  have _h1 := intervalScheduleWithCount_snd_le L
  have h_size : 1 ≤ Nat.size L.length := Nat.size_pos.mpr hn
  have _h_n_le : L.length ≤ L.length * Nat.size L.length := by
    calc L.length = L.length * 1 := by ring
    _ ≤ L.length * Nat.size L.length := Nat.mul_le_mul_left L.length h_size
  linarith

end Amort.Greedy
