/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Order.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Online Running Median with Dual Heaps

> **Status: stub — not verified** (Phase 3 canon stub; partition median soundness is proven,
> but heap insertion/rebalancing operations are specification stubs).

This module formalizes the dual-heap streaming model for computing the running median
over an online data stream:
- Lower half maintained in a max-heap `low`.
- Upper half maintained in a min-heap `high`.
- Balance invariant: `|size(low) - size(high)| ≤ 1`, with `size(low) = size(high)` or
  `size(low) = size(high) + 1`.
- Partition invariant: every element in `low` is `≤` every element in `high`.
- Median query in $O(1)$ operations, proven mathematically identical to the true median.
- Insertion and rebalancing in $O(\log n)$ operations.

## Mathematical Architecture

1. **Dual Heap Structure & Invariants**:
   - `DualHeap α`: pair of lists `(low, high)` representing the two heap partitions.
   - `IsBalanced`: invariant that `low.length = high.length ∨ low.length = high.length + 1`.
   - `IsPartitioned`: invariant that `∀ x ∈ low, ∀ y ∈ high, x ≤ y`.

2. **Median Mathematical Characterization**:
   For any stream of elements $L = low ++ high$, an element $m$ is a median if at least
   $\lceil |L| / 2 \rceil$ elements are $\le m$ and at least $\lceil |L| / 2 \rceil$ elements
   (or $\lfloor |L| / 2 \rfloor + 1$) are $\ge m$.
   We prove that the maximal element of `low` satisfies these count bounds whenever
   `IsBalanced` and `IsPartitioned` hold.

3. **Step Bounds**:
   - `medianQuerySteps = 1`: peeking the root takes $O(1)$ time.
   - `onlineMedianInsertBound n = 5 * Nat.size n + 1`: inserting an element and rebalancing
     by moving at most one element between heaps takes $O(\log n)$ steps.

## Key Definitions and Theorems
- `Amort.DataStructure.DualHeap`: Structure representing the dual-heap state.
- `Amort.DataStructure.DualHeap.IsBalanced`: Balance invariant.
- `Amort.DataStructure.DualHeap.IsPartitioned`: Partition ordering invariant.
- `Amort.DataStructure.IsMaxOf`: Characterization of maximum element of a collection.
- `Amort.DataStructure.dualHeap_max_low_is_median`: Theorem proving dual-heap root is
  the mathematically valid median of all inserted elements.
- `Amort.DataStructure.medianQuerySteps`: Constant query work.
- `Amort.DataStructure.onlineMedianInsertBound`: Logarithmic insertion work model.
-/

namespace Amort.DataStructure

/-- Dual-heap structure holding elements in lower and upper partitions. -/
structure DualHeap (α : Type*) where
  low : List α
  high : List α
  deriving Repr, DecidableEq

namespace DualHeap

/-- Total number of elements stored across both heaps. -/
def size {α : Type*} (d : DualHeap α) : ℕ :=
  d.low.length + d.high.length

/-- Flattened list of all elements stored in the dual heap. -/
def toList {α : Type*} (d : DualHeap α) : List α :=
  d.low ++ d.high

@[simp]
theorem length_toList {α : Type*} (d : DualHeap α) :
    d.toList.length = d.size := by
  dsimp [toList, size]
  rw [List.length_append]

/-- Balance invariant: `low` contains either the same number of elements as `high`,
or exactly one more element than `high`. -/
def IsBalanced {α : Type*} (d : DualHeap α) : Prop :=
  d.low.length = d.high.length ∨ d.low.length = d.high.length + 1

/-- Balance invariant implies size difference is at most 1. -/
theorem balance_diff_le_one {α : Type*} (d : DualHeap α) (h : d.IsBalanced) :
    d.low.length ≤ d.high.length + 1 ∧ d.high.length ≤ d.low.length := by
  rcases h with h_eq | h_succ
  · omega
  · omega

/-- Balance invariant implies `low.length` is at least `(d.size + 1) / 2`. -/
theorem low_length_ge_half {α : Type*} (d : DualHeap α) (h : d.IsBalanced) :
    (d.size + 1) / 2 ≤ d.low.length := by
  dsimp [size]
  rcases h with h_eq | h_succ
  · omega
  · omega

/-- Partition invariant: every element in `low` is `≤` every element in `high`. -/
def IsPartitioned {α : Type*} [Preorder α] (d : DualHeap α) : Prop :=
  ∀ x ∈ d.low, ∀ y ∈ d.high, x ≤ y

/-- Valid dual-heap bundling balance and partition invariants. -/
structure Valid {α : Type*} [Preorder α] (d : DualHeap α) : Prop where
  balanced : d.IsBalanced
  partitioned : d.IsPartitioned

end DualHeap

/-! ### Mathematical Median Specification & Soundness -/

/-- Predicate that `m` is the maximum element of a list `l`. -/
def IsMaxOf {α : Type*} [Preorder α] (m : α) (l : List α) : Prop :=
  m ∈ l ∧ ∀ x ∈ l, x ≤ m

/-- Predicate that `m` is the minimum element of a list `l`. -/
def IsMinOf {α : Type*} [Preorder α] (m : α) (l : List α) : Prop :=
  m ∈ l ∧ ∀ x ∈ l, m ≤ x

/-- An element `m` is a median of a list `l` if:
1. At least `(l.length + 1) / 2` elements are `≤ m`.
2. At least `l.length / 2` elements are `≥ m`. -/
def IsMedianOfList {α : Type*} [LinearOrder α]
    (m : α) (l : List α) : Prop :=
  (l.length + 1) / 2 ≤ (l.filter (· ≤ m)).length ∧
  l.length / 2 ≤ (l.filter (m ≤ ·)).length

/-- Lower count bound: if `m` is the maximum of `d.low` in a partitioned dual heap,
all elements of `d.low` are `≤ m`. -/
theorem count_le_m_ge_low {α : Type*} [LinearOrder α]
    (d : DualHeap α) (m : α) (hm : IsMaxOf m d.low) :
    d.low.length ≤ (d.toList.filter (· ≤ m)).length := by
  dsimp [DualHeap.toList]
  rw [List.filter_append, List.length_append]
  have h_all : d.low.filter (· ≤ m) = d.low := by
    apply List.filter_eq_self.mpr
    intro x hx
    simp [hm.2 x hx]
  rw [h_all]
  omega

/-- Upper count bound: if `m` is the maximum of `d.low` in a partitioned dual heap,
then `m` itself plus all elements of `d.high` are `≥ m`. -/
theorem count_ge_m_ge_high {α : Type*} [LinearOrder α]
    (d : DualHeap α) (hpart : d.IsPartitioned) (m : α) (hm : IsMaxOf m d.low) :
    d.high.length ≤ (d.toList.filter (m ≤ ·)).length := by
  dsimp [DualHeap.toList]
  rw [List.filter_append, List.length_append]
  have h_high : d.high.filter (m ≤ ·) = d.high := by
    apply List.filter_eq_self.mpr
    intro y hy
    simp [hpart m hm.1 y hy]
  rw [h_high]
  omega

/-- Theorem: in a valid balanced and partitioned dual heap, the maximum element
of `d.low` is mathematically a median of the combined inserted elements `d.toList`. -/
theorem dualHeap_max_low_is_median {α : Type*} [LinearOrder α]
    (d : DualHeap α) (hval : d.Valid) (m : α) (hm : IsMaxOf m d.low) :
    IsMedianOfList m d.toList := by
  constructor
  · have h_count := count_le_m_ge_low d m hm
    have h_half := d.low_length_ge_half hval.balanced
    rw [d.length_toList]
    exact h_half.trans h_count
  · have h_count := count_ge_m_ge_high d hval.partitioned m hm
    rw [d.length_toList]
    dsimp [DualHeap.size]
    rcases hval.balanced with h_eq | h_succ
    · omega
    · omega

/-! ### Step Bounds -/

/-- Peeking the root of the heap takes $O(1)$ operations. -/
def medianQuerySteps : ℕ := 1

@[simp]
theorem medianQuerySteps_eq : medianQuerySteps = 1 := rfl

/-- Total operational work for inserting an element into a dual heap of size `n`
and restoring the balance and partition invariants:
1 comparison to route to heap, sift-up into heap ($\le \text{Nat.size } n$),
plus at most 1 extraction and insertion to rebalance ($\le 4 \cdot \text{Nat.size } n$). -/
def onlineMedianInsertBound (n : ℕ) : ℕ :=
  5 * Nat.size n + 1

/-- Insertion work is bounded by `6 * Nat.size n + 1`. -/
theorem onlineMedianInsertWork_le (n : ℕ) :
    onlineMedianInsertBound n ≤ 6 * Nat.size n + 1 := by
  dsimp [onlineMedianInsertBound]
  omega

end Amort.DataStructure
