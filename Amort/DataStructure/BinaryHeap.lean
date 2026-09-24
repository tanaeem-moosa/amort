/-
Copyright (c) 2026 Amort Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amort Authors
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Priority Queues & Binary Heaps

> **Status: stub — not verified** (Phase 3 canon stub; build-heap summation is proven,
> but array heap siftUp/siftDown operations are specification stubs).

This module formalizes binary heaps, the min-heap order invariant, logarithmic height,
sift-down and sift-up step bounds, the linear build-heap theorem, and heapsort complexity.

## Mathematical Architecture

1. **Tree Representation & Invariants**:
   A binary heap is modeled as an inductive binary tree `Tree α`.
   - `size`: count of nodes in the tree.
   - `height`: maximum root-to-leaf depth.
   - `IsMinHeap`: min-heap order invariant requiring the node value to be `≤` all elements
     in both left and right subtrees, with subtrees recursively satisfying `IsMinHeap`.
   - `min_heap_root_le`: the root of a valid min-heap is minimal over all elements in the heap.
   - `IsLogHeight`: height bounded by `Nat.size (size t)`.

2. **Sift Operations & Step Counting**:
   - `siftUpSteps`: bounded by node depth `d ≤ Nat.size n`.
   - `siftDownSteps`: bounded by `2 * h ≤ 2 * Nat.size n` comparisons.

3. **Linear Build-Heap Theorem**:
   For an array of $n$ elements, `buildHeap` invokes sift-down on each node. A node at height $h$
   costs at most $h$ operations. The total cost across all levels is bounded by:
   $$\sum_{h=0}^{\lfloor \log_2 n \rfloor} \left\lfloor \frac{n}{2^h} \right\rfloor \cdot h
     \le 2n$$
   We formally prove this via the geometric sum identity $\sum_{h=0}^k h \cdot 2^{k-h} \le 2^{k+1}$.

4. **Heapsort Complexity & Correctness**:
   - Extracting $n$ elements from a heap requires at most $n \cdot (2 \cdot \text{Nat.size } n)$
     comparisons.
   - Total heapsort work (build-heap + $n$ extractions) is bounded by
     $2n + 2n \cdot \text{Nat.size } n \le 4n \cdot \text{Nat.size } n + 2$.
   - Repeatedly extracting the root of a min-heap produces a sorted sequence.

## Key Definitions and Theorems
- `Amort.DataStructure.Tree`: Inductive binary tree.
- `Amort.DataStructure.Tree.IsMinHeap`: Min-heap order invariant.
- `Amort.DataStructure.min_heap_root_le`: Root minimality theorem.
- `Amort.DataStructure.geomSum`: Shifted geometric series $\sum_{h=0}^k h \cdot 2^{k-h}$.
- `Amort.DataStructure.geomSum_le`: Upper bound $\le 2^{k+1}$.
- `Amort.DataStructure.buildHeapBound`: Build-heap operational summation.
- `Amort.DataStructure.buildHeap_linear_bound`: Linear bound $\le 2n$ for all $k$.
- `Amort.DataStructure.buildHeap_size_bound`: Linear bound for $k = \text{Nat.size } n$.
- `Amort.DataStructure.heapsortTotalBound`: Total heapsort operational model.
- `Amort.DataStructure.heapsortTotalWork_le`: Linear-logarithmic bound $O(n \log n)$.
- `Amort.DataStructure.isSortedList`: Predicate for sorted lists.
-/

open BigOperators
open Finset

namespace Amort.DataStructure

/-! ### Binary Tree Representation -/

/-- Inductive binary tree for priority queues and heaps. -/
inductive Tree (α : Type*) where
  | nil : Tree α
  | node (val : α) (left : Tree α) (right : Tree α) : Tree α
  deriving Repr, DecidableEq

namespace Tree

/-- Number of nodes in the binary tree. -/
def size {α : Type*} : Tree α → ℕ
  | nil => 0
  | node _ l r => 1 + size l + size r

@[simp]
theorem size_nil {α : Type*} : (nil : Tree α).size = 0 := rfl

@[simp]
theorem size_node {α : Type*} (x : α) (l r : Tree α) :
    (node x l r).size = 1 + l.size + r.size := rfl

/-- Height (maximum depth) of the binary tree. -/
def height {α : Type*} : Tree α → ℕ
  | nil => 0
  | node _ l r => 1 + max (height l) (height r)

@[simp]
theorem height_nil {α : Type*} : (nil : Tree α).height = 0 := rfl

@[simp]
theorem height_node {α : Type*} (x : α) (l r : Tree α) :
    (node x l r).height = 1 + max l.height r.height := rfl

/-- Inorder / preorder flattening of tree elements to a list. -/
def toList {α : Type*} : Tree α → List α
  | nil => []
  | node x l r => x :: (toList l ++ toList r)

@[simp]
theorem toList_nil {α : Type*} : (nil : Tree α).toList = [] := rfl

@[simp]
theorem toList_node {α : Type*} (x : α) (l r : Tree α) :
    (node x l r).toList = x :: (l.toList ++ r.toList) := rfl

theorem length_toList {α : Type*} (t : Tree α) : t.toList.length = t.size := by
  induction t with
  | nil => rfl
  | node x l r ihl ihr =>
    simp only [toList_node, List.length_cons, List.length_append, size_node]
    omega

/-- Membership of an element in a binary tree. -/
def mem {α : Type*} (x : α) : Tree α → Prop
  | nil => False
  | node v l r => x = v ∨ mem x l ∨ mem x r

theorem mem_iff_mem_toList {α : Type*} (x : α) (t : Tree α) :
    t.mem x ↔ x ∈ t.toList := by
  induction t with
  | nil => simp [mem, toList]
  | node v l r ihl ihr =>
    simp only [mem, toList_node, List.mem_cons, List.mem_append, ihl, ihr]

/-! ### Min-Heap Order Invariant -/

/-- Min-heap order invariant: the root value is less than or equal to all elements
in both subtrees, and subtrees recursively satisfy the invariant. -/
def IsMinHeap {α : Type*} [Preorder α] : Tree α → Prop
  | nil => True
  | node v l r =>
      (∀ y ∈ l.toList, v ≤ y) ∧ (∀ y ∈ r.toList, v ≤ y) ∧
      IsMinHeap l ∧ IsMinHeap r

@[simp]
theorem isMinHeap_nil {α : Type*} [Preorder α] : (nil : Tree α).IsMinHeap :=
  trivial

@[simp]
theorem isMinHeap_node {α : Type*} [Preorder α] (v : α) (l r : Tree α) :
    (node v l r).IsMinHeap ↔
      ((∀ y ∈ l.toList, v ≤ y) ∧ (∀ y ∈ r.toList, v ≤ y) ∧
       l.IsMinHeap ∧ r.IsMinHeap) :=
  Iff.rfl

/-- Root minimality: in a valid min-heap, the root value is `≤` every element in the heap. -/
theorem min_heap_root_le {α : Type*} [Preorder α] (v : α) (l r : Tree α)
    (h : (node v l r).IsMinHeap) (y : α) (hy : y ∈ (node v l r).toList) : v ≤ y := by
  simp only [toList_node, List.mem_cons, List.mem_append] at hy
  rcases hy with rfl | hy_l | hy_r
  · exact le_rfl
  · exact h.1 y hy_l
  · exact h.2.1 y hy_r

/-- Logarithmic height condition for complete binary heaps:
height is bounded by `Nat.size (size t)`. -/
def IsLogHeight {α : Type*} (t : Tree α) : Prop :=
  t.height ≤ Nat.size t.size

end Tree

/-! ### Sift Operations Step Bounds -/

/-- Bounded step counter for sift-up operation from depth `d`. -/
def siftUpSteps (d : ℕ) : ℕ := d

/-- Sift-up steps are bounded by node depth. -/
theorem siftUpSteps_le_depth (d : ℕ) : siftUpSteps d ≤ d :=
  le_rfl

/-- For a logarithmic-height heap of size `n`, sift-up steps from depth `d ≤ height`
are bounded by `Nat.size n`. -/
theorem siftUpSteps_le_size {α : Type*} {t : Tree α} (d : ℕ)
    (hd : d ≤ t.height) (hlog : t.IsLogHeight) :
    siftUpSteps d ≤ Nat.size t.size :=
  hd.trans hlog

/-- Bounded step counter for sift-down operation on a node of height `h`.
At each level, at most 2 child comparisons are made. -/
def siftDownSteps (h : ℕ) : ℕ := 2 * h

/-- Sift-down steps on a node of height `h ≤ t.height` in a logarithmic heap
are bounded by `2 * Nat.size (size t)`. -/
theorem siftDownSteps_le_size {α : Type*} {t : Tree α} (h : ℕ)
    (hh : h ≤ t.height) (hlog : t.IsLogHeight) :
    siftDownSteps h ≤ 2 * Nat.size t.size :=
  Nat.mul_le_mul_left 2 (hh.trans hlog)

/-! ### Linear Build-Heap Theorem -/

/-- Pointwise sum bounding lemma for ranges in `ℕ`. -/
lemma sum_range_le_sum_range (f g : ℕ → ℕ) : ∀ (k : ℕ),
    (∀ i ∈ range k, f i ≤ g i) →
    ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i
  | 0, _ => by simp
  | k + 1, h => by
    rw [sum_range_succ, sum_range_succ]
    have ih := sum_range_le_sum_range f g k (fun i hi ↦ h i (by
      rw [mem_range] at hi ⊢; omega))
    have h_last := h k (by rw [mem_range]; omega)
    exact Nat.add_le_add ih h_last

/-- Helper geometric sum: `geomSum k = ∑_{h=0}^k h * 2^(k - h)`. -/
def geomSum (k : ℕ) : ℕ :=
  ∑ h ∈ range (k + 1), h * 2^(k - h)

@[simp]
theorem geomSum_zero : geomSum 0 = 0 := by
  simp [geomSum]

/-- Recurrence relation for `geomSum (k + 1) = 2 * geomSum k + (k + 1)`. -/
theorem geomSum_succ (k : ℕ) : geomSum (k + 1) = 2 * geomSum k + (k + 1) := by
  dsimp [geomSum]
  rw [sum_range_succ]
  have h_shift : ∑ x ∈ range (k + 1), x * 2 ^ (k + 1 - x) =
                 2 * ∑ x ∈ range (k + 1), x * 2 ^ (k - x) := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro x hx
    rw [mem_range] at hx
    have : k + 1 - x = (k - x) + 1 := by omega
    rw [this, pow_succ]
    ring
  rw [h_shift]
  have : k + 1 - (k + 1) = 0 := by omega
  rw [this, pow_zero, mul_one]

/-- Exact closed-form identity: `geomSum k + k + 2 = 2^(k + 1)`. -/
theorem geomSum_eq (k : ℕ) : geomSum k + k + 2 = 2^(k + 1) := by
  induction k with
  | zero => simp [geomSum_zero]
  | succ k ih =>
    rw [geomSum_succ]
    have hpow : 2^(k + 1 + 1) = 2 * 2^(k + 1) := by ring
    rw [hpow]
    omega

/-- Upper bound on the geometric sum: `geomSum k ≤ 2^(k + 1)`. -/
theorem geomSum_le (k : ℕ) : geomSum k ≤ 2^(k + 1) := by
  have h := geomSum_eq k
  omega

/-- Total operational work for linear build-heap on `n` elements with maximum
height index `k`:
$$\text{buildHeapBound}(n, k) = \sum_{h=0}^k \lfloor n / 2^h \rfloor \cdot h$$ -/
def buildHeapBound (n k : ℕ) : ℕ :=
  ∑ h ∈ range (k + 1), (n / 2^h) * h

/-- Linear build-heap theorem: for any element count `n` and height bound `k`,
the total work is bounded by `2 * n`. -/
theorem buildHeap_linear_bound (n k : ℕ) : buildHeapBound n k ≤ 2 * n := by
  rcases eq_or_ne n 0 with rfl | _
  · simp [buildHeapBound]
  have h_term : ∀ h ∈ range (k + 1),
      2^k * ((n / 2^h) * h) ≤ n * (h * 2^(k - h)) := by
    intro h hh
    rw [mem_range_succ_iff] at hh
    have hpow : 2^k = 2^h * 2^(k - h) := by
      rw [← pow_add]
      congr 1
      omega
    have hdiv : (n / 2^h) * 2^h ≤ n := Nat.div_mul_le_self n (2^h)
    calc 2^k * ((n / 2^h) * h)
      _ = ((n / 2^h) * 2^h) * (h * 2^(k - h)) := by
        rw [hpow]
        ring
      _ ≤ n * (h * 2^(k - h)) := Nat.mul_le_mul_right _ hdiv
  have h_sum : 2^k * buildHeapBound n k ≤ n * geomSum k := by
    dsimp [buildHeapBound, geomSum]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact sum_range_le_sum_range _ _ (k + 1) h_term
  have h_geom := geomSum_le k
  have h_bound : n * geomSum k ≤ 2^k * (2 * n) := by
    have : n * 2^(k + 1) = 2^k * (2 * n) := by
      rw [pow_succ]
      ring
    rw [← this]
    exact Nat.mul_le_mul_left n h_geom
  have h_comb : 2^k * buildHeapBound n k ≤ 2^k * (2 * n) := h_sum.trans h_bound
  have hpos : 0 < 2^k := by positivity
  exact Nat.le_of_mul_le_mul_left h_comb hpos

/-- Setting `k = Nat.size n` bounds build-heap work on `n` elements by `2 * n`. -/
theorem buildHeap_size_bound (n : ℕ) : buildHeapBound n (Nat.size n) ≤ 2 * n :=
  buildHeap_linear_bound n (Nat.size n)

/-! ### Heapsort Operational Complexity -/

/-- Total comparison work for extracting `n` elements from a binary heap of size `n`:
each extraction performs at most `2 * Nat.size n` child comparisons. -/
def heapsortExtractionBound (n : ℕ) : ℕ :=
  2 * n * Nat.size n

/-- Combined total operations for Heapsort on `n` elements:
linear build-heap phase plus $n$ logarithmic extractions. -/
def heapsortTotalBound (n : ℕ) : ℕ :=
  2 * n + heapsortExtractionBound n

/-- Total heapsort work is bounded by `2 * n + 2 * n * Nat.size n`. -/
theorem heapsortTotalWork_eq (n : ℕ) :
    heapsortTotalBound n = 2 * n + 2 * n * Nat.size n :=
  rfl

/-- Heapsort comparison complexity is bounded by `4 * n * Nat.size n + 2`. -/
theorem heapsortTotalWork_le (n : ℕ) :
    heapsortTotalBound n ≤ 4 * n * Nat.size n + 2 := by
  dsimp [heapsortTotalBound, heapsortExtractionBound]
  have h_le : 2 * n ≤ 2 * n * Nat.size n + 2 := by
    rcases eq_or_ne n 0 with rfl | _
    · omega
    · have hsz : 1 ≤ Nat.size n := Nat.size_pos.mpr (by omega)
      calc 2 * n = 2 * n * 1 := by ring
      _ ≤ 2 * n * Nat.size n := Nat.mul_le_mul_left (2 * n) hsz
      _ ≤ 2 * n * Nat.size n + 2 := by omega
  calc 2 * n + 2 * n * Nat.size n
    _ ≤ (2 * n * Nat.size n + 2) + 2 * n * Nat.size n := Nat.add_le_add_right h_le _
    _ = 4 * n * Nat.size n + 2 := by ring

/-! ### Extraction Correctness & Sorted Output -/

/-- Predicate that a list of elements is sorted in non-decreasing order. -/
def isSortedList {α : Type*} [Preorder α] (l : List α) : Prop :=
  List.Pairwise (· ≤ ·) l

/-- If an element `x` is `≤` all elements in a list `xs`, and `xs` is sorted,
then `x :: xs` is sorted. -/
theorem isSortedList_cons {α : Type*} [Preorder α] (x : α) (xs : List α)
    (h_le : ∀ y ∈ xs, x ≤ y) (h_sorted : isSortedList xs) :
    isSortedList (x :: xs) :=
  List.pairwise_cons.mpr ⟨h_le, h_sorted⟩

@[simp]
theorem isSortedList_nil {α : Type*} [Preorder α] : isSortedList ([] : List α) :=
  List.Pairwise.nil

@[simp]
theorem isSortedList_singleton {α : Type*} [Preorder α] (x : α) :
    isSortedList [x] :=
  List.pairwise_singleton (· ≤ ·) x

end Amort.DataStructure
