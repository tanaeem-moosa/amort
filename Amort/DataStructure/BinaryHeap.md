# Priority Queues & Binary Heaps

> **Status: stub — not verified** (Phase 3 canon stub; build-heap summation is proven,
> but array heap siftUp/siftDown operations are specification stubs).


This document details the Lean 4 formalization of priority queues and binary heaps in
`Amort.DataStructure.BinaryHeap`, covering the min-heap order invariant, logarithmic height,
sift-down and sift-up step bounds, the linear build-heap theorem, and heapsort complexity.

---

## 1. Tree Representation & Invariants

A binary heap is represented as an inductive binary tree:

```lean
inductive Tree (α : Type*) where
  | nil : Tree α
  | node (val : α) (left : Tree α) (right : Tree α) : Tree α
```

### Min-Heap Order Invariant
The min-heap property requires the root value of every subtree to be less than or equal to all
elements in both its left and right subtrees:

```lean
def IsMinHeap {α : Type*} [Preorder α] : Tree α → Prop
  | nil => True
  | node v l r =>
      (∀ y ∈ l.toList, v ≤ y) ∧ (∀ y ∈ r.toList, v ≤ y) ∧
      IsMinHeap l ∧ IsMinHeap r
```

Milestone theorem `min_heap_root_le` proves that the root of a valid min-heap is minimal across all
elements in the entire heap:
```lean
theorem min_heap_root_le {α : Type*} [Preorder α] (v : α) (l r : Tree α)
    (h : (node v l r).IsMinHeap) (y : α) (hy : y ∈ (node v l r).toList) : v ≤ y
```

### Logarithmic Height
For complete binary heaps of size $n$, the height is bounded by `Nat.size n`:
```lean
def IsLogHeight {α : Type*} (t : Tree α) : Prop :=
  t.height ≤ Nat.size t.size
```

---

## 2. Sift Operations & Step Counting

### Sift-Up
When an element is inserted at depth $d$, `siftUp` traverses towards the root, executing at most $d$
comparisons and swaps:
```lean
def siftUpSteps (d : ℕ) : ℕ := d
theorem siftUpSteps_le_size {α : Type*} {t : Tree α} (d : ℕ)
    (hd : d ≤ t.height) (hlog : t.IsLogHeight) :
    siftUpSteps d ≤ Nat.size t.size
```

### Sift-Down
When restoring heap order at a node of height $h$, `siftDown` descends towards the leaves,
performing
at most 2 child comparisons per level:
```lean
def siftDownSteps (h : ℕ) : ℕ := 2 * h
theorem siftDownSteps_le_size {α : Type*} {t : Tree α} (h : ℕ)
    (hh : h ≤ t.height) (hlog : t.IsLogHeight) :
    siftDownSteps h ≤ 2 * Nat.size t.size
```

---

## 3. Linear Build-Heap Theorem

In textbook algorithms (CLRS Chapter 6), `buildHeap` invokes `siftDown` bottom-up on all internal
nodes. A node at height $h$ takes at most $h$ operations. Since there are at most $\lfloor n / 2^h
\rfloor$
nodes at height $h$, the total work is:
$$\text{buildHeapWork}(n, k) = \sum_{h=0}^k \left\lfloor \frac{n}{2^h} \right\rfloor \cdot h$$

We formalize this via the geometric sum identity:
$$\text{geomSum}(k) = \sum_{h=0}^k h \cdot 2^{k-h}$$

We prove:
1. Recurrence: `geomSum (k + 1) = 2 * geomSum k + (k + 1)`.
2. Exact closed form: `geomSum k + k + 2 = 2^(k + 1)`.
3. Upper bound: `geomSum k ≤ 2^(k + 1)`.
4. Milestone Linear Bound:
   $$\text{buildHeapWork}(n, k) \le 2n$$
   ```lean
   theorem buildHeap_linear_bound (n k : ℕ) : buildHeapWork n k ≤ 2 * n
   theorem buildHeap_size_bound (n : ℕ) : buildHeapWork n (Nat.size n) ≤ 2 * n
   ```

---

## 4. Heapsort Complexity and Correctness

Heapsort consists of:
1. Linear build-heap phase: $\le 2n$ operations.
2. Extraction phase: $n$ extractions, each executing at most $2 \cdot \text{Nat.size } n$
comparisons.

```lean
def heapsortExtractionWork (n : ℕ) : ℕ := 2 * n * Nat.size n
def heapsortTotalWork (n : ℕ) : ℕ := 2 * n + heapsortExtractionWork n
theorem heapsortTotalWork_le (n : ℕ) : heapsortTotalWork n ≤ 4 * n * Nat.size n + 2
```

Milestone theorem `isSortedList_cons` confirms that repeatedly extracting the minimal element from
a min-heap yields a non-decreasing sorted list (`List.Pairwise (· ≤ ·)`).
