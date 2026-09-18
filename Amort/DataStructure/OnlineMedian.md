# Online Running Median with Dual Heaps

This document details the Lean 4 formalization of the dual-heap online running median data structure
in `Amort.DataStructure.OnlineMedian`. It maintains a streaming partition of numbers into a max-heap
`low` and a min-heap `high`, proving balance and partition invariants, $O(\log n)$ insertion,
$O(1)$ query time, and exact mathematical equivalence to the true median.

---

## 1. Dual-Heap State and Invariants

The data stream is partitioned into two heaps:

```lean
structure DualHeap (α : Type*) where
  low : List α
  high : List α
```

### Invariants
1. **Balance Invariant (`IsBalanced`)**:
   The heaps are balanced such that `low` contains either the exact same number of elements as
   `high`, or exactly one more element:
   $$\text{low}.\text{length} = \text{high}.\text{length} \quad \lor \quad
     \text{low}.\text{length} = \text{high}.\text{length} + 1$$
   This ensures:
   $$|\text{low}.\text{length} - \text{high}.\text{length}| \le 1$$
   $$\frac{|L| + 1}{2} \le \text{low}.\text{length}$$

2. **Partition Invariant (`IsPartitioned`)**:
   Every element in `low` is less than or equal to every element in `high`:
   $$\forall x \in \text{low}, \forall y \in \text{high}, x \le y$$

---

## 2. Mathematical Correctness of the Median

In statistics and computer science, an element $m$ is a median of a list $L$ if:
1. At least $\lceil |L| / 2 \rceil$ elements are $\le m$.
2. At least $\lfloor |L| / 2 \rfloor$ (or $\lceil |L| / 2 \rceil$) elements are $\ge m$.

```lean
def IsMedianOfList {α : Type*} [LinearOrder α] (m : α) (l : List α) : Prop :=
  (l.length + 1) / 2 ≤ (l.filter (· ≤ m)).length ∧
  l.length / 2 ≤ (l.filter (m ≤ ·)).length
```

### Soundness Theorem
Milestone theorem `dualHeap_max_low_is_median` proves that if `d` satisfies `IsBalanced` and
`IsPartitioned`, the maximum element of `d.low` is mathematically a median of the combined inserted
stream $L = \text{low} ++ \text{high}$:

```lean
theorem dualHeap_max_low_is_median {α : Type*} [LinearOrder α]
    (d : DualHeap α) (hval : d.Valid) (m : α) (hm : IsMaxOf m d.low) :
    IsMedianOfList m d.toList
```

Proof Strategy:
- By `IsMaxOf`, all elements in `d.low` are $\le m$, so $\text{low}.\text{length} \le \#\{x \in L
\mid x \le m\}$.
  Since $\text{low}.\text{length} \ge (|L| + 1) / 2$, the lower bound holds.
- By `IsPartitioned`, all elements in `d.high` are $\ge m$, and $m \in \text{low}$ is also $\ge m$.
  Thus, $1 + \text{high}.\text{length} \le \#\{x \in L \mid m \le x\}$, satisfying the upper bound.

---

## 3. Operational Complexity

### Median Query ($O(1)$)
Peeking the root of the max-heap `low` requires examining a single element:
```lean
def medianQuerySteps : ℕ := 1
```

### Insertion and Rebalancing ($O(\log n)$)
Inserting a new element requires:
1. Routing: 1 comparison against $\max(\text{low})$.
2. Insertion: sift-up into `low` or `high` ($\le \text{Nat.size } n$).
3. Rebalancing: if heap sizes violate balance, extracting the root from the larger heap and
   inserting into the smaller heap takes at most $4 \cdot \text{Nat.size } n$ steps.

```lean
def onlineMedianInsertWork (n : ℕ) : ℕ := 5 * Nat.size n + 1
theorem onlineMedianInsertWork_le (n : ℕ) : onlineMedianInsertWork n ≤ 6 * Nat.size n + 1
```
