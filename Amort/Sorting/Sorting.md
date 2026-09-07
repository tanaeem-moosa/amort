# Formalization of Sorting Complexity: Insertion Sort ($O(n^2)$) and Merge Sort ($O(n \log n)$)

This document details the Lean 4 formalization of comparison counting, mathematical correctness,
concrete upper bounds, and asymptotic time complexity for Insertion Sort ($O(n^2)$) and Merge Sort
($O(n \log n)$), reusing Mathlib's sorting definitions and connecting to `Mathlib.Analysis.Asymptotics.IsBigO`.

---

## 1. Architectural Overview

The sorting complexity formalization comprises three dedicated modules under `Amort/Sorting/`:

```
Amort/
├── Amort.lean                  -- Root library export
├── GCD/                        -- Stein's Binary GCD & Euclidean GCD modules
└── Sorting/
    ├── InsertionSort.lean      -- Comparison counting, instrumented sort, triangular & O(n²) bounds
    ├── MergeSort.lean          -- Merge comparison counting, D&C recurrence, O(n * size n) bounds
    ├── Asymptotics.lean        -- Asymptotic bridges connecting concrete bounds to Mathlib IsBigO
    └── Sorting.md              -- Architectural and mathematical documentation
```

All modules are exported by `Amort.lean`.

---

## 2. Insertion Sort: Comparison Counting & $O(n^2)$ Bound (R1)

### Mathematical Model

Mathlib defines insertion sort (`List.insertionSort`) via right fold with `List.orderedInsert`:
```lean
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l

def insertionSort : List α → List α := foldr (orderedInsert r) []
```

We formalize comparison counting with two complementary representations:
1. **Direct Counters**:
   - `orderedInsertCount (r : α → α → Prop) [DecidableRel r] (a : α) : List α → ℕ`:
     Counts comparisons when inserting `a` into a list. In the base case `[]`, 0 comparisons
     are made; in the inductive case `b :: l`, 1 comparison is made between `a` and `b`, and
     if `¬ r a b`, insertion continues recursively into `l`.
   - `insertionSortCount (r : α → α → Prop) [DecidableRel r] : List α → ℕ`:
     Counts the total comparisons performed across all insertions:
     `insertionSortCount r (a :: l) = orderedInsertCount r a (insertionSort r l) + insertionSortCount r l`.

2. **Instrumented Representations**:
   - `orderedInsertWithCount (r : α → α → Prop) [DecidableRel r] (a : α) : List α → List α × ℕ`
   - `insertionSortWithCount (r : α → α → Prop) [DecidableRel r] : List α → List α × ℕ`

### Equivalence to Mathlib

We prove that the instrumented sorting functions compute the exact sorted output of Mathlib's
`List.insertionSort` and track the exact counts of `List.insertionSortCount`:
- `orderedInsertWithCount_fst`: `(orderedInsertWithCount r a l).1 = List.orderedInsert r a l`
- `orderedInsertWithCount_snd`: `(orderedInsertWithCount r a l).2 = orderedInsertCount r a l`
- `insertionSortWithCount_fst`: `(insertionSortWithCount r l).1 = List.insertionSort r l`
- `insertionSortWithCount_snd`: `(insertionSortWithCount r l).2 = insertionSortCount r l`

### Concrete Comparison Upper Bounds

1. **Single-Insertion Bound**:
   `orderedInsertCount_le`: Inserting into a list of length $k$ requires at most $k$ comparisons:
   $$\text{orderedInsertCount } r\ a\ l \le l.\text{length}$$

2. **Triangular Number Bound**:
   By Mathlib's `List.length_insertionSort`, sorting preserves list length:
   $$(\text{insertionSort } r\ l).\text{length} = l.\text{length}$$
   Therefore, inserting the $(k+1)$-th element into the sorted prefix of length $k$ takes at most $k$ comparisons.
   Summing over $k = 0, 1, \dots, n-1$:
   $$\sum_{k=0}^{n-1} k = \frac{n(n-1)}{2}$$
   In `Amort/Sorting/InsertionSort.lean`, this is formalized as:
   ```lean
   theorem insertionSortCount_le_triangular (l : List α) :
       insertionSortCount r l ≤ l.length * (l.length - 1) / 2
   ```

3. **Quadratic Bound**:
   Since $\frac{n(n-1)}{2} \le n(n-1) \le n^2$:
   ```lean
   theorem insertionSortCount_le_sq (l : List α) :
       insertionSortCount r l ≤ l.length ^ 2
   ```
   and for instrumented sort:
   ```lean
   theorem insertionSortWithCount_snd_le_sq (l : List α) :
       (insertionSortWithCount r l).2 ≤ l.length ^ 2
   ```

---

## 3. Merge Sort: Comparison Counting & $O(n \log n)$ Bound (R2)

### Mathematical Model

Lean core / Mathlib defines `List.merge` and `List.mergeSort`:
- `merge xs ys le`: Merges two sorted lists by comparing heads `le x y`.
- `mergeSort xs le`: Recursively splits `xs` via `splitInTwo` into contiguous sublists of lengths
  $(n+1)/2$ and $n/2$, sorts each recursively, and merges the results.

We define:
1. `mergeCount le xs ys`: Exact comparisons performed during merging.
2. `mergeWithCount le xs ys`: Instrumented merge returning `(merged_list, comparisons)`.
3. `mergeSortCount le xs`: Exact comparisons performed by merge sort.
4. `mergeSortWithCount le xs`: Instrumented merge sort returning `(sorted_list, comparisons)`.
5. `mergeSortRecBound (n : ℕ) : ℕ`:
   $$T(0) = 0, \quad T(1) = 0, \quad T(n+2) = T((n+3)/2) + T((n+2)/2) + (n+2)$$

### Equivalence to Mathlib & Core

We formally prove:
- `mergeWithCount_fst`: `(mergeWithCount le xs ys).1 = merge xs ys le`
- `mergeWithCount_snd`: `(mergeWithCount le xs ys).2 = mergeCount le xs ys`
- `mergeSortWithCount_fst`: `(mergeSortWithCount le xs).1 = mergeSort xs le`
- `mergeSortWithCount_snd`: `(mergeSortWithCount le xs).2 = mergeSortCount le xs`
- `mergeSortWithCount_fst_eq_insertionSort`: For total, transitive, antisymmetric relations,
  `(mergeSortWithCount (r · ·) xs).1 = insertionSort r xs`, connecting directly to
  Mathlib's `mergeSort_eq_insertionSort`.

### Concrete Comparison Upper Bounds

1. **Merge Step Bound**:
   In each comparison between `x :: xs` and `y :: ys`, at least one element is emitted to the output.
   Thus:
   ```lean
   theorem mergeCount_le (le : α → α → Bool) (xs ys : List α) :
       mergeCount le xs ys ≤ xs.length + ys.length
   ```

2. **Reduction to Divide-and-Conquer Recurrence**:
   Since `(mergeSort lr.1.1 le).length = lr.1.1.length` by `List.length_mergeSort`, the merge step
   takes at most $\text{length}(lr.1.1) + \text{length}(lr.2.1) = xs.\text{length}$ comparisons.
   Therefore, by well-founded structural induction:
   ```lean
   lemma mergeSortCount_le_recBound (le : α → α → Bool) (xs : List α) :
       mergeSortCount le xs ≤ mergeSortRecBound xs.length
   ```

3. **Power-of-Two Bounding Lemma**:
   We prove the strong induction lemma on the tree height $k \in \mathbb{N}$:
   $$\forall k \in \mathbb{N},\; \forall n \le 2^k,\; T(n) \le n \cdot k$$
   *Proof Idea*:
   - Base case $k = 0$: $n \le 2^0 = 1$, so $n = 0$ or $n = 1$, where $T(n) = 0 \le n \cdot 0$.
   - Inductive step $k+1$: For $n \le 2^{k+1}$, both subproblems satisfy:
     $$(n+1)/2 \le (2^{k+1}+1)/2 = 2^k \quad \text{and} \quad n/2 \le 2^{k+1}/2 = 2^k$$
     By the induction hypothesis:
     $$T((n+1)/2) \le ((n+1)/2) \cdot k \quad \text{and} \quad T(n/2) \le (n/2) \cdot k$$
     Summing them:
     $$T(n) \le ((n+1)/2 + n/2) \cdot k + n = n \cdot k + n = n \cdot (k + 1)$$
   In `Amort/Sorting/MergeSort.lean`:
   ```lean
   theorem mergeSortRecBound_le_mul_of_le_two_pow :
       ∀ (k : ℕ) (n : ℕ), n ≤ 2 ^ k → mergeSortRecBound n ≤ n * k
   ```

4. **Bit-Size Upper Bound**:
   By Mathlib's `Nat.lt_size_self`, $n < 2^{\text{Nat.size } n}$, so $n \le 2^{\text{Nat.size } n}$.
   Instantiating $k = \text{Nat.size } n$:
   ```lean
   theorem mergeSortRecBound_le_mul_size (n : ℕ) :
       mergeSortRecBound n ≤ n * Nat.size n

   theorem mergeSortCount_le_mul_size (le : α → α → Bool) (xs : List α) :
       mergeSortCount le xs ≤ xs.length * Nat.size xs.length

   theorem mergeSortWithCount_snd_le_mul_size (le : α → α → Bool) (xs : List α) :
       (mergeSortWithCount le xs).2 ≤ xs.length * Nat.size xs.length
   ```

---

## 4. Asymptotics Bridge to Mathlib `IsBigO` (R1, R2)

In `Amort/Sorting/Asymptotics.lean`, concrete comparison bounds are connected to Mathlib's
`Mathlib.Analysis.Asymptotics.IsBigO` framework.

### Universal Filter Bounds
Because both bounds hold pointwise with constant $c = 1$:
$$\text{insertionSortCount } r\ l \le 1 \cdot l.\text{length}^2$$
$$\text{mergeSortCount } le\ l \le 1 \cdot (l.\text{length} \cdot \text{Nat.size } l.\text{length})$$
the asymptotic relation holds with respect to *any* filter $F$ on `List α`:
- `isBigO_insertionSortCount_sq (F : Filter (List α))`
- `isBigO_mergeSortCount_mul_size (le : α → α → Bool) (F : Filter (List α))`

### Pullback Filter under `List.length` towards `Filter.atTop`
Specializing $F$ to `Filter.comap List.length Filter.atTop` yields asymptotic theorems as
input list length grows to infinity:
```lean
theorem isBigO_insertionSortCount_atTop :
    (fun l : List α ↦ ((insertionSortCount r l : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length ^ 2 : ℕ) : ℝ))

theorem isBigO_insertionSortWithCount_snd_atTop :
    (fun l : List α ↦ (((insertionSortWithCount r l).2 : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length ^ 2 : ℕ) : ℝ))

theorem isBigO_mergeSortCount_atTop (le : α → α → Bool) :
    (fun l : List α ↦ ((mergeSortCount le l : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length * Nat.size l.length : ℕ) : ℝ))

theorem isBigO_mergeSortWithCount_snd_atTop (le : α → α → Bool) :
    (fun l : List α ↦ (((mergeSortWithCount le l).2 : ℕ) : ℝ)) =O[
      Filter.comap List.length Filter.atTop]
    (fun l : List α ↦ ((l.length * Nat.size l.length : ℕ) : ℝ))
```

### Arithmetic Recurrence Asymptotics on `ℕ`
Directly on natural numbers under `Filter.atTop`:
```lean
theorem isBigO_insertionSort_triangular_atTop :
    (fun n : ℕ ↦ ((n * (n - 1) / 2 : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n ^ 2 : ℕ) : ℝ))

theorem isBigO_mergeSortRecBound_atTop :
    (fun n : ℕ ↦ ((mergeSortRecBound n : ℕ) : ℝ)) =O[Filter.atTop]
    (fun n : ℕ ↦ ((n * Nat.size n : ℕ) : ℝ))
```

---

## 5. Axiom Integrity Verification (R3)

All definitions, auxiliary lemmas, and main theorems adhere strictly to standard foundational
axioms. `#print axioms` confirms zero reliance on `sorryAx`:

| Declaration | Axioms Used | Status |
| :--- | :--- | :--- |
| `List.insertionSortCount_le_triangular` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.insertionSortCount_le_sq` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.insertionSortWithCount_fst` | `[propext]` | Clean |
| `List.insertionSortWithCount_snd` | `[propext, Quot.sound]` | Clean |
| `List.mergeSortCount_le_mul_size` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.mergeSortWithCount_fst` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.mergeSortWithCount_snd` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.mergeSortWithCount_fst_eq_insertionSort` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSortCount_sq` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSortCount_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSortWithCount_snd_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_insertionSort_triangular_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortCount_mul_size` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortCount_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortWithCount_snd_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |
| `List.isBigO_mergeSortRecBound_atTop` | `[propext, Classical.choice, Quot.sound]` | Clean |

---

## 6. Style & Linter Conformance (R3)

- **Namespacing**: Scoped under `namespace List`.
- **Classification**: `lemma` for auxiliaries (`orderedInsertCount_le`, `mergeCount_le`, `mergeSortCount_le_recBound`), `theorem` for milestones.
- **Documentation**: All public definitions and theorems documented with docstrings `/-- ... -/`.
- **Line Length**: All lines across all Lean source files $\le 100$ characters.
- **Build Status**: `lake build` succeeds with 0 errors and 0 warnings (1474 jobs).
